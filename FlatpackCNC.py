import adsk.core, adsk.fusion, traceback, math, os, random, time, json

ATTR_GROUP = 'FlatpackCNC'
ATTR_ITEMS = 'PartList'          # JSON list of the parts, stored on the design
COMP_NAME = 'Flatpack CNC'
CMD_MAIN = 'flatpackMainCmd'
CMD_LABEL = 'flatpackLabelCmd'
CMD_BUILD = 'flatpackBuildCmd'
CMD_CLEAR = 'flatpackClearCmd'
CMD_SHOW = 'flatpackShowCmd'
PANEL_ID = 'SolidScriptsAddinsPanel'      # Utilities > Add-Ins
MODIFY_PANEL_ID = 'SolidModifyPanel'      # Design > Modify
OWN_PANEL_ID = 'FlatpackCNCPanel'         # old versions only (cleaned up)

app = adsk.core.Application.get()
ui = app.userInterface
handlers = []          # keep handler references alive


# ---------------------------------------------------------------- helpers
def get_design():
    return adsk.fusion.Design.cast(app.activeProduct)


def face_frame(face, align_edge=True):
    """Origin, X, Y, Z (unit) of a local frame: Z = outward face normal,
    X = longest straight outer edge (projected into the face plane)."""
    pt = face.pointOnFace
    _, n = face.evaluator.getNormalAtPoint(pt)
    n.normalize()

    x = None
    if align_edge:
        best = 0.0
        for loop in face.loops:
            if not loop.isOuter:
                continue
            for e in loop.edges:
                if isinstance(e.geometry, adsk.core.Line3D) and e.length > best:
                    a, b = e.startVertex.geometry, e.endVertex.geometry
                    best = e.length
                    x = adsk.core.Vector3D.create(b.x - a.x, b.y - a.y, b.z - a.z)
    if x is not None:
        d = x.dotProduct(n)
        x = adsk.core.Vector3D.create(x.x - d * n.x, x.y - d * n.y, x.z - d * n.z)
        if x.length < 1e-9:
            x = None
    if x is None:
        helper = adsk.core.Vector3D.create(1, 0, 0)
        if abs(n.dotProduct(helper)) > 0.9:
            helper = adsk.core.Vector3D.create(0, 1, 0)
        x = n.crossProduct(helper)
    x.normalize()
    y = n.crossProduct(x)
    y.normalize()
    return pt, x, y, n


def translation(dx, dy, dz):
    m = adsk.core.Matrix3D.create()
    m.translation = adsk.core.Vector3D.create(dx, dy, dz)
    return m


# ---------------------------------------------------------------- part list
# Each entry: {'uid', 'token' (entity token of the face or body picked), 'body' (token of
# the body), 'kind' ('body' | 'face'), 'name' (body name), 'copies'}
items = []
uid_counter = [0]


def _entity(token, cls):
    try:
        for ent in get_design().findEntityByToken(token):
            e = cls.cast(ent)
            if e:
                return e
    except:
        pass
    return None


def _entity_for_item(it):
    if it['kind'] == 'face':
        return _entity(it['token'], adsk.fusion.BRepFace)
    return _entity(it['token'], adsk.fusion.BRepBody)


def _new_uid():
    uid_counter[0] += 1
    return uid_counter[0]


def persist_items():
    """Remember the part list inside the design so it survives closing the dialog / file."""
    try:
        design = get_design()
        data = json.dumps([{k: it[k] for k in ('token', 'body', 'kind', 'name', 'copies')}
                           for it in items])
        a = design.attributes.itemByName(ATTR_GROUP, ATTR_ITEMS)
        if a:
            a.value = data
        else:
            design.attributes.add(ATTR_GROUP, ATTR_ITEMS, data)
    except:
        pass


def load_items():
    try:
        a = get_design().attributes.itemByName(ATTR_GROUP, ATTR_ITEMS)
        if not a:
            return
        for d in json.loads(a.value):
            d['uid'] = _new_uid()
            items.append(d)
    except:
        pass


def validate_items():
    """Drop entries whose face/body no longer exists, refresh names."""
    for it in list(items):
        e = _entity_for_item(it)
        if e is None:
            items.remove(it)
        else:
            body = e.body if it['kind'] == 'face' else e
            it['name'] = body.name


def best_face(body):
    """Largest planar face: the natural 'top' of a panel-like part."""
    best, area = None, 0.0
    for f in body.faces:
        if f.geometry.surfaceType == adsk.core.SurfaceTypes.PlaneSurfaceType and f.area > area:
            best, area = f, f.area
    return best


def resolve_items():
    """[{'body', 'face' (None = free orientation), 'copies', 'name'}] for the build."""
    jobs = []
    for it in items:
        e = _entity_for_item(it)
        if e is None:
            continue
        if it['kind'] == 'face':
            jobs.append({'body': e.body, 'face': e, 'copies': it['copies'], 'name': e.body.name})
        else:
            jobs.append({'body': e, 'face': None, 'copies': it['copies'], 'name': e.name})
    return jobs


# ---------------------------------------------------------------- step 2: build
def _hull(pts):
    pts = sorted(set(pts))
    if len(pts) < 3:
        return pts
    def cross(o, a, b):
        return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lo = []
    for p in pts:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0:
            lo.pop()
        lo.append(p)
    up = []
    for p in reversed(pts):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 0:
            up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]


def _min_rect_angle(pts):
    """Angle (radians) that turns the point set into its smallest bounding rectangle,
    with the long side along X."""
    h = _hull(pts)
    if len(h) < 3:
        return 0.0
    best = None
    for i in range(len(h)):
        x1, y1 = h[i]
        x2, y2 = h[(i + 1) % len(h)]
        a = math.atan2(y2 - y1, x2 - x1)
        c, sn = math.cos(-a), math.sin(-a)
        xs = [c*px - sn*py for px, py in h]
        ys = [sn*px + c*py for px, py in h]
        w, hh = max(xs) - min(xs), max(ys) - min(ys)
        area = w * hh
        if best is None or area < best[0] - 1e-12:
            best = (area, a, w, hh)
    _, a, w, hh = best
    return a + math.pi / 2 if hh > w else a


def _body_points_2d(body, origin, x, y):
    try:
        calc = body.meshManager.createMeshCalculator()
        calc.setQuality(adsk.fusion.TriangleMeshQualityOptions.LowQualityTriangleMesh)
        c = calc.calculate().nodeCoordinatesAsDouble
        pts = []
        for k in range(0, len(c), 3):
            d = (c[k]-origin.x, c[k+1]-origin.y, c[k+2]-origin.z)
            pts.append((d[0]*x.x + d[1]*x.y + d[2]*x.z,
                        d[0]*y.x + d[1]*y.y + d[2]*y.z))
        return pts
    except:
        return []


def _contains(a, b, eps=1e-9):
    return (b[0] >= a[0]-eps and b[1] >= a[1]-eps and
            b[0]+b[2] <= a[0]+a[2]+eps and b[1]+b[3] <= a[1]+a[3]+eps)


def _maxrects_fill(items, W, H, gap, allow_rot, mode):
    """MaxRects bin packing that skips any part that no longer fits.
    items = [(idx, w, h)]. Returns ({idx: (x, y, rotated)}, free rectangles)."""
    eps = 1e-9
    free = [[0.0, 0.0, W + gap, H + gap]]
    out = {}
    for idx, w, h in items:
        best = None
        for fx, fy, fw, fh in free:
            for rot in ((False, True) if allow_rot else (False,)):
                rw, rh = (h + gap, w + gap) if rot else (w + gap, h + gap)
                if rw <= fw + eps and rh <= fh + eps:
                    dw, dh = fw - rw, fh - rh
                    if mode == 'bssf':
                        sc = (min(dw, dh), max(dw, dh))
                    elif mode == 'baf':
                        sc = (fw*fh - rw*rh, min(dw, dh))
                    else:
                        sc = (fy + rh, fx)
                    if best is None or sc < best[0]:
                        best = (sc, fx, fy, rw, rh, rot)
        if best is None:
            continue
        _, px, py, rw, rh, rot = best
        out[idx] = (px, py, rot)
        new = []
        for r in free:
            fx, fy, fw, fh = r
            if px >= fx+fw-eps or px+rw <= fx+eps or py >= fy+fh-eps or py+rh <= fy+eps:
                new.append(r)
                continue
            if px > fx + eps:
                new.append([fx, fy, px - fx, fh])
            if px + rw < fx + fw - eps:
                new.append([px + rw, fy, fx + fw - px - rw, fh])
            if py > fy + eps:
                new.append([fx, fy, fw, py - fy])
            if py + rh < fy + fh - eps:
                new.append([fx, py + rh, fw, fy + fh - py - rh])
        free = [r for i, r in enumerate(new)
                if not any(j != i and _contains(new[j], r) and (new[j] != r or j < i)
                           for j in range(len(new)))]
    return out, free


def _fill_sheet(parts, idxs, W, H, gap, allow_rot):
    """Fill one sheet as fully as possible from the parts in idxs.
    Many orderings x 3 placement rules are tried; the best layout is the one that
    (1) places the most part area and then (2) leaves the single largest free block,
    so the waste stays together. Returns {global idx: (x, y, rotated)}."""
    rng = random.Random(12345)
    keys = [
        lambda i: -(parts[i]['w'] * parts[i]['h']),
        lambda i: -max(parts[i]['w'], parts[i]['h']),
        lambda i: -parts[i]['w'],
        lambda i: -parts[i]['h'],
        lambda i: -(parts[i]['w'] + parts[i]['h']),
    ]
    orders = [sorted(idxs, key=k) for k in keys]
    for _ in range(40 if len(idxs) > 1 else 0):
        o = list(idxs)
        rng.shuffle(o)
        orders.append(o)
    best = None
    for order in orders:
        items = [(i, parts[i]['w'], parts[i]['h']) for i in order]
        for mode in ('bssf', 'baf', 'bl'):
            out, free = _maxrects_fill(items, W, H, gap, allow_rot, mode)
            if not out:
                continue
            area = sum(parts[i]['w'] * parts[i]['h'] for i in out)
            largest = max((r[2] * r[3] for r in free), default=0.0)
            score = (round(area, 6), largest)
            if best is None or score > best[0]:
                best = (score, out)
    return best[1] if best else {}


def _pack_all(parts, allidx, W, H, gap, allow_rot, time_limit=6.0, progress=None):
    """Pack every part onto as FEW sheets as possible, and make the earlier sheets as
    full as possible so the waste ends up on the LAST sheet as one big block.
    Searches many whole-job orderings (not sheet by sheet), scoring each by
    (number of sheets, part area on the last sheet - lower is better, largest
    free block on the last sheet - higher is better).
    Returns [ {global idx: (x, y, rotated)} per sheet ] or None."""
    area = lambda i: parts[i]['w'] * parts[i]['h']
    rng = random.Random(777)
    modes = ('bssf', 'baf', 'bl')

    def run(order, mode):
        remaining = list(order)
        sheets, frees = [], []
        while remaining:
            items = [(i, parts[i]['w'], parts[i]['h']) for i in remaining]
            out, free = _maxrects_fill(items, W, H, gap, allow_rot, mode)
            if not out:
                return None
            sheets.append(out)
            frees.append(free)
            remaining = [i for i in remaining if i not in out]
        # fullest sheets first, emptiest (the one with the waste) last
        used = [sum(area(i) for i in sh) for sh in sheets]
        k = used.index(min(used))
        sheets.append(sheets.pop(k))
        used.append(used.pop(k))
        last_free = frees.pop(k)
        largest = max((r[2] * r[3] for r in last_free), default=0.0)
        return (len(sheets), round(used[-1], 6), -largest), sheets

    keys = [lambda i: -area(i),
            lambda i: -max(parts[i]['w'], parts[i]['h']),
            lambda i: -parts[i]['w'], lambda i: -parts[i]['h'],
            lambda i: -(parts[i]['w'] + parts[i]['h'])]
    best = None

    def consider(order):
        nonlocal best
        for mode in modes:
            r = run(order, mode)
            if r and (best is None or r[0] < best[0]):
                best = r
                best_order[0] = list(order)

    best_order = [None]
    for k in keys:
        consider(sorted(allidx, key=k))
    t0 = time.time()
    # random restarts + hill climbing (swap / move) from the best order found
    while time.time() - t0 < time_limit and len(allidx) > 1:
        if progress:
            progress(min(1.0, (time.time() - t0) / time_limit))
        if best_order[0] is not None and rng.random() < 0.7:
            o = list(best_order[0])
            a, b = rng.randrange(len(o)), rng.randrange(len(o))
            if rng.random() < 0.5:
                o[a], o[b] = o[b], o[a]
            else:
                o.insert(b, o.pop(a))
        else:
            o = list(allidx)
            rng.shuffle(o)
        consider(o)
    return best[1] if best else None


class _Cancelled(Exception):
    pass


class _Progress:
    """Progress dialog with a Cancel button. set() raises _Cancelled if pressed."""
    def __init__(self):
        self.pd = None
        self.last = 0.0
        try:
            self.pd = ui.createProgressDialog()
            self.pd.isBackgroundTranslucent = False
            self.pd.cancelButtonText = 'Cancel'
            self.pd.show('Flatpack CNC', 'Starting...  %p%', 0, 100, 0)
            adsk.doEvents()
        except:
            self.pd = None

    def set(self, pct, msg=None, force=False):
        if not self.pd:
            return
        now = time.time()
        if not force and now - self.last < 0.1:
            return                      # throttle UI updates
        self.last = now
        try:
            self.pd.progressValue = max(0, min(100, int(pct)))
            if msg:
                self.pd.message = msg + '   %p%'
            adsk.doEvents()
            cancelled = self.pd.wasCancelled
        except:
            return
        if cancelled:
            raise _Cancelled()

    def hide(self):
        try:
            if self.pd:
                self.pd.hide()
        except:
            pass
        self.pd = None

    def msg(self, text):
        self.hide()
        ui.messageBox(text)


def _cut(free, px, py, rw, rh):
    """Remove the rectangle (px,py,rw,rh) from a MaxRects free list."""
    eps = 1e-9
    new = []
    for r in free:
        fx, fy, fw, fh = r
        if px >= fx+fw-eps or px+rw <= fx+eps or py >= fy+fh-eps or py+rh <= fy+eps:
            new.append(r)
            continue
        if px > fx + eps:
            new.append([fx, fy, px - fx, fh])
        if px + rw < fx + fw - eps:
            new.append([px + rw, fy, fx + fw - px - rw, fh])
        if py > fy + eps:
            new.append([fx, fy, fw, py - fy])
        if py + rh < fy + fh - eps:
            new.append([fx, py + rh, fw, fy + fh - py - rh])
    return [r for i, r in enumerate(new)
            if not any(j != i and _contains(new[j], r) and (new[j] != r or j < i)
                       for j in range(len(new)))]


def _unnest_to_free_space(parts, sheets, W, H, gap, allow_rot):
    """Parts that were tucked into a big part's cutout are moved out again onto
    another sheet's free space when they fit there. Cutouts are scrap anyway, and this
    leaves the host sheet with just the big part. sheets = [(idxs, {j: (x,y,rot)})]
    is edited in place. Returns the number of parts moved."""
    if len(sheets) < 2:
        return 0
    eps = 1e-9
    frees = []
    for idxs, lay in sheets:
        fr = [[0.0, 0.0, W + gap, H + gap]]
        for j, i in enumerate(idxs):
            px, py, rot = lay[j]
            w, h = parts[i]['w'], parts[i]['h']
            rw, rh = (h + gap, w + gap) if rot else (w + gap, h + gap)
            fr = _cut(fr, px, py, rw, rh)
        frees.append(fr)
    moved = 0
    kids = []
    for sn, (idxs, lay) in enumerate(sheets):
        for i in idxs:
            for c, k, sx, sy in parts[i]['children']:
                kids.append((sn, i, c))
    kids.sort(key=lambda t: -(parts[t[2]]['w'] * parts[t[2]]['h']))
    for host_sn, host, c in kids:
        p = parts[c]
        best = None
        for sn in range(len(sheets)):
            if sn == host_sn:
                continue
            for fx, fy, fw, fh in frees[sn]:
                for rot in ((False, True) if allow_rot else (False,)):
                    rw, rh = (p['h'] + gap, p['w'] + gap) if rot else (p['w'] + gap, p['h'] + gap)
                    if rw <= fw + eps and rh <= fh + eps:
                        sc = (min(fw - rw, fh - rh), max(fw - rw, fh - rh))
                        if best is None or sc < best[0]:
                            best = (sc, sn, fx, fy, rw, rh, rot)
        if best is None:
            continue
        _, sn, fx, fy, rw, rh, rot = best
        frees[sn] = _cut(frees[sn], fx, fy, rw, rh)
        parts[host]['children'] = [t for t in parts[host]['children'] if t[0] != c]
        p['parent'] = None
        sheets[sn][0].append(c)
        sheets[sn][1][len(sheets[sn][0]) - 1] = (fx, fy, rot)
        moved += 1
    return moved


def _child_offset(p, k, tx, ty):
    if k == 0:
        return tx, ty
    if k == 1:
        return p['h'] + tx, ty
    if k == 2:
        return p['w'] + tx, p['h'] + ty
    return tx, p['w'] + ty


def _renest_bottom_left(parts, sheets, gap):
    """Re-seat the nested parts inside each host so they sit as far towards the
    sheet's bottom-left as the cutouts allow (measured on the finished sheet)."""
    for idxs, lay in sheets:
        for j, hi in enumerate(idxs):
            host = parts[hi]
            if not host['children'] or not host.get('mesh'):
                continue
            rot = lay[j][2]
            try:
                hs = _Host(host, gap, hi)
                key = (lambda x, y: x - y) if rot else (lambda x, y: x + y)
                kids = sorted((c for c, _, _, _ in host['children']),
                              key=lambda c: -(parts[c]['w'] * parts[c]['h']))
                new = []
                for c in kids:
                    p = parts[c]
                    best = None
                    for k in (0, 1, 2, 3):
                        rows, runs, wc, hc, wk, hk = hs.child_raster(p, k)
                        pos = hs.find(rows, runs, wc, hc, key)
                        if pos is None:
                            continue
                        kv = key(*pos)
                        if best is None or kv < best[0]:
                            best = (kv, k, pos, rows, wc)
                    if best is None:
                        raise ValueError('no spot')
                    _, k, (gx, gy), rows, wc = best
                    hs.stamp(rows, wc, gx, gy)
                    sx, sy = _child_offset(p, k, gx * hs.cell, gy * hs.cell)
                    new.append((c, k, sx, sy))
                host['children'] = new
            except _Cancelled:
                raise
            except:
                pass                                   # keep the earlier arrangement


def _compact_bottom_left(parts, sheets, gap):
    """Slide every part on every sheet left, then down, until nothing can move."""
    eps = 1e-9
    for idxs, lay in sheets:
        rects = []
        for j, i in enumerate(idxs):
            px, py, rot = lay[j]
            w, h = parts[i]['w'], parts[i]['h']
            rw, rh = (h + gap, w + gap) if rot else (w + gap, h + gap)
            rects.append([px, py, rw, rh])
        for _ in range(60):
            moved = False
            for a in sorted(range(len(rects)), key=lambda q: (rects[q][0], rects[q][1])):
                x, y, rw, rh = rects[a]
                nx = 0.0
                for b, (bx, by, bw, bh) in enumerate(rects):
                    if b != a and by < y + rh - eps and by + bh > y + eps and bx + bw <= x + eps:
                        nx = max(nx, bx + bw)
                if nx < x - 1e-7:
                    rects[a][0] = nx
                    moved = True
                x = rects[a][0]
                ny = 0.0
                for b, (bx, by, bw, bh) in enumerate(rects):
                    if b != a and bx < x + rw - eps and bx + bw > x + eps and by + bh <= y + eps:
                        ny = max(ny, by + bh)
                if ny < y - 1e-7:
                    rects[a][1] = ny
                    moved = True
            if not moved:
                break
        for j in range(len(idxs)):
            lay[j] = (rects[j][0], rects[j][1], lay[j][2])


# ---------------------------------------------------------------- nesting into cutouts
# Each part's real outline (its projected mesh triangles) is rasterised onto a grid. Smaller
# parts are then placed inside the holes / notches of larger ones, so they share the larger
# part's rectangle instead of using fresh sheet area.
def _body_mesh_2d(body, origin, x, y, mnx, mny):
    """Triangles of the body projected onto the part's flat frame (same frame as the copy)."""
    try:
        calc = body.meshManager.createMeshCalculator()
        try:
            calc.surfaceTolerance = 0.03
        except:
            calc.setQuality(adsk.fusion.TriangleMeshQualityOptions.NormalQualityTriangleMesh)
        mesh = calc.calculate()
        c = mesh.nodeCoordinatesAsDouble
        idx = mesh.nodeIndices
        pts = []
        for k in range(0, len(c), 3):
            d = (c[k]-origin.x, c[k+1]-origin.y, c[k+2]-origin.z)
            pts.append((d[0]*x.x + d[1]*x.y + d[2]*x.z - mnx,
                        d[0]*y.x + d[1]*y.y + d[2]*y.z - mny))
        tris = [(idx[k], idx[k+1], idx[k+2]) for k in range(0, len(idx) - 2, 3)]
        return pts, tris
    except:
        return None


def _rot_pts(pts, k):
    if k == 0:
        r = pts
    elif k == 1:
        r = [(-y, x) for x, y in pts]
    elif k == 2:
        r = [(-x, -y) for x, y in pts]
    else:
        r = [(y, -x) for x, y in pts]
    mx = min(p[0] for p in r)
    my = min(p[1] for p in r)
    return [(x - mx, y - my) for x, y in r], mx, my


def _raster(pts, tris, cell, wc, hc):
    """Row bitmasks (bit x of rows[y] set = cell covered) of the projected triangles."""
    rows = [0] * hc
    full = (1 << wc) - 1
    eps = 1e-9
    for a, b, c in tris:
        p0, p1, p2 = pts[a], pts[b], pts[c]
        ymin = min(p0[1], p1[1], p2[1])
        ymax = max(p0[1], p1[1], p2[1])
        r0 = max(0, int(math.ceil(ymin / cell - 0.5 - eps)))
        r1 = min(hc - 1, int(math.floor(ymax / cell - 0.5 + eps)))
        for r in range(r0, r1 + 1):
            yc = (r + 0.5) * cell
            xs = []
            for (xa, ya), (xb, yb) in ((p0, p1), (p1, p2), (p2, p0)):
                if (ya - yc) * (yb - yc) <= 0 and ya != yb:
                    xs.append(xa + (xb - xa) * (yc - ya) / (yb - ya))
            if len(xs) < 2:
                continue
            c0 = max(0, int(math.ceil(min(xs) / cell - 0.5 - eps)))
            c1 = min(wc - 1, int(math.floor(max(xs) / cell - 0.5 + eps)))
            if c1 >= c0:
                rows[r] |= (((1 << (c1 - c0 + 1)) - 1) << c0) & full
    return rows


def _dilate(rows, r, wc):
    """Grow every set cell by r cells in all directions (square)."""
    full = (1 << wc) - 1
    h = []
    for m in rows:
        d = m
        for _ in range(r):
            d |= (d << 1) | (d >> 1)
        h.append(d & full)
    n = len(h)
    out = [0] * n
    for y in range(n):
        v = 0
        for k in range(max(0, y - r), min(n, y + r + 1)):
            v |= h[k]
        out[y] = v
    return out


def _runs(m):
    """[(start, length)] of the runs of set bits in m."""
    res = []
    pos = 0
    while m:
        low = (m & -m).bit_length() - 1
        m >>= low
        pos += low
        ln = ((~m) & (m + 1)).bit_length() - 1      # number of trailing ones
        res.append((pos, ln))
        m >>= ln
        pos += ln
    return res


class _Host:
    def __init__(self, part, gap, idx):
        self.part = part
        self.idx = idx
        w, h = part['w'], part['h']
        self.cell = max(0.1, max(w, h) / 600.0)
        self.wc = int(math.ceil(w / self.cell)) + 1
        self.hc = int(math.ceil(h / self.cell)) + 1
        self.r = int(math.ceil(gap / self.cell)) + 1
        pts, tris = part['mesh']
        self.full = (1 << self.wc) - 1
        self.occ = _dilate(_raster(pts, tris, self.cell, self.wc, self.hc), self.r, self.wc)
        self.memo = {}
        self.rcache = {}

    def free(self, y):
        return ~self.occ[y] & self.full

    def runfree(self, y, ln):
        key = (y, ln)
        v = self.memo.get(key)
        if v is None:
            v = self.free(y)
            have = 1
            while have < ln:
                step = min(have, ln - have)
                v &= (v >> step)
                have += step
            self.memo[key] = v
        return v

    def child_raster(self, child, k):
        key = (id(child), k)
        r = self.rcache.get(key)
        if r is None:
            pts, tris = child['mesh']
            rp, _, _ = _rot_pts(pts, k)
            wk = max(p[0] for p in rp)
            hk = max(p[1] for p in rp)
            wc = int(math.ceil(wk / self.cell)) + 1
            hc = int(math.ceil(hk / self.cell)) + 1
            rows = _raster(rp, tris, self.cell, wc, hc)
            runs = [_runs(m) for m in rows]
            r = (rows, runs, wc, hc, wk, hk)
            self.rcache[key] = r
        return r

    def find(self, rows, runs, wc, hc, key=None):
        """First free spot (lowest y, then x), or with key(x, y) the spot minimising it."""
        if wc > self.wc or hc > self.hc:
            return None
        xlim = (1 << (self.wc - wc + 1)) - 1
        bestpos = None
        for y in range(0, self.hc - hc + 1):
            valid = xlim
            for rr in range(hc):
                for s, ln in runs[rr]:
                    valid &= self.runfree(y + rr, ln) >> s
                    if not valid:
                        break
                if not valid:
                    break
            if valid:
                x = (valid & -valid).bit_length() - 1
                if key is None:
                    return x, y
                kv = key(x, y)
                if bestpos is None or kv < bestpos[0]:
                    bestpos = (kv, x, y)
        return (bestpos[1], bestpos[2]) if bestpos else None

    def stamp(self, rows, wc, gx, gy):
        r = self.r
        padded = [0] * r + [m << r for m in rows] + [0] * r
        dil = _dilate(padded, r, wc + 2 * r)
        for t, row in enumerate(dil):
            yy = gy - r + t
            if 0 <= yy < self.hc:
                self.occ[yy] |= ((row << gx) >> r) & self.full
        self.memo.clear()


def _nest_parts(parts, gap, progress=None):
    """Move small parts into cutouts of larger ones. Fills parts[i]['parent'/'children']."""
    order = sorted(range(len(parts)), key=lambda i: -(parts[i]['w'] * parts[i]['h']))
    hosts = []
    nested = 0
    for step, i in enumerate(order):
        if progress:
            progress(step, len(order))
        p = parts[i]
        if not p.get('mesh'):
            continue
        placed = False
        for hs in hosts:
            hp = hs.part
            big, small = max(p['w'], p['h']), min(p['w'], p['h'])
            if big > max(hp['w'], hp['h']) + 1e-9 or small > min(hp['w'], hp['h']) + 1e-9:
                continue
            for k in (0, 1, 2, 3):
                rows, runs, wc, hc, wk, hk = hs.child_raster(p, k)
                pos = hs.find(rows, runs, wc, hc)
                if pos is None:
                    continue
                gx, gy = pos
                hs.stamp(rows, wc, gx, gy)
                tx, ty = gx * hs.cell, gy * hs.cell
                if k == 0:
                    sx, sy = tx, ty
                elif k == 1:
                    sx, sy = p['h'] + tx, ty
                elif k == 2:
                    sx, sy = p['w'] + tx, p['h'] + ty
                else:
                    sx, sy = tx, p['w'] + ty
                p['parent'] = hs.idx
                hp['children'].append((i, k, sx, sy))
                nested += 1
                placed = True
                break
            if placed:
                break
        if not placed:
            hosts.append(_Host(p, gap, i))
    return nested


def build_flatpack(gap, margin, max_width, max_depth, auto_orient, allow_rot, multi):
    pd = _Progress()
    try:
        _build_flatpack(pd, gap, margin, max_width, max_depth, auto_orient, allow_rot, multi)
    except _Cancelled:
        pd.hide()
        ui.messageBox('Build cancelled.')
    finally:
        pd.hide()


def _build_flatpack(pd, gap, margin, max_width, max_depth, auto_orient, allow_rot, multi):
    design = get_design()
    root = design.rootComponent
    um = design.unitsManager
    fmt = lambda v: um.formatInternalValue(v, um.defaultLengthUnits, True)

    jobs = resolve_items()
    if not jobs:
        pd.msg('The part list is empty. Pick some bodies or faces first.')
        return

    tbm = adsk.fusion.TemporaryBRepManager.get()
    parts = []

    # copy each body (once per requested copy), point its top face up (+Z), put the
    # opposite side on Z = 0 and turn it in-plane to its tightest bounding rectangle.
    # A picked face is the top face. A picked body uses its largest flat face as the top,
    # so it can lie any way up in the model.
    for n, job in enumerate(jobs):
        body, face = job['body'], job['face']
        pd.set(2 + 28.0 * n / len(jobs), 'Reading part %d of %d: %s' % (n + 1, len(jobs), body.name))
        if face is None:
            face = best_face(body)
        if face is not None:
            origin, x, y, z = face_frame(face, True)
        else:
            origin = body.boundingBox.minPoint
            x = adsk.core.Vector3D.create(1, 0, 0)
            y = adsk.core.Vector3D.create(0, 1, 0)
            z = adsk.core.Vector3D.create(0, 0, 1)
        if auto_orient:
            pts = _body_points_2d(body, origin, x, y)
            if pts:
                a = _min_rect_angle(pts)
                c, sn = math.cos(a), math.sin(a)
                nx = adsk.core.Vector3D.create(c*x.x + sn*y.x, c*x.y + sn*y.y, c*x.z + sn*y.z)
                nx.normalize()
                ny = z.crossProduct(nx)
                ny.normalize()
                x, y = nx, ny
        m = adsk.core.Matrix3D.create()
        m.setToAlignCoordinateSystems(
            origin, x, y, z,
            adsk.core.Point3D.create(0, 0, 0),
            adsk.core.Vector3D.create(1, 0, 0),
            adsk.core.Vector3D.create(0, 1, 0),
            adsk.core.Vector3D.create(0, 0, 1))
        mesh = None
        for cn in range(max(1, job['copies'])):
            tmp = tbm.copy(body)
            tbm.transform(tmp, m)
            bb = tmp.boundingBox
            mnx, mny = bb.minPoint.x, bb.minPoint.y
            tbm.transform(tmp, translation(-bb.minPoint.x, -bb.minPoint.y, -bb.minPoint.z))
            bb = tmp.boundingBox
            if cn == 0 and auto_orient:
                mesh = _body_mesh_2d(body, origin, x, y, mnx, mny)
            nm = job['name'] + ('_%d' % (cn + 1) if job['copies'] > 1 else '')
            parts.append({'name': nm, 'tmp': tmp, 'mesh': mesh, 'parent': None,
                          'children': [], 'w': bb.maxPoint.x, 'h': bb.maxPoint.y})

    # usable area inside the edge margin
    uw, uh = max_width - 2 * margin, max_depth - 2 * margin
    if uw <= 0 or uh <= 0:
        pd.msg('The edge margin is too large for the sheet size. Nothing was created.')
        return

    def fits_alone(p):
        ok = p['w'] <= uw + 1e-9 and p['h'] <= uh + 1e-9
        if allow_rot:
            ok = ok or (p['h'] <= uw + 1e-9 and p['w'] <= uh + 1e-9)
        return ok
    too_big = [p['name'] for p in parts if not fits_alone(p)]
    if too_big:
        pd.msg('These parts are larger than the usable sheet area (%s x %s inside a '
                      '%s margin):\n%s\n\nNothing was created.'
                      % (fmt(uw), fmt(uh), fmt(margin), ', '.join(too_big)))
        return

    # Auto Fit: tuck small parts into cutouts / notches of larger parts
    nested_count = 0
    if auto_orient and len(parts) > 1:
        try:
            nested_count = _nest_parts(
                parts, gap,
                lambda a, b: pd.set(30 + 10.0 * a / max(1, b), 'Nesting small parts into cutouts...'))
        except _Cancelled:
            raise
        except:
            for q in parts:
                q['parent'] = None
                q['children'] = []
            nested_count = 0

    # Pack the whole job at once: fewest sheets, earlier sheets as full as possible,
    # and the waste gathered on the last sheet as one large block.
    sheets = []          # [(global part indices, {local index: (x, y, rot)})]
    allidx = [i for i in range(len(parts)) if parts[i]['parent'] is None]
    pd.set(40, 'Optimising sheet layout...', True)
    packed = _pack_all(parts, allidx, uw, uh, gap, allow_rot,
                       progress=lambda f: pd.set(40 + 25.0 * f, 'Optimising sheet layout...'))
    remaining = [] if packed else list(allidx)
    for out in (packed or []):
        placed = [i for i in allidx if i in out]
        sheets.append((placed, {j: out[i] for j, i in enumerate(placed)}))
    if len(sheets) > 1 and nested_count:
        pd.set(66, 'Moving small parts into free space on other sheets...', True)
        moved = _unnest_to_free_space(parts, sheets, uw, uh, gap, allow_rot)
        nested_count -= moved
    if not remaining:
        pd.set(67, 'Moving parts to the bottom-left of each sheet...', True)
        if nested_count:
            _renest_bottom_left(parts, sheets, gap)
        _compact_bottom_left(parts, sheets, gap)
    if remaining:
        pd.msg('Some parts could not be placed. Nothing was created.')
        return
    if len(sheets) > 1 and not multi:
        total = sum(p['w'] * p['h'] for p in parts)
        pd.msg('The parts do not fit on one sheet.\n\nSheet: %s x %s (margin %s)\n'
                      'Parts need about %.0f%% of the usable area before spacing.\n\n'
                      'Tick "Allow multiple sheets", increase the sheet size, or remove '
                      'parts. Nothing was created.'
                      % (fmt(max_width), fmt(max_depth), fmt(margin),
                         100.0 * total / (uw * uh)))
        return

    pd.set(68, 'Creating flat bodies...', True)
    total_members = len(parts)
    built = 0
    # remove any previous flatpack component so the layout can be re-run
    for o in [o for o in root.occurrences if o.component.name == COMP_NAME]:
        o.deleteMe()

    # new component (Part Design documents allow only one component)
    try:
        occ = root.occurrences.addNewComponent(adsk.core.Matrix3D.create())
    except RuntimeError as e:
        if 'one component' in str(e):
            pd.msg('This design must be an Assembly to create the new "%s" '
                          'component. Convert it to an assembly and run Build Layout again.'
                          % COMP_NAME)
            return
        raise
    comp = occ.component
    comp.name = COMP_NAME

    rot90 = adsk.core.Matrix3D.create()
    rot90.setToRotation(math.pi / 2, adsk.core.Vector3D.create(0, 0, 1),
                        adsk.core.Point3D.create(0, 0, 0))

    base = None
    if design.designType == adsk.fusion.DesignTypes.ParametricDesignType:
        base = comp.features.baseFeatures.add()
        base.startEdit()
    try:
        stride = max_width + 10.0          # space between sheets (10 cm)
        for sn, (idxs, lay) in enumerate(sheets):
            for j, i in enumerate(idxs):
                host = parts[i]
                px, py, rot = lay[j]
                if rot:
                    px += host['h']                          # x' = -y, y' = x
                members = [(host, None)] + [(parts[c], (k, sx, sy))
                                            for c, k, sx, sy in host['children']]
                for p, loc in members:
                    if loc:                                  # position inside the host's frame
                        k, sx, sy = loc
                        if k:
                            mk = adsk.core.Matrix3D.create()
                            mk.setToRotation(k * math.pi / 2, adsk.core.Vector3D.create(0, 0, 1),
                                             adsk.core.Point3D.create(0, 0, 0))
                            tbm.transform(p['tmp'], mk)
                        tbm.transform(p['tmp'], translation(sx, sy, 0))
                    if rot:
                        tbm.transform(p['tmp'], rot90)
                    tbm.transform(p['tmp'], translation(px + margin + sn * stride, py + margin, 0))
                    nb = comp.bRepBodies.add(p['tmp'], base) if base else comp.bRepBodies.add(p['tmp'])
                    built += 1
                    pd.set(68 + 27.0 * built / total_members, 'Creating flat bodies (%d of %d)...' % (built, total_members))
                    nb.name = ('S%d_' % (sn + 1) if len(sheets) > 1 else '') + p['name'] + '_flat'
    finally:
        if base:
            base.finishEdit()

    pd.set(96, 'Drawing sheet outlines...', True)
    # one sketch per sheet: sheet outline + (construction) edge-margin outline
    stride = max_width + 10.0
    P = adsk.core.Point3D.create
    for sn in range(len(sheets)):
        x0 = sn * stride
        sk = comp.sketches.add(comp.xYConstructionPlane)
        sk.name = 'Sheet %d' % (sn + 1)
        lines = sk.sketchCurves.sketchLines
        lines.addTwoPointRectangle(P(x0, 0, 0), P(x0 + max_width, max_depth, 0))
        inner = lines.addTwoPointRectangle(P(x0 + margin, margin, 0),
                                           P(x0 + max_width - margin, max_depth - margin, 0))
        for ln in inner:
            ln.isConstruction = True

    pd.set(100, 'Done', True)
    pd.msg('Flatpack built: %d part(s) on %d sheet(s) in "%s", with a sketch '
                  'of each sheet.%s' % (len(parts), len(sheets), COMP_NAME,
                                        ('\n%d small part(s) were nested inside cutouts of larger parts.'
                                         % nested_count) if nested_count else ''))


class BuildExecute(adsk.core.CommandEventHandler):
    def notify(self, args):
        try:
            i = args.command.commandInputs
            build_flatpack(i.itemById('gap').value,
                           i.itemById('margin').value,
                           i.itemById('width').value,
                           i.itemById('depth').value,
                           True,
                           True,                      # 90 degree rotation always allowed
                           True)
        except:
            ui.messageBox('Flatpack failed:\n' + traceback.format_exc())


# ---------------------------------------------------------------- single dialog
ACTIONS = ['Build Layout']
GROUP_ID = {name: 'grp%d' % k for k, name in enumerate(ACTIONS)}
current_cmd = [None]
reopen = [False]
EVENT_ID = 'FlatpackReopenEvent'
SYNC_ID = 'FlatpackSyncEvent'
BUILD_ID = 'FlatpackBuildEvent'
TABLE_ID = 'partTable'
pending_build = [None]
busy = [False]
settings = {'gap': 1.0, 'margin': 1.0, 'width': 120.0, 'depth': 240.0}


class _Finder:
    """commandInputs.itemById that also looks inside the groups."""
    def __init__(self, inputs):
        self.inputs = inputs

    def itemById(self, iid):
        r = self.inputs.itemById(iid)
        if r:
            return r
        for gid in GROUP_ID.values():
            g = adsk.core.GroupCommandInput.cast(self.inputs.itemById(gid))
            if g:
                r = g.children.itemById(iid)
                if r:
                    return r
        return None


def _type_text(it):
    return 'Face (top)' if it['kind'] == 'face' else 'Body'


def add_row(inputs, table, it):
    """Add one row: Name | Body/Face | Copies (editable)."""
    row = table.rowCount
    uid = it['uid']
    nm = inputs.addStringValueInput('nm_%d' % uid, 'Name', it['name'])
    nm.isReadOnly = True
    ty = inputs.addStringValueInput('ty_%d' % uid, 'Type', _type_text(it))
    ty.isReadOnly = True
    cp = inputs.addIntegerSpinnerCommandInput('cp_%d' % uid, 'Copies', 1, 999, 1, it['copies'])
    xx = inputs.addStringValueInput('xx_%d' % uid, 'x', 'x')
    xx.isReadOnly = True
    dl = inputs.addBoolValueInput('dl_%d' % uid, '\u2715', False, '', False)
    table.addCommandInput(dl, row, 0)
    table.addCommandInput(nm, row, 1)
    table.addCommandInput(ty, row, 2)
    table.addCommandInput(xx, row, 3)
    table.addCommandInput(cp, row, 4)


def add_pick(inputs, table, ent, kind):
    """Add a picked body/face to the list. Several faces of one body are allowed; a body
    and a face of the same body are not (the newest pick wins)."""
    body = ent.body if kind == 'face' else ent
    if body.parentComponent.name == COMP_NAME:
        return
    btok = body.entityToken
    for it in items:
        if it['kind'] == kind and it['token'] == ent.entityToken:
            return
    for row in range(len(items) - 1, -1, -1):
        if items[row]['body'] == btok and items[row]['kind'] != kind:
            table.deleteRow(row)
            items.pop(row)
    it = {'uid': _new_uid(), 'token': ent.entityToken, 'body': btok,
          'kind': kind, 'name': body.name, 'copies': 1}
    items.append(it)
    add_row(inputs, table, it)


def sync_sel(sel, kind):
    """Make a selection input hold exactly the entities of that kind in the list."""
    want = []
    for it in items:
        if it['kind'] == kind:
            e = _entity_for_item(it)
            if e is not None:
                want.append(e)
    have = set(sel.selection(k).entity.entityToken for k in range(sel.selectionCount))
    if have == set(e.entityToken for e in want):
        return
    sel.clearSelection()
    for e in want:
        try:
            sel.addSelection(e)
        except:
            pass


class MainChanged(adsk.core.InputChangedEventHandler):
    def notify(self, args):
        if busy[0]:
            return
        busy[0] = True
        try:
            iid = args.input.id
            inputs = args.inputs
            table = adsk.core.TableCommandInput.cast(inputs.itemById(TABLE_ID))
            if iid in ('bodySel', 'faceSel'):
                kind = 'body' if iid == 'bodySel' else 'face'
                sel = adsk.core.SelectionCommandInput.cast(args.input)
                cls = adsk.fusion.BRepBody if kind == 'body' else adsk.fusion.BRepFace
                cur = [cls.cast(sel.selection(k).entity) for k in range(sel.selectionCount)]
                cur = [e for e in cur if e]
                tokens = set(e.entityToken for e in cur)
                # anything of this kind no longer selected (or cleared with the x) is removed
                for row in range(len(items) - 1, -1, -1):
                    if items[row]['kind'] == kind and items[row]['token'] not in tokens:
                        table.deleteRow(row)
                        items.pop(row)
                for ent in cur:
                    add_pick(inputs, table, ent, kind)
                # keep both pickers in step with the list (a body picked as a face, etc.)
                sync_sel(adsk.core.SelectionCommandInput.cast(inputs.itemById('bodySel')), 'body')
                sync_sel(adsk.core.SelectionCommandInput.cast(inputs.itemById('faceSel')), 'face')
            elif iid.startswith('dl_'):
                uid = int(iid[3:])
                for row, it in enumerate(items):
                    if it['uid'] == uid:
                        table.deleteRow(row)
                        items.pop(row)
                        break
                sync_sel(adsk.core.SelectionCommandInput.cast(inputs.itemById('bodySel')), 'body')
                sync_sel(adsk.core.SelectionCommandInput.cast(inputs.itemById('faceSel')), 'face')
            elif iid.startswith('cp_'):
                uid = int(iid[3:])
                sp = adsk.core.IntegerSpinnerCommandInput.cast(args.input)
                for it in items:
                    if it['uid'] == uid:
                        it['copies'] = max(1, sp.value)
        except:
            ui.messageBox('Failed:\n' + traceback.format_exc())
        finally:
            busy[0] = False


def save_settings(finder):
    try:
        g = lambda k: finder.itemById(k).value
        settings.update(gap=g('gap'), margin=g('margin'), width=g('width'), depth=g('depth'))
    except:
        pass


class MainExecute(adsk.core.CommandEventHandler):
    """The OK button is 'Build Layout'."""
    def notify(self, args):
        try:
            finder = _Finder(args.command.commandInputs)
            save_settings(finder)
            reopen[0] = True                 # dialog reopens after the build has run
            g = lambda k: finder.itemById(k).value
            # the build itself runs from a custom event, once this dialog has closed
            # Auto Fit and multiple sheets are always on
            pending_build[0] = (g('gap'), g('margin'), g('width'), g('depth'),
                                True, True, True)
        except:
            ui.messageBox('Failed:\n' + traceback.format_exc())


class MainDestroy(adsk.core.CommandEventHandler):
    def notify(self, args):
        try:
            if reopen[0]:
                reopen[0] = False
                app.fireCustomEvent(BUILD_ID if pending_build[0] else EVENT_ID)
            else:
                app.fireCustomEvent(SYNC_ID)
        except:
            pass


class BuildHandler(adsk.core.CustomEventHandler):
    """Runs the build after the dialog is gone, then reopens the dialog."""
    def notify(self, args):
        params, pending_build[0] = pending_build[0], None
        try:
            persist_items()
            if params:
                build_flatpack(*params)
        except:
            ui.messageBox('Flatpack failed:\n' + traceback.format_exc())
        try:
            ui.commandDefinitions.itemById(CMD_MAIN).execute()
        except:
            ui.messageBox('Could not reopen dialog:\n' + traceback.format_exc())


class ReopenHandler(adsk.core.CustomEventHandler):
    def notify(self, args):
        try:
            ui.commandDefinitions.itemById(CMD_MAIN).execute()
        except:
            ui.messageBox('Could not reopen dialog:\n' + traceback.format_exc())


class SyncHandler(adsk.core.CustomEventHandler):
    def notify(self, args):
        persist_items()


class MainCreated(adsk.core.CommandCreatedEventHandler):
    def notify(self, args):
        try:
            cmd = args.command
            current_cmd[0] = cmd
            busy[0] = False
            top = cmd.commandInputs

            validate_items()
            if not items:
                load_items()
                validate_items()

            # two pickers: bodies (any way up) or faces (the picked face is the top)
            bsel = top.addSelectionInput('bodySel', 'Select Body',
                                         'Pick a whole body - it may lie any way up')
            bsel.addSelectionFilter('SolidBodies')
            bsel.setSelectionLimits(0, 0)
            fsel = top.addSelectionInput('faceSel', 'Select Face',
                                         'Pick the face that must point UP (top face)')
            fsel.addSelectionFilter('PlanarFaces')
            fsel.setSelectionLimits(0, 0)

            # part list
            table = top.addTableCommandInput(TABLE_ID, 'Parts', 5, '2:12:8:2:5')
            table.minimumVisibleRows = 3
            table.maximumVisibleRows = 6          # more rows than this scroll
            for it in items:
                add_row(top, table, it)
            busy[0] = True
            try:
                sync_sel(bsel, 'body')
                sync_sel(fsel, 'face')
            finally:
                busy[0] = False

            # Build Layout
            g = top.addGroupCommandInput(GROUP_ID['Build Layout'], 'Build Layout')
            g.isExpanded = True
            i = g.children
            unit = get_design().unitsManager.defaultLengthUnits
            i.addValueInput('gap', 'Gap between parts', unit,
                            adsk.core.ValueInput.createByReal(settings['gap']))
            i.addValueInput('margin', 'Edge margin', unit,
                            adsk.core.ValueInput.createByReal(settings['margin']))
            i.addValueInput('width', 'Sheet width (X)', unit,
                            adsk.core.ValueInput.createByReal(settings['width']))
            i.addValueInput('depth', 'Sheet depth (Y)', unit,
                            adsk.core.ValueInput.createByReal(settings['depth']))

            cmd.okButtonText = 'Build Layout'
            cmd.cancelButtonText = 'Close'

            for ev, cls in ((cmd.inputChanged, MainChanged), (cmd.execute, MainExecute),
                            (cmd.destroy, MainDestroy)):
                h = cls()
                ev.add(h)
                handlers.append(h)
        except:
            ui.messageBox('Failed:\n' + traceback.format_exc())


# ---------------------------------------------------------------- lifecycle
def _add_button(cmd_id, name, tip, created_cls):
    defs = ui.commandDefinitions
    existing = defs.itemById(cmd_id)
    if existing:
        existing.deleteMe()
    # icon: Fusion reads 16x16.png, 32x32.png (and optionally 64x64.png) from this folder
    res = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'resources')
    if os.path.isfile(os.path.join(res, '16x16.png')):
        d = defs.addButtonDefinition(cmd_id, name, tip, res)
    else:
        d = defs.addButtonDefinition(cmd_id, name, tip)
    h = created_cls()
    d.commandCreated.add(h)
    handlers.append(h)
    for pid in (PANEL_ID, MODIFY_PANEL_ID):
        panel = ui.allToolbarPanels.itemById(pid)
        if panel and not panel.controls.itemById(cmd_id):
            ctrl = panel.controls.addCommand(d)
            if pid == PANEL_ID:
                ctrl.isPromoted = True


def run(context):
    try:
        try:
            app.unregisterCustomEvent(EVENT_ID)
        except:
            pass
        try:
            app.unregisterCustomEvent(SYNC_ID)
        except:
            pass
        ev = app.registerCustomEvent(EVENT_ID)
        rh = ReopenHandler()
        ev.add(rh)
        handlers.append(rh)
        ev2 = app.registerCustomEvent(SYNC_ID)
        sh = SyncHandler()
        ev2.add(sh)
        handlers.append(sh)
        try:
            app.unregisterCustomEvent(BUILD_ID)
        except:
            pass
        ev3 = app.registerCustomEvent(BUILD_ID)
        bh = BuildHandler()
        ev3.add(bh)
        handlers.append(bh)
        _add_button(CMD_MAIN, 'Flatpack CNC',
                    'Label faces, build the flat layout and sheet sketches',
                    MainCreated)
    except:
        ui.messageBox('Add-in start failed:\n' + traceback.format_exc())


def stop(context):
    try:
        try:
            app.unregisterCustomEvent(EVENT_ID)
            app.unregisterCustomEvent(SYNC_ID)
            app.unregisterCustomEvent(BUILD_ID)
        except:
            pass
        for pid in (OWN_PANEL_ID, PANEL_ID, MODIFY_PANEL_ID):          # also clears old installs
            panel = ui.allToolbarPanels.itemById(pid)
            if not panel:
                continue
            for cid in (CMD_MAIN, CMD_LABEL, CMD_SHOW, CMD_BUILD, CMD_CLEAR):
                c = panel.controls.itemById(cid)
                if c:
                    c.deleteMe()
            if pid == OWN_PANEL_ID:
                panel.deleteMe()
        for cid in (CMD_MAIN, CMD_LABEL, CMD_SHOW, CMD_BUILD, CMD_CLEAR):
            d = ui.commandDefinitions.itemById(cid)
            if d:
                d.deleteMe()
    except:
        ui.messageBox('Add-in stop failed:\n' + traceback.format_exc())
