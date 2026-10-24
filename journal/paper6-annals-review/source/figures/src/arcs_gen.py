# Writes the TikZ body of the schematic major/minor arcs figure.
import math, sys
A, B = 4.3, 1.6          # outer ellipse radii
k = 0.80                 # inner radius ratio
def P(beta, rad, h):
    phi = 2*math.pi*beta - math.pi/2   # beta = 0 at the front
    return (rad*A*math.cos(phi), rad*B*math.sin(phi) + h)
def poly(pts):
    return " -- ".join(f"({x:.3f},{y:.3f})" for x, y in pts) + " -- cycle"
def arc(b1, b2, rad, h, n=16):
    return [P(b1 + (b2-b1)*i/n, rad, h) for i in range(n+1)]
slabs = []
major = [(0,1,0.050,1.30),(1/2,2,0.036,1.05),(1/3,3,0.028,0.90),(2/3,3,0.028,0.90),
         (1/4,4,0.023,0.78),(3/4,4,0.023,0.78)]
for b, r, w, h in major:
    slabs.append((b, w, h, 'majtop', 'orange!60!black'))
minor = [0.10, 0.17, 0.20, 0.29, 0.39, 0.43, 0.57, 0.61, 0.71, 0.80, 0.83, 0.90]
for i, b in enumerate(minor):
    slabs.append((b, 0.012, 0.14 + 0.05*((7*i) % 3), 'mintop', 'blue!50!black'))
out = []
# the ring itself
outer = arc(0, 1, 1, 0, 120); inner = arc(0, 1, k, 0, 120)
out.append(r"\fill[gray!12] " + poly(outer) + ";")
out.append(r"\fill[white] " + poly(inner) + ";")
out.append(r"\draw[gray!60!black] " + poly(outer) + ";")
out.append(r"\draw[gray!60!black] " + poly(inner) + ";")
# painter's order: back (beta near 1/2) first
def depth(b):
    return math.sin(2*math.pi*b - math.pi/2)
for b, w, h, fill, edge in sorted(slabs, key=lambda s: -depth(s[0])):
    b1, b2 = b - w, b + w
    outer_wall = arc(b1, b2, 1, 0) + arc(b2, b1, 1, h)
    inner_wall = arc(b1, b2, k, 0) + arc(b2, b1, k, h)
    top = arc(b1, b2, 1, h) + arc(b2, b1, k, h)
    s1 = [P(b1, 1, 0), P(b1, k, 0), P(b1, k, h), P(b1, 1, h)]
    s2 = [P(b2, 1, 0), P(b2, k, 0), P(b2, k, h), P(b2, 1, h)]
    def fdepth(f):
        return sum(y for x, y in f[:len(f)//2]) / (len(f)//2)
    faces = [outer_wall, inner_wall, s1, s2]
    # a face is drawn before the faces in front of it; heights are equal across a face pair
    base = {0: arc(b1, b2, 1, 0), 1: arc(b1, b2, k, 0), 2: [P(b1, 1, 0), P(b1, k, 0)], 3: [P(b2, 1, 0), P(b2, k, 0)]}
    order = sorted(range(4), key=lambda i: -sum(y for x, y in base[i]) / len(base[i]))
    for f in [faces[i] for i in order]:
        out.append(rf"\filldraw[fill={fill}side,draw={edge},line width=0.3pt] " + poly(f) + ";")
    out.append(rf"\filldraw[fill={fill},draw={edge},line width=0.3pt] " + poly(top) + ";")
labels = [(0,'0'),(1/2,r'\tfrac12'),(1/3,r'\tfrac13'),(2/3,r'\tfrac23'),(1/4,r'\tfrac14'),(3/4,r'\tfrac34')]
hs = {b: h for b, r, w, h in major}
for b, lab in labels:
    x, y = P(b, (1+k)/2, hs[b])
    out.append(rf"\node[font=\scriptsize,above] at ({x:.3f},{y:.3f}) {{${lab}$}};")
sys.stdout.write("\n".join(out) + "\n")
