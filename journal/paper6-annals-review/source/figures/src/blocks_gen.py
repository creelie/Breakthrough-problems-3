# Writes the TikZ body of the schematic figure of the dyadic blocks.
import sys
J = 14            # number of blocks drawn
w, d = 0.62, 0.55  # width of a block and depth of the boxes
ox, oy = 0.42, 0.30  # oblique direction of the depth axis
base_h = 0.55     # the layer 2 log 2 common to all blocks
top_scale = 3.2   # the layer log q/(j+1)
def box(x0, y0, x1, y1, front, top, side):
    p = lambda x, y, z: f"({x + z*ox:.3f},{y + z*oy:.3f})"
    s = []
    s.append(rf"\filldraw[fill={front},draw=black!55,line width=0.3pt] {p(x0,y0,0)}--{p(x1,y0,0)}--{p(x1,y1,0)}--{p(x0,y1,0)}--cycle;")
    s.append(rf"\filldraw[fill={top},draw=black!55,line width=0.3pt] {p(x0,y1,0)}--{p(x1,y1,0)}--{p(x1,y1,d)}--{p(x0,y1,d)}--cycle;")
    s.append(rf"\filldraw[fill={side},draw=black!55,line width=0.3pt] {p(x1,y0,0)}--{p(x1,y0,d)}--{p(x1,y1,d)}--{p(x1,y1,0)}--cycle;")
    return s
out = []
for j in range(J):
    x0 = j*w; x1 = x0 + w*0.86
    h1 = base_h
    h2 = top_scale/(j+1)
    out += box(x0, 0, x1, h1, "gray!35", "gray!20", "gray!50")
    out += box(x0, h1, x1, h1 + h2, "teal!45", "teal!25", "teal!65")
    if j in (0, 1, 2, 3, 5, 9, 13):
        lab = r"\cdots" if False else str(j)
        out.append(rf"\node[font=\scriptsize,below] at ({x0 + 0.43*w:.3f},0) {{${lab}$}};")
sys.stdout.write("\n".join(out) + "\n")
