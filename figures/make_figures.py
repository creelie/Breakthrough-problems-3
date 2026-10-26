#!/usr/bin/env python3
"""make_figures.py: the three figures of the paper, written as PNG at 200 dpi to figures/.

fig_flow    the structure of the proofs
fig_splane  the truncated contour of Proposition 3.7
fig_arcs    the major and minor arcs of Proposition 5.5, drawn for R = 4
Needs matplotlib and numpy.
"""
import os
import sys
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Rectangle

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "figures")
os.makedirs(OUT, exist_ok=True)
plt.rcParams.update({"font.family": "serif", "font.size": 9, "mathtext.fontset": "cm"})

def box(ax, x, y, w, h, text, fc="#f2f2f2"):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0.02,rounding_size=0.08",
                                fc=fc, ec="black", lw=0.8))
    ax.text(x, y, text, ha="center", va="center", fontsize=8.3)

def arrow(ax, p, q, text=None, dx=0.0, dy=0.0):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=10, lw=0.8, color="black",
                                 shrinkA=0, shrinkB=0))
    if text:
        ax.text((p[0] + q[0]) / 2 + dx, (p[1] + q[1]) / 2 + dy, text, fontsize=7.5, ha="center", va="center",
                bbox=dict(fc="white", ec="none", pad=1))

# ---------------------------------------------------------------- fig_flow
fig, ax = plt.subplots(figsize=(8.0, 5.0))
ax.set_xlim(0, 11); ax.set_ylim(0, 7); ax.axis("off")
F = 7.4
def tb(x, y, w, h, t, fc="#f2f2f2"):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0.02,rounding_size=0.08",
                                fc=fc, ec="black", lw=0.8))
    ax.text(x, y, t, ha="center", va="center", fontsize=F)
tb(5.5, 6.45, 5.0, 0.75, "Theorem 1.2: $M(\\chi)\\leq C_\\varepsilon\\sqrt{q}\\log\\log q$\nfor all but $q^{\\varepsilon}$ of the primitive characters mod $q$", fc="#dde8f5")
tb(2.75, 5.0, 5.0, 0.95, "Theorem 1.1 (transfer): if no $L(s,\\chi\\psi)$, $\\psi$ mod $r\\leq R$,\nhas a zero in $\\mathrm{Re}\\,s>\\theta$, $|\\mathrm{Im}\\,s|\\leq5q^2$,\nthen $M(\\chi)\\leq C_\\theta\\sqrt{q}\\log\\log q$", fc="#dde8f5")
tb(8.25, 5.0, 5.0, 0.95, "Section 6: count the characters $\\chi$ for which\nsome twist $\\chi\\psi$ has such a zero,\nby the zero-density theorem", fc="#f5e6dd")
arrow(ax, (2.75, 5.48), (4.3, 6.07))
arrow(ax, (8.25, 5.48), (6.7, 6.07))
tb(2.75, 3.55, 5.0, 0.8, "Lemma 5.1: $M(\\chi)\\leq\\sqrt{q}\\,(B+6)$ if\n$|\\sum_{m\\leq H}\\bar\\chi(m)e(m\\beta)/m|\\leq B$ for $H\\leq q/2$")
arrow(ax, (2.75, 3.95), (2.75, 4.52))
tb(2.75, 2.3, 5.0, 0.8, "Proposition 5.5: $B=C_4\\log\\log q$\n(major arcs, minor arcs, smooth $m$: Lemma 5.2)")
arrow(ax, (2.75, 2.7), (2.75, 3.15))
tb(1.3, 0.75, 2.2, 1.05, "major arcs:\nLemma 5.4, Cor. 3.8,\nProposition 3.7\n(contour shift)", fc="#e8f0e0")
tb(4.2, 0.75, 2.2, 1.05, "minor arcs:\nTheorem 4.1\n(bilinear forms,\nsieve, Lemma 2.2)", fc="#e8f0e0")
arrow(ax, (1.3, 1.28), (2.2, 1.9))
arrow(ax, (4.2, 1.28), (3.3, 1.9))
tb(8.25, 3.55, 5.0, 0.8, "Theorem 2.3 (Appendix A): nonprincipal $\\xi$ mod $k$ together,\n$\\sum N(\\sigma,T,\\xi)\\leq 10^{12}(kT)^{12(1-\\sigma)}(\\log kT)^{9}$, $\\sigma\\geq\\frac{11}{12}$", fc="#f5e6dd")
arrow(ax, (8.25, 3.95), (8.25, 4.52))
tb(8.25, 2.3, 5.0, 0.8, "Theorem 1.4: $|L'/L(1,\\chi)|\\leq C_\\varepsilon\\log\\log q$\nfor all but $q^{\\varepsilon}$ of the nonprincipal characters", fc="#dde8f5")
arrow(ax, (8.25, 3.15), (8.25, 2.7))
tb(8.25, 0.75, 5.0, 1.05, "Section 7: residue of $L'/L(s+1,\\chi)\\,x^s/(s(s+1))$ at $s=0$;\nthe zero-free rectangle has height\n$(\\log q)^{4/(1-\\theta)}$ only", fc="#e8f0e0")
arrow(ax, (8.25, 1.28), (8.25, 1.9))
fig.savefig(os.path.join(OUT, "fig_flow.png"), dpi=200, bbox_inches="tight")
plt.close(fig)

# ---------------------------------------------------------------- fig_splane
fig, ax = plt.subplots(figsize=(6.4, 4.2))
ax.set_xlim(-1.6, 2.8); ax.set_ylim(-3.4, 3.7)
ax.axhline(0, color="black", lw=0.6); ax.axvline(0, color="black", lw=0.6)
ax.set_xlabel("$\\mathrm{Re}\\,s$"); ax.set_ylabel("$\\mathrm{Im}\\,s$")
ax.set_yticks([]); ax.set_xticks([0, 1, 2]); ax.set_xticklabels(["$0$", "$1$", "$2$"])
T = 2.2
s0 = 0.95
# zero-free rectangle (hypothesis), slightly larger than the contour rectangle
ax.add_patch(Rectangle((0.82, -T - 0.5), 2.8, 2 * T + 1.0, fc="#eef4ea", ec="none"))
ax.text(1.45, T + 0.72, "no zero: $\\mathrm{Re}\\,s>a+2\\delta$,\n$|\\mathrm{Im}\\,s|\\leq x^2+2$", fontsize=7.5, ha="center", va="bottom")
# contour rectangle
ax.add_patch(Rectangle((s0, -T), 2 - s0, 2 * T, fill=False, ec="#1f4e9c", lw=1.4))
ax.plot([2, 2], [T, 3.4], color="#1f4e9c", lw=1.4, ls="--")
ax.plot([2, 2], [-3.4, -T], color="#1f4e9c", lw=1.4, ls="--")
ax.annotate("", xy=(2, 1.2), xytext=(2, 0.4), arrowprops=dict(arrowstyle="-|>", color="#1f4e9c", lw=1.2))
ax.annotate("", xy=(s0, -1.2), xytext=(s0, -0.4), arrowprops=dict(arrowstyle="-|>", color="#1f4e9c", lw=1.2))
ax.text(2.06, 0.75, "$\\mathrm{Re}\\,s=2$", fontsize=8, va="center")
ax.text(s0 + 0.05, -0.8, "$\\mathrm{Re}\\,s=\\sigma_0$", fontsize=8, va="center")
ax.text(1.5, T + 0.12, "$\\mathrm{Im}\\,s=x^2$", fontsize=8, ha="center")
ax.text(1.5, -T - 0.3, "$\\mathrm{Im}\\,s=-x^2$", fontsize=8, ha="center")
ax.text(2.08, -3.0, "tail: $|t|>x^2$,\nbounded by $32$", fontsize=7.5, va="center")
# poles of the kernel
ax.plot([0, -1], [0, 0], "x", color="#b03030", ms=8, mew=1.6)
ax.text(0.04, -0.33, "$0$", fontsize=8); ax.text(-0.96, -0.33, "$-1$", fontsize=8)
# zeros: on the critical line and some off it, all outside the shaded region
rng = np.random.default_rng(7)
ys = np.linspace(-3.1, 3.1, 14)
ax.plot(np.full(14, 0.5), ys + rng.normal(0, 0.08, 14), "o", color="#444", ms=3)
ax.plot([0.7, 0.72, 0.65], [2.95, -3.0, -1.4], "o", color="#444", ms=3)
ax.text(0.36, 3.1, "$\\mathrm{Re}\\,s=\\frac{1}{2}$", fontsize=7.5, ha="right", va="center")
fig.savefig(os.path.join(OUT, "fig_splane.png"), dpi=200, bbox_inches="tight")
plt.close(fig)

# ---------------------------------------------------------------- fig_arcs
fig, ax = plt.subplots(figsize=(7.4, 2.9))
R = 4
fracs = sorted({(a, r) for r in range(1, R + 1) for a in range(0, r + 1) if math.gcd(a, r) == 1})
xs = np.linspace(0, 1, 4000)
y = np.zeros_like(xs)
for a, r in fracs:
    c = a / r
    w = 0.012 / r
    y += (1.0 / r) * np.exp(-((xs - c) / w) ** 2 / 2)
ax.fill_between(xs, 0, y, color="#c9d8ee", lw=0)
ax.plot(xs, y, color="#1f4e9c", lw=0.9)
for a, r in fracs:
    c = a / r
    ax.axvspan(c - 0.045 / r, c + 0.045 / r, ymin=0, ymax=0.08, color="#b03030", alpha=0.75, lw=0)
    ax.text(c, -0.11, "$\\frac{%d}{%d}$" % (a, r) if r > 1 else "$%d$" % a, ha="center", va="top", fontsize=8)
ax.set_xlim(-0.02, 1.02); ax.set_ylim(-0.45, 1.15)
ax.set_yticks([]); ax.set_xticks([])
for s in ax.spines.values():
    s.set_visible(False)
ax.plot([0, 1], [0, 0], color="black", lw=0.7)
ax.text(0.5, 1.02, "major arcs: $\\beta$ within $R/t$ of $a/r$, $r\\leq R$ (red); minor arcs: the rest", ha="center", fontsize=8.5)
ax.text(0.5, -0.4, "$\\beta\\in\\mathbb{R}/\\mathbb{Z}$, drawn for $R=4$", ha="center", fontsize=8)
fig.savefig(os.path.join(OUT, "fig_arcs.png"), dpi=200, bbox_inches="tight")
plt.close(fig)
print("figures written to", OUT)
