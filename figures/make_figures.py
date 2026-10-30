#!/usr/bin/env python3
"""make_figures.py: the four figures of the paper, written as PNG at 200 dpi to paper/figures/.

fig_flow       the structure of the proofs
fig_splane     the truncated contour of Proposition 3.7
fig_arcs       the major and minor arcs of Proposition 5.5, drawn for R = 4
fig_halfplane  the structure of the proof of the zero-free half-plane, Appendix B
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

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "paper", "figures")
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
fig, ax = plt.subplots(figsize=(10.0, 5.9))
ax.set_xlim(0, 15.3); ax.set_ylim(0.2, 9.0); ax.axis("off")
F = 6.9
W = 4.75
XL, XM, XR = 2.5, 7.65, 12.8
def tb(x, y, w, h, t, fc="#f2f2f2"):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0.02,rounding_size=0.08",
                                fc=fc, ec="black", lw=0.8))
    ax.text(x, y, t, ha="center", va="center", fontsize=F)
BLUE, RED, GREEN, GREY = "#dde8f5", "#f5e6dd", "#e8f0e0", "#f2f2f2"
# left column: the transfer theorem
tb(XL, 7.6, W, 1.0, "Theorem 1.1 (transfer): if no $L(s,\\chi\\psi)$\nwith $\\psi$ mod $r\\leq R$ has a zero in $\\mathrm{Re}\\,s>\\theta$,\n$|\\mathrm{Im}\\,s|\\leq5q^2$, then $M(\\chi)\\leq C_\\theta\\sqrt{q}\\log\\log q$", fc=BLUE)
tb(XL, 6.05, W, 0.85, "Lemma 5.1: $M(\\chi)\\leq\\sqrt{q}\\,(B+6)$ if\n$|\\sum_{m\\leq H}\\bar\\chi(m)e(m\\beta)/m|\\leq B$ for $H\\leq q/2$")
tb(XL, 4.6, W, 0.85, "Proposition 5.5: $B=C_4\\log\\log q$\n(major arcs, minor arcs, smooth $m$: Lemma 5.2)")
tb(1.25, 2.9, 2.25, 1.15, "major arcs:\nLemma 5.4, Cor. 3.8,\nProposition 3.7\n(contour shift)", fc=GREEN)
tb(3.75, 2.9, 2.25, 1.15, "minor arcs:\nTheorem 4.1\n(bilinear forms,\nsieve, Lemma 2.2)", fc=GREEN)
arrow(ax, (XL, 6.48), (XL, 7.1))
arrow(ax, (XL, 5.03), (XL, 5.62))
arrow(ax, (1.25, 3.48), (1.9, 4.17))
arrow(ax, (3.75, 3.48), (3.1, 4.17))
# middle column: the exceptional characters
tb(XM, 7.6, W, 1.0, "Theorem 1.2: $M(\\chi)\\leq C_\\varepsilon\\sqrt{q}\\log\\log q$\nfor all but $q^{\\varepsilon}$ of the\nprimitive characters mod $q$", fc=BLUE)
tb(XM, 6.05, W, 0.85, "Section 6: count the characters $\\chi$ for which\nsome twist $\\chi\\psi$ has a zero in the rectangle", fc=RED)
tb(XM, 4.6, W, 0.85, "Theorem 2.3 (Appendix A): for $\\sigma\\geq\\frac{11}{12}$,\n$\\sum_{\\xi\\neq\\xi_0}N(\\sigma,T,\\xi)\\leq 10^{12}(kT)^{12(1-\\sigma)}(\\log kT)^{9}$", fc=RED)
tb(XM, 3.05, W, 0.85, "Theorem 1.4: $|L'/L(1,\\chi)|\\leq C_\\varepsilon\\log\\log q$\nfor all but $q^{\\varepsilon}$ of the nonprincipal characters", fc=BLUE)
tb(XM, 1.35, W, 1.05, "Section 7, Proposition 7.1: residue of\n$L'/L(s+1,\\chi)\\,x^s/(s(s+1))$ at $s=0$; the zero-free\nrectangle has height $(\\log q)^{4/(1-\\theta)}$ only", fc=GREEN)
arrow(ax, (XM, 6.48), (XM, 7.1))
arrow(ax, (XM, 5.03), (XM, 5.62))
arrow(ax, (XM, 4.17), (XM, 3.48))
arrow(ax, (XM, 1.88), (XM, 2.62))
# right column: the half-plane and its consequences
tb(XR, 7.6, W, 1.0, "Theorem 1.5: $M(\\chi)\\leq C\\sqrt{q}\\log\\log q$ and\n$|L'/L(1,\\chi)|\\leq C\\log\\log q$\nfor every character", fc=BLUE)
tb(XR, 6.05, W, 0.85, "Theorem B.1 (Appendix B, due to OpenAI):\nno Dirichlet $L$-function has a zero\nwith $\\mathrm{Re}\\,s>11/12$", fc=RED)
tb(XR, 4.6, W, 0.85, "Theorem 1.6: $\\gamma_m\\leq12\\log m+36\\log\\log m+C$,\n$\\gamma_q\\geq-C\\log q\\log\\log q$ for primes $q$", fc=BLUE)
tb(XR, 3.05, W, 0.85, "Section 8: explicit formula for $\\sum_\\chi\\psi(x,\\chi)$,\n$\\zeta_{\\mathbb{Q}(\\zeta_m)}=\\prod_\\chi L(s,\\chi^*)$, Brun–Titchmarsh", fc=GREEN)
arrow(ax, (XR, 6.48), (XR, 7.1))
arrow(ax, (XR, 5.62), (XR, 5.03))
arrow(ax, (XR, 3.48), (XR, 4.17))
# across the columns
arrow(ax, (XL + W / 2 + 0.03, 7.6), (XM - W / 2 - 0.03, 7.6))
ax.add_patch(FancyArrowPatch((XL, 8.12), (XR, 8.12), arrowstyle="-|>", mutation_scale=10, lw=0.8, color="black",
                             shrinkA=0, shrinkB=0, connectionstyle="arc3,rad=-0.09"))
ax.text((XL + XR) / 2, 8.82, "$\\theta=11/12$", fontsize=7.5, ha="center", va="center",
        bbox=dict(fc="white", ec="none", pad=1))
XG = (XM + XR) / 2
ax.plot([XM + W / 2 + 0.03, XG, XG], [1.35, 1.35, 7.35], color="black", lw=0.8)
arrow(ax, (XG, 7.35), (XR - W / 2 - 0.03, 7.35))
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
# ---------------------------------------------------------------- fig_halfplane
fig, ax = plt.subplots(figsize=(8.0, 6.2))
ax.set_xlim(0, 11); ax.set_ylim(0, 9.2); ax.axis("off")
def hb(x, y, w, h, t, fc="#f2f2f2"):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0.02,rounding_size=0.08",
                                fc=fc, ec="black", lw=0.8))
    ax.text(x, y, t, ha="center", va="center", fontsize=7.3)
hb(5.5, 8.6, 6.2, 0.8, "Theorem B.1: no zero of a finite-order Hecke $L$-function\nover $\\mathbb{Q}(\\sqrt{-3})$ with $\\mathrm{Re}\\,s>11/12$", fc="#f5e6dd")
hb(5.5, 7.2, 6.2, 0.9, "Proposition B.2 (mean square): $\\sum_{u}|\\sum_{n}\\mu(n)\\nu(n)\\chi_{n}(u)W(\\mathrm{N}n/D)|^2\\ll D^{5/6+\\varepsilon}H$;\nMellin inversion (B.2) turns the saving into the half-plane", fc="#dde8f5")
arrow(ax, (5.5, 7.65), (5.5, 8.2))
hb(2.5, 5.6, 4.4, 1.0, "Poisson summation with excluded\nprimes (Lemma B.4) and the Gauss\nsum identities (Lemma B.3): the\nM\u00f6bius sums become cubic Gauss sums", fc="#e8f0e0")
hb(8.5, 5.6, 4.4, 1.0, "Reduction to the dual mean square\n$\\mathcal{E}_n$ (Proposition B.7) and the\ncanonical induction (Proposition B.8):\na finite iteration at smaller scales", fc="#e8f0e0")
arrow(ax, (2.5, 6.1), (4.2, 6.75))
arrow(ax, (8.5, 6.1), (6.8, 6.75))
arrow(ax, (4.7, 5.6), (6.3, 5.6))
hb(2.5, 3.8, 4.4, 1.0, "Cube reduction (Lemma B.10) and\nProposition B.9: the completed sums\n$T(X;k,f)$ are bounded on average\nover $k$ by $D^{\\varepsilon}(H+H^2\\mathrm{N}f/X)$", fc="#e8f0e0")
hb(8.5, 3.8, 4.4, 1.0, "Transfer (Proposition B.11): two more\nPoisson summations (Lemmas B.18 to B.20)\nreturn to sums of the original kind,\nlosing only a divisor function", fc="#e8f0e0")
arrow(ax, (2.5, 4.3), (2.5, 5.1))
arrow(ax, (8.5, 4.3), (8.5, 5.1))
hb(1.6, 1.75, 2.9, 1.55, "Kubota's cubic theta\nfunction: automorphy,\nPatterson coefficients,\nthe fixed ray class\ntransformation\n(B.12 to B.15, \u00a7B.14)", fc="#f2f2f2")
hb(4.75, 1.75, 2.9, 1.55, "quadratic large sieve\n(Goldmakher and\nLouvel, Lemma B.16)\nand squarefree rows\n(Lemma B.17)", fc="#f2f2f2")
hb(8.5, 1.75, 3.4, 1.55, "smooth weights: separation\nof variables and the\nrecombination of row\nkernels (Lemmas B.21\nto B.23, \u00a7B.15)", fc="#f2f2f2")
arrow(ax, (1.6, 2.45), (2.0, 3.3))
arrow(ax, (4.75, 2.45), (3.4, 3.3))
arrow(ax, (8.5, 2.45), (8.5, 3.3))
arrow(ax, (6.2, 2.1), (6.7, 3.3))
ax.text(5.5, 0.45, "The argument of OpenAI, Appendix B; the arrows point from a result to the result that uses it.", ha="center", fontsize=8)
fig.savefig(os.path.join(OUT, "fig_halfplane.png"), dpi=200, bbox_inches="tight")
plt.close(fig)

print("figures written to", OUT)
