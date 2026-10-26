Deep Bhattacharjee and Ushashi Bhattacharya, *The Pólya–Vinogradov inequality with log log q for every character*. Final revision, single column (amsart), 51 pages.

M(χ) ≤ C √q log log q for every primitive Dirichlet character χ modulo q ≥ 3, with an absolute
constant C, where M(χ) is the largest modulus of a partial sum of χ, and |L'/L(1, χ)| ≤ C log log q
for every nonprincipal character (Theorem 1.5). From Chebyshev's bounds alone: for every ε > 0
at most q^ε of the primitive characters modulo q have M(χ) > C_ε √q log log q, and at most q^ε of
the nonprincipal characters have |L'/L(1, χ)| > C_ε log log q (Theorems 1.2 and 1.4). The proof
is a transfer theorem for a single character (a zero-free rectangle for the twists of χ by the
characters of small moduli gives the bound), proved by a contour shift, the circle method and a
weak Montgomery–Vaughan bound from Selberg's sieve; a count of the exceptional characters by a
zero-density theorem, proved in full in Appendix A with explicit constants; and the zero-free
half-plane Re s > 11/12 for all finite-order Hecke L-functions over Q(√−3), due to OpenAI, whose
proof Appendix B reproduces in full with credit to them, so that every statement of the paper is
proved in the text. OpenAI's Lean 4 proof of the wider half-plane Re s > 7/8 is compiled from
source and checked by the Lean kernel in this repository as an independent check.

This release adds Appendix B, retitles the paper, redraws the figures (the structure of the
proofs now includes the half-plane, and a new figure shows the parts of its proof) and sets the
paper in amsart. The results were first made public on 15 October 2026 as release v1.0.0 of this
repository; an earlier and incomplete version of the paper appeared on Hexagon as
hexagon:2610.00256.

Files: the paper (`PolyaVinogradovLogLog_final2.pdf`), its LaTeX source with the figures
(`PolyaVinogradovLogLog_final2-tex.zip`) and the arXiv tarball
(`PolyaVinogradovLogLog_final2-arxiv.tar.gz`).

Contact: d.bhattacharjee@erl-forschung.de, itsdeep@live.com; for this repository egspl@proton.me.
