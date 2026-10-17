Deep Bhattacharjee and Ushashi Bhattacharya, *The Pólya–Vinogradov inequality with log log q*.

- Theorem 1.1: |∑_{n ≤ x} χ(n)| ≤ C √q log log q for every primitive character χ modulo q ≥ 3,
  the bound Montgomery and Vaughan proved under the generalised Riemann hypothesis.
- Theorem 1.3: |L'/L(1, χ)| ≤ C log log q for every nonprincipal χ, and
  −C log q log log q ≤ γ_q ≤ C log q for the Euler–Kronecker constants of Q(ζ_q), q prime.

The input is OpenAI's zero-free half-plane Re s > 7/8 (https://github.com/openai/math), whose
Lean 4 proof is compiled with ours. The Lean proofs use only propext, Classical.choice and
Quot.sound; four programs in Python, Julia, C and C++ check the numerical steps.

In this release every reference of the paper is in its bibliography, each checked against
its publisher or Crossref record, and the paper ends with data and code availability and
ethical declarations. The paper is set in the IMPAN template of Acta Arithmetica, its title-page
footnote names the Hexagon preprint 2610.00256v1, and `journal/submission-acta/` holds the
submission package. The mathematics is unchanged.

Files: the paper (`PolyaVinogradovLogLog_final2.pdf`), its LaTeX source with the figures as PNG
(`PolyaVinogradovLogLog_final2-tex.zip`) and the arXiv tarball
(`PolyaVinogradovLogLog_final2-arxiv.tar.gz`). The archive of the tag holds the Lean project, the
check programs and the master zip `MasterPolyaVinogradovLogLog_masterzipfinal2.zip`.
