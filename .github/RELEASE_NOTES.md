Deep Bhattacharjee and Ushashi Bhattacharya, *The Pólya–Vinogradov inequality with log log q*.

- Theorem 1.1: |∑_{n ≤ x} χ(n)| ≤ C √q log log q for every primitive character χ modulo q ≥ 3,
  the bound Montgomery and Vaughan proved under the generalised Riemann hypothesis.
- Theorem 1.3: |L'/L(1, χ)| ≤ C log log q for every nonprincipal χ, and
  −C log q log log q ≤ γ_q ≤ C log q for the Euler–Kronecker constants of Q(ζ_q), q prime.

The input is OpenAI's zero-free half-plane Re s > 7/8 (https://github.com/openai/math), whose
Lean 4 proof is compiled with ours. The Lean proofs use only propext, Classical.choice and
Quot.sound; four programs in Python, Julia, C and C++ check the numerical steps.

Release v1.2.0 adds the version of the paper submitted to the Annals of Mathematics and posted as
Hexagon 2610.00256v3: `paper/paper1/PolyaVinogradovLogLog-Annals.pdf` (22 pages, class aomart) and
its source `paper/paper2/PolyaVinogradovLogLog-Annals-tex.zip`, both also attached to the release.
After Theorem 1.2 it names the Lean theorem
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` and states that this archive
compiles OpenAI's Lean sources unchanged with the paper's own proofs. The submission notes, cover
letter and Hexagon form are in `journal/submission-annals/`. The mathematics and the Lean
formalisation are unchanged.

Files: the Annals version (`PolyaVinogradovLogLog-Annals.pdf`, `PolyaVinogradovLogLog-Annals-tex.zip`), the Acta Arithmetica version (`PolyaVinogradovLogLog_final2.pdf`), its LaTeX source with the figures as PNG
(`PolyaVinogradovLogLog_final2-tex.zip`) and the arXiv tarball
(`PolyaVinogradovLogLog_final2-arxiv.tar.gz`). The archive of the tag holds the Lean project, the
check programs and the master zip `MasterPolyaVinogradovLogLog_masterzipfinal2.zip`.
