# Use of AI tools: The Pólya–Vinogradov inequality with log log q

Journal: Annals of Mathematics. Authors: Deep Bhattacharjee (corresponding) and Ushashi Bhattacharya. No AI system is an author.

## The journal's policy (checked 21 October 2026, https://annals.math.princeton.edu/submission-guidelines)

- Authors must be human and take full responsibility for the content of the submission, including its correctness and the integrity and accuracy of its citations.
- AI agents cannot be named authors.
- If an AI tool or LLM contributed an idea, the authors should describe that idea and say where it is in the paper.

The manuscript meets these points in its section "Use of AI tools" (after the last proof, before the references).

## What was done with AI

Claude (Anthropic), used through Claude Code under Deep Bhattacharjee's direction, drafted:
- the proofs;
- the Lean 4 formalisation (`lean/Vinogradov/` in the repository);
- the programs that check the numerical steps;
- the figures and the LaTeX text.

Deep Bhattacharjee chose the problem, directed the work, ran the computations and the Lean build, and set the target journal. The authors checked the manuscript and take full responsibility for it.

## Ideas that came from the AI-assisted work, and where they are

1. Replacing the generalised Riemann hypothesis on the major arcs by the zero-free half-plane: Section 3, Corollary 3.8, Lemma 5.3.
2. A weak form of the Montgomery–Vaughan bound with Selberg's sieve as the only arithmetic input: Section 4 (Theorem 4.1).
3. Selberg's sieve applied in dyadic blocks to prime powers in progressions modulo q: Lemma 6.3.

## Work of others

The zero-free half-plane Re s > 7/8 (Theorem 1.2) is OpenAI's, from "The quasi-Riemann hypothesis: a zero-free half-plane Re s > 7/8", 30 September 2026, https://github.com/openai/math. It has not been refereed. The paper cites it as OpenAI's result and claims nothing about its proof.

## Checks

- Lean 4.34.1 with Mathlib v4.34.1. Main theorems: `Vinogradov.PV.polya_vinogradov_loglog`, `Vinogradov.logDeriv_one_le`, `Vinogradov.sum_logDeriv_one`, `Vinogradov.MV.weak_mv`. They depend only on `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no added axiom.
- Repository: https://github.com/creelie/Breakthrough-problems-3, release v1.2.0: https://github.com/creelie/Breakthrough-problems-3/releases/tag/v1.2.0
