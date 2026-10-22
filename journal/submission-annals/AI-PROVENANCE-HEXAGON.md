# AI provenance: The Pólya–Vinogradov inequality with log log q

Authors: Deep Bhattacharjee and Ushashi Bhattacharya. No AI system is an author or contributor.

## How the work was produced

Deep Bhattacharjee chose the problem, directed the work, ran the computations and the Lean build, and set the target journal. Claude (Anthropic), through Claude Code, drafted the proofs, the Lean 4 formalisation, the checking programs in Python, Julia, C and C++, the figures and the text. The authors take full responsibility for the content.

## How the results are checked

Every proof is formalised in Lean 4 (Lean 4.34.1, Mathlib v4.34.1) and compiled together with the unchanged Lean sources of OpenAI's zero-free half-plane. The main theorems Vinogradov.PV.polya_vinogradov_loglog, Vinogradov.logDeriv_one_le, Vinogradov.sum_logDeriv_one and Vinogradov.MV.weak_mv depend only on propext, Classical.choice and Quot.sound; there is no sorry and no added axiom.

## What is not claimed

The zero-free half-plane Re s > 7/8 (Theorem 1.2) is OpenAI's result, from an unrefereed preprint of 30 September 2026 (https://github.com/openai/math). It is the one result used without proof, and the paper claims nothing about it.

## Labels given on the Hexagon form

- Text of the contribution: a mix of human-written and AI-generated.
- Human understanding at submission: some parts, but not all, checked and understood by a human.

## Where everything is

Release v1.2.0: https://github.com/creelie/Breakthrough-problems-3/releases/tag/v1.2.0. The paper's Data availability and Use of AI tools sections say the same.
