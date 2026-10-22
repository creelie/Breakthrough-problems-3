# Hexagon submission form: The Pólya–Vinogradov inequality with log log q

Every field of the hexagonmath.org submission form, in the order of the form. This is version 3 of the record hexagon:2610.00256 (the earlier versions are 2610.00256v1 and 2610.00256v2); the change notes are in `HEXAGON-RESUBMISSION.md`.

## 01 The work

**Title** (required)

The Pólya–Vinogradov inequality with log log q

**Abstract** (required, plain text)

We prove that every primitive Dirichlet character chi modulo q >= 3 has character sums sum_{n <= x} chi(n) of size at most C sqrt(q) log log q, with an absolute constant C. Montgomery and Vaughan proved this bound under the generalised Riemann hypothesis, and Paley showed that it is optimal. The only input from outside the paper is the zero-free half-plane Re s > 7/8 for Dirichlet L-functions. On the major arcs this half-plane gives a power saving for twisted prime sums; on the minor arcs we prove a weak form of the Montgomery-Vaughan bound for exponential sums with multiplicative coefficients, with Selberg's sieve as the only arithmetic input. The same half-plane gives |L'/L(1, chi)| << log log q for every nonprincipal chi and, for every prime q, the two-sided bound -C log q log log q <= gamma_q <= C log q for the Euler-Kronecker constant of the cyclotomic field Q(zeta_q).

**Primary subject** (required)

math.NT - Number Theory

**Tags**

Polya-Vinogradov inequality, character sums, zero-free regions, Selberg sieve, Euler-Kronecker constants

**Cross-list subjects**

- math.CV - Complex Variables

**MSC2020 codes**

- MSC code 1: 11L40 (primary)
- MSC code 2: 11M06
- MSC code 3: 11M20
- MSC code 4: 11L07
- MSC code 5: 11N13
- MSC code 6: 11N36
- MSC code 7: 11R42

**arXiv identifier** (optional)

Leave empty: the paper is not on arXiv.

## 02 Contributors

AI systems cannot be contributors; none is listed. In citation order:

1. Deep Bhattacharjee (submitting contributor). ORCID 0000-0003-0466-750X. Affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; formerly, University of Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal, India. Email itsdeep@live.com.
2. Ushashi Bhattacharya. ORCID 0009-0002-2254-3914. Affiliation: Formerly, National Taiwan University, Taipei 106319, Taiwan. Email rai.bhattacharya.in@gmail.com.

**Which of the following best describes the text of your contribution?** (required)

**A mix of human-written and AI-generated.**

**Which of the following best describes the human understanding of your contribution at time of submission?** (required)

**Some parts of this contribution, but not all, have been checked and understood by a human.**

**Provenance statement** (optional, paste as is)

The proofs, the Lean 4 formalisation, the checking programs and the text were drafted with Claude (Anthropic) through Claude Code under the direction of Deep Bhattacharjee, who ran the computations and the Lean build. Every proof is formalised in Lean 4 (Lean 4.34.1, Mathlib v4.34.1) and compiled together with the unchanged Lean sources of OpenAI's zero-free half-plane Re s > 7/8; the main theorems depend only on propext, Classical.choice and Quot.sound, with no sorry. The half-plane is OpenAI's unrefereed preprint of 30 September 2026 and is the one result used without proof. Release v1.2.0: https://github.com/creelie/Breakthrough-problems-3/releases/tag/v1.2.0. Both authors approved the final version.

## 03 Tools used

- Anthropic - Claude (Claude Code)
- Lean community - Lean 4
- Other - Python
- Other - Julia
- Other - C
- Other - C++

## 04 Formalization

- https://github.com/creelie/Breakthrough-problems-3/tree/v1.2.0/lean

## 05 Files and license

**Source files or ZIP** (required)

`paper/paper2/PolyaVinogradovLogLog-Annals-tex.zip`: `pvloglog-annals.tex` with the bibliography inside, `aomart.cls` and `figures/`; pdflatex compiles it on its own. The compiled paper is `paper/paper1/PolyaVinogradovLogLog-Annals.pdf` (22 pages).

**AI provenance files** (optional)

`AI-PROVENANCE-HEXAGON.md` (this folder).

**License** (required)

CC BY 4.0 - Creative Commons Attribution 4.0

## Related links (not form fields)

- Lean formalisation and checks: https://github.com/creelie/Breakthrough-problems-3/releases/tag/v1.2.0
- Earlier versions of this record: https://hexagonmath.org/2610.00256v1 and https://hexagonmath.org/2610.00256v2
- Journal field (if asked): submitted to the Annals of Mathematics.

The GitHub release link stands for the code; the Zenodo DOI of release v1.2.0 is added here when Zenodo mints it.
