To the Editors of the Annals of Mathematics

Dear Editors,

We submit the manuscript "The Pólya–Vinogradov inequality with log log q" by Deep Bhattacharjee and Ushashi Bhattacharya for consideration in the Annals of Mathematics.

The paper proves that every primitive Dirichlet character χ modulo q ≥ 3 satisfies |∑_{n≤x} χ(n)| ≤ C √q log log q with an absolute constant C. Montgomery and Vaughan obtained this bound in 1977 under the generalised Riemann hypothesis, and Paley's theorem of 1932 shows that it cannot be improved beyond the value of C. Without hypothesis, the best general bound has remained √q log q, apart from the saving of Granville and Soundararajan for characters of fixed odd order.

The one result used without proof is the zero-free half-plane Re s > 7/8 for Dirichlet L-functions, established, with a Lean 4 formalisation, in the OpenAI preprint "The quasi-Riemann hypothesis: a zero-free half-plane Re s > 7/8" (30 September 2026). That preprint has not been refereed; the manuscript states the dependence in its introduction and credits the theorem to its authors. Everything else is proved in the paper with effective constants. On the major arcs the half-plane gives a power saving for twisted prime sums; on the minor arcs we prove a weak form of the Montgomery–Vaughan bound for exponential sums with multiplicative coefficients, with Selberg's sieve as the only arithmetic input. The same half-plane gives |L′/L(1, χ)| ≪ log log q and, for every prime q, the bound −C log q log log q ≤ γ_q ≤ C log q for the Euler–Kronecker constants of the cyclotomic fields, where the previous bound valid for all primes was |γ_q| ≪_ε q^ε (Ihara, Murty and Shimura).

Every proof in the paper is formalised in Lean 4 and compiled together with the unchanged Lean sources of the half-plane theorem, so the Lean kernel checks the whole chain from the half-plane to the main theorems; they depend only on the standard axioms propext, Classical.choice and Quot.sound. The formalisation and the checking programs are in the GitHub repository https://github.com/creelie/Breakthrough-problems-3, release v1.2.0: https://github.com/creelie/Breakthrough-problems-3/releases/tag/v1.2.0, archived at Zenodo under doi:10.5281/zenodo.23563651.

In line with the journal's AI policy, the manuscript contains a section "Use of AI tools" that states that the proofs, the formalisation and the text were drafted with Claude (Anthropic) under the authors' direction, and names the ideas that came from that work and where they appear. The authors are the only authors, have checked every statement, and take full responsibility for the paper, including its correctness and its citations.

Earlier versions are the preprints 2610.00256v1 and 2610.00256v2 at hexagonmath.org. The manuscript is not under consideration elsewhere. Deep Bhattacharjee is the corresponding author.

Yours sincerely,

Deep Bhattacharjee (itsdeep@live.com, d.bhattacharjee@erl-forschung.de; ORCID 0000-0003-0466-750X)
Ushashi Bhattacharya (rai.bhattacharya.in@gmail.com; ORCID 0009-0002-2254-3914)
