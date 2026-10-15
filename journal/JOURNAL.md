# Target journal: Acta Arithmetica

| Item | Details |
|---|---|
| Journal | Acta Arithmetica |
| Publisher | Institute of Mathematics, Polish Academy of Sciences (IMPAN) |
| ISSN | 0065-1036 (print), 1730-6264 (online) |
| Homepage | https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica |
| Submission | https://ef.msp.org/submit/impan_ActaArith (MSP EditFlow) |
| Template | `amsart`, 12 pt, text width 13.5 cm, as in `paper/pvloglog.tex` |
| Open access | optional, CC BY, for a fee of 400 euros |

## Scope fit

Acta Arithmetica publishes research papers in number theory; its editors
include D. R. Heath-Brown, J. Kaczorowski, W. M. Schmidt and U. Zannier. The
paper is an analytic number theory article of 20 pages. From the zero-free
half-plane Re s > 7/8 of OpenAI's preprint it proves that the Pólya–Vinogradov
inequality holds with the optimal factor √q log log q for every primitive
character, which Montgomery and Vaughan proved under the generalised Riemann
hypothesis; on the minor arcs it proves a weak form of their bound for
exponential sums with multiplicative coefficients, with Selberg's sieve as the
only arithmetic input. From the same half-plane it proves
|L'/L(1, χ)| ≪ log log q and −C log q log log q ≤ γ_q ≤ C log q for the
Euler–Kronecker constants of Q(ζ_q) for every prime q, which Ford, Luca and
Moree proved for a set of primes of density one and which improves the bound
|γ_q| ≪_ε q^ε of Ihara, Murty and Shimura, published in Acta Arithmetica
(137 (2009)). The Lean 4 formalisation covers both theorems with no hypothesis
beyond the preprint's theorem, which is compiled with it. That preprint is
unrefereed; a referee will need its Lean verification or a published version.
The Journal of Number Theory and Mathematika are alternatives.

## Length and format

- 20 pages in `amsart` 12 pt with a 13.5 cm text width, four figures.
- Front matter, all present: title; two authors with addresses, emails and
  ORCID iDs, Deep Bhattacharjee marked as corresponding author; abstract
  (three sentences); MSC 2020 primary 11L40, secondary 11M06, 11M20, 11L07,
  11N13, 11N36, 11R42; keywords.
- Back matter: Data availability (the Zenodo DOI of the Lean formalisation and
  the link to the PDF in `preprintPolyaVinogradovLogLog/`), Competing
  interests (none), Funding (none).
- Submission is a single PDF on EditFlow; the LaTeX source is sent after
  acceptance. `dist/PolyaVinogradovLogLog_final2-tex.zip` and
  `dist/PolyaVinogradovLogLog_final2-arxiv.tar.gz` contain the source with
  the figures as PNG.
- The submission form asks for a cover letter, suggested referees if wished,
  and competing interests.

## Policy on AI assistance

The journal page (checked 14 October 2026) states no policy on generative AI.
The Data availability section states that Deep Bhattacharjee computed the Lean
formalisation and the Julia, C, C++, shell and Python computations with the
help of AI assistance (Claude, Anthropic). The authors are responsible for
every statement, the references included.
