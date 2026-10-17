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

- 22 pages in the IMPAN `amsart` template (12 pt, text width 13.5 cm, text
  height 23 cm, line spread 1.2, equations numbered by section, French
  spacing), four figures; no overfull or underfull boxes, all fonts Type 1.
- Front matter: title with running head; two authors with affiliations,
  emails and ORCID iDs; title-page footnote naming Deep Bhattacharjee as
  corresponding author and the Hexagon preprint 2610.00256v1
  (https://hexagonmath.org/2610.00256v1); abstract of three sentences; MSC
  2020 primary 11L40, secondary 11M06, 11M20, 11L07, 11N13, 11N36, 11R42;
  keywords.
- Back matter: Data and code availability (the Zenodo concept DOI
  10.5281/zenodo.23383715 and the PDF in `preprintPolyaVinogradovLogLog/`,
  with the AI disclosure), Ethical declarations (funding none, competing
  interests none).
- References in alphabetical order of surnames, styled as in the journal's
  examples (no boldface), MathSciNet abbreviations, each DOI on its own line
  below the item; every entry checked against Crossref or the publisher.
- Submission is a single PDF on EditFlow; the LaTeX source is sent after
  acceptance. The submission package is in `journal/submission-acta/`.

## Policy on AI assistance

The journal page (read 17 October 2026) says: AI tools may not be authors;
"the principal mathematical ideas, results, arguments, and proofs presented
in a paper must originate with the authors"; use of AI should as a rule be
limited to language, formatting and checking arguments the authors wrote;
"any substantial use of AI tools beyond such limited assistance must be fully
disclosed in the manuscript"; papers generated in substantial part by AI
without adequate human contribution may be rejected on editorial grounds.
The proofs and the text of this paper were drafted with Claude under Deep
Bhattacharjee's direction (see the AI provenance file), so the Data and code
availability section discloses that, and the authors must have read and
verified every proof before submitting. The Journal of Number Theory
(Elsevier), whose policy asks only for a declaration of generative AI use,
is the alternative.
