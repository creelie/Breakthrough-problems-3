# Target journal: Acta Arithmetica

| Item | Details |
|---|---|
| Journal | Acta Arithmetica |
| Publisher | Institute of Mathematics, Polish Academy of Sciences (IMPAN) |
| ISSN | 0065-1036 (print), 1730-6264 (online) |
| Homepage | https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica |
| Submission | https://ef.msp.org/submit/impan_ActaArith (MSP EditFlow) |
| Template | `amsart`, 12 pt, text width 13.5 cm, as in `paper/primroot.tex` |
| Open access | optional, CC BY, for a fee of 400 euros |

## Scope fit

Acta Arithmetica publishes research papers in number theory; its editors
include D. R. Heath-Brown, J. Kaczorowski, W. M. Schmidt and U. Zannier. The
paper is an analytic number theory article (14 pages): from the zero-free
half-plane Re s > 7/8 of OpenAI's preprint it proves that the least prime
primitive root is O((τ(p-1)^2 log p)^(8+η)), hence Vinogradov's conjecture
g(p) = O_ε(p^ε), that character sums satisfy
∑_{n≤x} χ(n) ≪ q^ε x^(7/8+ε), hence Vinogradov's conjecture that they are o(x)
for x ≥ q^η, and that the Pólya–Vinogradov inequality holds with the optimal
factor √q log log q for primitive characters, which Montgomery and Vaughan
proved under GRH. A Lean 4 verification covers the whole chain, with
Montgomery–Vaughan's Corollary 1 as a stated hypothesis of the last result. The result depends on
that preprint, which is unrefereed; a referee will need its Lean verification
or a published version. The Journal of Number Theory and Mathematika are
alternatives.

## Length and format

- 14 pages in `amsart` 12 pt with a 13.5 cm text width.
- Front matter, all present: title, author with address and emails, abstract
  (5 sentences, under the 200-word limit), MSC 2020 codes (11A07, 11L40,
  11M06, 11N13, 68V15), keywords.
- Submission is a single PDF on EditFlow; the LaTeX source is sent after
  acceptance. The arXiv tarball in `dist/` contains the source.
- The submission form asks for a cover letter, suggested referees if wished,
  and competing interests.

## Policy on AI assistance

The journal page (checked 14 October 2026) states no policy on generative AI.
The paper's Data availability section names the archive; the Lean
formalisation and the programs are the record of the computations. The author
is responsible for every statement, the references included.
