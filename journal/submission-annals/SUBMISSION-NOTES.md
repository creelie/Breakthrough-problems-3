# Annals of Mathematics submission: The Pólya–Vinogradov inequality with log log q

- Submit at https://ef.msp.org/submit/annals (the online system the journal uses for papers submitted after 22 August 2026).
- Upload: `paper/paper1/PolyaVinogradovLogLog-Annals.pdf` (22 pages). Keep `paper/paper2/PolyaVinogradovLogLog-Annals-tex.zip` for when the source is requested; it builds with `pdflatex` (aomart.cls is included).
- Author fee: none. The Annals charges no article publishing charges.
- Format: the journal's own class `aomart`; abstract of about 130 words with no citations; MSC 2020 and keywords; every reference is cited, with titles and page ranges; no forced line or page breaks.
- AI: see `AI-USE-NOTE.md`; the manuscript has a "Use of AI tools" section as the journal asks.
- The paper's own archive is cited as the GitHub release v1.2.0; its Zenodo DOI is added when Zenodo mints it.
- Paste the text of `COVER-LETTER-ANNALS.md` into the cover-letter field.

## Changes from the Acta Arithmetica version

- Class `aomart`, no page-geometry hacks.
- New abstract that names the half-plane as the only outside input, in place of the word "unconditionally".
- Removed the paragraph on the first author's unrelated work and its three references.
- Data availability now cites the GitHub release and lists the Lean theorem names; new "Use of AI tools" section in the form the journal asks for.
- Bibliography without forced line breaks.

The mathematics is unchanged.

## Changes in v1.2.0 (Hexagon version 3)

- The paragraph after Theorem 1.2 now names the Lean theorem of OpenAI's formalisation, `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, and says that the archive compiles it unchanged with the paper's own Lean proofs, the kernel accepting it with only propext, Classical.choice and Quot.sound.
- The title-page footnote names both earlier Hexagon versions, and the archive is cited as release v1.2.0.

## How likely is acceptance

Low. The theorem itself is of Annals interest: the optimal Pólya–Vinogradov bound without GRH has been open since 1977. But the hard input is the quasi-Riemann hypothesis, which is OpenAI's unrefereed preprint, and the paper's own contribution is to carry the Montgomery–Vaughan argument through with that half-plane in place of GRH. An editor is likely to see it as a consequence of the half-plane and decline it. If it is declined, Acta Arithmetica (package in `D:\Hexagon\01 PolyaVinogradovLogLog\submission-acta`) remains the realistic home. Duke Mathematical Journal is not an option: Duke University Press does not accept work substantially written by generative AI.
