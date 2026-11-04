# Kindle export

The repository's canonical manuscript is `manuscript/`. Do not edit an exported EPUB as the master; rebuild it from the Markdown so chapter order, formulas, and wording remain in sync.

## Build a review EPUB

Install Pandoc, open PowerShell at the repository root, and run:

```powershell
./publishing/build-kindle.ps1
```

The script reads the linked Markdown files in `manuscript/SUMMARY.md` and writes a reflowable EPUB 3 review artifact to `build/kindle/Advanced-Lean-for-Mathematics.epub`. It uses the same `\\(...\\)` and `\\[...\\]` math delimiters as the manuscript and asks Pandoc to convert formulas to MathML. The generated directory is ignored by Git.

The script checks that every linked Markdown file exists and stays inside `manuscript/`. Run `python scripts/check_chapter_coverage.py --strict` and `lake build Book` before making a release build. The Lean build checks the extracted examples; it does not check the EPUB's visual layout or prove every statement in the prose.

## Review before upload

Open the EPUB in Kindle Previewer and inspect phone, tablet, and E Ink views at several text sizes. Check chapter navigation, the contents page, formulas, links, code indentation and wrapping, and any figures and alternative text. Then use KDP's upload preview for a final check. Math rendering can vary across reading apps, so a successful EPUB conversion is not a substitute for visual review.

The metadata uses the working title. Add the final title, subtitle, author name, copyright notice, and cover details only after those decisions and permissions are settled. KDP accepts EPUB and KPF for eBooks and recommends validating an EPUB with Kindle Previewer. KDP does not require an ISBN for an eBook; print editions have separate ISBN requirements.

## Official guidance

- [KDP supported eBook manuscript formats](https://kdp.amazon.com/en_US/help/topic/G200634390)
- [Kindle Previewer](https://kdp.amazon.com/en_US/help/topic/G202131170)
- [KDP metadata guidelines](https://kdp.amazon.com/en_US/help/topic/G201097560)
- [KDP ISBN and imprint guidance](https://kdp.amazon.com/en_US/help/topic/G7DMSKCM9DVS65TC)
- [Pandoc EPUB guide](https://pandoc.org/epub.html)
- [Pandoc math support](https://pandoc.org/MANUAL.html#math)
