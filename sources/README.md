# Source materials

The PDFs in this directory are primary and dependency sources for the Lean
formalization. They are included for citation and transcription checking only;
they are not licensed under this repository's Apache-2.0 license.

`TR1995-711.pdf` is Cox, Ericson, and Mishra, *The Average Case Complexity of
Multilevel Syllogistic* (Courant Institute Technical Report CS-TR 711, 1995).
The dependency sources are `RS93.pdf`, `CS87.pdf`, `COP90.pdf`, `Gur91.pdf`,
and `Lev86.pdf`.

## Vision OCR

From the repository root (requires `pdftoppm`, `pdfinfo`, and
`CURSOR_API_KEY` in `../tokens_ssto.yaml`):

```bash
bash scripts/ocr_pdf_pipeline.sh TR1995-711.pdf
bash scripts/ocr_pdf_pipeline.sh RS93.pdf
bash scripts/ocr_pdf_pipeline.sh CS87.pdf
bash scripts/ocr_pdf_pipeline.sh COP90.pdf
bash scripts/ocr_pdf_pipeline.sh Gur91.pdf
bash scripts/ocr_pdf_pipeline.sh Lev86.pdf
```

The committed `*_vision.md` files are draft transcriptions used to locate and
cross-check statements and proofs. Generated page images, intermediate passes,
and run logs are ignored. A transcription does not supersede its source PDF.
