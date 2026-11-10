# Analyze goldens — V1 front-end

Goldens for the V1 front-end (`pyAnalyzeLaurel`), the shipping Python→Laurel→Core
pipeline. Regenerate from the package root with `lake exe pyAnalyzeUpdate --update`.

These files used to live in `../expected_laurel/`, which now holds the **V2**
goldens. For why the two sets sit at those paths — and what currently differs
between them — see [`../expected_laurel/README.md`](../expected_laurel/README.md).
