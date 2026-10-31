# Formalization modules

This directory contains the specification, supporting lemmas, and completed
Lean proofs for the infill GLS results.

`ManuscriptEndpoints.lean` re-exports the main public endpoints:

- `L029.manuscriptConsistency_complete`
- `L055.manuscriptNormality_complete`
- `L063.manuscriptVariance_complete`
- `L064.residualScale_rate_decomposition`
- `L065.conditionalMean_bias_tendsto`

From `lib/InfillGLSLean`, run `lake build` to build the full project, or
`lake build InfillGLSManuscript` to build this theorem closure only.
