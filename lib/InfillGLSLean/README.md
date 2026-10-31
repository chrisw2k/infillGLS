# InfillGLSLean

Lean formalization for infill generalized least-squares results.

The project pins Lean 4.35.0 and Mathlib v4.35.0. The finite foundation is in
`InfillGLSLean/`; the complete theorem dependency closure is in
`Manuscript/`.

## Build

    lake build

To build only the theorem closure:

    lake build InfillGLSManuscript

## Endpoints

`Manuscript/ManuscriptEndpoints.lean` re-exports the completed endpoints:

- `L029.manuscriptConsistency_complete`
- `L055.manuscriptNormality_complete`
- `L063.manuscriptVariance_complete`
- `L064.residualScale_rate_decomposition`
- `L065.conditionalMean_bias_tendsto`
