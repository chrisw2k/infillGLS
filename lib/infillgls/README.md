# infillgls

`infillgls` provides spatial generalized least squares with a fixed,
user-specified working covariance. It returns GLS estimates, residual-scale
standard errors, normal confidence intervals, normal p-values, fitted values,
and residuals.

## Main interface

```r
fit <- spatial_gls(
  outcome ~ treatment + control_1 + control_2,
  data = regions,
  treatment = "treatment",
  kernel = matern1_kernel(range = 25000, nugget = 0.05),
  coordinates = c("east_m", "north_m")
)

summary(fit)
coef(fit)
vcov(fit)
confint(fit)
```

`treatment` selects the coefficient of interest; the remaining formula terms
are controls. `offset()` terms are supported as known additions to the
outcome. Inference is conditional on the supplied working covariance and uses
normal approximations.

## Data and kernels

The no-dependency path accepts an ordinary data frame with two planar
coordinate columns. With the optional `sf` package installed, `spatial_gls()`
also accepts `sf` objects, legacy `sp` spatial objects, and spatial file paths
such as GeoPackage, Shapefile, and GeoJSON. `sf` inputs use CRS-aware
distances.

For polygons or another non-point `sf` geometry, select a representative
location explicitly:

```r
spatial_gls(
  outcome ~ treatment + control,
  data = polygons,
  treatment = "treatment",
  kernel = matern1_kernel(range = 10000, nugget = 1e-6),
  nonpoint = "point_on_surface"
)
```

`matern_kernel()` implements a normalized Matérn family, and
`matern1_kernel()` is its smoothness-one shortcut. A custom kernel accepts an
`n` by `n` distance matrix and returns a symmetric positive-definite covariance
matrix:

```r
exponential_kernel <- function(distance) exp(-distance / 15000)

fit <- spatial_gls(
  outcome ~ treatment + control,
  data = regions,
  treatment = "treatment",
  kernel = exponential_kernel,
  coordinates = c("east_m", "north_m")
)
```

Kernel ranges use the same units as the distance matrix. For longitude and
latitude data, use an `sf` input so distances are CRS-aware.

## Low-level interface

`infill_gls(y, x, controls, K)` fits a single-target GLS model from an already
constructed positive-definite covariance matrix.

For repeated fits under one fixed covariance, use an exact cached Cholesky
operator:

```r
K_operator <- factorized_covariance(K)
fit <- infill_gls(y, x, controls, K = K_operator)
scaled_operator <- scale_factorized_covariance(K_operator, C)
```

The operator represents `K = t(R) %*% R` and uses triangular solves rather
than refactoring `K` for each fit. For positive `C`, the scaled operator
represents `C * K` without a new factorization.

## Checks

From this package directory, run:

```r
source("tests/manual_smoke.R")
```

With the optional `testthat` dependency installed:

```r
testthat::test_local(".")
```
