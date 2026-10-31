project_root <- Sys.getenv("INFILLGLS_ROOT", unset = getwd())
project_root <- normalizePath(project_root, winslash = "/", mustWork = TRUE)
package_root <- file.path(project_root, "lib", "infillgls")

if (!requireNamespace("pkgload", quietly = TRUE)) {
  stop("pkgload is required for the package-load smoke test.", call. = FALSE)
}
pkgload::load_all(package_root, quiet = TRUE, export_all = FALSE)

set.seed(1201)
n <- 20
data <- data.frame(
  y = 1 + 0.75 * (x <- stats::rnorm(n)) + stats::rnorm(n, sd = 0.2),
  x = x,
  east = seq_len(n),
  north = rep(c(0, 1), length.out = n)
)
identity_kernel <- function(distance) diag(nrow(distance))
fit <- spatial_gls(
  y ~ x,
  data = data,
  treatment = "x",
  kernel = identity_kernel,
  coordinates = c("east", "north")
)

stopifnot(inherits(fit, "spatial_gls"))
stopifnot(is.matrix(stats::vcov(fit)), identical(dim(stats::vcov(fit)), c(2L, 2L)))
stopifnot(is.finite(summary(fit)$coefficients["x", "Pr(>|z|)"]))
cat("infillgls package-load smoke test passed.\n")
