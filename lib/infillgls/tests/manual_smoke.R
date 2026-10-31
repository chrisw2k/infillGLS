project_root <- Sys.getenv("INFILLGLS_ROOT", unset = getwd())
project_root <- normalizePath(project_root, winslash = "/", mustWork = TRUE)
source(file.path(project_root, "lib", "infillgls", "R", "infill_gls.R"))
source(file.path(project_root, "lib", "infillgls", "R", "kernels.R"))
source(file.path(project_root, "lib", "infillgls", "R", "spatial_data.R"))
source(file.path(project_root, "lib", "infillgls", "R", "spatial_gls.R"))

set.seed(902)
x <- stats::rnorm(80)
z <- stats::rnorm(80)
y <- 1.25 * x - 0.5 * z + 2 + stats::rnorm(80, sd = 0.3)
fit <- infill_gls(y, x, cbind(intercept = 1, z = z))
reference <- stats::lm(y ~ x + z)

stopifnot(isTRUE(all.equal(
  fit$beta,
  unname(stats::coef(reference)[["x"]]),
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  fit$se,
  summary(reference)$coefficients["x", "Std. Error"],
  tolerance = 1e-10
)))
stopifnot(fit$Q > 0)

spatial_data <- data.frame(
  outcome = y,
  treatment = x,
  control = z,
  east = seq(0, 79),
  north = rep(c(0, 1), length.out = 80)
)
identity_kernel <- function(distance) {
  diag(nrow(distance))
}
spatial_fit <- spatial_gls(
  outcome ~ treatment + control,
  data = spatial_data,
  treatment = "treatment",
  kernel = identity_kernel,
  coordinates = c("east", "north")
)
stopifnot(isTRUE(all.equal(
  coef(spatial_fit)[["treatment"]],
  unname(stats::coef(reference)[["x"]]),
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  spatial_fit$Q,
  1 / solve(crossprod(model.matrix(reference)))[2, 2],
  tolerance = 1e-10
)))
matrix_fit <- spatial_gls(
  outcome ~ treatment + control,
  data = spatial_data,
  treatment = "treatment",
  kernel = diag(nrow(spatial_data)),
  coordinates = c("east", "north")
)
stopifnot(isTRUE(all.equal(coef(matrix_fit), coef(spatial_fit), tolerance = 1e-10)))

matern_fit <- spatial_gls(
  outcome ~ treatment + control,
  data = spatial_data,
  treatment = "treatment",
  kernel = matern1_kernel(range = 10, nugget = 0.05),
  coordinates = c("east", "north")
)
matern_summary <- summary(matern_fit)
stopifnot(inherits(matern_fit, "spatial_gls"))
stopifnot(all(is.finite(coef(matern_fit))))
stopifnot(all(diag(matern_fit$working_covariance) > 1))
stopifnot(all(matern_summary$coefficients[, "Pr(>|z|)"] >= 0))
stopifnot(all(matern_summary$coefficients[, "Pr(>|z|)"] <= 1))
stopifnot(all(is.finite(confint(matern_fit))))

# Formula offsets use ordinary R formula semantics: they are not estimated as
# a regression coefficient, but are retained on the fitted-value scale.
offset_data <- transform(spatial_data, known_offset = seq_along(outcome) / 50)
offset_fit <- spatial_gls(
  outcome ~ treatment + control + offset(known_offset),
  data = offset_data,
  treatment = "treatment",
  kernel = identity_kernel,
  coordinates = c("east", "north")
)
offset_reference <- stats::lm(
  outcome ~ treatment + control + offset(known_offset),
  data = offset_data
)
stopifnot(isTRUE(all.equal(
  coef(offset_fit),
  stats::coef(offset_reference),
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  fitted(offset_fit),
  stats::fitted(offset_reference),
  tolerance = 1e-10
)))

# An exact factorized covariance is a reusable alternative representation of a
# dense SPD K.  Its spatial path deliberately does not construct distances.
diagonal_covariance <- diag(seq(1, 2, length.out = nrow(spatial_data)))
factorized_covariance_operator <- factorized_covariance(diagonal_covariance)
dense_covariance_fit <- spatial_gls(
  outcome ~ treatment + control,
  data = spatial_data,
  treatment = "treatment",
  kernel = diagonal_covariance,
  coordinates = c("east", "north")
)
factorized_covariance_fit <- spatial_gls(
  outcome ~ treatment + control,
  data = spatial_data,
  treatment = "treatment",
  kernel = factorized_covariance_operator,
  coordinates = c("east", "north")
)
direct_design <- stats::model.matrix(
  outcome ~ treatment + control,
  data = spatial_data
)
direct_Kinv_outcome <- solve(diagonal_covariance, spatial_data$outcome)
direct_Kinv_design <- solve(diagonal_covariance, direct_design)
direct_gram <- crossprod(direct_design, direct_Kinv_design)
direct_coefficients <- drop(solve(
  direct_gram,
  crossprod(direct_design, direct_Kinv_outcome)
))
names(direct_coefficients) <- colnames(direct_design)
direct_residuals <- spatial_data$outcome - drop(direct_design %*% direct_coefficients)
direct_sigma2 <- drop(crossprod(
  direct_residuals,
  solve(diagonal_covariance, direct_residuals)
)) / (nrow(spatial_data) - ncol(direct_design))
direct_vcov <- direct_sigma2 * solve(direct_gram)
direct_Q <- 1 / solve(direct_gram)["treatment", "treatment"]
direct_se <- sqrt(direct_vcov["treatment", "treatment"])
direct_ci <- c(
  lower = direct_coefficients[["treatment"]] - stats::qnorm(0.975) * direct_se,
  upper = direct_coefficients[["treatment"]] + stats::qnorm(0.975) * direct_se
)
stopifnot(is.null(factorized_covariance_fit$distance_matrix))
stopifnot(isTRUE(all.equal(
  coef(factorized_covariance_fit),
  direct_coefficients,
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  factorized_covariance_fit$Q,
  direct_Q,
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  factorized_covariance_fit$sigma2,
  direct_sigma2,
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  vcov(factorized_covariance_fit),
  direct_vcov,
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  confint(factorized_covariance_fit)["treatment", ],
  direct_ci,
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  coef(factorized_covariance_fit),
  coef(dense_covariance_fit),
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  factorized_covariance_fit$Q,
  dense_covariance_fit$Q,
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  factorized_covariance_fit$sigma2,
  dense_covariance_fit$sigma2,
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  vcov(factorized_covariance_fit),
  vcov(dense_covariance_fit),
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(
  confint(factorized_covariance_fit),
  confint(dense_covariance_fit),
  tolerance = 1e-10
)))

scaled_operator <- scale_factorized_covariance(factorized_covariance_operator, 2.5)
refactored_scaled_operator <- factorized_covariance(2.5 * diagonal_covariance)
scaled_fit <- infill_gls(y, x, cbind(intercept = 1, z = z), K = scaled_operator)
refactored_scaled_fit <- infill_gls(
  y,
  x,
  cbind(intercept = 1, z = z),
  K = refactored_scaled_operator
)
stopifnot(isTRUE(all.equal(
  scaled_fit$coefficients,
  refactored_scaled_fit$coefficients,
  tolerance = 1e-10
)))
stopifnot(isTRUE(all.equal(scaled_fit$Q, refactored_scaled_fit$Q,
                           tolerance = 1e-10)))
stopifnot(isTRUE(all.equal(scaled_fit$sigma2, refactored_scaled_fit$sigma2,
                           tolerance = 1e-10)))
stopifnot(isTRUE(all.equal(scaled_fit$vcov, refactored_scaled_fit$vcov,
                           tolerance = 1e-10)))

cat("infillgls base-R and spatial API smoke tests passed.\n")
