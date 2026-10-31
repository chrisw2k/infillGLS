factorized_covariance_fixture <- function() {
  n <- 8L
  upper_factor <- diag(c(1.4, 1.2, 1.5, 1.3, 1.6, 1.1, 1.7, 1.25))
  upper_factor[1, 2] <- 0.15
  upper_factor[2, 4] <- -0.10
  upper_factor[3, 5] <- 0.12
  upper_factor[4, 7] <- 0.08
  upper_factor[6, 8] <- -0.09

  list(
    y = c(2.1, -0.7, 1.8, 0.2, 3.4, -1.2, 0.5, 2.6),
    x = c(-1.5, -0.9, -0.2, 0.4, 0.8, 1.1, 1.7, 2.0),
    z = c(0.3, -0.5, 1.2, -0.8, 0.6, 1.4, -1.1, 0.2),
    K = crossprod(upper_factor)
  )
}

test_that("cached factorized covariance matches an independent direct GLS calculation", {
  fixture <- factorized_covariance_fixture()
  X <- cbind(treatment = fixture$x, intercept = 1, z = fixture$z)
  operator <- factorized_covariance(fixture$K)
  fit <- infill_gls(
    fixture$y,
    fixture$x,
    controls = cbind(intercept = 1, z = fixture$z),
    K = operator
  )

  Kinv_y <- solve(fixture$K, fixture$y)
  Kinv_X <- solve(fixture$K, X)
  gram <- crossprod(X, Kinv_X)
  direct_coefficients <- drop(solve(gram, crossprod(X, Kinv_y)))
  names(direct_coefficients) <- colnames(X)
  direct_residuals <- fixture$y - drop(X %*% direct_coefficients)
  direct_sigma2 <- drop(crossprod(direct_residuals, solve(fixture$K, direct_residuals))) /
    (length(fixture$y) - ncol(X))
  direct_vcov <- direct_sigma2 * solve(gram)
  residualized_x <- fixture$x - drop(
    X[, c("intercept", "z"), drop = FALSE] %*%
      solve(
        crossprod(
          X[, c("intercept", "z"), drop = FALSE],
          solve(fixture$K, X[, c("intercept", "z"), drop = FALSE])
        ),
        crossprod(X[, c("intercept", "z"), drop = FALSE], solve(fixture$K, fixture$x))
      )
  )
  direct_Q <- drop(crossprod(residualized_x, solve(fixture$K, residualized_x)))

  expect_s3_class(operator, "infillgls_factorized_covariance")
  expect_equal(crossprod(operator$cholesky), fixture$K, tolerance = 1e-12)
  expect_equal(fit$coefficients, direct_coefficients, tolerance = 1e-10)
  expect_equal(fit$Q, direct_Q, tolerance = 1e-10)
  expect_equal(fit$sigma2, direct_sigma2, tolerance = 1e-10)
  expect_equal(fit$vcov, direct_vcov, tolerance = 1e-10)
  expect_equal(fit$se, sqrt(direct_vcov["treatment", "treatment"]),
               tolerance = 1e-10)
  expect_equal(
    infill_gls_ci(fit),
    c(
      lower = fit$beta - stats::qnorm(0.975) * fit$se,
      estimate = fit$beta,
      upper = fit$beta + stats::qnorm(0.975) * fit$se
    ),
    tolerance = 1e-12
  )
})

test_that("factorized covariance is accepted by the formula interface without distances", {
  fixture <- factorized_covariance_fixture()
  data <- data.frame(
    outcome = fixture$y,
    treatment = fixture$x,
    control = fixture$z,
    east = seq(0, 70, by = 10),
    north = rep(c(0, 5), length.out = length(fixture$y))
  )
  operator <- factorized_covariance(fixture$K)

  dense_fit <- spatial_gls(
    outcome ~ treatment + control,
    data = data,
    treatment = "treatment",
    kernel = fixture$K,
    coordinates = c("east", "north")
  )
  cached_fit <- spatial_gls(
    outcome ~ treatment + control,
    data = data,
    treatment = "treatment",
    kernel = operator,
    coordinates = c("east", "north")
  )

  expect_equal(dense_fit$distance_matrix, as.matrix(stats::dist(data[c("east", "north")])))
  expect_null(cached_fit$distance_matrix)
  expect_match(cached_fit$spatial_input$distance_method, "Not materialized")
  expect_equal(cached_fit$kernel_name, "exact factorized covariance")
  expect_equal(coef(cached_fit), coef(dense_fit), tolerance = 1e-10)
  expect_equal(cached_fit$Q, dense_fit$Q, tolerance = 1e-10)
  expect_equal(cached_fit$sigma2, dense_fit$sigma2, tolerance = 1e-10)
  expect_equal(vcov(cached_fit), vcov(dense_fit), tolerance = 1e-10)
  expect_equal(cached_fit$target_standard_error, dense_fit$target_standard_error,
               tolerance = 1e-10)
  expect_equal(confint(cached_fit), confint(dense_fit), tolerance = 1e-10)
  expect_equal(
    summary(cached_fit)$coefficients[, "Pr(>|z|)"],
    summary(dense_fit)$coefficients[, "Pr(>|z|)"],
    tolerance = 1e-10
  )
})

test_that("scaling a cached factor matches a factorization of the scaled covariance", {
  fixture <- factorized_covariance_fixture()
  base_operator <- factorized_covariance(fixture$K)
  C <- 2.75
  scaled_operator <- scale_factorized_covariance(base_operator, C)
  refactored_operator <- factorized_covariance(C * fixture$K)
  controls <- cbind(intercept = 1, z = fixture$z)

  scaled_fit <- infill_gls(fixture$y, fixture$x, controls, K = scaled_operator)
  refactored_fit <- infill_gls(fixture$y, fixture$x, controls, K = refactored_operator)

  expect_s3_class(scaled_operator, "infillgls_factorized_covariance")
  expect_equal(
    crossprod(scaled_operator$cholesky),
    C * fixture$K,
    tolerance = 1e-12
  )
  expect_equal(scaled_fit$coefficients, refactored_fit$coefficients,
               tolerance = 1e-10)
  expect_equal(scaled_fit$Q, refactored_fit$Q, tolerance = 1e-10)
  expect_equal(scaled_fit$sigma2, refactored_fit$sigma2, tolerance = 1e-10)
  expect_equal(scaled_fit$vcov, refactored_fit$vcov, tolerance = 1e-10)
  expect_error(scale_factorized_covariance(base_operator, 0), "positive")
})
