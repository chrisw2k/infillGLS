test_that("identity GLS matches least squares without an intercept", {
  set.seed(101)
  x <- rnorm(80)
  y <- 1.7 * x + rnorm(80, sd = 0.4)

  fit <- infill_gls(y, x)
  reference <- stats::lm(y ~ x + 0)

  expect_equal(fit$beta, unname(stats::coef(reference)[["x"]]))
  expect_equal(fit$Q, sum(x^2))
  expect_gt(fit$se, 0)
})

test_that("controls reproduce ordinary least squares under identity covariance", {
  set.seed(102)
  x <- rnorm(100)
  z <- rnorm(100)
  controls <- cbind(intercept = 1, z = z)
  y <- 0.8 * x - 0.4 * z + 2 + rnorm(100, sd = 0.3)

  fit <- infill_gls(y, x, controls)
  reference <- stats::lm(y ~ x + z)

  expect_equal(fit$beta, unname(stats::coef(reference)[["x"]]))
  expect_equal(fit$se, summary(reference)$coefficients["x", "Std. Error"])
})

test_that("a supplied working covariance gives the direct GLS solution", {
  set.seed(103)
  x <- rnorm(12)
  y <- 1.2 * x + rnorm(12)
  K <- diag(seq(1, 2, length.out = 12))

  fit <- infill_gls(y, x, K = K)
  direct <- solve(crossprod(x, solve(K, x)), crossprod(x, solve(K, y)))

  expect_equal(fit$beta, unname(direct))
  expect_equal(infill_gls_ci(fit)[["estimate"]], fit$beta)
})

test_that("invalid working covariance is rejected", {
  expect_error(infill_gls(1:3, 1:3, K = diag(c(1, 0, 1))),
               "positive definite")
})
