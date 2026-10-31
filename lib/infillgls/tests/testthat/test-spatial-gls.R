test_that("formula-facing spatial GLS with identity covariance matches OLS", {
  set.seed(201)
  n <- 60
  data <- data.frame(
    y = 2 + 1.4 * (x <- rnorm(n)) - 0.3 * (z <- rnorm(n)) + rnorm(n, sd = 0.2),
    x = x,
    z = z,
    east = seq_len(n),
    north = rep(c(0, 1), length.out = n)
  )
  identity_kernel <- function(distance) diag(nrow(distance))

  fit <- spatial_gls(
    y ~ x + z,
    data = data,
    treatment = "x",
    kernel = identity_kernel,
    coordinates = c("east", "north")
  )
  reference <- stats::lm(y ~ x + z, data = data)
  report <- summary(fit)

  expect_s3_class(fit, "spatial_gls")
  expect_equal(coef(fit), stats::coef(reference))
  expect_equal(vcov(fit), stats::vcov(reference))
  expect_equal(fit$Q, 1 / solve(crossprod(stats::model.matrix(reference)))[2, 2])
  expect_true(all(report$coefficients[, "Pr(>|z|)"] >= 0))
  expect_true(all(report$coefficients[, "Pr(>|z|)"] <= 1))
  expect_equal(confint(fit)["x", "lower"], coef(fit)[["x"]] -
    stats::qnorm(0.975) * sqrt(vcov(fit)["x", "x"]))

  matrix_fit <- spatial_gls(
    y ~ x + z,
    data = data,
    treatment = "x",
    kernel = diag(n),
    coordinates = c("east", "north")
  )
  expect_equal(coef(matrix_fit), coef(fit))
})

test_that("Matérn-1 kernels create valid working covariances", {
  distance <- as.matrix(stats::dist(cbind(0:4, rep(0, 5))))
  kernel <- matern1_kernel(range = 2, nugget = 0.05)
  covariance <- infillgls:::.infillgls_kernel_covariance(kernel, distance)

  expect_equal(diag(covariance), rep(1.05, 5))
  expect_equal(covariance, t(covariance))
  expect_silent(chol(covariance))
})

test_that("spatial GLS rejects unspecified or ambiguous spatial inputs", {
  data <- data.frame(y = 1:4, x = 2:5, east = 1:4, north = 5:8)
  identity_kernel <- function(distance) diag(nrow(distance))

  expect_error(
    spatial_gls(y ~ x, data = data, treatment = "x",
                kernel = identity_kernel),
    "coordinates"
  )
  expect_error(
    spatial_gls(y ~ x, data = data, treatment = "not_x",
                kernel = identity_kernel, coordinates = c("east", "north")),
    "model-matrix"
  )
})

test_that("formula offsets follow ordinary R formula semantics", {
  set.seed(202)
  n <- 40
  data <- data.frame(
    y = rnorm(n),
    x = rnorm(n),
    z = rnorm(n),
    known_offset = seq_len(n) / 20,
    east = seq_len(n),
    north = rep(c(0, 1), length.out = n)
  )
  identity_kernel <- function(distance) diag(nrow(distance))
  fit <- spatial_gls(
    y ~ x + z + offset(known_offset),
    data = data,
    treatment = "x",
    kernel = identity_kernel,
    coordinates = c("east", "north")
  )
  reference <- stats::lm(y ~ x + z + offset(known_offset), data = data)

  expect_equal(coef(fit), stats::coef(reference))
  expect_equal(fitted(fit), stats::fitted(reference))
  expect_equal(residuals(fit), stats::residuals(reference))
})

test_that("sf POINT input is supported when sf is installed", {
  skip_if_not_installed("sf")
  data <- data.frame(
    y = c(1, 3, 4, 7),
    x = c(0, 1, 2, 3),
    east = c(0, 1, 2, 3),
    north = c(0, 0, 1, 1)
  )
  spatial_data <- sf::st_as_sf(data, coords = c("east", "north"), crs = 3857)
  identity_kernel <- function(distance) diag(nrow(distance))

  fit <- spatial_gls(y ~ x, spatial_data, treatment = "x",
                     kernel = identity_kernel)
  expect_equal(coef(fit), stats::coef(stats::lm(y ~ x, data = data)))
  expect_match(fit$spatial_input$distance_method, "sf::st_distance")
})
