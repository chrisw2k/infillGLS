#' Construct a Matérn working covariance kernel
#'
#' The kernel uses the normalized Matérn correlation
#' rho(d) = 2^(1 - nu) / Gamma(nu) * (d / range)^nu *
#' BesselK(d / range, nu), with rho(0) = 1. The range must use the same
#' units as the distance matrix supplied to spatial_gls.
#'
#' @param range Positive Matérn scale parameter.
#' @param smoothness Positive Matérn smoothness parameter nu.
#' @param variance Positive working covariance multiplier.
#' @param nugget Nonnegative variance added to the diagonal.
#' @return An infillgls_kernel object accepted by spatial_gls.
#' @export
matern_kernel <- function(range, smoothness = 1, variance = 1, nugget = 0) {
  .infillgls_positive_scalar(range, "range")
  .infillgls_positive_scalar(smoothness, "smoothness")
  .infillgls_positive_scalar(variance, "variance")
  if (length(nugget) != 1L || !is.finite(nugget) || nugget < 0) {
    stop("nugget must be a finite nonnegative scalar.", call. = FALSE)
  }

  covariance <- function(distance) {
    distance <- as.matrix(distance)
    if (!is.numeric(distance) || any(!is.finite(distance)) || any(distance < 0)) {
      stop("distance must be a finite nonnegative numeric matrix.",
           call. = FALSE)
    }
    z <- distance / range
    correlation <- matrix(0, nrow = nrow(z), ncol = ncol(z))
    zero <- z == 0
    correlation[zero] <- 1
    nonzero <- !zero
    correlation[nonzero] <- (2^(1 - smoothness) / gamma(smoothness)) *
      z[nonzero]^smoothness * besselK(z[nonzero], nu = smoothness)
    covariance_matrix <- variance * correlation
    if (nrow(covariance_matrix) == ncol(covariance_matrix)) {
      diag(covariance_matrix) <- diag(covariance_matrix) + nugget
    }
    covariance_matrix
  }

  structure(
    list(
      name = "Matern",
      range = range,
      smoothness = smoothness,
      variance = variance,
      nugget = nugget,
      covariance = covariance
    ),
    class = "infillgls_kernel"
  )
}

#' Construct a Matérn-1 working covariance kernel
#'
#' This is shorthand for matern_kernel with smoothness equal to one.
#'
#' @inheritParams matern_kernel
#' @return An infillgls_kernel object.
#' @export
matern1_kernel <- function(range, variance = 1, nugget = 0) {
  matern_kernel(
    range = range,
    smoothness = 1,
    variance = variance,
    nugget = nugget
  )
}

#' @rdname matern1_kernel
#' @export
matern1 <- function(range, variance = 1, nugget = 0) {
  matern1_kernel(range = range, variance = variance, nugget = nugget)
}

#' @export
print.infillgls_kernel <- function(x, ...) {
  cat(
    x$name, "kernel (range =", format(x$range, digits = 6),
    ", smoothness =", format(x$smoothness, digits = 6),
    ", variance =", format(x$variance, digits = 6),
    ", nugget =", format(x$nugget, digits = 6), ")\n"
  )
  invisible(x)
}

.infillgls_kernel_covariance <- function(kernel, distance) {
  n <- nrow(distance)
  covariance <- if (inherits(kernel, "infillgls_kernel")) {
    kernel$covariance(distance)
  } else if (is.function(kernel)) {
    kernel(distance)
  } else if (is.matrix(kernel)) {
    kernel
  } else {
    stop(
      "kernel must be an infillgls_kernel, a function of a distance matrix, or a covariance matrix.",
      call. = FALSE
    )
  }
  .infillgls_covariance(covariance, n)
}

.infillgls_kernel_name <- function(kernel) {
  if (.infillgls_is_factorized_covariance(kernel)) {
    return("exact factorized covariance")
  }
  if (inherits(kernel, "infillgls_kernel")) {
    return(kernel$name)
  }
  if (is.function(kernel)) {
    return("custom function")
  }
  "supplied covariance matrix"
}

.infillgls_positive_scalar <- function(value, name) {
  if (length(value) != 1L || !is.finite(value) || value <= 0) {
    stop(name, " must be a finite positive scalar.", call. = FALSE)
  }
  invisible(value)
}
