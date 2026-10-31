#' Fit a generalized least-squares regression with one treatment variable
#'
#' The fitted model is y = beta * x + W gamma + epsilon, with a supplied
#' positive-definite working covariance K.  The returned Q is the GLS
#' information in x after residualizing W.
#'
#' @param y Numeric outcome vector.
#' @param x Numeric treatment vector.
#' @param controls Optional numeric vector, matrix, or data frame of controls.
#' @param K Optional positive-definite working covariance matrix or an
#'   object returned by [factorized_covariance()]. The identity is used when
#'   K is NULL.
#' @return An object of class infill_gls.
#' @export
infill_gls <- function(y, x, controls = NULL, K = NULL) {
  y <- .infillgls_numeric_vector(y, "y")
  x <- .infillgls_numeric_vector(x, "x")
  if (length(y) != length(x)) {
    stop("y and x must have the same length.", call. = FALSE)
  }

  n <- length(y)
  if (n < 2L) {
    stop("At least two observations are required.", call. = FALSE)
  }

  W <- .infillgls_controls(controls, n)
  X <- cbind(treatment = x, W)
  fit <- .infillgls_fit_matrix(y, X, K)
  covariance_operator <- fit$covariance_operator

  Kinv_x <- .infillgls_operator_solve(covariance_operator, x)
  residualized_x <- if (ncol(W) == 0L) {
    x
  } else {
    Kinv_W <- .infillgls_operator_solve(covariance_operator, W)
    control_gram <- crossprod(W, Kinv_W)
    if (qr(control_gram)$rank < ncol(W)) {
      stop("The controls are not full rank in the GLS metric.", call. = FALSE)
    }
    control_projection <- solve(control_gram, crossprod(W, Kinv_x))
    x - drop(W %*% control_projection)
  }
  Q <- drop(crossprod(
    residualized_x,
    .infillgls_operator_solve(covariance_operator, residualized_x)
  ))
  if (!is.finite(Q) || Q <= 0) {
    stop("The residualized treatment must have positive GLS information.",
         call. = FALSE)
  }

  structure(
    list(
      coefficients = fit$coefficients,
      beta = unname(fit$coefficients[["treatment"]]),
      controls = colnames(W),
      Q = Q,
      sigma2 = fit$sigma2,
      vcov = fit$vcov,
      se = sqrt(fit$vcov["treatment", "treatment"]),
      residuals = fit$residuals,
      fitted_values = fit$fitted_values,
      degrees_freedom = fit$degrees_freedom,
      working_covariance = fit$working_covariance
    ),
    class = "infill_gls"
  )
}

#' Construct a normal confidence interval for the treatment coefficient
#'
#' @param object An object returned by infill_gls.
#' @param level Confidence level strictly between zero and one.
#' @return A named numeric vector with lower, estimate, and upper entries.
#' @export
infill_gls_ci <- function(object, level = 0.95) {
  if (!inherits(object, "infill_gls")) {
    stop("object must be an infill_gls fit.", call. = FALSE)
  }
  if (length(level) != 1L || !is.finite(level) || level <= 0 || level >= 1) {
    stop("level must be strictly between zero and one.", call. = FALSE)
  }
  critical_value <- stats::qnorm((1 + level) / 2)
  c(
    lower = object$beta - critical_value * object$se,
    estimate = object$beta,
    upper = object$beta + critical_value * object$se
  )
}

#' @export
print.infill_gls <- function(x, ...) {
  cat("GLS treatment coefficient:", format(x$beta, digits = 6), "\n")
  cat("Residual scale:", format(sqrt(x$sigma2), digits = 6),
      "  Q:", format(x$Q, digits = 6), "\n")
  invisible(x)
}

#' Cache an exact dense covariance as a Cholesky operator
#'
#' Factorizes an exact supplied symmetric positive-definite covariance once and
#' returns an object that can be reused as `K` in [infill_gls()] or as `kernel`
#' in [spatial_gls()]. Reusing the object avoids refactoring the covariance for
#' each fit. The operator represents exactly `t(R) %*% R`, where `R` is the
#' stored upper Cholesky factor of `K`; it is not a low-rank approximation.
#'
#' @param K A finite symmetric positive-definite numeric matrix.
#' @return An `infillgls_factorized_covariance` object.
#' @export
factorized_covariance <- function(K) {
  if (!is.numeric(K)) {
    stop("K must be numeric.", call. = FALSE)
  }
  K <- as.matrix(K)
  storage.mode(K) <- "double"
  if (nrow(K) == 0L || nrow(K) != ncol(K)) {
    stop("K must be a nonempty square matrix.", call. = FALSE)
  }
  if (any(!is.finite(K))) {
    stop("K must be finite.", call. = FALSE)
  }
  if (!isTRUE(all.equal(K, t(K), tolerance = sqrt(.Machine$double.eps)))) {
    stop("K must be symmetric.", call. = FALSE)
  }
  cholesky <- try(chol(K), silent = TRUE)
  if (inherits(cholesky, "try-error")) {
    stop("K must be positive definite.", call. = FALSE)
  }
  structure(
    list(
      cholesky = cholesky,
      dimension = nrow(K),
      validated = TRUE
    ),
    class = "infillgls_factorized_covariance"
  )
}

#' Scale an exact factorized covariance operator
#'
#' Returns an operator for `C * K` without reconstructing or refactoring the
#' dense covariance. If `operator` represents `K = t(R) %*% R`, the result
#' stores `sqrt(C) * R`, so it represents exactly `C * K` up to ordinary
#' floating-point arithmetic. This is useful for fixed global covariance-scale
#' sensitivity analyses and does not estimate `C` from outcome errors.
#'
#' @param operator An object returned by [factorized_covariance()] or by this
#'   function.
#' @param C A finite positive covariance scale.
#' @return An `infillgls_factorized_covariance` object for `C * K`.
#' @export
scale_factorized_covariance <- function(operator, C) {
  if (length(C) != 1L || !is.finite(C) || C <= 0) {
    stop("C must be a finite positive scalar.", call. = FALSE)
  }
  if (!.infillgls_is_factorized_covariance(operator)) {
    stop("operator must be returned by factorized_covariance().", call. = FALSE)
  }
  validated_operator <- .infillgls_covariance_operator(
    operator,
    operator$dimension
  )
  structure(
    list(
      cholesky = sqrt(C) * validated_operator$cholesky,
      dimension = validated_operator$dimension,
      validated = TRUE
    ),
    class = "infillgls_factorized_covariance"
  )
}

#' @export
print.infillgls_factorized_covariance <- function(x, ...) {
  cat(
    "Exact factorized covariance operator with",
    x$dimension, "observation(s)\n"
  )
  invisible(x)
}

.infillgls_numeric_vector <- function(value, name) {
  if (!is.numeric(value) || !is.atomic(value)) {
    stop(name, " must be a numeric vector.", call. = FALSE)
  }
  value <- as.numeric(value)
  if (length(value) == 0L || any(!is.finite(value))) {
    stop(name, " must be nonempty and finite.", call. = FALSE)
  }
  value
}

.infillgls_controls <- function(controls, n) {
  if (is.null(controls)) {
    return(matrix(numeric(0), nrow = n, ncol = 0L))
  }
  if (is.data.frame(controls)) {
    controls <- as.matrix(controls)
  }
  if (!is.numeric(controls)) {
    stop("controls must be numeric.", call. = FALSE)
  }
  controls <- as.matrix(controls)
  storage.mode(controls) <- "double"
  if (nrow(controls) != n) {
    stop("controls must have one row per observation.", call. = FALSE)
  }
  if (any(!is.finite(controls))) {
    stop("controls must be finite.", call. = FALSE)
  }
  if (is.null(colnames(controls))) {
    colnames(controls) <- paste0("control_", seq_len(ncol(controls)))
  }
  controls
}

.infillgls_covariance <- function(K, n) {
  if (is.null(K)) {
    return(diag(n))
  }
  if (!is.numeric(K)) {
    stop("K must be numeric.", call. = FALSE)
  }
  K <- as.matrix(K)
  storage.mode(K) <- "double"
  if (!identical(dim(K), c(n, n))) {
    stop("K must be an n by n matrix.", call. = FALSE)
  }
  if (any(!is.finite(K))) {
    stop("K must be finite.", call. = FALSE)
  }
  if (!isTRUE(all.equal(K, t(K), tolerance = sqrt(.Machine$double.eps)))) {
    stop("K must be symmetric.", call. = FALSE)
  }
  if (inherits(try(chol(K), silent = TRUE), "try-error")) {
    stop("K must be positive definite.", call. = FALSE)
  }
  K
}

.infillgls_is_factorized_covariance <- function(K) {
  inherits(K, "infillgls_factorized_covariance")
}

.infillgls_covariance_operator <- function(K, n) {
  if (.infillgls_is_factorized_covariance(K)) {
    if (!is.list(K) || !identical(K$dimension, n)) {
      stop("The factorized covariance must have one row and column per observation.",
           call. = FALSE)
    }
    cholesky <- K$cholesky
    # Public constructors make and mark an upper, finite Cholesky factor. On
    # repeated county-scale fits, trust that immutable-by-convention object so
    # validation itself does not allocate another O(n^2) lower triangle.
    if (isTRUE(K$validated)) {
      if (!is.numeric(cholesky) || !is.matrix(cholesky) ||
          !identical(dim(cholesky), c(n, n))) {
        stop("The factorized covariance has an invalid Cholesky factor.",
             call. = FALSE)
      }
      return(list(
        kind = "factorized",
        dimension = n,
        cholesky = cholesky,
        working_covariance = K
      ))
    }
    if (!is.numeric(cholesky)) {
      stop("The factorized covariance has an invalid Cholesky factor.",
           call. = FALSE)
    }
    cholesky <- as.matrix(cholesky)
    storage.mode(cholesky) <- "double"
    if (!identical(dim(cholesky), c(n, n)) || any(!is.finite(cholesky)) ||
        any(diag(cholesky) <= 0)) {
      stop("The factorized covariance has an invalid Cholesky factor.",
           call. = FALSE)
    }
    lower_triangle <- cholesky[lower.tri(cholesky)]
    if (length(lower_triangle) > 0L &&
        any(abs(lower_triangle) > sqrt(.Machine$double.eps))) {
      stop("The factorized covariance must store an upper Cholesky factor.",
           call. = FALSE)
    }
    return(list(
      kind = "factorized",
      dimension = n,
      cholesky = cholesky,
      working_covariance = K
    ))
  }

  covariance <- .infillgls_covariance(K, n)
  list(
    kind = "dense",
    dimension = n,
    covariance = covariance,
    working_covariance = covariance
  )
}

.infillgls_operator_solve <- function(operator, right_hand_side) {
  if (!is.list(operator) || !operator$kind %in% c("dense", "factorized")) {
    stop("operator must be an internal covariance operator.", call. = FALSE)
  }
  is_vector <- is.null(dim(right_hand_side))
  right_hand_side <- as.matrix(right_hand_side)
  storage.mode(right_hand_side) <- "double"
  if (nrow(right_hand_side) != operator$dimension) {
    stop("The right-hand side has incompatible covariance dimension.",
         call. = FALSE)
  }

  solution <- if (identical(operator$kind, "dense")) {
    solve(operator$covariance, right_hand_side)
  } else {
    # If K = t(R) R for the cached upper factor R, solve t(R) z = b and
    # R x = z. `transpose = TRUE` avoids allocating t(R) for each fit.
    intermediate <- backsolve(
      operator$cholesky,
      right_hand_side,
      upper.tri = TRUE,
      transpose = TRUE
    )
    backsolve(operator$cholesky, intermediate, upper.tri = TRUE)
  }
  if (is_vector) {
    drop(solution)
  } else {
    solution
  }
}

.infillgls_fit_matrix <- function(y, X, K) {
  y <- .infillgls_numeric_vector(y, "y")
  if (!is.numeric(X)) {
    stop("X must be a numeric design matrix.", call. = FALSE)
  }
  X <- as.matrix(X)
  storage.mode(X) <- "double"
  if (nrow(X) != length(y) || ncol(X) == 0L) {
    stop("X must have one or more columns and one row per outcome.",
         call. = FALSE)
  }
  if (any(!is.finite(X))) {
    stop("X must be finite.", call. = FALSE)
  }
  if (is.null(colnames(X))) {
    colnames(X) <- paste0("coefficient_", seq_len(ncol(X)))
  }
  if (anyDuplicated(colnames(X))) {
    stop("X must have unique column names.", call. = FALSE)
  }

  covariance_operator <- .infillgls_covariance_operator(K, length(y))
  Kinv_y <- .infillgls_operator_solve(covariance_operator, y)
  Kinv_X <- .infillgls_operator_solve(covariance_operator, X)
  gram <- crossprod(X, Kinv_X)
  if (qr(gram)$rank < ncol(X)) {
    stop("The design matrix is not full rank in the GLS metric.",
         call. = FALSE)
  }

  coefficients <- drop(solve(gram, crossprod(X, Kinv_y)))
  names(coefficients) <- colnames(X)
  residuals <- y - drop(X %*% coefficients)
  degrees_freedom <- length(y) - ncol(X)
  if (degrees_freedom <= 0L) {
    stop("Positive residual degrees of freedom are required.", call. = FALSE)
  }

  residual_sum_squares <- drop(crossprod(
    residuals,
    .infillgls_operator_solve(covariance_operator, residuals)
  ))
  sigma2 <- residual_sum_squares / degrees_freedom
  covariance <- sigma2 * solve(gram)
  dimnames(covariance) <- list(colnames(X), colnames(X))
  information <- 1 / diag(solve(gram))
  names(information) <- colnames(X)

  list(
    coefficients = coefficients,
    residuals = residuals,
    fitted_values = drop(X %*% coefficients),
    degrees_freedom = degrees_freedom,
    residual_sum_squares = residual_sum_squares,
    sigma2 = sigma2,
    vcov = covariance,
    information = information,
    design_matrix = X,
    gram = gram,
    working_covariance = covariance_operator$working_covariance,
    covariance_operator = covariance_operator
  )
}
