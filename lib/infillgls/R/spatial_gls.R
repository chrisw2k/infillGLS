#' Fit a spatial generalized least-squares regression
#'
#' spatial_gls is the formula-facing interface for the infill GLS package. It
#' constructs a fixed working covariance from locations and a user-supplied
#' kernel, then reports GLS estimates and working-model normal inference.
#' The kernel is not estimated from the outcome data.
#'
#' @param formula A two-sided model formula. The response must be numeric.
#'   `offset()` terms follow ordinary R formula semantics.
#' @param data An sf object, legacy sp Spatial object, spatial-file path
#'   readable by sf, or data frame.
#' @param treatment Name of one model-matrix column designated as the
#'   paper-facing target coefficient.
#' @param kernel An infillgls_kernel, a function mapping the distance matrix to
#'   a covariance matrix, an n by n covariance matrix, or an exact cached
#'   covariance returned by [factorized_covariance()]. A factorized covariance
#'   bypasses coordinate-distance construction.
#' @param coordinates For a data frame, two column names or an n by 2 numeric
#'   matrix. For sf data, this optionally overrides geometry-derived locations.
#' @param nonpoint How sf geometries other than POINT are represented when
#'   coordinates is NULL. The default errors rather than choosing silently.
#' @return An object of class spatial_gls.
#' @export
spatial_gls <- function(formula, data, treatment, kernel, coordinates = NULL,
                        nonpoint = c("error", "point_on_surface", "centroid")) {
  if (!inherits(formula, "formula") || length(formula) != 3L) {
    stop("formula must have a numeric response and a right-hand side.",
         call. = FALSE)
  }
  if (!is.character(treatment) || length(treatment) != 1L ||
      is.na(treatment) || !nzchar(treatment)) {
    stop("treatment must be the name of one model-matrix column.", call. = FALSE)
  }
  nonpoint <- match.arg(nonpoint)
  uses_factorized_covariance <- .infillgls_is_factorized_covariance(kernel)

  spatial_input <- .infillgls_spatial_input(
    data,
    coordinates,
    nonpoint,
    compute_distance = !uses_factorized_covariance
  )
  model_frame <- stats::model.frame(
    formula,
    data = spatial_input$attributes,
    na.action = stats::na.fail,
    drop.unused.levels = TRUE
  )
  if (nrow(model_frame) != nrow(spatial_input$attributes)) {
    stop(
      "All model variables must be observed; row-dropping NA actions are not supported.",
      call. = FALSE
    )
  }
  outcome <- stats::model.response(model_frame)
  if (is.matrix(outcome) || !is.numeric(outcome) || length(outcome) != nrow(model_frame)) {
    stop("formula must have a single numeric response.", call. = FALSE)
  }
  model_offset <- stats::model.offset(model_frame)
  if (!is.null(model_offset)) {
    if (!is.numeric(model_offset) || length(model_offset) != length(outcome) ||
        any(!is.finite(model_offset))) {
      stop("formula offsets must be finite numeric values.", call. = FALSE)
    }
    # model.matrix excludes offset() terms.  Fit the ordinary GLS problem to
    # y - offset, then put the offset back on the fitted-value scale below.
    outcome <- outcome - model_offset
  }
  design_matrix <- stats::model.matrix(
    stats::terms(model_frame),
    data = model_frame
  )
  if (!treatment %in% colnames(design_matrix)) {
    stop(
      "treatment must exactly match a model-matrix column. Available columns: ",
      paste(colnames(design_matrix), collapse = ", "),
      call. = FALSE
    )
  }
  if (identical(treatment, "(Intercept)")) {
    stop("treatment cannot be the intercept.", call. = FALSE)
  }

  working_covariance <- if (uses_factorized_covariance) {
    kernel
  } else {
    .infillgls_kernel_covariance(kernel, spatial_input$distance)
  }
  fit <- .infillgls_fit_matrix(outcome, design_matrix, working_covariance)
  if (!is.null(model_offset)) {
    fit$fitted_values <- fit$fitted_values + model_offset
  }
  target_index <- match(treatment, names(fit$coefficients))
  # The operator is needed while fitting but is not part of the public fit
  # object; working_covariance retains the supplied exact representation.
  fit$covariance_operator <- NULL

  structure(
    c(
      list(
        call = match.call(),
        formula = formula,
        treatment = treatment,
        Q = unname(fit$information[[target_index]]),
        target_standard_error = sqrt(fit$vcov[target_index, target_index]),
        kernel = kernel,
        kernel_name = .infillgls_kernel_name(kernel),
        distance_matrix = spatial_input$distance,
        locations = spatial_input$locations,
        offset = model_offset,
        spatial_input = list(
          class = spatial_input$input_class,
          coordinate_source = spatial_input$coordinate_source,
          distance_method = spatial_input$distance_method
        ),
        inference = "Working-covariance normal inference"
      ),
      fit
    ),
    class = "spatial_gls"
  )
}

#' @export
coef.spatial_gls <- function(object, ...) {
  object$coefficients
}

#' @export
vcov.spatial_gls <- function(object, ...) {
  object$vcov
}

#' @export
fitted.spatial_gls <- function(object, ...) {
  object$fitted_values
}

#' @export
residuals.spatial_gls <- function(object, ...) {
  object$residuals
}

#' @export
confint.spatial_gls <- function(object, parm, level = 0.95, ...) {
  if (!inherits(object, "spatial_gls")) {
    stop("object must be a spatial_gls fit.", call. = FALSE)
  }
  if (length(level) != 1L || !is.finite(level) || level <= 0 || level >= 1) {
    stop("level must be strictly between zero and one.", call. = FALSE)
  }
  available <- names(object$coefficients)
  if (missing(parm)) {
    parm <- available
  } else if (is.numeric(parm)) {
    parm <- available[parm]
  }
  if (!is.character(parm) || anyNA(match(parm, available))) {
    stop("parm must select fitted coefficient names or positions.", call. = FALSE)
  }
  estimates <- object$coefficients[parm]
  standard_errors <- sqrt(diag(object$vcov))[parm]
  critical_value <- stats::qnorm((1 + level) / 2)
  result <- cbind(
    lower = estimates - critical_value * standard_errors,
    upper = estimates + critical_value * standard_errors
  )
  rownames(result) <- parm
  result
}

#' @export
summary.spatial_gls <- function(object, level = 0.95, ...) {
  if (!inherits(object, "spatial_gls")) {
    stop("object must be a spatial_gls fit.", call. = FALSE)
  }
  if (length(level) != 1L || !is.finite(level) || level <= 0 || level >= 1) {
    stop("level must be strictly between zero and one.", call. = FALSE)
  }
  estimates <- object$coefficients
  standard_errors <- sqrt(diag(object$vcov))
  z_values <- estimates / standard_errors
  p_values <- 2 * stats::pnorm(abs(z_values), lower.tail = FALSE)
  intervals <- stats::confint(object, level = level)
  coefficient_table <- cbind(
    estimates,
    standard_errors,
    z_values,
    p_values,
    intervals[names(estimates), "lower"],
    intervals[names(estimates), "upper"]
  )
  colnames(coefficient_table) <- c(
    "Estimate", "Std. Error", "z value", "Pr(>|z|)", "CI lower", "CI upper"
  )
  structure(
    list(
      call = object$call,
      formula = object$formula,
      treatment = object$treatment,
      coefficients = coefficient_table,
      sigma = sqrt(object$sigma2),
      degrees_freedom = object$degrees_freedom,
      Q = object$Q,
      kernel_name = object$kernel_name,
      inference = object$inference,
      level = level
    ),
    class = "summary.spatial_gls"
  )
}

#' @export
print.spatial_gls <- function(x, ...) {
  cat(
    "Spatial GLS fit with", length(x$coefficients), "coefficient(s),",
    "n =", length(x$residuals), "\n"
  )
  cat("Working kernel:", x$kernel_name, "\n")
  cat(
    "Target", x$treatment, ":",
    format(x$coefficients[[x$treatment]], digits = 6),
    "(SE", format(x$target_standard_error, digits = 6), ")\n"
  )
  invisible(x)
}

#' @export
print.summary.spatial_gls <- function(x, ...) {
  cat("Spatial GLS formula:\n")
  print(x$formula)
  cat("\nWorking kernel:", x$kernel_name, "\n")
  cat("Inference:", x$inference, "\n")
  cat("Target information Q:", format(x$Q, digits = 6), "\n\n")
  stats::printCoefmat(x$coefficients, ...)
  cat(
    "\nResidual scale:", format(x$sigma, digits = 6),
    "on", x$degrees_freedom, "degrees of freedom\n"
  )
  invisible(x)
}
