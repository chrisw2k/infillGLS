.infillgls_spatial_input <- function(data, coordinates, nonpoint,
                                     compute_distance = TRUE) {
  if (is.character(data) && length(data) == 1L) {
    if (!file.exists(data)) {
      stop("Spatial data file does not exist: ", data, call. = FALSE)
    }
    .infillgls_require_sf("Reading a spatial file")
    data <- sf::st_read(data, quiet = TRUE)
  }

  if (inherits(data, "Spatial")) {
    .infillgls_require_sf("Converting a legacy sp object")
    data <- sf::st_as_sf(data)
  }

  if (inherits(data, "sf")) {
    return(.infillgls_sf_input(data, coordinates, nonpoint, compute_distance))
  }
  if (!is.data.frame(data)) {
    stop(
      "data must be a data frame, sf object, legacy sp Spatial object, or readable spatial-file path.",
      call. = FALSE
    )
  }

  location_matrix <- .infillgls_coordinate_matrix(data, coordinates)
  if (compute_distance && !is.null(coordinates) && is.character(coordinates)) {
    coordinate_names <- tolower(coordinates)
    if (all(coordinate_names %in% c("lon", "lat")) ||
        all(coordinate_names %in% c("longitude", "latitude"))) {
      warning(
        "A plain data frame has no CRS. For longitude/latitude, use an sf object so distances have geographic units.",
        call. = FALSE
      )
    }
  }

  list(
    attributes = data,
    distance = if (compute_distance) as.matrix(stats::dist(location_matrix)) else NULL,
    locations = location_matrix,
    input_class = class(data)[[1L]],
    coordinate_source = "supplied coordinate table",
    distance_method = if (compute_distance) {
      "Euclidean distance in supplied coordinate units"
    } else {
      "Not materialized: an exact factorized covariance was supplied"
    }
  )
}

.infillgls_sf_input <- function(data, coordinates, nonpoint,
                                compute_distance = TRUE) {
  .infillgls_require_sf("Using sf spatial data")
  if (nrow(data) == 0L) {
    stop("Spatial data must contain at least one observation.", call. = FALSE)
  }
  if (any(sf::st_is_empty(data))) {
    stop("Spatial data cannot contain empty geometries.", call. = FALSE)
  }

  attributes <- sf::st_drop_geometry(data)
  if (!is.null(coordinates)) {
    location_matrix <- .infillgls_coordinate_matrix(attributes, coordinates)
    return(list(
      attributes = attributes,
      distance = if (compute_distance) as.matrix(stats::dist(location_matrix)) else NULL,
      locations = location_matrix,
      input_class = "sf",
      coordinate_source = "supplied attribute columns or matrix",
      distance_method = if (compute_distance) {
        "Euclidean distance in supplied coordinate units"
      } else {
        "Not materialized: an exact factorized covariance was supplied"
      }
    ))
  }

  geometry <- sf::st_geometry(data)
  geometry_types <- as.character(sf::st_geometry_type(geometry, by_geometry = TRUE))
  if (all(geometry_types == "POINT")) {
    locations <- geometry
    coordinate_source <- "POINT geometry"
  } else if (identical(nonpoint, "point_on_surface")) {
    locations <- sf::st_point_on_surface(geometry)
    coordinate_source <- "point_on_surface of non-POINT geometry"
  } else if (identical(nonpoint, "centroid")) {
    locations <- sf::st_centroid(geometry)
    coordinate_source <- "centroid of non-POINT geometry"
  } else {
    stop(
      "Non-POINT sf geometries require nonpoint = 'point_on_surface' or 'centroid', or explicit coordinates.",
      call. = FALSE
    )
  }

  location_matrix <- sf::st_coordinates(locations)
  if (ncol(location_matrix) < 2L) {
    stop("Spatial locations must have at least two coordinate dimensions.",
         call. = FALSE)
  }
  location_matrix <- location_matrix[, seq_len(2L), drop = FALSE]
  storage.mode(location_matrix) <- "double"
  distance <- if (compute_distance) {
    result <- sf::st_distance(locations)
    matrix(as.numeric(result), nrow = nrow(data), ncol = nrow(data))
  } else {
    NULL
  }

  list(
    attributes = attributes,
    distance = distance,
    locations = location_matrix,
    input_class = "sf",
    coordinate_source = coordinate_source,
    distance_method = if (compute_distance) {
      "sf::st_distance; units follow the sf CRS"
    } else {
      "Not materialized: an exact factorized covariance was supplied"
    }
  )
}

.infillgls_coordinate_matrix <- function(data, coordinates) {
  if (is.null(coordinates)) {
    stop(
      "coordinates must identify two coordinate columns or supply an n by 2 matrix for a non-sf data frame.",
      call. = FALSE
    )
  }
  location_matrix <- if (is.character(coordinates)) {
    if (length(coordinates) != 2L || !all(coordinates %in% names(data))) {
      stop("Character coordinates must name exactly two columns in data.",
           call. = FALSE)
    }
    as.matrix(data[, coordinates, drop = FALSE])
  } else if (is.matrix(coordinates)) {
    coordinates
  } else {
    stop("coordinates must be a character vector or numeric matrix.",
         call. = FALSE)
  }
  if (!is.numeric(location_matrix) || ncol(location_matrix) != 2L ||
      nrow(location_matrix) != nrow(data)) {
    stop(
      "coordinates must be a numeric matrix with two columns and one row per observation.",
      call. = FALSE
    )
  }
  storage.mode(location_matrix) <- "double"
  if (any(!is.finite(location_matrix))) {
    stop("coordinates must be finite.", call. = FALSE)
  }
  location_matrix
}

.infillgls_require_sf <- function(action) {
  if (!requireNamespace("sf", quietly = TRUE)) {
    stop(
      action, " requires the optional sf package. Install it with install.packages('sf'), or supply a data frame with coordinates.",
      call. = FALSE
    )
  }
}
