
################################################################################
################################################################################
###                                                                          ###
### Flow ID: 50                                                              ###
### 4394: Financial Econometrics                                             ###
### 2022-01-10                                                               ###
###                                                                          ###
################################################################################
################################################################################

library(rmgarch)
library(rugarch)
library(Rsolnp)
library(moments)


################################################################################
### Theoretical part - Problem 7, b                                          ###
################################################################################

### Testing for strong stationarity using Monte Carlo simulation
# referencing direct Monte Carlo simulation following R note presented in
# class 2021-11-04

# Gaussian GARCH
draws <- 1e7
set.seed(123)

eps_n <- rnorm(draws)
# \mathbb{E}[\ln(\beta+\alpha\varepsilon_{t}^{2})]
moment_cond <- mean(log(0.96 + 0.041 * eps_n**2))

print(
    paste(
        c(
            "Simulated Gaussian Moment-Cond.:",
            round(moment_cond, 5)
        )
    )
)


# For T distribution (standardized)
set.seed(123)
nu_t_1 <- 2.5
eps_t_1 <- rt(draws, df = 2.5) / sqrt(nu_t_1 / (nu_t_1 - 2))

set.seed(123)
nu_t_2 <- 20
eps_t_2 <- rt(draws, df = 20) / sqrt(nu_t_2 / (nu_t_2 - 2))

# \mathbb{E}[\ln(\beta+\alpha\varepsilon_{t}^{2})]
moment_cond_1 <- mean(log(0.96 + 0.06 * eps_t_1**2))
moment_cond_2 <- mean(log(0.96 + 0.06 * eps_t_2**2))

print(
    paste(
        c(
            "Simulated T Moment-Cond. (nu=2.5):",
            round(moment_cond_1, 5)
        )
    )
)
print(
    paste(
        c(
            "Simulated T Moment-Cond. (nu=20):",
            round(moment_cond_2, 5)
        )
    )
)

################################################################################
### Computational part - Problem 1                                           ###
################################################################################
### Write a code to simulate T observations from the model of                ###
### Tse and Tsui (2002)                                                      ###
################################################################################


simulate_model <- function(obs, p, m, omega, alpha, beta, r, a, b) {
    #' Simulate model by Tse and Tsui (2002)
    #'
    #' @description Provide `obs` simulations from Tse and Tsui (2002) model
    #'
    #' This function features the dynamic varying correlation MGARCH model
    #' from the 2002 paper of Tse and Tsui. It implements the updating rule
    #' for the conditional-correlation matrix R using the standardized
    #' residuals. The function checks for stationarity conditions of the
    #' given parameters. The function has two important methods/subfunctions
    #' described in their own docstrings. It allows for any M parameter (m<obs)
    #' and assumes that the shocks of the univariate GARCH(1,1) processes are
    #' iid Gaussian with unit variance and covariance 0.
    #'
    #'
    #' @param obs integer. Number of periods to simulate (T).
    #' @param p integer. Number of financial return series to simulate.
    #' @param m integer. Number of periods to "look back" when calculating Psi
    #' based on the standardized residuals.
    #' @param omega vector. Omega parameters to simulate sigma from GARCH(1,1)
    #' process (1 x p)
    #' @param alpha vector. Alpha parameters to simulate sigma from GARCH(1,1)
    #' process (1 x p)
    #' @param beta vector. Beta parameters to simulate sigma from GARCH(1,1)
    #' process (1 x p)
    #' @param r matrix. Initial (time-varying) correlation matrix (p x p)
    #' @param a double. Parameter for the updating equation of matrix R
    #' @param b double. Parameter for the updating equation of matrix R
    #'
    #' @return list.
    #'  sigma array: Covariance matrix (p x p x obs)
    #'  y matrix: Simulated financial return series (obs x p)
    #'  r array: Simulated conditional correlation matrix (p x p x obs)
    #'

    # test parameters
    if (min(omega) < 0 || min(alpha) < 0 || min(beta) < 0) {
        stop("GARCH incorrectly specified")
    }
    if (max(alpha + beta) > 1) {
        stop("GARCH incorrectly specified")
    }
    if (a < 0 || b < 0) {
        stop("Updating parameters incorrectly specified")
    }
    if (a + b > 1) {
        stop("Updating parameters incorrectly specified")
    }


    # refactor initial r object into array
    r_array <- array(
        0,
        dim = c(p, p, obs)
    )
    r_array[, , 1] <- r
    r <- r_array

    # covariance-matrix in array with p x p matrix for each t
    sigma <- array(
        0,
        dim = c(p, p, obs)
    )

    # diagonal-matrix in array with p x p matrix for each t
    d <- array(
        0,
        dim = c(p, p, obs)
    )

    # initialize psi as p x p matrix for each t (only used for t > m)
    psi <- array(
        NA,
        dim = c(p, p, obs)
    )


    # initialize diagonal of d at unconditional value of GARCH(1,1)
    diag(d[, , 1]) <- sqrt(omega / (1 - alpha - beta))

    # initialize sigma
    sigma[, , 1] <- d[, , 1] %*% r[, , 1] %*% d[, , 1]


    # initialize y as p x t matrix
    y <- matrix(data = 0, nrow = obs, ncol = p)
    # drawing from univariate distribution as covariance-matrix for epsilon is I
    y[1, ] <- chol(sigma[, , 1]) %*% rnorm(p, mean = 0, sd = 1)


    update_psi <- function() {
        #' Function to update Psi matrix
        #'
        #' @description This function has access to the semi-global space of
        #' `simulate_model()`. Thus it is able to condition on `m` and `t` and
        #' calculate a new Psi matrix.
        #'
        #' @param NA
        #' @return matrix
        #'  Psi matrix at time (t - 1) (p x p)
        #'

        # following Tse and Tsui (2002) return I for m == 1
        if (m == 1) {
            return(
                diag(1, p, p)
            )
        }

        # jump one period for psi if m == p
        # restriction in my design...
        if (m == 2 && t == 2) {
            return(
                matrix(NA, p, p)
            )
        }

        if (t < m) {
            return(
                matrix(NA, p, p)
            )
        } else {
            # extract [(t - m):(t - 1)] observations from diag(sigma) and y
            y_subset <- y[seq(t - m, t - 1), ]
            sigma_subset <- sigma[, , seq(t - m, t - 1)]

            # clever apply over 3rd dimension of array
            sigma_subset <- t(apply(sigma_subset, 3, diag))

            # calculate each eta at each time back till t-m
            eta <- y_subset / sqrt(sigma_subset)

            # define b matrix from Tse and Tsui (2002) (Eq. 4)
            b <- diag(sqrt(apply(eta**2, 2, sum)), nrow = p, ncol = p)

            # apply Tse and Tsui (2002) (Eq. 5)
            psi_t <- solve(b) %*% t(eta) %*% eta %*% solve(b)

            return(
                psi_t
            )
        }
    }

    update_r <- function() {
        #' Function to calculate new conditional correlation matrix R_t
        #'
        #' @description This function has access to the semi-global space of
        #' `simulate_model()`. Thus it is able to condition on `m` and `t` and
        #' calculate a new Psi matrix. The function conditions on t<=m to return
        #' constant R given t<m.
        #'
        #' @param NA
        #' @return matrix
        #'  R matrix at time t (p x p)
        #'

        if (t <= m) {
            return(
                r[, , 1]
            )
        } else {
            r_t <- (1 - a - b) * r[, , 1] + a * psi[, , t - 1] +
                b * r[, , t - 1]
            return(
                r_t
            )
        }
    }

    # main recursion
    for (t in seq(2, obs)) {
        # update volatility of each asset i at time t
        diag(d[, , t]) <- sqrt(omega + alpha * y[t - 1, ]**2 +
            beta * diag(d[, , t - 1]**2))

        # apply `update_r()` and `update_psi()` function to
        # update r and psi matrix
        psi[, , t - 1] <- update_psi()
        r[, , t] <- update_r()

        # update covariance-matrix
        sigma[, , t] <- d[, , t] %*% r[, , t] %*% d[, , t]

        # drawing from univariate dist. as covariance-matrix is I
        y[t, ] <- chol(sigma[, , t]) %*% rnorm(p, mean = 0, sd = 1)

        if (t == obs) {
            # update the last psi matrix (t - 1) for T + 1
            t <- t + 1
            psi[, , t - 1] <- update_psi()
        }
    }


    return(
        list(
            sigma = sigma,
            y = y,
            r = r
        )
    )
}



################################################################################
### Computational part - Problem 2                                           ###
################################################################################
### Write a code to estimate a and b using the two steps Quasi Maximum       ###
### Likelihood estimator for multivariate volatility models discussed in     ###
### Engle (2002)                                                             ###
################################################################################


tvc_filter <- function(etas, a, b, r, m) {
    #' Filter function to calculate conditional correlation and log-likelihood
    #' for any combination of parameters `a` and `b` within constraints
    #'      a > 0, b > 0, a + b < 1
    #'
    #' @param etas vector. Standardized residuals from the univariate GARCH
    #' estimation (p x T).
    #' @param a double. a parameter to use in the calculation of log-likelihood
    #' and updating function for conditional correlaiton.
    #' @param b double. b parameter to use in the calculation of log-likelihood
    #' and updating function for conditional correlaiton.
    #' @param r array. Conditional correlation matrix in array for each t
    #' (p x p x T).
    #' @param m integer. Number of periods to "look back" when calculating Psi
    #' based on the standardized residuals.
    #'
    #' @return list()
    #'  r array. Time varying conditional correlation.
    #'  ll double. Log-likelihood given inputs of the TVC model
    #'

    # dimensions
    p <- ncol(etas)
    obs <- nrow(etas)

    # initialize psi as p x p matrix for each t (only used for t > m)
    psi <- array(
        NA,
        dim = c(p, p, obs)
    )

    # refactor initial r object into array
    r_array <- array(
        0,
        dim = c(p, p, obs)
    )
    r_array[, , 1] <- r
    r <- r_array

    # compute initial log-likelihood contribution
    ll <- etas[1, , drop = 0] %*% solve(r[, , 1]) %*% t(etas[1, , drop = 0]) -
        etas[1, , drop = 0] %*% t(etas[1, , drop = 0]) + log(det(r[, , 1]))


    update_psi <- function() {
        #' Function to update Psi matrix
        #'
        #' @description This function has access to the semi-global space of
        #' `simulate_model()`. Thus it is able to condition on `m` and `t` and
        #' calculate a new Psi matrix.
        #'
        #' @param NA
        #' @return matrix
        #'  Psi matrix at time (t - 1) (p x p)
        #'

        # following Tse and Tsui (2002) return I for m == 1
        if (m == 1) {
            return(
                diag(1, p, p)
            )
        }

        # jump one period for psi if m == p
        # restriction in my design...
        if (m == 2 && t == 2) {
            return(
                matrix(NA, p, p)
            )
        }


        if (t < m) {
            return(
                matrix(NA, p, p)
            )
        } else {
            # extract [(t - m):(t - 1)] observations from eta
            eta_subset <- etas[seq(t - m, t - 1), ]

            # define b matrix from Tse and Tsui (2002) (Eq. 4)
            b <- diag(sqrt(apply(eta_subset**2, 2, sum)), nrow = p, ncol = p)

            # apply Tse and Tsui (2002) (Eq. 5)
            psi_t <- solve(b) %*% t(eta_subset) %*% eta_subset %*% solve(b)

            return(
                psi_t
            )
        }
    }

    update_r <- function() {
        #' Function to calculate new conditional correlation matrix R_t
        #'
        #' @description This function has access to the semi-global space of
        #' `simulate_model()`. Thus it is able to condition on `m` and `t` and
        #' calculate a new Psi matrix. The function conditions on t<=m to return
        #' constant R given t<m.
        #'
        #' @param NA
        #' @return matrix
        #'  R matrix at time t (p x p)
        #'

        if (t <= m) {
            return(
                r[, , 1]
            )
        } else {
            r_t <- (1 - a - b) * r[, , 1] + a * psi[, , t - 1] +
                b * r[, , t - 1]
            return(
                r_t
            )
        }
    }


    for (t in seq(2, obs)) {

        # apply `update_r()` and `update_psi()` function to
        # update r and psi matrix
        psi[, , t - 1] <- update_psi()
        r[, , t] <- update_r()


        # calculate updated ll
        ll <- ll + etas[t, , drop = 0] %*% solve(r[, , t]) %*%
            t(etas[t, , drop = 0]) - etas[t, , drop = 0] %*%
            t(etas[t, , drop = 0]) + log(det(r[, , t]))
    }

    return(
        list(
            "ll" = -(1 / 2) * ll,
            "r" = r
        )
    )
}


estimate_tvc <- function(returns, m, params = c(a = 0.003, b = 0.995)) {
    #' Estimate TVC model on `returns` using QML
    #'
    #' @description Estimate TVC model from Tse and Tsui (2002)
    #'
    #' @param returns matrix. Matrix of financial returns to estimate the TVC
    #' model on. This argument can be of type `data.frame()` or `list()` as
    #' these types are coerced when estimating from rugarch package. (t x p)
    #' @param m integer. Number of periods to "look back" when calculating Psi
    #' based on the standardized residuals.
    #' @param params vector. Named vector of dim (1 x 2). Should be named `a`
    #' and `b`. Defaults to 0.003, 0.995.
    #'
    #' @return list.
    #'  garch_volatilities matrix: Estimated univariate GARCH volatilities for
    #'  each p. (T x p).
    #'  r array: Optimal conditional correlation matrix in array (p x p x T).
    #'  garch_params matrix: Matrix of estimated univariate GARCH. (3 x p).
    #'  params vector: Optimal parameters estimed using QML (1 x 2).
    #'  ll_total double: Total log-likelihood of the TVC model.

    # require external packages
    require(Rsolnp)
    require(rugarch)

    # set limits for optimizer
    lower_limit <- 1e-4
    upper_limit <- 1.0 - lower_limit

    # specify/initialize GARCH(1, 1) model
    # specify model according to specification in Eq. (2) and (3) in exam
    garch_specification <- ugarchspec(
        variance.model = list(model = "sGARCH", garchOrder = c(1, 1)),
        mean.model = list(armaOrder = c(0, 0), include.mean = FALSE)
    )

    # create list of specifications for multifit
    garch_specification <- multispec(
        replicate(ncol(returns), garch_specification)
    )

    # fit all models in multispec
    garch_fit <- multifit(
        multispec = garch_specification, data = returns
    )

    # compute standardized residuals and store them in `n x T` matrix
    etas <- residuals(garch_fit, standardize = TRUE)

    # extract univariate volatility processes and store them in `n x T` matrix
    garch_sigma <- sigma(garch_fit)

    # extract estimated univariate parameters
    garch_params <- coef(garch_fit)

    # calculate unconditional correlation
    eta_correlation <- cor(etas)


    # setup `Rsolnp` object to perform ML estimation
    optimizer <- solnp(
        params,
        fun = function(params, etas, r, m) {
            filter <- tvc_filter(
                etas, params["a"], params["b"], r, m
            )
            ll <- as.numeric(filter$ll)

            # return negative log-likelihood
            return(-ll)
        },

        # stationarity condition a + b < 1
        ineqfun = function(params, ...) {
            params[1] + params[2]
        }, ineqLB = lower_limit, ineqUB = upper_limit,

        # 0 < (a, b) < 1, (a, b) > 0
        LB = c(lower_limit, lower_limit),
        UB = c(upper_limit, upper_limit),

        # supress output (run quietly)
        control = list(trace = 0),

        # additional arguments
        etas = etas, r = eta_correlation, m = m
    )

    # extract estimated parameters
    optimal_params <- optimizer$pars

    # filter dynamic correlation using estimated parameters
    optimal_filter <- tvc_filter(
        etas = etas,
        a = optimal_params[1],
        b = optimal_params[2],
        r = eta_correlation,
        m = m
    )


    # calculate likelihood of volatility component
    # compute each volatility likelihood contribution at time t
    # using method from slide 35 lecture 10
    ll_v <- 0


    for (i in seq(1, nrow(returns))) {
        # R is being impolite with my date-time indices
        ret_i <- as.numeric(returns[i, ])

        ll_v <- ll_v + ncol(returns) * log(2 * pi) +
            log(det(diag(garch_sigma[i, ]))) +
            t(ret_i) %*% solve(diag(garch_sigma[i, ])) %*% ret_i
    }
    ll_v <- -(1 / 2) * ll_v

    # calculate total log-likelihood
    ll_total <- ll_v + optimal_filter$ll

    return(
        list(
            "garch_volatilites" = garch_sigma,
            "r" = optimal_filter$r,
            "garch_params" = garch_params,
            "params" = optimal_params,
            "ll_total" = ll_total
        )
    )
}


################################################################################
### Computational part - Problem 3, a)                                       ###
################################################################################
### Simulate T = 1000 observations from the model using the function you     ###
### created at point 1). Plot the series of simulated returns, time-varying  ###
### variances, and time-varying correlation.                                 ###
################################################################################


set.seed(123)

# run simulation given the information in the exam
sim <- simulate_model(
    obs = 1000,
    p = 2,
    m = 5,
    omega = c(0.01, 0.01),
    alpha = c(0.04, 0.04),
    beta = c(0.95, 0.95),
    r = matrix(data = c(1, 0.8, 0.8, 1), nrow = 2, ncol = 2),
    a = 0.003,
    b = 0.995
)

{
    # plot simulated returns
    par(mfrow = c(3, 2), cex = 0.85)

    ret_y1 <- sim$y[, 1]
    plot(
        ret_y1,
        type = "l",
        xlab = "Time",
        ylab = "Returns",
        lwd = 2
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 0.5
    )
    title(main = "Asset 1 Returns")

    ret_y2 <- sim$y[, 2]
    plot(
        ret_y2,
        type = "l",
        xlab = "Time",
        ylab = "Returns",
        lwd = 2
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 0.5
    )
    title(main = "Asset 2 Returns")

    sigma_y1 <- t(apply(sim$sigma, 3, diag))[, 1]
    plot(
        sigma_y1,
        type = "l",
        xlab = "Time",
        ylab = "Variance",
        lwd = 2
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 0.5
    )
    title(main = "Asset 1 Volatility")

    sigma_y2 <- t(apply(sim$sigma, 3, diag))[, 2]
    plot(
        sigma_y2,
        type = "l",
        xlab = "Time",
        ylab = "Variance",
        lwd = 2
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 0.5
    )
    title(main = "Asset 2 Volatility")

    plot(
        apply(sim$r, 3, function(x) {
            return(x[1, 2])
        }),
        type = "l",
        xlab = "Time",
        ylab = "Correlation",
        lwd = 2
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 0.5
    )
    title(main = "Time-varying Correlation")

    # reset plotting settings
    par(mfrow = c(1, 1))
}



################################################################################
### Computational part - Problem 3, b)                                       ###
################################################################################
### Estimate the parameters of the model using the function you created at   ###
### point 2). Compare the estimated parameters with the true ones.           ###
################################################################################


tvc <- estimate_tvc(
    sim$y,
    m = 5
)

print("Estimated TVC parameters from simulated process")
print(tvc$params)


################################################################################
### Empirical Part                                                           ###
################################################################################
### Consider p = 3 series of your choice from the dji30ret dataset in the    ###
### rugarch package. Multiply the series by 100 and remove the mean.         ###
################################################################################

################################################################################
### Empirical Part - Problem 1                                               ###
################################################################################
### Report descriptive statistics of your choice for the three series.       ###
### Discuss the unconditional distribution of these series and provide       ###
### evidence for the presence of heteroscedasticity.                         ###
################################################################################


download_data <- function(tickers = c()) {
    #' Fetches data from the dji30ret data-set of the rugarch package
    #'
    #' @description Fetches and formats the data of the dji30ret data-set.
    #'
    #' The function defaults to return all assets in the data-set. It
    #' automatically demeans the returns and multiplies them by 100.
    #'
    #'
    #' @param tickers vector (character). Vector of tickers to extract from the
    #' index.
    #'
    #' @return list.
    #'  ret. Demeaned returns of `tickers` subset (or all tickers if default)
    #'  of DJ index (x100)
    #'


    # require external packages
    require(rugarch)

    data(dji30ret)

    ret <- dji30ret

    if (length(tickers) == 0) {
        ret <- ret
    } else {
        ret <- ret[, tickers]
    }


    # demean each series of financial returns
    return_means <- apply(ret, 2, mean)

    for (asset in names(ret)) {
        ret[asset] <- ret[asset] - return_means[asset]
    }

    # multiply by 100
    ret <- ret * 100

    return(
        ret
    )
}

rolling_variance <- function(return_matrix, window_size) {
    #' Function to calculate variance on a rolling basis based
    #' on window-size argument.
    #'
    #' Output is `window_size` observations shorter than input.
    #'
    #' @param return_matrix list. Data-set fetched from rugarch.
    #' @param window_size integer. Window-length to calculate rolling
    #' variance.
    #'
    #' @return data.frame()
    #'


    p <- ncol(return_matrix)
    t <- nrow(return_matrix)

    rolling_var <- matrix(
        data = NA,
        nrow = t,
        ncol = p
    )


    for (i in seq(window_size, t)) {
        rolling_var[i, ] <- diag(
            var(return_matrix[seq(i - window_size, i), ])
        )
    }

    colnames(rolling_var) <- colnames(return_matrix)

    # do data transformations to keep date-time index for plotting
    rolling_var <- data.frame(rolling_var)
    row.names(rolling_var) <- rownames(return_matrix)
    rolling_var <- na.omit(rolling_var)

    return(
        rolling_var
    )
}



assets <- c("IBM", "GE", "JPM")
# download data
dj_returns <- download_data(
    tickers = assets
)

# calculate rolling variance for plotting
dj_rolling <- rolling_variance(
    dj_returns, 25
)


# plot rolling variance
{
    plot_colors <- c("black", "red", "orange")
    plot(
        y = dj_rolling[, 1],
        x = as.Date(rownames(dj_rolling)),
        type = "l",
        ylim = c(0, max(dj_rolling) * 1.1),
        col = plot_colors[1],
        lwd = 1.5,
        ylab = "Variance",
        xlab = "Time"
    )

    lines(
        y = dj_rolling[, 2],
        x = as.Date(rownames(dj_rolling)),
        col = plot_colors[2],
        lwd = 1.5
    )

    lines(
        y = dj_rolling[, 3],
        x = as.Date(rownames(dj_rolling)),
        col = plot_colors[3],
        lwd = 1.5
    )

    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 1
    )
    title("Rolling variance for each asset (window-length 25)")

    # increase legend scaling to 150%
    op <- par(cex = 1.5)

    legend(
        "topleft",
        legend = assets,
        col = plot_colors,
        lty = 1,
        fonts
    )
    # reset plotting settings
    par(mfrow = c(1, 1))
}


{
    plot_colors <- c("black", "red", "orange")
    plot(
        density(dj_returns[, 1]),
        type = "l",
        ylim = c(0, 0.35),
        col = plot_colors[1],
        lwd = 1.5,
        ylab = "Density",
        main = ""
    )

    lines(
        density(dj_returns[, 2]),
        col = plot_colors[2], lwd = 1.5
    )
    lines(
        density(dj_returns[, 3]),
        col = plot_colors[3], lwd = 1.5
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 1
    )
    title("Empirical densities for each asset")

    # increase legend scaling to 150%
    op <- par(cex = 1.5)

    legend(
        "topright",
        legend = assets,
        col = plot_colors,
        lty = 1,
        fonts
    )
    # reset plotting settings
    par(mfrow = c(1, 1))
}


# Descriptive statistics

print("Unconditional correlation")
print(cor(dj_returns))

print("Unconditional skewness")
print(skewness(dj_returns))

print("Unconditional kurtosis")
print(kurtosis(dj_returns))



################################################################################
### Empirical Part - Problem 2                                               ###
################################################################################
### For M = 1,...,5 estimate the model of Tse and Tsui (2002) on the three   ###
### series. Select the value of M that resulted in the highest log           ###
### likelihood value at its maximum.                                         ###
################################################################################

# estimate tvc model for m = 1...5
m_1 <- estimate_tvc(dj_returns, m = 1)
m_2 <- estimate_tvc(dj_returns, m = 2)
m_3 <- estimate_tvc(dj_returns, m = 3)
m_4 <- estimate_tvc(dj_returns, m = 4)
m_5 <- estimate_tvc(dj_returns, m = 5)


model_fits <- list(
    m_1 = m_1,
    m_2 = m_2,
    m_3 = m_3,
    m_4 = m_4,
    m_5 = m_5
)

for (m in model_fits) {
    print(m$ll_total)
}


# estimate tvc model using the optimal m which yields the highest likelihood
tvc_fit <- estimate_tvc(dj_returns, m = 4)


# print the estimated parameters (a,b) for m=4
print("TVC parameters for m=4")
print(tvc_fit$params)

################################################################################
### Empirical Part - Problem 3                                               ###
################################################################################
### Estimate the DCC model of Engle (2002) using the rmgarch                 ###
################################################################################


# first specifying multispec from uGARCH

# specify/initialize GARCH(1, 1) model
# specify model according to specification in Eq. (2) and (3) in exam
garch_specification <- ugarchspec(
    variance.model = list(model = "sGARCH", garchOrder = c(1, 1)),
    mean.model = list(armaOrder = c(0, 0), include.mean = FALSE)
)

# create list of specifications for multifit
garch_specification <- multispec(
    replicate(3, garch_specification)
)

# creating the dcc_specification object according to the model
dcc_specification <- dccspec(
    garch_specification,
    distribution = "mvnorm",
    dccOrder = c(1, 1),
    model = c("DCC")
)

# fitting the model
engle_fit <- dccfit(
    dcc_specification,
    data = dj_returns
)

print("Likelihood of Engle model")
print(likelihood(engle_fit))


################################################################################
### Empirical Part - Problem 4                                               ###
################################################################################
### In a plot, compare the estimated correlations of the two models.         ###
################################################################################

{
    plot_colors <- c("black", "red", "orange")
    legend_labels <- c("IBM x GE", "IBM x JPM", "GE x JPM")
    par(mfrow = c(2, 1), cex = 0.85)

    plot(
        x = as.Date(rownames(dj_returns)),
        y = rcor(engle_fit)[1, 2, ],
        type = "l",
        xlab = "Time",
        ylab = "Correlations",
        col = plot_colors[1],
        ylim = c(0, 1),
        lwd = 2
    )
    lines(
        x = as.Date(rownames(dj_returns)),
        y = rcor(engle_fit)[1, 3, ],
        col = plot_colors[2],
        lwd = 1.5
    )
    lines(
        x = as.Date(rownames(dj_returns)),
        y = rcor(engle_fit)[2, 3, ],
        col = plot_colors[3],
        lwd = 1.5
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 0.5
    )

    legend(
        "topright",
        legend = legend_labels,
        col = plot_colors,
        lty = 1,
        fonts
    )
    title(main = "Correlations from Engle DCC model")


    plot(
        x = as.Date(rownames(dj_returns)),
        y = tvc_fit$r[1, 2, ],
        type = "l",
        xlab = "Time",
        ylab = "Correlations",
        col = plot_colors[1],
        ylim = c(0, 1),
        lwd = 2
    )
    lines(
        x = as.Date(rownames(dj_returns)),
        y = tvc_fit$r[1, 3, ],
        col = plot_colors[2],
        lwd = 1.5
    )
    lines(
        x = as.Date(rownames(dj_returns)),
        y = tvc_fit$r[2, 3, ],
        col = plot_colors[3],
        lwd = 1.5
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 0.5
    )
    legend(
        "topright",
        legend = legend_labels,
        col = plot_colors,
        lty = 1,
        fonts
    )
    title(main = "Correlations from Tse and Tsui TVC model (M=4)")


    # reset plotting settings
    par(mfrow = c(1, 1))
}



################################################################################
### Empirical Part - Problem 5                                               ###
################################################################################
### Draw some general conclusion about the evolution of the estimated        ###
### volatilities and correlations for the series you considered.             ###
################################################################################


{
    plot_colors <- c("black", "red", "orange")
    legend_labels <- c("IBM", "GE", "JPM")
    par(mfrow = c(1, 1), cex = 1.2)

    plot(
        x = as.Date(rownames(dj_returns)),
        y = sigma(engle_fit)[, 1],
        type = "l",
        xlab = "Time",
        ylab = "Conditional variance",
        col = plot_colors[1],
        ylim = c(0, 12),
        lwd = 2
    )
    lines(
        x = as.Date(rownames(dj_returns)),
        y = sigma(engle_fit)[, 2],
        col = plot_colors[2],
        lwd = 1.5
    )
    lines(
        x = as.Date(rownames(dj_returns)),
        y = sigma(engle_fit)[, 3],
        col = plot_colors[3],
        lwd = 1.5
    )
    grid(
        nx = NULL, ny = NULL,
        lty = 2,
        col = "gray",
        lwd = 0.5
    )

    legend(
        "topleft",
        legend = legend_labels,
        col = plot_colors,
        lty = 1,
        fonts
    )
    title(main = "Estimated volatilites from the univariate GARCH models")

    # reset plotting settings
    par(mfrow = c(1, 1))
}
