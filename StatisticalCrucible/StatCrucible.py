import numpy as np
from scipy.optimize import curve_fit, differential_evolution
from scipy.stats import kstest, chi2, shapiro, anderson, jarque_bera, zscore
from statsmodels.stats.diagnostic import het_breuschpagan, acorr_breusch_godfrey, lilliefors
from statsmodels.stats.stattools import durbin_watson
from statsmodels.regression.linear_model import OLS
from statsmodels.sandbox.stats.runs import runstest_1samp
from scipy.stats import levene
import warnings
from colorama import Fore, Style, init

# Initialize colorama
init(autoreset=True)

def symmetry_bifurcation(t, n, d, A_d, k_d, B_d, C_d, alpha, epsilon=0.05):
    return (A_d / (n ** k_d)) * ((t - 0.5 + epsilon) ** (B_d * np.log(n) + C_d + alpha))

def linear_model(t, beta_0, beta_1):
    return beta_0 + beta_1 * t

def exponential_model(t, gamma_0, gamma_1):
    return np.exp(gamma_0 + gamma_1 * t)

def logarithmic_model(t, delta_0, delta_1, epsilon=0.05):
    return delta_0 + delta_1 * np.log(t + epsilon)

def fit_logarithmic(t_values, actual_result):
    # Define a cost function for differential evolution
    def cost_function(params):
        delta_0, delta_1 = params
        model_values = logarithmic_model(t_values, delta_0, delta_1)
        return ((actual_result - model_values) ** 2).sum()

    result = differential_evolution(cost_function, [(-1, 1), (0, 2)], maxiter=100000)
    return result.x

def cross_validation_split(t_values, num_folds):
    """Splits t_values into num_folds for cross-validation"""
    fold_size = len(t_values) // num_folds
    return [t_values[i * fold_size:(i + 1) * fold_size] for i in range(num_folds)]

def advanced_statistical_analysis(num_simulations=100000, noise_levels=[0.0, 0.1, 0.2, 0.3, 1.0], num_folds=5):
    objects = [
        {'name': 'Triangle', 'n': 3, 'd': 2, 'A_d': 6, 'k_d': np.log(3), 'B_d': 0.1, 'C_d': 2.23},
        {'name': 'Square', 'n': 4, 'd': 2, 'A_d': 8, 'k_d': np.log(4), 'B_d': 0.1139, 'C_d': 2.23},
        {'name': 'Hexagon', 'n': 6, 'd': 2, 'A_d': 12, 'k_d': np.log(6), 'B_d': 0.1179, 'C_d': 2.23},
        {'name': 'Cube', 'n': 6, 'd': 3, 'A_d': 24, 'k_d': np.log(6), 'B_d': 0.1179, 'C_d': 1.77},
        {'name': 'Dodecahedron', 'n': 12, 'd': 3, 'A_d': 60, 'k_d': np.log(12), 'B_d': 0.1248, 'C_d': 1.77},
        {'name': 'Tesseract', 'n': 8, 'd': 4, 'A_d': 384, 'k_d': np.log(8), 'B_d': 0.15, 'C_d': 3.1},
        {'name': '600-Cell', 'n': 600, 'd': 4, 'A_d': 14400, 'k_d': np.log(600), 'B_d': 0.1639, 'C_d': 2.876},
    ]

    for noise in noise_levels:
        print(f"\n{Fore.CYAN}Analyzing with noise level: {noise * 100:.0f}%{Style.RESET_ALL}")
        results = {obj['name']: np.zeros((num_simulations, 4)) for obj in objects}
        t_values = np.random.uniform(0.51, 1, num_simulations)

        for obj in objects:
            actual_result = symmetry_bifurcation(t_values, obj['n'], obj['d'], obj['A_d'], obj['k_d'], obj['B_d'], obj['C_d'], alpha=0, epsilon=noise)

            # Cross-validation
            cv_splits = cross_validation_split(t_values, num_folds)
            cv_errors = []
            for i in range(num_folds):
                test_set = cv_splits[i]
                train_set = np.hstack([cv_splits[j] for j in range(num_folds) if j != i])
                params_poly, _ = curve_fit(lambda x, alpha: symmetry_bifurcation(x, obj['n'], obj['d'], obj['A_d'], obj['k_d'], obj['B_d'], obj['C_d'], alpha), train_set, actual_result[:len(train_set)])
                predicted = symmetry_bifurcation(test_set, obj['n'], obj['d'], obj['A_d'], obj['k_d'], obj['B_d'], obj['C_d'], *params_poly)
                cv_errors.append(np.mean((actual_result[:len(test_set)] - predicted) ** 2))
            print(f"{obj['name']} Cross-validation MSE: {np.mean(cv_errors):.5f}")

            # Fitting alternative models
            params_poly, _ = curve_fit(lambda x, alpha: symmetry_bifurcation(x, obj['n'], obj['d'], obj['A_d'], obj['k_d'], obj['B_d'], obj['C_d'], alpha), t_values, actual_result)
            params_lin, _ = curve_fit(linear_model, t_values, actual_result)
            params_exp, _ = curve_fit(exponential_model, t_values, actual_result)

            # Use differential evolution for the logarithmic model fitting
            params_log = fit_logarithmic(t_values, actual_result)

            # Residuals and additional tests
            poly_residuals = actual_result - symmetry_bifurcation(t_values, obj['n'], obj['d'], obj['A_d'], obj['k_d'], obj['B_d'], obj['C_d'], *params_poly)
            lin_residuals = actual_result - linear_model(t_values, *params_lin)
            exp_residuals = actual_result - exponential_model(t_values, *params_exp)
            log_residuals = actual_result - logarithmic_model(t_values, *params_log)

            # Durbin-Watson Test for autocorrelation in residuals
            dw_poly = durbin_watson(poly_residuals)
            print(f"{obj['name']} Durbin-Watson (Polynomial): {dw_poly:.2f}")

            # Breusch-Pagan test for heteroscedasticity
            X_poly = np.vstack([t_values, np.ones(len(t_values))]).T
            bp_test_stat, _, _, _ = het_breuschpagan(poly_residuals, X_poly)
            print(f"{obj['name']} Breusch-Pagan Test Statistic (Polynomial): {bp_test_stat:.2f}")

            # Kolmogorov-Smirnov test for normality of residuals
            ks_stat_poly, p_value_poly = kstest(poly_residuals, 'norm')
            print(f"{obj['name']} Kolmogorov-Smirnov Test (Polynomial Residuals): KS Statistic = {ks_stat_poly:.2f}, p-value = {p_value_poly:.5f}")

            # Shapiro-Wilk Test for normality
            sw_stat_poly, sw_p_value_poly = shapiro(poly_residuals)
            print(f"{obj['name']} Shapiro-Wilk Test: Statistic = {sw_stat_poly:.2f}, p-value = {sw_p_value_poly:.5f}")

            # Anderson-Darling Test for normality
            ad_test_poly = anderson(poly_residuals)
            print(f"{obj['name']} Anderson-Darling Test: Statistic = {ad_test_poly.statistic:.2f}, Critical Values = {ad_test_poly.critical_values}")

            # Lilliefors Test for normality
            lillie_stat_poly, lillie_p_value_poly = lilliefors(poly_residuals)
            print(f"{obj['name']} Lilliefors Test: Statistic = {lillie_stat_poly:.2f}, p-value = {lillie_p_value_poly:.5f}")

            # Jarque-Bera Test for normality
            jb_stat_poly, jb_p_value_poly = jarque_bera(poly_residuals)
            print(f"{obj['name']} Jarque-Bera Test: Statistic = {jb_stat_poly:.2f}, p-value = {jb_p_value_poly:.5f}")

            # Runs Test for randomness in residuals
            runs_stat_poly, runs_p_value_poly = runstest_1samp(poly_residuals)
            print(f"{obj['name']} Runs Test for Randomness: Statistic = {runs_stat_poly:.2f}, p-value = {runs_p_value_poly:.5f}")

            # Breusch-Godfrey Test for autocorrelation
            bg_test_stat_poly, bg_p_value_poly, _, _ = acorr_breusch_godfrey(OLS(poly_residuals, X_poly).fit(), nlags=1)
            print(f"{obj['name']} Breusch-Godfrey Test: Statistic = {bg_test_stat_poly:.2f}, p-value = {bg_p_value_poly:.5f}")

            # Levene’s Test for equality of variances
            levene_stat_poly, levene_p_value_poly = levene(poly_residuals, lin_residuals)
            print(f"{obj['name']} Levene’s Test for Equality of Variances: Statistic = {levene_stat_poly:.2f}, p-value = {levene_p_value_poly:.5f}")

            # Z-test for whether residual mean is zero
            z_stat_poly = np.mean(poly_residuals) / np.std(poly_residuals)
            print(f"{obj['name']} Z-test for Residual Mean = 0: Z-statistic = {z_stat_poly:.2f}")

            # Chi-Square goodness of fit
            chi_square_stat_poly = np.sum((poly_residuals ** 2) / np.var(poly_residuals))
            print(f"{obj['name']} Chi-Square Test Statistic (Polynomial): {chi_square_stat_poly:.2f}")

            # AIC and BIC comparison
            mean_poly_mse = np.mean(poly_residuals**2)
            n_params_poly = 1  # Number of parameters for polynomial variation
            num_samples = len(t_values)
            aic_poly = num_samples * np.log(mean_poly_mse) + 2 * n_params_poly
            bic_poly = num_samples * np.log(mean_poly_mse) + np.log(num_samples) * n_params_poly
            print(f"{obj['name']} AIC (Polynomial): {aic_poly:.2f}, BIC: {bic_poly:.2f}")

# Running the advanced statistical analysis
if __name__ == "__main__":
    advanced_statistical_analysis()
