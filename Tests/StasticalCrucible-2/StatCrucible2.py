import numpy as np
import pandas as pd
from scipy.optimize import curve_fit
from scipy.stats import shapiro, kstest, anderson, jarque_bera, levene, chisquare
from statsmodels.stats.diagnostic import het_breuschpagan, acorr_breusch_godfrey, het_white, lilliefors
from statsmodels.stats.stattools import durbin_watson
from statsmodels.formula.api import glm
from sklearn.model_selection import KFold
from statsmodels.genmod.families import Poisson, NegativeBinomial
import statsmodels.api as sm
from statsmodels.sandbox.stats.runs import runstest_1samp  # Correct import for the Runs Test
import warnings
from colorama import Fore, Style, init

# Initialize colorama
init(autoreset=True)

warnings.filterwarnings("ignore")

def symmetry_bifurcation(t_values, n, d, A_d, k_d, B_d, C_d, alpha=0, epsilon=0):
    DeltaG = np.zeros_like(t_values)
    mask = t_values > 0.5
    DeltaG[mask] = (A_d / n**k_d) * ((t_values[mask] - 0.5 + epsilon) ** (B_d * np.log(n) + C_d + alpha))
    return DeltaG

def linear_model(x, a, b):
    return a * x + b

def exponential_model(x, a, b):
    return a * np.exp(b * x)

def logarithmic_model(x, a, b):
    return a * np.log(x) + b

def fit_logarithmic(xdata, ydata):
    def log_func(x, a, b):
        return a * np.log(x) + b
    params, _ = curve_fit(log_func, xdata, ydata)
    return params

def cross_validation_split(data, num_folds):
    fold_size = len(data) // num_folds
    return [data[i * fold_size:(i + 1) * fold_size] for i in range(num_folds)]

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
        t_values = np.random.uniform(0.51, 1, num_simulations)

        for obj in objects:
            actual_result = symmetry_bifurcation(
                t_values, obj['n'], obj['d'], obj['A_d'],
                obj['k_d'], obj['B_d'], obj['C_d'], alpha=0, epsilon=noise
            )

            # Add noise to the actual results
            noise_data = np.random.normal(0, noise, num_simulations)
            actual_result_noisy = actual_result + noise_data

            # Clip negative values in actual_result_noisy to 0 for Negative Binomial
            actual_result_noisy = np.clip(actual_result_noisy, 0, None)

            # Cross-validation
            kf = KFold(n_splits=num_folds)
            cv_errors = []
            for train_index, test_index in kf.split(t_values):
                X_train, X_test = t_values[train_index], t_values[test_index]
                y_train, y_test = actual_result_noisy[train_index], actual_result_noisy[test_index]
                try:
                    params_poly, _ = curve_fit(
                        lambda x, alpha: symmetry_bifurcation(
                            x, obj['n'], obj['d'], obj['A_d'],
                            obj['k_d'], obj['B_d'], obj['C_d'], alpha
                        ), X_train, y_train
                    )
                except RuntimeError:
                    params_poly = [0]
                predicted = symmetry_bifurcation(
                    X_test, obj['n'], obj['d'], obj['A_d'],
                    obj['k_d'], obj['B_d'], obj['C_d'], *params_poly
                )
                cv_errors.append(np.mean((y_test - predicted) ** 2))
            print(f"{Fore.YELLOW}{obj['name']} Cross-validation MSE: {np.mean(cv_errors):.5f}{Style.RESET_ALL}")

            # Prepare data for regression models
            data = pd.DataFrame({'t_values': t_values, 'actual_result': actual_result_noisy})

            # Ordinary Least Squares Regression with White's Standard Errors
            X = sm.add_constant(data['t_values'])
            model_ols = sm.OLS(data['actual_result'], X).fit(cov_type='HC0')  # White's standard errors

            # Poisson Regression
            model_pois = glm('actual_result ~ t_values', data=data, family=Poisson()).fit()

            # Negative Binomial Regression
            try:
                model_nb = glm('actual_result ~ t_values', data=data, family=NegativeBinomial()).fit()
                print(f"{obj['name']} Negative Binomial Regression AIC: {model_nb.aic:.2f}, BIC: {model_nb.bic:.2f}")
            except ValueError as e:
                print(f"{Fore.RED}{obj['name']} Negative Binomial Regression failed: {e}{Style.RESET_ALL}")

            # Residuals
            residuals_ols = model_ols.resid
            residuals_pois = model_pois.resid_response

            # Durbin-Watson Test for autocorrelation in residuals
            dw_ols = durbin_watson(residuals_ols)
            print(f"{obj['name']} {Fore.GREEN}Durbin-Watson (OLS): {dw_ols:.2f}{Style.RESET_ALL}")

            # Breusch-Pagan test for heteroscedasticity
            bp_test_stat, bp_p_value, _, _ = het_breuschpagan(residuals_ols, X)
            print(f"{obj['name']} Breusch-Pagan Test Statistic (OLS): {bp_test_stat:.2f}, p-value: {bp_p_value:.5f}")

            # White's test for heteroscedasticity
            white_test_stat, white_p_value, _, _ = het_white(residuals_ols, X)
            print(f"{obj['name']} White's Test Statistic (OLS): {white_test_stat:.2f}, p-value: {white_p_value:.5f}")

            # Kolmogorov-Smirnov test for normality of residuals
            ks_stat_ols, p_value_ks_ols = kstest(residuals_ols, 'norm', args=(np.mean(residuals_ols), np.std(residuals_ols)))
            print(f"{obj['name']} Kolmogorov-Smirnov Test (OLS Residuals): KS Statistic = {ks_stat_ols:.2f}, p-value = {p_value_ks_ols:.5f}")

            # Shapiro-Wilk Test for normality
            shapiro_stat_ols, shapiro_p_value_ols = shapiro(residuals_ols[:5000])  # Limit to 5000 samples for Shapiro-Wilk
            print(f"{obj['name']} Shapiro-Wilk Test: Statistic = {shapiro_stat_ols:.2f}, p-value = {shapiro_p_value_ols:.5f}")

            # Anderson-Darling Test for normality
            ad_test_ols = anderson(residuals_ols)
            print(f"{obj['name']} Anderson-Darling Test: Statistic = {ad_test_ols.statistic:.2f}, Critical Values = {ad_test_ols.critical_values}")

            # Lilliefors Test for normality
            lillie_stat_ols, lillie_p_value_ols = lilliefors(residuals_ols[:1000])  # Limit to 1000 samples
            print(f"{obj['name']} Lilliefors Test: Statistic = {lillie_stat_ols:.2f}, p-value = {lillie_p_value_ols:.5f}")

            # Jarque-Bera Test for normality
            jb_stat_ols, jb_p_value_ols = jarque_bera(residuals_ols)
            print(f"{obj['name']} Jarque-Bera Test: Statistic = {jb_stat_ols:.2f}, p-value = {jb_p_value_ols:.5f}")

            # Runs Test for randomness in residuals
            runs_stat_ols, runs_p_value_ols = runstest_1samp(residuals_ols)
            print(f"{obj['name']} {Fore.MAGENTA}Runs Test for Randomness: Z = {runs_stat_ols:.2f}, p-value = {runs_p_value_ols:.5f}{Style.RESET_ALL}")

            # Breusch-Godfrey Test for autocorrelation
            bg_test_stat_ols, bg_p_value_ols, _, _ = acorr_breusch_godfrey(model_ols, nlags=1)
            print(f"{obj['name']} Breusch-Godfrey Test: Statistic = {bg_test_stat_ols:.2f}, p-value = {bg_p_value_ols:.5f}")

            # Levene’s Test for equality of variances between OLS and Poisson residuals
            levene_stat, levene_p_value = levene(residuals_ols, residuals_pois)
            print(f"{obj['name']} Levene’s Test for Equality of Variances: Statistic = {levene_stat:.2f}, p-value = {levene_p_value:.5f}")

            # Z-test for whether residual mean is zero
            z_stat_ols = np.mean(residuals_ols) / (np.std(residuals_ols) / np.sqrt(len(residuals_ols)))
            print(f"{obj['name']} Z-test for Residual Mean = 0: Z-statistic = {z_stat_ols:.2f}")

            # Chi-Square goodness of fit
            chi_square_stat_ols, chi_square_p_value_ols = chisquare(residuals_ols)
            print(f"{obj['name']} Chi-Square Test Statistic (OLS): {chi_square_stat_ols:.2f}, p-value: {chi_square_p_value_ols:.5f}")

            # AIC and BIC comparison
            print(f"{Fore.CYAN}{obj['name']} OLS AIC: {model_ols.aic:.2f}, BIC: {model_ols.bic:.2f}")
            print(f"{obj['name']} Poisson AIC: {model_pois.aic:.2f}, BIC: {model_pois.bic:.2f}")
            print(f"{obj['name']} Negative Binomial AIC: {model_nb.aic:.2f}, BIC: {model_nb.bic:.2f}")

# Running the advanced statistical analysis
if __name__ == "__main__":
    advanced_statistical_analysis()
