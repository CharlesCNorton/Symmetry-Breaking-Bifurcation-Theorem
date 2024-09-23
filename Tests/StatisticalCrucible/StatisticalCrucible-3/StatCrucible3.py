import numpy as np
import pandas as pd
from scipy.optimize import curve_fit
from scipy.stats import (
    shapiro, kstest, anderson, jarque_bera, levene, chisquare, skewtest, kurtosistest, chi2_contingency
)
from statsmodels.stats.diagnostic import (
    het_breuschpagan, acorr_breusch_godfrey, het_white, lilliefors, linear_rainbow, compare_encompassing
)
from statsmodels.stats.stattools import durbin_watson, omni_normtest
from statsmodels.stats.outliers_influence import variance_inflation_factor
from statsmodels.formula.api import glm
from sklearn.model_selection import KFold, StratifiedKFold, RepeatedKFold
from sklearn.preprocessing import PolynomialFeatures
from sklearn.metrics import mean_squared_error, r2_score
from statsmodels.genmod.families import Poisson, NegativeBinomial, Gaussian
from statsmodels.sandbox.stats.runs import runstest_1samp
import statsmodels.api as sm
import warnings
from colorama import Fore, Style, init

# Initialize colorama
init(autoreset=True)
warnings.filterwarnings("ignore")

# Symmetry-bifurcation function definition
def symmetry_bifurcation(t_values, n, d, A_d, k_d, B_d, C_d, alpha=0, epsilon=0):
    DeltaG = np.zeros_like(t_values)
    mask = t_values > 0.5
    DeltaG[mask] = (A_d / n**k_d) * ((t_values[mask] - 0.5 + epsilon) ** (B_d * np.log(n) + C_d + alpha))
    return DeltaG

# Fit models: linear, polynomial, logarithmic, etc.
def linear_model(x, a, b):
    return a * x + b

def polynomial_model(x, *params):
    return np.polyval(params, x)

def exponential_model(x, a, b):
    return a * np.exp(b * x)

def logarithmic_model(x, a, b):
    return a * np.log(x) + b

# Cross-validation splitting (includes different strategies)
def cross_validation_split(data, num_folds, stratified=False):
    if stratified:
        skf = StratifiedKFold(n_splits=num_folds)
        return skf.split(data, np.zeros(len(data)))
    else:
        kf = KFold(n_splits=num_folds)
        return kf.split(data)

# Full statistical analysis function
def advanced_statistical_analysis(num_simulations=100000, noise_levels=[0.0, 0.1, 0.2, 0.3, 1.0], num_folds=5):
    # Define objects with geometric properties
    objects = [
        {'name': 'Triangle', 'n': 3, 'd': 2, 'A_d': 6, 'k_d': np.log(3), 'B_d': 0.1, 'C_d': 2.23},
        {'name': 'Square', 'n': 4, 'd': 2, 'A_d': 8, 'k_d': np.log(4), 'B_d': 0.1139, 'C_d': 2.23},
        {'name': 'Hexagon', 'n': 6, 'd': 2, 'A_d': 12, 'k_d': np.log(6), 'B_d': 0.1179, 'C_d': 2.23},
        {'name': 'Cube', 'n': 6, 'd': 3, 'A_d': 24, 'k_d': np.log(6), 'B_d': 0.1179, 'C_d': 1.77},
        {'name': 'Dodecahedron', 'n': 12, 'd': 3, 'A_d': 60, 'k_d': np.log(12), 'B_d': 0.1248, 'C_d': 1.77},
        {'name': 'Tesseract', 'n': 8, 'd': 4, 'A_d': 384, 'k_d': np.log(8), 'B_d': 0.15, 'C_d': 3.1},
        {'name': '600-Cell', 'n': 600, 'd': 4, 'A_d': 14400, 'k_d': np.log(600), 'B_d': 0.1639, 'C_d': 2.876},
    ]

    # Loop over noise levels
    for noise in noise_levels:
        print(f"\n{Fore.CYAN}Analyzing with noise level: {noise * 100:.0f}%{Style.RESET_ALL}")
        t_values = np.random.uniform(0.51, 1, num_simulations)

        for obj in objects:
            actual_result = symmetry_bifurcation(
                t_values, obj['n'], obj['d'], obj['A_d'],
                obj['k_d'], obj['B_d'], obj['C_d'], alpha=0, epsilon=noise
            )

            # Add noise to actual results
            noise_data = np.random.normal(0, noise, num_simulations)
            actual_result_noisy = actual_result + noise_data
            actual_result_noisy = np.clip(actual_result_noisy, 0, None)  # Clip to avoid negative values

            # Cross-validation with more folds and more diverse strategies
            cv_errors = []
            kf = RepeatedKFold(n_splits=num_folds, n_repeats=3, random_state=42)
            for train_index, test_index in kf.split(t_values):
                X_train, X_test = t_values[train_index], t_values[test_index]
                y_train, y_test = actual_result_noisy[train_index], actual_result_noisy[test_index]

                # Fit polynomial models to check overfitting
                poly_features = PolynomialFeatures(degree=3)
                X_train_poly = poly_features.fit_transform(X_train.reshape(-1, 1))
                X_test_poly = poly_features.fit_transform(X_test.reshape(-1, 1))

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
                mse = mean_squared_error(y_test, predicted)
                r2 = r2_score(y_test, predicted)
                cv_errors.append(mse)

            print(f"{Fore.YELLOW}{obj['name']} Cross-validation MSE: {np.mean(cv_errors):.5f}{Style.RESET_ALL}")
            print(f"{Fore.YELLOW}{obj['name']} R-squared (average): {r2:.5f}{Style.RESET_ALL}")

            # Create DataFrame for regression analysis
            data = pd.DataFrame({'t_values': t_values, 'actual_result': actual_result_noisy})

            # Ordinary Least Squares (OLS) regression
            X = sm.add_constant(data['t_values'])
            model_ols = sm.OLS(data['actual_result'], X).fit(cov_type='HC0')  # White's standard errors

            # Poisson regression
            model_pois = glm('actual_result ~ t_values', data=data, family=Poisson()).fit()

            # Negative Binomial regression
            try:
                model_nb = glm('actual_result ~ t_values', data=data, family=NegativeBinomial()).fit()
                print(f"{obj['name']} Negative Binomial Regression AIC: {model_nb.aic:.2f}, BIC: {model_nb.bic:.2f}")
            except ValueError as e:
                print(f"{Fore.RED}{obj['name']} Negative Binomial Regression failed: {e}{Style.RESET_ALL}")

            # Residuals for diagnostics
            residuals_ols = model_ols.resid
            residuals_pois = model_pois.resid_response

            # Durbin-Watson Test for autocorrelation
            dw_ols = durbin_watson(residuals_ols)
            print(f"{obj['name']} {Fore.GREEN}Durbin-Watson (OLS): {dw_ols:.2f}{Style.RESET_ALL}")

            # Variance Inflation Factor (VIF) to check multicollinearity
            vif_data = pd.DataFrame()
            vif_data["VIF"] = [variance_inflation_factor(X.values, i) for i in range(X.shape[1])]
            vif_data["Feature"] = X.columns
            print(f"{obj['name']} Variance Inflation Factor (VIF):\n{vif_data}")

            # Breusch-Pagan and White’s test for heteroscedasticity
            bp_test_stat, bp_p_value, _, _ = het_breuschpagan(residuals_ols, X)
            white_test_stat, white_p_value, _, _ = het_white(residuals_ols, X)
            print(f"{obj['name']} Breusch-Pagan Test Statistic: {bp_test_stat:.2f}, p-value: {bp_p_value:.5f}")
            print(f"{obj['name']} White's Test Statistic: {white_test_stat:.2f}, p-value: {white_p_value:.5f}")

            # Kolmogorov-Smirnov test for normality of residuals
            ks_stat_ols, p_value_ks_ols = kstest(residuals_ols, 'norm', args=(np.mean(residuals_ols), np.std(residuals_ols)))
            print(f"{obj['name']} Kolmogorov-Smirnov Test: KS Statistic = {ks_stat_ols:.2f}, p-value = {p_value_ks_ols:.5f}")

            # Shapiro-Wilk Test
            shapiro_stat_ols, shapiro_p_value_ols = shapiro(residuals_ols[:5000])
            print(f"{obj['name']} Shapiro-Wilk Test: Statistic = {shapiro_stat_ols:.2f}, p-value = {shapiro_p_value_ols:.5f}")

            # Anderson-Darling Test
            ad_test_ols = anderson(residuals_ols)
            print(f"{obj['name']} Anderson-Darling Test: Statistic = {ad_test_ols.statistic:.2f}")

            # Lilliefors Test
            lillie_stat_ols, lillie_p_value_ols = lilliefors(residuals_ols[:1000])
            print(f"{obj['name']} Lilliefors Test: Statistic = {lillie_stat_ols:.2f}, p-value = {lillie_p_value_ols:.5f}")

            # Jarque-Bera Test
            jb_stat_ols, jb_p_value_ols = jarque_bera(residuals_ols)
            print(f"{obj['name']} Jarque-Bera Test: Statistic = {jb_stat_ols:.2f}, p-value = {jb_p_value_ols:.5f}")

            # Skewness and Kurtosis Tests
            skew_stat, skew_p_value = skewtest(residuals_ols)
            kurt_stat, kurt_p_value = kurtosistest(residuals_ols)
            print(f"{obj['name']} Skewness Test: Statistic = {skew_stat:.2f}, p-value = {skew_p_value:.5f}")
            print(f"{obj['name']} Kurtosis Test: Statistic = {kurt_stat:.2f}, p-value = {kurt_p_value:.5f}")

            # Z-test for mean residual
            z_stat_ols = np.mean(residuals_ols) / (np.std(residuals_ols) / np.sqrt(len(residuals_ols)))
            print(f"{obj['name']} Z-test for Residual Mean = 0: Z-statistic = {z_stat_ols:.2f}")

            # Chi-Square Test
            chi_square_stat_ols, chi_square_p_value_ols = chisquare(residuals_ols)
            print(f"{obj['name']} Chi-Square Test: Statistic = {chi_square_stat_ols:.2f}, p-value = {chi_square_p_value_ols:.5f}")

            # Cross-validation AIC/BIC comparison
            print(f"{Fore.CYAN}{obj['name']} OLS AIC: {model_ols.aic:.2f}, BIC: {model_ols.bic:.2f}")
            print(f"{obj['name']} Poisson AIC: {model_pois.aic:.2f}, BIC: {model_pois.bic:.2f}")
            print(f"{obj['name']} Negative Binomial AIC: {model_nb.aic:.2f}, BIC: {model_nb.bic:.2f}")

# Run advanced statistical analysis
if __name__ == "__main__":
    advanced_statistical_analysis()
