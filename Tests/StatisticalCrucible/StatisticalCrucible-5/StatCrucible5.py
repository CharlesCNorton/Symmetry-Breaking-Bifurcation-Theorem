import numpy as np
import pandas as pd
from scipy.optimize import curve_fit
from scipy.stats import (
    shapiro, kstest, anderson, jarque_bera, levene, chisquare, skewtest, kurtosistest, chi2_contingency
)
from statsmodels.stats.diagnostic import (
    het_breuschpagan, het_white
)
from statsmodels.stats.stattools import durbin_watson, omni_normtest
from statsmodels.regression.linear_model import OLS
from statsmodels.tools import add_constant
from statsmodels.formula.api import glm
from statsmodels.genmod.families import Poisson, NegativeBinomial
from statsmodels.stats.outliers_influence import variance_inflation_factor
from sklearn.model_selection import KFold, RepeatedKFold
from sklearn.preprocessing import PolynomialFeatures
from sklearn.metrics import mean_squared_error, r2_score
from sklearn.linear_model import HuberRegressor, Ridge, Lasso
from sklearn.utils import check_array
from sklearn.exceptions import ConvergenceWarning
import warnings
from colorama import Fore, Style, init

# Initialize colorama and suppress warnings
init(autoreset=True)
warnings.filterwarnings("ignore", category=ConvergenceWarning)
warnings.filterwarnings("ignore")

# Symmetry-bifurcation function definition
def symmetry_bifurcation(t_values, n, d, A_d, k_d, B_d, C_d, alpha=0, epsilon=0):
    DeltaG = np.zeros_like(t_values)
    mask = t_values > 0.5
    DeltaG[mask] = (A_d / n**k_d) * ((t_values[mask] - 0.5 + epsilon) ** (B_d * np.log(n) + C_d + alpha))
    return DeltaG

# Fit models: linear, polynomial, logarithmic, exponential
def linear_model(x, a, b):
    return a * x + b

def polynomial_model(x, *params):
    return np.polyval(params, x)

def exponential_model(x, a, b):
    return a * np.exp(b * x)

def logarithmic_model(x, a, b):
    return a * np.log(x) + b

# Robust Regression Models
def huber_regression(X_train, y_train):
    huber = HuberRegressor().fit(X_train.values.reshape(-1, 1), y_train)
    return huber

def ridge_regression(X_train, y_train, alpha=1.0):
    ridge = Ridge(alpha=alpha).fit(X_train.values.reshape(-1, 1), y_train)
    return ridge

def lasso_regression(X_train, y_train, alpha=0.1):
    lasso = Lasso(alpha=alpha).fit(X_train.values.reshape(-1, 1), y_train)
    return lasso

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
            r2_scores = []
            kf = RepeatedKFold(n_splits=num_folds, n_repeats=3, random_state=42)
            for train_index, test_index in kf.split(t_values):
                X_train, X_test = t_values[train_index], t_values[test_index]
                y_train, y_test = actual_result_noisy[train_index], actual_result_noisy[test_index]

                # Polynomial model fitting (degree 3)
                poly_features = PolynomialFeatures(degree=3)
                X_train_poly = poly_features.fit_transform(X_train.reshape(-1, 1))
                X_test_poly = poly_features.fit_transform(X_test.reshape(-1, 1))

                try:
                    params_poly, _ = curve_fit(
                        lambda x, alpha: symmetry_bifurcation(
                            x, obj['n'], obj['d'], obj['A_d'],
                            obj['k_d'], obj['B_d'], obj['C_d'], alpha=0, epsilon=noise
                        ), X_train, y_train
                    )
                except RuntimeError:
                    params_poly = [0]
                predicted = symmetry_bifurcation(
                    X_test, obj['n'], obj['d'], obj['A_d'],
                    obj['k_d'], obj['B_d'], obj['C_d'], alpha=params_poly[0], epsilon=noise
                )
                mse = mean_squared_error(y_test, predicted)
                r2 = r2_score(y_test, predicted)
                cv_errors.append(mse)
                r2_scores.append(r2)

            print(f"{Fore.YELLOW}{obj['name']} Cross-validation MSE: {np.mean(cv_errors):.5f}{Style.RESET_ALL}")
            print(f"{Fore.YELLOW}{obj['name']} R-squared (average): {np.mean(r2_scores):.5f}{Style.RESET_ALL}")

            # Create DataFrame for regression analysis
            data = pd.DataFrame({'t_values': t_values, 'actual_result': actual_result_noisy})

            # Ordinary Least Squares (OLS) regression
            X_ols = add_constant(data['t_values'])
            model_ols = OLS(data['actual_result'], X_ols).fit()

            # Poisson regression
            model_pois = glm('actual_result ~ t_values', data=data, family=Poisson()).fit()

            # Negative Binomial regression
            try:
                model_nb = glm('actual_result ~ t_values', data=data, family=NegativeBinomial()).fit()
                nb_aic = model_nb.aic
                nb_bic = model_nb.bic
            except ValueError as e:
                nb_aic = np.nan
                nb_bic = np.nan

            # Logarithmic Model
            try:
                params_log, _ = curve_fit(logarithmic_model, data['t_values'], data['actual_result'], maxfev=10000)
                log_pred = logarithmic_model(data['t_values'], *params_log)
                log_mse = mean_squared_error(data['actual_result'], log_pred)
                log_r2 = r2_score(data['actual_result'], log_pred)
            except RuntimeError:
                log_mse = np.nan
                log_r2 = np.nan

            # Exponential Model
            try:
                params_exp, _ = curve_fit(exponential_model, data['t_values'], data['actual_result'], maxfev=10000)
                exp_pred = exponential_model(data['t_values'], *params_exp)
                exp_mse = mean_squared_error(data['actual_result'], exp_pred)
                exp_r2 = r2_score(data['actual_result'], exp_pred)
            except RuntimeError:
                exp_mse = np.nan
                exp_r2 = np.nan

            # Robust Regression: Huber
            huber = HuberRegressor().fit(data['t_values'].values.reshape(-1, 1), data['actual_result'])
            huber_pred = huber.predict(data['t_values'].values.reshape(-1, 1))
            huber_mse = mean_squared_error(data['actual_result'], huber_pred)
            huber_r2 = r2_score(data['actual_result'], huber_pred)

            # Regularization: Ridge
            ridge = Ridge(alpha=1.0).fit(data['t_values'].values.reshape(-1, 1), data['actual_result'])
            ridge_pred = ridge.predict(data['t_values'].values.reshape(-1, 1))
            ridge_mse = mean_squared_error(data['actual_result'], ridge_pred)
            ridge_r2 = r2_score(data['actual_result'], ridge_pred)

            # Regularization: Lasso
            lasso = Lasso(alpha=0.1).fit(data['t_values'].values.reshape(-1, 1), data['actual_result'])
            lasso_pred = lasso.predict(data['t_values'].values.reshape(-1, 1))
            lasso_mse = mean_squared_error(data['actual_result'], lasso_pred)
            lasso_r2 = r2_score(data['actual_result'], lasso_pred)

            print(f"{Fore.MAGENTA}{obj['name']} Logarithmic Model MSE: {log_mse:.5f}, R-squared: {log_r2:.5f}{Style.RESET_ALL}")
            print(f"{Fore.MAGENTA}{obj['name']} Exponential Model MSE: {exp_mse:.5f}, R-squared: {exp_r2:.5f}{Style.RESET_ALL}")
            print(f"{Fore.MAGENTA}{obj['name']} Huber Regression MSE: {huber_mse:.5f}, R-squared: {huber_r2:.5f}{Style.RESET_ALL}")
            print(f"{Fore.MAGENTA}{obj['name']} Ridge Regression MSE: {ridge_mse:.5f}, R-squared: {ridge_r2:.5f}{Style.RESET_ALL}")
            print(f"{Fore.MAGENTA}{obj['name']} Lasso Regression MSE: {lasso_mse:.5f}, R-squared: {lasso_r2:.5f}{Style.RESET_ALL}")

            # Residuals for diagnostics
            residuals_ols = model_ols.resid
            residuals_pois = model_pois.resid_response
            residuals_nb = model_nb.resid_response if 'model_nb' in locals() else np.nan

            # Durbin-Watson Test for OLS
            dw_ols = durbin_watson(residuals_ols)
            print(f"{obj['name']} {Fore.GREEN}Durbin-Watson (OLS): {dw_ols:.2f}{Style.RESET_ALL}")

            # Variance Inflation Factor (VIF) to check multicollinearity
            vif_data = pd.DataFrame()
            vif_data["VIF"] = [variance_inflation_factor(X_ols.values, i) for i in range(X_ols.shape[1])]
            vif_data["Feature"] = X_ols.columns
            print(f"{obj['name']} Variance Inflation Factor (VIF):\n{vif_data}")

            # Breusch-Pagan and White’s test for heteroscedasticity
            bp_test_stat, bp_p_value, _, _ = het_breuschpagan(residuals_ols, X_ols)
            white_test_stat, white_p_value, _, _ = het_white(residuals_ols, X_ols)
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
            from statsmodels.stats.diagnostic import lilliefors
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
            print(f"{Fore.CYAN}{obj['name']} OLS AIC: {model_ols.aic:.2f}, BIC: {model_ols.bic:.2f}{Style.RESET_ALL}")
            print(f"{obj['name']} Poisson AIC: {model_pois.aic:.2f}, BIC: {model_pois.bic:.2f}")
            print(f"{obj['name']} Negative Binomial AIC: {nb_aic:.2f}, BIC: {nb_bic:.2f}")
            print(f"{obj['name']} Huber Regression MSE: {huber_mse:.5f}, R-squared: {huber_r2:.5f}")
            print(f"{obj['name']} Ridge Regression MSE: {ridge_mse:.5f}, R-squared: {ridge_r2:.5f}")
            print(f"{obj['name']} Lasso Regression MSE: {lasso_mse:.5f}, R-squared: {lasso_r2:.5f}")

# Run advanced statistical analysis
if __name__ == "__main__":
    advanced_statistical_analysis()
