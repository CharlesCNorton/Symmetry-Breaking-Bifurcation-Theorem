import numpy as np
import pandas as pd
from scipy.optimize import curve_fit
from scipy.stats import (
    shapiro, kstest, anderson, jarque_bera, skewtest, kurtosistest
)
from statsmodels.stats.diagnostic import (
    het_breuschpagan, het_white
)
from statsmodels.stats.stattools import durbin_watson
from statsmodels.regression.linear_model import OLS, WLS
from statsmodels.tools import add_constant
from statsmodels.formula.api import glm
from statsmodels.genmod.families import Gamma, links
from statsmodels.robust.robust_linear_model import RLM
from statsmodels.robust.norms import HuberT
from statsmodels.stats.outliers_influence import variance_inflation_factor
from sklearn.model_selection import KFold, RepeatedKFold
from sklearn.preprocessing import PowerTransformer
from sklearn.metrics import mean_squared_error, r2_score
from sklearn.linear_model import HuberRegressor, Ridge, Lasso
import warnings
from colorama import Fore, Style, init

# Initialize colorama and suppress warnings
init(autoreset=True)
warnings.filterwarnings("ignore")

# Symmetry-bifurcation function definition
def symmetry_bifurcation(t_values, n, d, A_d, k_d, B_d, C_d, alpha=0, epsilon=0):
    DeltaG = np.zeros_like(t_values)
    mask = t_values > 0.5
    DeltaG[mask] = (A_d / n**k_d) * ((t_values[mask] - 0.5 + epsilon) ** (B_d * np.log(n) + C_d + alpha))
    return DeltaG

# Advanced statistical analysis function with enhancements
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

                # Fit the theorem-based model
                try:
                    params_theorem, _ = curve_fit(
                        lambda x, alpha: symmetry_bifurcation(
                            x, obj['n'], obj['d'], obj['A_d'],
                            obj['k_d'], obj['B_d'], obj['C_d'], alpha=alpha, epsilon=noise
                        ), X_train, y_train
                    )
                except RuntimeError:
                    params_theorem = [0]
                predicted = symmetry_bifurcation(
                    X_test, obj['n'], obj['d'], obj['A_d'],
                    obj['k_d'], obj['B_d'], obj['C_d'], alpha=params_theorem[0], epsilon=noise
                )
                mse = mean_squared_error(y_test, predicted)
                r2 = r2_score(y_test, predicted)
                cv_errors.append(mse)
                r2_scores.append(r2)

            print(f"{Fore.YELLOW}{obj['name']} Cross-validation MSE: {np.mean(cv_errors):.5f}{Style.RESET_ALL}")
            print(f"{Fore.YELLOW}{obj['name']} R-squared (average): {np.mean(r2_scores):.5f}{Style.RESET_ALL}")

            # Create DataFrame for regression analysis
            data = pd.DataFrame({'t_values': t_values, 'actual_result': actual_result_noisy})

            # Transformations to handle non-normal residuals
            if np.all(data['actual_result'] >= 0):
                # Using Yeo-Johnson transformation
                pt = PowerTransformer(method='yeo-johnson')
                data['transformed_result'] = pt.fit_transform(data['actual_result'].values.reshape(-1, 1)).flatten()
                print(f"{obj['name']} Applied Yeo-Johnson Transformation.")
            else:
                data['transformed_result'] = data['actual_result']
                print(f"{obj['name']} Data contains negative values. Skipping Transformation.")

            # Weighted Least Squares (WLS)
            X_ols = add_constant(data['t_values'])
            initial_ols = OLS(data['transformed_result'], X_ols).fit()
            residuals = initial_ols.resid
            # Estimate weights as the inverse of variance (adding a small constant to avoid division by zero)
            weights = 1 / (residuals ** 2 + 1e-5)
            wls_model = WLS(data['transformed_result'], X_ols, weights=weights).fit()

            # Robust Regression using RLM (M-estimators)
            rlm_model = RLM(data['transformed_result'], X_ols, M=HuberT()).fit()

            # Generalized Linear Models with alternative distributions
            try:
                gamma_model = glm('transformed_result ~ t_values', data=data, family=Gamma(link=links.log())).fit()
            except Exception as e:
                print(f"Error fitting GLM Gamma model for {obj['name']}: {e}")
                gamma_model = None

            # Evaluate models
            models = {
                'OLS': initial_ols,
                'WLS': wls_model,
                'Robust Regression (RLM)': rlm_model,
            }
            if gamma_model is not None:
                models['GLM Gamma'] = gamma_model

            for model_name, model in models.items():
                predicted = model.predict(X_ols)
                mse = mean_squared_error(data['transformed_result'], predicted)
                r2 = r2_score(data['transformed_result'], predicted)
                print(f"{Fore.MAGENTA}{obj['name']} {model_name} MSE: {mse:.5f}, R-squared: {r2:.5f}{Style.RESET_ALL}")

                # Residuals for diagnostics
                residuals = model.resid

                # Durbin-Watson Test
                dw_stat = durbin_watson(residuals)
                print(f"{obj['name']} {model_name} {Fore.GREEN}Durbin-Watson: {dw_stat:.2f}{Style.RESET_ALL}")

                # Breusch-Pagan Test for heteroscedasticity
                bp_test_stat, bp_p_value, _, _ = het_breuschpagan(residuals, X_ols)
                print(f"{obj['name']} {model_name} Breusch-Pagan Test Statistic: {bp_test_stat:.2f}, p-value: {bp_p_value:.5f}")

                # Shapiro-Wilk Test for normality
                shapiro_stat, shapiro_p_value = shapiro(residuals[:5000])  # Limiting to first 5000 samples
                print(f"{obj['name']} {model_name} Shapiro-Wilk Test: Statistic = {shapiro_stat:.2f}, p-value = {shapiro_p_value:.5f}")

                # Variance Inflation Factor (VIF)
                vif_data = pd.DataFrame()
                vif_data["VIF"] = [variance_inflation_factor(X_ols.values, i) for i in range(X_ols.shape[1])]
                vif_data["Feature"] = X_ols.columns
                print(f"{obj['name']} {model_name} Variance Inflation Factor (VIF):\n{vif_data}")

            print(f"{Fore.CYAN}{obj['name']} Completed analysis with model enhancements.{Style.RESET_ALL}")

# Run advanced statistical analysis with enhancements
if __name__ == "__main__":
    advanced_statistical_analysis()
