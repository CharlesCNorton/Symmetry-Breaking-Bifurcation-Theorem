# Import necessary libraries
import numpy as np
import pandas as pd
from colorama import Fore, Style, init

# Initialize colorama
init(autoreset=True)

# Constants for each dimension from the new derivation
def k_d(d):
    return -0.5095 * d**2 + 2.7424 * d - 2.1642

# Data for 2D Polygons
n_2d = np.array([3, 4, 6, 8, 10, 12])
ln_n_2d = np.log(n_2d)
deformation_modes_2d = np.array([3, 5, 9, 13, 17, 21])

# Data for 3D Polyhedra
n_3d = np.array([4, 6, 8, 12, 20])
ln_n_3d = np.log(n_3d)
deformation_modes_3d = np.array([6, 12, 12, 54, 30])

# Data for 4D Polytopes
n_4d = np.array([5, 8, 16, 24, 120, 600])
ln_n_4d = np.log(n_4d)
deformation_modes_4d = np.array([10, 16, 24, 48, 600, 1200])

# Fitted constants a_d and b_d for each dimension (from empirical analysis)
a_2, b_2 = 0.8791, 1.2826
a_3, b_3 = 1.1068, 1.4776
a_4, b_4 = 18.8541, 0.6535

# Functions to calculate predicted deformation modes based on the new derived constants
def predicted_modes(n, a, b):
    return a * n**b

# Predictions for 2D
predicted_2d = predicted_modes(n_2d, a_2, b_2)
# Predictions for 3D
predicted_3d = predicted_modes(n_3d, a_3, b_3)
# Predictions for 4D
predicted_4d = predicted_modes(n_4d, a_4, b_4)

# Function to calculate deviation in absolute number and percentage
def calculate_deviation(actual, predicted):
    abs_deviation = np.abs(actual - predicted)
    percent_deviation = (abs_deviation / actual) * 100
    return abs_deviation, percent_deviation

# Adding deviation for 2D data
abs_dev_2d, percent_dev_2d = calculate_deviation(deformation_modes_2d, predicted_2d)
results_2d = pd.DataFrame({
    'n (2D Polygons)': n_2d,
    'ln(n)': ln_n_2d,
    'Actual Modes': deformation_modes_2d,
    'Predicted Modes': predicted_2d,
    'Absolute Deviation': abs_dev_2d,
    'Percent Deviation (%)': percent_dev_2d
})

# Adding deviation for 3D data
abs_dev_3d, percent_dev_3d = calculate_deviation(deformation_modes_3d, predicted_3d)
results_3d = pd.DataFrame({
    'n (3D Polyhedra)': n_3d,
    'ln(n)': ln_n_3d,
    'Actual Modes': deformation_modes_3d,
    'Predicted Modes': predicted_3d,
    'Absolute Deviation': abs_dev_3d,
    'Percent Deviation (%)': percent_dev_3d
})

# Adding deviation for 4D data
abs_dev_4d, percent_dev_4d = calculate_deviation(deformation_modes_4d, predicted_4d)
results_4d = pd.DataFrame({
    'n (4D Polytopes)': n_4d,
    'ln(n)': ln_n_4d,
    'Actual Modes': deformation_modes_4d,
    'Predicted Modes': predicted_4d,
    'Absolute Deviation': abs_dev_4d,
    'Percent Deviation (%)': percent_dev_4d
})

# Function to print tables with color-coding for easy comparison
def print_colored_table(df, dimension_name):
    print(Fore.CYAN + f"\n{dimension_name} Results:")
    print(Style.RESET_ALL)
    for index, row in df.iterrows():
        actual = row['Actual Modes']
        predicted = row['Predicted Modes']
        abs_dev = row['Absolute Deviation']
        percent_dev = row['Percent Deviation (%)']
        color = Fore.GREEN if percent_dev < 10 else Fore.YELLOW if percent_dev < 50 else Fore.RED
        print(f"n: {row[df.columns[0]]}, ln(n): {row['ln(n)']:.4f}, Actual: {actual}, "
              f"Predicted: {predicted:.2f}, Absolute Deviation: {abs_dev:.2f}, "
              f"Percent Deviation: {color}{percent_dev:.2f}%{Style.RESET_ALL}")

# Print tables with color-coded results for each dimension
print_colored_table(results_2d, "2D Polygons")
print_colored_table(results_3d, "3D Polyhedra")
print_colored_table(results_4d, "4D Polytopes")
