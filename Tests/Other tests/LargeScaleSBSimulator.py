import numpy as np
import pandas as pd

# Ensure double precision
np.set_printoptions(precision=15)

# Symmetry-Breaking Bifurcation Equation Parameters for 2D, 3D, and 4D
params = {
    2: {"A_d": 4.08, "k_d": 0.76, "B_d": -0.13, "C_d": 2.23},  # 2D Polygons
    3: {"A_d": 0.022, "k_d": 0.85, "B_d": 0.1, "C_d": 1.77},   # 3D Polyhedra
    4: {"A_d": 0.0067, "k_d": 1.0, "B_d": 0.09, "C_d": 1.12},  # 4D Polytopes
}

# Default values for complexity, dimensionality, deformation, and number of points
default_min_n = 1000
default_max_n = 1e7
default_min_t = 0.49
default_max_t = 1.0
default_num_points = 1000  # Default number of points capped at 1000 initially
default_n_values = np.linspace(default_min_n, default_max_n, default_num_points)  # Complexity with default points
default_t_values = np.linspace(default_min_t, default_max_t, default_num_points)  # Deformation with default points
default_d_values = [2, 3, 4]  # Default dimensionalities from 2D to 4D

# Symmetry-Breaking Bifurcation Function
def symmetry_breaking_bifurcation(t, n, d, A_d, k_d, B_d, C_d, epsilon=1e-9):
    t_c = 0.5
    if t <= t_c:
        return 0
    else:
        return (A_d / n**k_d) * (t - t_c + epsilon)**(B_d * np.log(n) + C_d)

# Function to run naturalistic, high-precision tests (without plotting)
def run_naturalistic_tests(n_values, d_values, t_values):
    # Results storage
    results = []

    # Loop through each dimensionality, complexity, and deformation parameter
    for d in d_values:
        A_d, k_d, B_d, C_d = params[d]["A_d"], params[d]["k_d"], params[d]["B_d"], params[d]["C_d"]
        for n in n_values:
            for t in t_values:
                delta_G = symmetry_breaking_bifurcation(t, n, d, A_d, k_d, B_d, C_d)
                results.append({"Dimensionality": d, "Complexity (n)": n, "Deformation (t)": t, "Bifurcation Metric (ΔG)": delta_G})

    # Convert results to DataFrame
    df_results = pd.DataFrame(results)

    # Now calculate statistics
    mean_delta_G = df_results["Bifurcation Metric (ΔG)"].mean()
    median_delta_G = df_results["Bifurcation Metric (ΔG)"].median()
    std_delta_G = df_results["Bifurcation Metric (ΔG)"].std()
    min_delta_G = df_results["Bifurcation Metric (ΔG)"].min()
    max_delta_G = df_results["Bifurcation Metric (ΔG)"].max()

    # Get the complexity and deformation at max ΔG
    max_row = df_results[df_results["Bifurcation Metric (ΔG)"] == max_delta_G]
    max_complexity = max_row["Complexity (n)"].values[0]
    max_deformation = max_row["Deformation (t)"].values[0]

    # Print statistics and set values
    print(f"\n=== Simulation Completed ===")
    print(f"Complexity Range: {n_values[0]} to {n_values[-1]} ({len(n_values)} points)")
    print(f"Deformation Range: {t_values[0]} to {t_values[-1]} ({len(t_values)} points)")
    print(f"Dimensionalities: {d_values}")
    print("\n=== Statistics for the Bifurcation Metric (ΔG): ===")
    print(f"Mean ΔG: {mean_delta_G}")
    print(f"Median ΔG: {median_delta_G}")
    print(f"Standard Deviation ΔG: {std_delta_G}")
    print(f"Minimum ΔG: {min_delta_G}")
    print(f"Maximum ΔG: {max_delta_G} (at complexity n = {max_complexity}, deformation t = {max_deformation})\n")

# Menu option to set custom number of points for complexity and deformation
def set_num_points():
    global default_num_points
    num_points = input("Enter the number of points to sample (Maximum 7000, default is 1000): ")
    default_num_points = 1000 if num_points == "" else min(int(num_points), 7000)  # Cap at 7000 points
    print(f"\nNumber of points set to {default_num_points}.")

# Menu option to set custom complexity range
def set_complexity_range():
    global default_min_n, default_max_n, default_n_values
    print("Enter the minimum and maximum complexity (n):")
    default_min_n = float(input("Minimum complexity: "))
    default_max_n = float(input("Maximum complexity: "))
    default_n_values = np.linspace(default_min_n, default_max_n, default_num_points)

# Menu option to set custom deformation range
def set_deformation_range():
    global default_min_t, default_max_t, default_t_values
    print("Enter the minimum and maximum deformation (t):")
    default_min_t = float(input("Minimum deformation: "))
    default_max_t = float(input("Maximum deformation: "))
    default_t_values = np.linspace(default_min_t, default_max_t, default_num_points)

# Menu option to set custom dimensionalities
def set_dimensionalities():
    global default_d_values
    print("Enter the dimensionalities (comma-separated, e.g., 2,3,4):")
    dim_input = input("Dimensionalities: ")
    default_d_values = [int(d) for d in dim_input.split(",")]
    print(f"Dimensionalities set to {default_d_values}.")

# Main menu function
def main_menu():
    global default_n_values, default_t_values

    while True:
        print("\n==============================")
        print(" Symmetry-Breaking Bifurcation")
        print("==============================")
        print(f"Current number of points for complexity and deformation: {default_num_points}")
        print(f"Complexity Range: {default_min_n} to {default_max_n}")
        print(f"Deformation Range: {default_min_t} to {default_max_t}")
        print(f"Dimensionalities: {default_d_values}")
        print("==============================")
        print("1. Start Simulation")
        print("2. Set Number of Points")
        print("3. Set Complexity Range")
        print("4. Set Deformation Range")
        print("5. Set Dimensionalities")
        print("6. Exit")

        choice = input("Enter your choice (1-6): ")

        if choice == '1':
            print("\nStarting the simulation...")
            run_naturalistic_tests(default_n_values, default_d_values, default_t_values)
        elif choice == '2':
            set_num_points()
            # Update complexity and deformation ranges with new number of points
            default_n_values = np.linspace(default_min_n, default_max_n, default_num_points)
            default_t_values = np.linspace(default_min_t, default_max_t, default_num_points)
        elif choice == '3':
            print("\nSetting custom complexity range...")
            set_complexity_range()
        elif choice == '4':
            print("\nSetting custom deformation range...")
            set_deformation_range()
        elif choice == '5':
            print("\nSetting custom dimensionalities...")
            set_dimensionalities()
        elif choice == '6':
            print("Exiting the program. Goodbye!")
            break
        else:
            print("Invalid choice. Please enter a number between 1 and 6.")

# Run the program with a menu loop
if __name__ == "__main__":
    main_menu()
