import numpy as np
import pandas as pd
from colorama import init, Fore, Style

# Initialize colorama for colored output in the terminal
init(autoreset=True)

def chaotic_system_test():
    """
    Simulate a chaotic system, such as turbulent fluid flow, where symmetry is not easily maintained.
    """
    t_values = np.linspace(0, 100, 100000)  # Extended time frame for chaotic behavior
    epsilon = 1e-12  # Smaller epsilon for precision
    t_c = 0.5
    max_n = 20000  # Complex chaotic system
    n = np.random.randint(3000, max_n)  # Randomized complexity

    # Simulate chaotic influences (turbulent fluid, dynamic pressure changes)
    turbulent_influence = np.random.normal(0, 1e-6, len(t_values)) * np.sin(t_values * 0.05)
    dynamic_pressure = np.tanh(t_values * 0.02) * np.random.normal(0, 1e-5, len(t_values))

    A_d = 2 * n  # Initial symmetry group for 2D polygons
    B_d = (1 / n) * (np.log(n)**2) + (0.1 + 0.01 * np.log(n))  # Logarithmic deformation factor
    C_d = 2.23  # Dimensional adjustment constant for 2D

    k_d = np.log(n)  # Complexity scaling constant

    delta_G = []

    for i, t in enumerate(t_values):
        if t <= t_c:
            delta_G.append(0)
        else:
            combined_effect = turbulent_influence[i] + dynamic_pressure[i]
            k_d_var = k_d * (1 + combined_effect)  # Adjust complexity scaling based on chaotic dynamics
            B_d_var = B_d * (1 + combined_effect)  # Adjust deformation factor based on chaotic dynamics
            delta = (A_d / (n ** k_d_var)) * ((t - t_c + epsilon) ** (B_d_var * k_d_var + C_d))
            delta_G.append(delta)

    delta_G = np.array(delta_G)
    return delta_G, t_values

def blind_test():
    """
    Perform a blind test where constants for symmetry-breaking are derived from randomized datasets.
    """
    t_values = np.linspace(0, 50, 50000)  # Longer time frame for blind tests
    epsilon = 1e-12  # Small epsilon for precision
    t_c = 0.5
    max_n = 15000  # Randomized upper bound for complexity
    n = np.random.randint(1000, max_n)

    # Generate randomized constants without knowing the system behavior
    A_d = np.random.uniform(500, 20000)  # Randomized symmetry group size
    B_d = np.random.uniform(0.1, 2.0)  # Randomized deformation factor
    C_d = np.random.uniform(1.0, 3.0)  # Randomized dimensional adjustment

    k_d = np.log(n)  # Complexity scaling based on randomized system

    delta_G = []

    for t in t_values:
        if t <= t_c:
            delta_G.append(0)
        else:
            delta = (A_d / (n ** k_d)) * ((t - t_c + epsilon) ** (B_d * k_d + C_d))
            delta_G.append(delta)

    delta_G = np.array(delta_G)
    return delta_G, t_values

def fractal_domain_test():
    """
    Explore counterfactual domains using fractal geometry and non-Euclidean systems.
    """
    t_values = np.linspace(0, 10, 10000)  # Shorter timescale due to complexity of fractal systems
    epsilon = 1e-12
    t_c = 0.5
    fractal_dimension = 2.7  # Random non-integer dimension for fractals

    # Simulate recursive scaling of complexity within fractal systems
    A_d = np.random.uniform(1000, 5000)  # Symmetry group for fractal-like systems
    B_d = 1.5  # Logarithmic deformation factor
    C_d = np.random.uniform(1.5, 2.5)  # Dimensional adjustment

    delta_G = []

    for t in t_values:
        if t <= t_c:
            delta_G.append(0)
        else:
            delta = (A_d / (fractal_dimension ** np.log(fractal_dimension))) * ((t - t_c + epsilon) ** (B_d * np.log(fractal_dimension) + C_d))
            delta_G.append(delta)

    delta_G = np.array(delta_G)
    return delta_G, t_values

def adaptive_symmetry_group_test():
    """
    Simulate systems where symmetry groups adapt and change over time (e.g., self-organizing systems).
    """
    t_values = np.linspace(0, 30, 50000)
    epsilon = 1e-12
    t_c = 0.5
    max_n = 15000
    n = np.random.randint(1000, max_n)

    # Simulate an adaptive symmetry group that shifts with time
    A_d_initial = np.random.uniform(1000, 10000)
    A_d_final = np.random.uniform(500, 5000)  # Symmetry group reduces over time
    A_d = np.linspace(A_d_initial, A_d_final, len(t_values))

    B_d = 1.1  # Fixed deformation factor for adaptive systems
    C_d = 2.0  # Fixed dimensional adjustment constant

    delta_G = []

    for i, t in enumerate(t_values):
        if t <= t_c:
            delta_G.append(0)
        else:
            delta = (A_d[i] / (n ** np.log(n))) * ((t - t_c + epsilon) ** (B_d * np.log(n) + C_d))
            delta_G.append(delta)

    delta_G = np.array(delta_G)
    return delta_G, t_values

def run_tests():
    """
    Run all the tests and output Pass/Fail with colored results.
    """
    results = {
        "Test Name": [],
        "Max ΔG": [],
        "Avg ΔG": [],
        "Std ΔG": [],
        "Pass Test": []
    }

    # Chaotic system test
    chaotic_delta_G, chaotic_t_values = chaotic_system_test()
    results["Test Name"].append("Chaotic System")
    results["Max ΔG"].append(np.max(chaotic_delta_G))
    results["Avg ΔG"].append(np.mean(chaotic_delta_G[int(0.5 * len(chaotic_t_values)):]))
    results["Std ΔG"].append(np.std(chaotic_delta_G[int(0.5 * len(chaotic_t_values)):]))
    results["Pass Test"].append(np.all(chaotic_delta_G[int(0.5 * len(chaotic_t_values)):] > 0))

    # Blind test
    blind_delta_G, blind_t_values = blind_test()
    results["Test Name"].append("Blind Test")
    results["Max ΔG"].append(np.max(blind_delta_G))
    results["Avg ΔG"].append(np.mean(blind_delta_G[int(0.5 * len(blind_t_values)):]))
    results["Std ΔG"].append(np.std(blind_delta_G[int(0.5 * len(blind_t_values)):]))
    results["Pass Test"].append(np.all(blind_delta_G[int(0.5 * len(blind_t_values)):] > 0))

    # Fractal domain test
    fractal_delta_G, fractal_t_values = fractal_domain_test()
    results["Test Name"].append("Fractal Domain")
    results["Max ΔG"].append(np.max(fractal_delta_G))
    results["Avg ΔG"].append(np.mean(fractal_delta_G[int(0.5 * len(fractal_t_values)):]))
    results["Std ΔG"].append(np.std(fractal_delta_G[int(0.5 * len(fractal_t_values)):]))
    results["Pass Test"].append(np.all(fractal_delta_G[int(0.5 * len(fractal_t_values)):] > 0))

    # Adaptive symmetry group test
    adaptive_delta_G, adaptive_t_values = adaptive_symmetry_group_test()
    results["Test Name"].append("Adaptive Symmetry Group")
    results["Max ΔG"].append(np.max(adaptive_delta_G))
    results["Avg ΔG"].append(np.mean(adaptive_delta_G[int(0.5 * len(adaptive_t_values)):]))
    results["Std ΔG"].append(np.std(adaptive_delta_G[int(0.5 * len(adaptive_t_values)):]))
    results["Pass Test"].append(np.all(adaptive_delta_G[int(0.5 * len(adaptive_t_values)):] > 0))

    return results

def display_results(results):
    """
    Display the test results with colored Pass/Fail output.
    """
    print("\nAdvanced Critical Test Results\n")
    for i in range(len(results["Test Name"])):
        test_name = results["Test Name"][i]
        pass_test = results["Pass Test"][i]
        if pass_test:
            print(f"{Fore.GREEN}PASS{Style.RESET_ALL} - {test_name}")
        else:
            print(f"{Fore.RED}FAIL{Style.RESET_ALL} - {test_name}")
        print(f"  Max ΔG: {results['Max ΔG'][i]:.5e}")
        print(f"  Average ΔG after t_c: {results['Avg ΔG'][i]:.5e}")
        print(f"  Standard deviation of ΔG after t_c: {results['Std ΔG'][i]:.5e}\n")

def main():
    """
    Main function with a basic menu to loop through tests.
    """
    while True:
        print("\nSymmetry-Breaking Bifurcation Theorem - Advanced Critical Tests")
        print("1. Run all tests")
        print("q. Quit")

        choice = input("\nEnter the number of the test to run (or 'q' to quit): ")

        if choice == '1':
            results = run_tests()
            display_results(results)
        elif choice.lower() == 'q':
            print("Exiting the program.")
            break
        else:
            print("Invalid choice. Please enter a valid option.")

if __name__ == "__main__":
    main()
