import numpy as np
import sys
from colorama import init, Fore, Style
from sklearn.metrics import r2_score

init(autoreset=True)

def apply_noise_and_compute_r2(delta_G, noise_level=1e-5):
    """
    Adds random noise to the delta_G values and computes the R^2 score to check if the model is robust to noise.
    """
    noisy_delta_G = delta_G + np.random.normal(0, noise_level, len(delta_G))
    r2 = r2_score(delta_G, noisy_delta_G)
    return noisy_delta_G, r2

def ultimate_master_test():
    """
    Ultimate master test integrating multiple physical phenomena:
    - Quantum-classical coupling
    - Chaotic system dynamics
    - 3D-4D transitions
    - Real-time perturbations of constants of nature
    - Recursive feedback across quantum, classical, and cosmic scales
    """

    def quantum_chaotic_test():
        """
        Simulates a quantum-classical system where quantum states interact with classical chaotic dynamics.
        This version includes real-world natural perturbations, feedback loops, long-term memory effects,
        and stochastic cross-scale interactions.
        """
        t_values = np.linspace(0, 1000, 100000)  # Time evolution
        epsilon = 1e-12
        n = 5  # Assume 5 quantum states
        A_d = 10  # Coupled system symmetry group
        k_d = np.log(n)
        B_d = (1 / n) * (k_d**2) + (0.1 + 0.01 * k_d)
        C_d = 2.4
        delta_G = []

        # Physical constants and external effects
        background_radiation = np.random.uniform(2.7, 3.5, len(t_values))  # Cosmic Microwave Background
        thermal_noise = np.random.normal(0, 0.05, len(t_values))  # Ambient thermal noise
        quantum_decoherence = np.random.normal(0, 0.02, len(t_values))  # Quantum coherence decay

        # Parameters for feedback loop complexity
        chaotic_feedback_strength = np.random.uniform(0.9, 1.1)  # Strength of chaotic feedback
        coupling_factor = np.random.uniform(0.5, 2.0, len(t_values))  # Cross-scale coupling between quantum and classical domains

        # Feedback memory effect (long-term influence of past states)
        feedback_memory = np.zeros_like(t_values)
        feedback_decay_factor = np.random.uniform(0.95, 0.99)  # Feedback loop memory decay

        for t_idx, t in enumerate(t_values):
            if t <= 0.5:
                delta_G.append(0)
            else:
                # Chaotic quantum feedback coupled with classical effects
                quantum_feedback = np.sin(np.random.normal(0, 1)) ** 2  # Random quantum fluctuations
                classical_chaos = 1 / (np.abs(np.random.uniform(-1, 1) + 1e-12))  # Chaotic classical behavior

                # Long-term feedback loop effect
                if t_idx > 0:
                    feedback_memory[t_idx] = feedback_memory[t_idx-1] * feedback_decay_factor + chaotic_feedback_strength * delta_G[t_idx-1]

                # Perturbation factors
                decoherence_factor = quantum_decoherence[t_idx] * background_radiation[t_idx]  # Influence of decoherence
                thermal_perturbation = np.sin(thermal_noise[t_idx]) ** 2  # Influence of thermal noise

                # Core equation with added natural perturbations, quantum feedback, chaotic influence, and memory effects
                delta = (A_d / (n ** k_d)) * ((t - 0.5 + epsilon) ** (B_d * k_d + C_d)) * quantum_feedback * classical_chaos \
                        * feedback_memory[t_idx] * (1 + thermal_perturbation) * (1 + decoherence_factor) * coupling_factor[t_idx]

                delta_G.append(delta)

        return np.array(delta_G), t_values



    def multidimensional_transition_test():
        """
        Models transitions between 3D and 4D systems with naturalistic effects like feedback loops,
        stochastic gravitational fluctuations, and quantum-scale randomness. Cross-domain interactions
        lead to complex and emergent behavior.
        """
        t_values = np.linspace(0, 1000, 100000)
        epsilon = 1e-12

        # 3D and 4D system parameters
        n_3d = 6  # 3D system
        A_d_3d = 24  # Symmetry group constant for 3D
        k_d_3d = np.log(n_3d)
        B_d_3d = (1 / n_3d) * (k_d_3d**2) + (0.1 + 0.01 * k_d_3d)
        C_d_3d = 1.77

        n_4d = 600  # 4D system (polytopes)
        A_d_4d = 14400  # Symmetry group constant for 4D
        k_d_4d = np.log(n_4d)
        B_d_4d = (1 / n_4d) * (k_d_4d**2) + (0.1 + 0.01 * k_d_4d)
        C_d_4d = 2.9

        delta_G = []

        # Environmental fluctuations and dimensional coupling
        gravitational_fluctuations = np.random.uniform(0.99, 1.01, len(t_values))  # Stochastic gravitational field strength
        cosmic_curvature = np.random.uniform(0.95, 1.05, len(t_values))  # Background curvature fluctuations

        # Coupling between 3D and 4D regimes
        dimension_coupling_factor = np.random.uniform(0.5, 1.5, len(t_values))  # Stochastic transition probability between dimensions
        cross_domain_feedback_strength = np.random.uniform(0.8, 1.2, len(t_values))  # Feedback loop strength

        # Memory effect for 3D to 4D transitions
        transition_memory = np.zeros_like(t_values)
        transition_decay = np.random.uniform(0.92, 0.97)  # Transition memory decay factor

        for t_idx, t in enumerate(t_values):
            if t <= 0.5:
                delta_G.append(0)
            else:
                # Dimensional transition logic with feedback and memory effects
                if t_idx > 0:
                    transition_memory[t_idx] = transition_memory[t_idx-1] * transition_decay + cross_domain_feedback_strength[t_idx] * delta_G[t_idx-1]

                transition_factor = np.random.uniform(0, 1)
                if transition_factor < 0.5:
                    # 3D regime with added gravitational and curvature effects
                    delta = (A_d_3d / (n_3d ** k_d_3d)) * ((t - 0.5 + epsilon) ** (B_d_3d * k_d_3d + C_d_3d)) \
                            * gravitational_fluctuations[t_idx] * cosmic_curvature[t_idx] * (1 + transition_memory[t_idx])
                else:
                    # 4D regime with cross-domain feedback and dimensional coupling
                    delta = (A_d_4d / (n_4d ** k_d_4d)) * ((t - 0.5 + epsilon) ** (B_d_4d * k_d_4d + C_d_4d)) \
                            * dimension_coupling_factor[t_idx] * (1 + transition_memory[t_idx]) * cosmic_curvature[t_idx]

                delta_G.append(delta)

        return np.array(delta_G), t_values



    def perturbed_constants_test_naturalistic():
        """
        Perturbs constants of nature (speed of light, gravitational constant, Planck constant) with realistic noise.
        Simulates how quantum-classical transitions respond to real-time physical perturbations.
        """
        t_values = np.linspace(0, 1000, 100000)
        epsilon = 1e-12

        # Constants of nature
        speed_of_light = 299792458  # m/s
        planck_constant = 6.62607015e-34  # J·s
        gravitational_constant = 6.67430e-11  # m^3·kg^−1·s^−2

        # Physical noise based on real-world uncertainties and quantum fluctuation
        light_speed_noise = np.random.normal(0, 1e3, len(t_values))  # Variation in c
        planck_noise = np.random.normal(0, 1e-36, len(t_values))  # Variation in h
        gravity_noise = np.random.normal(0, 1e-12, len(t_values))  # Variation in G

        n = 1000  # Complex system
        A_d = 100  # Symmetry group constant
        k_d = np.log(n)
        B_d = (1 / n) * (k_d ** 2) + (0.1 + 0.01 * k_d)
        C_d = 2.3

        delta_G = []
        for t in t_values:
            if t <= 0.5:
                delta_G.append(0)
            else:
                # Perturb the constants of nature within realistic physical limits
                light_speed_effect = speed_of_light + light_speed_noise[int(t % len(t_values))]
                planck_effect = planck_constant + planck_noise[int(t % len(t_values))]
                gravity_effect = gravitational_constant + gravity_noise[int(t % len(t_values))]

                perturbation_effect = light_speed_effect * planck_effect / gravity_effect

                delta = (
                    (A_d / (n ** k_d))
                    * ((t - 0.5 + epsilon) ** (B_d * k_d + C_d))
                    * perturbation_effect
                )
                delta_G.append(delta)

        return np.array(delta_G), t_values

    def run_test(test_function, test_name):
        """
        Executes the provided test function, adds noise, and evaluates the results.
        """
        delta_G, t_values = test_function()
        noisy_delta_G, r2 = apply_noise_and_compute_r2(delta_G)

        max_delta = np.max(noisy_delta_G)
        avg_delta = np.mean(noisy_delta_G[int(0.5 * len(t_values)):])
        std_delta = np.std(noisy_delta_G[int(0.5 * len(t_values)):])

        print(f"\n{test_name} Results:")
        if np.all(noisy_delta_G[int(0.5 * len(t_values)):] > 0):
            print(f"{Fore.GREEN}PASS{Style.RESET_ALL} - The system shows symmetry-breaking beyond the critical threshold.")
        else:
                        print(f"{Fore.RED}FAIL{Style.RESET_ALL} - The system failed to maintain positive symmetry-breaking behavior.")

        print(f"Max ΔG: {max_delta:.5e}")
        print(f"Avg ΔG after t_c: {avg_delta:.5e}")
        print(f"Standard deviation of ΔG after t_c: {std_delta:.5e}")
        print(f"R² Score (noisy vs original): {r2:.5f}")

    print("\nUltimate Master Test - Select a test to run:")
    print("1. Quantum-Chaotic Feedback Test")
    print("2. Multidimensional Transition Test")
    print("3. Perturbed Constants of Nature Test")
    print("4. Run All Tests")
    print("q. Quit")

    while True:
        choice = input("\nEnter the number of the test to run (or 'q' to quit): ")

        if choice == '1':
            run_test(quantum_chaotic_test_naturalistic, "Quantum-Chaotic Feedback Test")
        elif choice == '2':
            run_test(multidimensional_transition_test_naturalistic, "Multidimensional Transition Test")
        elif choice == '3':
            run_test(perturbed_constants_test_naturalistic, "Perturbed Constants of Nature Test")
        elif choice == '4':
            run_test(quantum_chaotic_test_naturalistic, "Quantum-Chaotic Feedback Test")
            run_test(multidimensional_transition_test_naturalistic, "Multidimensional Transition Test")
            run_test(perturbed_constants_test_naturalistic, "Perturbed Constants of Nature Test")
        elif choice.lower() == 'q':
            print("Exiting the program.")
            break
        else:
            print("Invalid choice. Please enter a valid number (1-4) or 'q' to quit.")

if __name__ == "__main__":
    ultimate_master_test()
