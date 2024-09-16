import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
import matplotlib.colors as mcolors

def hexagon(radius=1):
    """
    Generate vertices of a regular hexagon.

    Parameters:
        radius (float): The radius of the hexagon.

    Returns:
        np.ndarray: A 2D array of vertices representing a regular hexagon.
    """
    angles = np.linspace(0, 2 * np.pi, 7, endpoint=False)
    return radius * np.c_[np.cos(angles), np.sin(angles)]

def create_7_cell_grid(radius=1):
    """
    Generate a 7-cell hexagonal grid (one center hexagon and 6 surrounding hexagons).

    Parameters:
        radius (float): The radius of each hexagon.

    Returns:
        list: A list of 2D arrays where each array represents the vertices of a hexagon.
    """
    center = np.array([0, 0])
    hexagons = [center]
    for i in range(6):
        angle = i * np.pi / 3  # 60 degrees between hexagons
        offset = np.array([np.cos(angle), np.sin(angle)]) * (2 * radius)
        hexagons.append(offset)
    return [hexagon(radius) + center for center in hexagons]

def apply_deformation(vertices, t, n, d, A_d, k_d, B_d, C_d, epsilon=1e-6):
    """
    Apply the Symmetry-Breaking Bifurcation Theorem-based deformation to a hexagonal grid.

    The deformation introduces controlled geometric symmetry-breaking based on the parameters of the theorem.

    Parameters:
        vertices (np.ndarray): Vertices of the hexagon.
        t (float): Deformation parameter (0.5 <= t <= 1).
        n (int): Complexity of the object (number of sides).
        d (int): Dimensionality of the object.
        A_d, k_d, B_d, C_d (float): Constants from the theorem specific to dimensionality.
        epsilon (float): Small constant to ensure smooth behavior near t_c.

    Returns:
        np.ndarray: Deformed vertices based on the theorem's parameters.
    """
    if n <= 0:
        raise ValueError("Complexity (n) must be positive.")
    if t <= 0.5:
        return vertices  # No deformation before the critical point
    ΔG = (A_d / n**k_d) * (t - 0.5 + epsilon)**(B_d * np.log(n) + C_d)
    return vertices * (1 + ΔG * np.random.uniform(-0.2, 0.2, vertices.shape))  # Exaggerated for visibility

def random_perturbation(vertices, max_deformation):
    """
    Apply random unstructured perturbation to the vertices of a hexagonal grid.

    This serves as a control model that simulates chaotic, unstructured deformation.

    Parameters:
        vertices (np.ndarray): Vertices of the hexagon.
        max_deformation (float): Maximum amount of deformation allowed.

    Returns:
        np.ndarray: Vertices with random perturbation applied.
    """
    return vertices * (1 + max_deformation * np.random.uniform(-0.2, 0.2, vertices.shape))

def apply_spring_mass_deformation(vertices, max_deformation, stiffness=0.2, damping=0.3):
    """
    Simulate deformation using a spring-mass system. This was a common pre-theorem method
    that focused on stable elastic deformation without a deep geometric basis.

    Parameters:
        vertices (np.ndarray): Vertices of the hexagon.
        max_deformation (float): Maximum amount of deformation allowed.
        stiffness (float): Spring stiffness constant (lower stiffness allows more movement).
        damping (float): Damping factor for stability.

    Returns:
        np.ndarray: Vertices deformed using a spring-mass model.
    """
    equilibrium = vertices.copy()  # The original positions are the equilibrium points
    displacement = vertices - equilibrium  # Displacement from equilibrium
    restoring_force = -stiffness * displacement  # Hooke's law: F = -kx
    damping_force = damping * np.random.uniform(-0.05, 0.05, vertices.shape)  # Damping for stability
    return vertices + (restoring_force + damping_force) * max_deformation

def apply_fem_like_deformation(vertices, max_deformation, stiffness=0.8):
    """
    Simulate deformation using a simplified finite element method (FEM-like) approach.

    FEM approximates material behavior by calculating forces on discrete elements of the object.

    Parameters:
        vertices (np.ndarray): Vertices of the hexagon.
        max_deformation (float): Maximum amount of deformation allowed.
        stiffness (float): Stiffness factor affecting how much deformation occurs.

    Returns:
        np.ndarray: Vertices deformed using a FEM-like method.
    """
    displacement = np.random.uniform(-0.05, 0.05, vertices.shape)
    force = stiffness * displacement
    return vertices + force * max_deformation

def colorize_deformation(deformation, max_deformation):
    """
    Return color based on the level of deformation. The color represents the intensity of
    deformation using a color gradient.

    Parameters:
        deformation (float): The amount of deformation.
        max_deformation (float): Maximum expected deformation.

    Returns:
        matplotlib.colors.Normalize: Color corresponding to the deformation level.
    """
    norm = plt.Normalize(0, max_deformation)
    cmap = plt.cm.coolwarm
    return cmap(norm(deformation))

def create_animation(num_sides=6, max_deformation=0.5, frames=100):
    """
    Create an animation that compares different deformation methods:

    1. Symmetry-Breaking Bifurcation Theorem: Structured, geometric-based deformation.
    2. Random Perturbation: Chaotic, unstructured deformation.
    3. Spring-Mass Model: Pre-theorem efficient deformation model, focused on stability.
    4. FEM-like Method: A commonly used material deformation approach.

    Parameters:
        num_sides (int): Number of sides for the polygon (default is 6 for hexagons).
        max_deformation (float): Maximum allowed deformation in the models.
        frames (int): Number of frames for the animation.
    """
    try:
        # Parameters specific to 2D polygons based on the theorem
        params = {"A_d": 4.08, "k_d": 0.76, "B_d": -0.13, "C_d": 2.23}
        hexagons = create_7_cell_grid()

        # Create subplots for each comparison
        fig, (ax1, ax2, ax3, ax4) = plt.subplots(1, 4, figsize=(24, 6))
        ax1.set_aspect('equal')
        ax1.set_xlim(-4, 4)
        ax1.set_ylim(-4, 4)
        ax1.set_title("Symmetry-Breaking Theorem")

        ax2.set_aspect('equal')
        ax2.set_xlim(-4, 4)
        ax2.set_ylim(-4, 4)
        ax2.set_title("Random Perturbation")

        ax3.set_aspect('equal')
        ax3.set_xlim(-4, 4)
        ax3.set_ylim(-4, 4)
        ax3.set_title("Spring-Mass Model")

        ax4.set_aspect('equal')
        ax4.set_xlim(-4, 4)
        ax4.set_ylim(-4, 4)
        ax4.set_title("FEM-Like Model")

        # Initialize hexagonal patches for each method
        hex_colors_1 = [ax1.fill([], [], color='blue', edgecolor='black')[0] for _ in range(7)]
        hex_colors_2 = [ax2.fill([], [], color='red', edgecolor='black')[0] for _ in range(7)]
        hex_colors_3 = [ax3.fill([], [], color='green', edgecolor='black')[0] for _ in range(7)]
        hex_colors_4 = [ax4.fill([], [], color='purple', edgecolor='black')[0] for _ in range(7)]

        def update(frame):
            """
            Update function for each frame of the animation. Deforms the hexagons based on
            the method being visualized.
            """
            t = (frame / frames) * (1 - 0.5) + 0.5  # Vary t from 0.5 to 1 (post-critical deformation)
            deformation = (frame / frames) * max_deformation

            # Apply Symmetry-Breaking Theorem deformation
            for i, vertices in enumerate(hexagons):
                new_vertices_1 = apply_deformation(vertices, t, num_sides, 2, **params)
                hex_colors_1[i].set_xy(new_vertices_1)
                color_1 = colorize_deformation(np.std(new_vertices_1), max_deformation)
                hex_colors_1[i].set_facecolor(color_1)

            # Apply random perturbation to the second set of hexagons
            for i, vertices in enumerate(hexagons):
                new_vertices_2 = random_perturbation(vertices, deformation)
                hex_colors_2[i].set_xy(new_vertices_2)
                color_2 = colorize_deformation(np.std(new_vertices_2), max_deformation)
                hex_colors_2[i].set_facecolor(color_2)

            # Apply Spring-Mass deformation to the third set of hexagons
            for i, vertices in enumerate(hexagons):
                new_vertices_3 = apply_spring_mass_deformation(vertices, deformation)
                hex_colors_3[i].set_xy(new_vertices_3)
                color_3 = colorize_deformation(np.std(new_vertices_3), max_deformation)
                hex_colors_3[i].set_facecolor(color_3)

            # Apply FEM-like deformation to the fourth set of hexagons
            for i, vertices in enumerate(hexagons):
                new_vertices_4 = apply_fem_like_deformation(vertices, deformation)
                hex_colors_4[i].set_xy(new_vertices_4)
                color_4 = colorize_deformation(np.std(new_vertices_4), max_deformation)
                hex_colors_4[i].set_facecolor(color_4)

            return hex_colors_1 + hex_colors_2 + hex_colors_3 + hex_colors_4

        # Create the animation
        ani = FuncAnimation(fig, update, frames=frames, interval=50, blit=True, repeat=True)
        plt.tight_layout()
        plt.show()

    except ValueError as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    create_animation()
