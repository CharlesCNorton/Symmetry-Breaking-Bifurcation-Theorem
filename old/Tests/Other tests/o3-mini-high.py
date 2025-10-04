import unittest
import numpy as np
import sympy as sp
from math import isclose, log
from scipy.optimize import newton

# =============================================================================
# I. Symbolic Validation (Pitchfork)
# =============================================================================

def pitchfork_solutions_symbolic(lam_val):
    """
    Symbolically solve the pitchfork equation: f(x, lambda) = lambda*x - x^3 = 0
    """
    x, lam = sp.symbols('x lam', real=True)
    f = lam*x - x**3
    sol = sp.solve(f.subs(lam, lam_val), x)
    sol = [float(s) for s in sol]
    return sorted(sol)

def pitchfork_jacobian_eigen(x_val, lam_val):
    """
    Return the derivative df/dx at (x_val, lam_val).
    For f(x, lambda) = lambda*x - x^3, df/dx = lambda - 3x^2.
    """
    x, lam = sp.symbols('x lam', real=True)
    f = lam*x - x**3
    df_dx = sp.diff(f, x)
    return float(df_dx.subs({x: x_val, lam: lam_val}))

# =============================================================================
# II. Numerical Bifurcation Tests
# =============================================================================

def pitchfork_f(x, lam):
    return lam*x - x**3

def pitchfork_fprime(x, lam):
    return lam - 3*x**2

def solve_pitchfork_newton(x0, lam_val, tol=1e-8):
    """
    Numerically solve pitchfork_f(x, lam_val) = 0 with Newton's method.
    """
    def f_func(x):
        return pitchfork_f(x, lam_val)
    def df_func(x):
        return pitchfork_fprime(x, lam_val)
    return newton(f_func, x0, fprime=df_func, tol=tol)

def find_jacobian_eigenvalue(x_val, lam_val):
    """
    Compute the eigenvalue of the Jacobian for f(x) = λx - x³.
    """
    return lam_val - 3*(x_val**2)

# =============================================================================
# III. Theorem Equation Checks (piecewise ΔG)
# =============================================================================

def delta_G_theorem(t, n, d, A_d, k_d, B_d, C_d, eps=0.01, t_c=0.5):
    """
    Implements the piecewise definition of ΔG from the theorem:

      For t <= t_c: ΔG(t,n,d) = 0
      For t >  t_c: ΔG(t,n,d) = (A_d / (n^k_d)) * ((t - t_c + eps)^(B_d*ln(n) + C_d))

    Returns the computed ΔG value.
    """
    if t <= t_c:
        return 0.0
    else:
        base = max(0.0, t - t_c + eps)
        exponent = B_d * np.log(n) + C_d
        return (A_d / (n**k_d)) * (base**exponent)

def compute_theorem_constants(n, d, geom_measure, euler_char=120):
    """
    Returns (A, k, B, C) for the theorem constants based on the dimension d.

    For 2D: A = 2n,   k = ln(n),
            B = (1/perimeter)*ln(n)^2 + (0.1 + 0.01 ln(n)),
            C = 2.23

    For 3D: A = |G(P)| (e.g. 24 for a cube, 60 for a dodecahedron),
            k = ln(n),
            B = (1/surface_area)*ln(n)^2 + (0.1 + 0.01 ln(n)),
            C = 1.77

    For 4D: A = |G(P)| (e.g. 14400 for a 600-cell),
            k = ln(n),
            B = (1/hypervolume)*ln(n)^2 + (0.1 + 0.01 ln(n)),
            C = 1.0 + 0.1*(χ/ln(n))
    """
    if d == 2:
        A = 2.0 * n
        k = log(n)
        B = (1.0/geom_measure) * (log(n)**2) + (0.1 + 0.01*log(n))
        C = 2.23
    elif d == 3:
        A = geom_measure  # using geom_measure as |G(P)| (e.g., 24 for a cube)
        k = log(n)
        B = (1.0/geom_measure) * (log(n)**2) + (0.1 + 0.01*log(n))
        C = 1.77
    elif d == 4:
        A = geom_measure  # e.g., 14400 for a 600-cell
        k = log(n)
        B = (1.0/geom_measure) * (log(n)**2) + (0.1 + 0.01*log(n))
        C = 1.0 + 0.1*(euler_char / log(n))
    else:
        raise ValueError("Invalid dimension d. Must be 2, 3, or 4.")
    return A, k, B, C

# =============================================================================
# IV. Geometric Simulation (Regular Polygons)
# =============================================================================

def create_polygon(n):
    """
    Create coordinates for a perfect regular n-gon of radius 1, centered at the origin.
    Returns a numpy array of shape (n, 2).
    """
    angles = np.linspace(0, 2*np.pi, n, endpoint=False)
    coords = np.column_stack([np.cos(angles), np.sin(angles)])
    return coords

def deform_polygon(coords, t, t_c=0.5):
    """
    Deform the polygon:
      - For t <= t_c, the polygon remains unchanged.
      - For t > t_c, apply an asymmetric radial deformation.
    
    Returns the deformed coordinate array.
    """
    new_coords = coords.copy()
    if t <= t_c:
        return new_coords
    else:
        factor = (t - t_c) * 0.2  # deformation magnitude
        n = len(coords)
        for i in range(n):
            direction = 1 if i % 2 == 0 else -1
            r = np.linalg.norm(new_coords[i])
            radial_unit = new_coords[i] / r if r > 1e-12 else np.array([1.0, 0.0])
            new_coords[i] += factor * direction * radial_unit
        return new_coords

def measure_symmetry(coords):
    """
    Measure the symmetry of a polygon by computing the standard deviation of
    the distances of vertices from the center.
    For a perfectly symmetric polygon, all vertices are equidistant from the center,
    so the standard deviation is zero.
    """
    distances = np.linalg.norm(coords, axis=1)
    return np.std(distances)

# =============================================================================
# UNITTEST SUITE
# =============================================================================

class TestSymmetryBreakingBifurcation(unittest.TestCase):
    # -------------------------------------------------------------------------
    # A. Symbolic Tests for Pitchfork
    # -------------------------------------------------------------------------
    
    def test_symbolic_pitchfork_below_threshold(self):
        lam_val = -1.0
        sol = pitchfork_solutions_symbolic(lam_val)
        self.assertEqual(len(sol), 1)
        self.assertTrue(isclose(sol[0], 0.0, abs_tol=1e-7))
    
    def test_symbolic_pitchfork_above_threshold(self):
        lam_val = 4.0
        sol = pitchfork_solutions_symbolic(lam_val)
        expected = [-2.0, 0.0, 2.0]
        self.assertEqual(len(sol), 3)
        for s, e in zip(sol, expected):
            self.assertTrue(isclose(s, e, rel_tol=1e-5))
    
    def test_symbolic_pitchfork_jacobian(self):
        lam_val = 2.0
        eig = pitchfork_jacobian_eigen(0.0, lam_val)
        self.assertTrue(isclose(eig, lam_val, rel_tol=1e-7))
    
    # -------------------------------------------------------------------------
    # B. Numerical Tests for Pitchfork
    # -------------------------------------------------------------------------
    
    def test_numerical_pitchfork_newton(self):
        lam_val = -0.5
        root_neg = solve_pitchfork_newton(0.1, lam_val)
        self.assertTrue(isclose(root_neg, 0.0, abs_tol=1e-6))
        
        lam_val = 9.0
        root_pos = solve_pitchfork_newton(3.0, lam_val)
        self.assertTrue(isclose(root_pos, 3.0, rel_tol=1e-6))
        root_neg = solve_pitchfork_newton(-2.5, lam_val)
        self.assertTrue(isclose(root_neg, -3.0, rel_tol=1e-6))
    
    # -------------------------------------------------------------------------
    # C. Theorem Equation Checks
    # -------------------------------------------------------------------------
    
    def test_delta_G_continuity(self):
        n, d = 6, 2
        perimeter = 6.0  # Example perimeter for a regular hexagon
        A_d, k_d, B_d, C_d = compute_theorem_constants(n, d, perimeter)
        t_c = 0.5
        eps = 0.01
        
        val_left = delta_G_theorem(t_c - 1e-5, n, d, A_d, k_d, B_d, C_d, eps=eps, t_c=t_c)
        val_right = delta_G_theorem(t_c + 1e-5, n, d, A_d, k_d, B_d, C_d, eps=eps, t_c=t_c)
        
        self.assertTrue(isclose(val_left, 0.0, abs_tol=1e-12),
                        "ΔG should be 0 for t <= t_c.")
        self.assertLess(val_right, 1e-3,
                        f"ΔG just above t_c should remain small with eps={eps} (got {val_right}).")
    
    def test_delta_G_scaling_above_threshold(self):
        n, d = 6, 2
        perimeter = 6.0
        A_d, k_d, B_d, C_d = compute_theorem_constants(n, d, perimeter)
        t_c = 0.5
        t1, t2 = 0.6, 0.9
        val1 = delta_G_theorem(t1, n, d, A_d, k_d, B_d, C_d)
        val2 = delta_G_theorem(t2, n, d, A_d, k_d, B_d, C_d)
        
        self.assertGreater(val2, val1, f"ΔG({t2}) should be larger than ΔG({t1}).")
    
    # -------------------------------------------------------------------------
    # D. Geometric Simulation (Regular Polygons)
    # -------------------------------------------------------------------------
    
    def test_polygon_symmetry_breaking_vs_theorem(self):
        # Test for a square (n=4) and hexagon (n=6)
        polygons = [(4, 4.0), (6, 6.0)]  # (n, approximate perimeter)
        t_c = 0.5
        eps = 0.01
        
        for (n, perimeter) in polygons:
            with self.subTest(n=n):
                A_d, k_d, B_d, C_d = compute_theorem_constants(n, 2, perimeter)
                Tvals = np.linspace(0, 1, 11)
                coords_initial = create_polygon(n)
                
                for t in Tvals:
                    coords_def = deform_polygon(coords_initial, t, t_c=t_c)
                    # Use standard deviation of radial distances as a measure of symmetry
                    error = measure_symmetry(coords_def)
                    model_val = delta_G_theorem(t, n, 2, A_d, k_d, B_d, C_d, eps=eps, t_c=t_c)
                    
                    if t <= t_c:
                        self.assertTrue(error < 1e-3, 
                                        f"n={n}, t={t}: Expected near-perfect symmetry (error={error}).")
                        self.assertTrue(isclose(model_val, 0.0, abs_tol=1e-7),
                                        f"n={n}, t={t}: ΔG(t) should be 0 (got {model_val}).")
                    else:
                        self.assertGreater(error, 1e-5, 
                                           f"n={n}, t={t}: Expected symmetry breaking (error={error}).")
                        self.assertGreater(model_val, 0.0,
                                           f"n={n}, t={t}: ΔG(t) should be positive (got {model_val}).")
                        # Check that both error and ΔG increase with t (qualitative correlation)

# =============================================================================
# Main Runner
# =============================================================================

if __name__ == '__main__':
    unittest.main()
