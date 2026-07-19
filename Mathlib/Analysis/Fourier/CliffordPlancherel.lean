/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.Analysis.CliffordAlgebra.EuclideanR3
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Plancherel's theorem for the Clifford–Fourier transform on `ℝ³`

The Clifford–Fourier transform (Ebling–Scheuermann) of a function
`f : ℝ³ → Cl(3,0)` replaces the imaginary unit in the Fourier kernel by the
pseudoscalar `ω = e₀e₁e₂` of the Clifford algebra:

`ℱ f ξ = ∫ x, exp (-2π ⟪x, ξ⟫ ω) * f x
       = ∫ x, cos (2π ⟪x, ξ⟫) • f x - sin (2π ⟪x, ξ⟫) • (ω * f x)`.

Since `ω` is central with `ω² = -1`, this is *literally* the ordinary Fourier
transform of an `H`-valued function for the complex structure on `Cl(3,0)`
induced by `ω` (`CliffordAlgebraR3.instAlgebraComplex`). Equipping the Clifford
algebra with a compatible complex Hilbert space structure, Plancherel's theorem
is inherited from the vector-valued case.

## Main definitions

* `CliffordAlgebraR3.cliffordFourierIntegral`: the Clifford–Fourier transform,
  defined by the real cos/sin kernel above (no complex structure appears in the
  definition).
* `CliffordAlgebraR3.cliffordFourierL2`: the Clifford–Fourier transform as a
  linear isometry equivalence of `L²(ℝ³, Cl(3,0))`.

## Main statements

* `CliffordAlgebraR3.cliffordFourierIntegral_eq_fourier`: the Clifford–Fourier
  transform is the Fourier transform for the pseudoscalar complex structure.
* `CliffordAlgebraR3.integral_inner_cliffordFourier_cliffordFourier`:
  Plancherel's theorem for Schwartz functions.
* `CliffordAlgebraR3.integral_norm_sq_cliffordFourier`: Plancherel's theorem
  for Schwartz functions, norm version.
* `CliffordAlgebraR3.norm_cliffordFourierL2_eq`: Plancherel's theorem on `L²`.

## References

* J. Ebling, G. Scheuermann, *Clifford Fourier transform on vector fields*,
  IEEE Transactions on Visualization and Computer Graphics 11 (2005)
* F. Brackx, N. De Schepper, F. Sommen, *The Clifford-Fourier transform*,
  J. Fourier Anal. Appl. 11 (2005)

-/

@[expose] public section

noncomputable section

open CliffordAlgebra MeasureTheory SchwartzMap Real
open scoped FourierTransform RealInnerProductSpace

namespace CliffordAlgebraR3

/-! ### Finite dimensionality -/

instance : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

instance : Module.Finite ℂ (CliffordAlgebra Q) := by
  -- pin the *native* real module structure of the Clifford algebra (rather than
  -- the one restricted from `ℂ`, which is only propositionally equal to it)
  letI : Module ℝ (CliffordAlgebra Q) := Algebra.toModule
  haveI : Module.Finite ℝ (ExteriorAlgebra ℝ (EuclideanSpace ℝ (Fin 3))) :=
    Module.Finite.of_basis ((PiLp.basisFun 2 ℝ (Fin 3)).ExteriorAlgebra)
  haveI : Module.Finite ℝ (CliffordAlgebra Q) := Module.Finite.equiv (equivExterior Q).symm
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

/-! ### The Hilbert space structure

We fix a complex Hilbert space structure on `Cl(3,0)` compatible with the
pseudoscalar complex structure by transporting the one of `EuclideanSpace ℂ (Fin 4)`
along a `ℂ`-basis. (Plancherel's theorem below holds for any such choice.) -/

/-- A `ℂ`-linear equivalence of `Cl(3,0)` with a complex Euclidean space,
fixing a Hilbert space structure. -/
def toEuclidean :
    CliffordAlgebra Q ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ (CliffordAlgebra Q))) :=
  (Module.finBasis ℂ _).equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm

scoped instance instNormedAddCommGroup : NormedAddCommGroup (CliffordAlgebra Q) :=
  NormedAddCommGroup.induced _ _ toEuclidean.toLinearMap
    toEuclidean.injective

scoped instance instInnerProductSpace : InnerProductSpace ℂ (CliffordAlgebra Q) :=
  InnerProductSpace.induced toEuclidean.toLinearMap

scoped instance instCompleteSpace : CompleteSpace (CliffordAlgebra Q) :=
  FiniteDimensional.complete ℂ _

/-! ### The Clifford–Fourier transform -/

/-- The Clifford–Fourier kernel `exp (-2π ⟪x, ξ⟫ ω) = cos (2π ⟪x, ξ⟫) - sin (2π ⟪x, ξ⟫) ω`,
where `ω` is the pseudoscalar. Defined by ring operations only, so it does not depend on
any choice of analytic structure on the Clifford algebra. -/
def cliffordFourierKernel (x ξ : EuclideanSpace ℝ (Fin 3)) : CliffordAlgebra Q :=
  algebraMap ℝ _ (Real.cos (2 * π * ⟪x, ξ⟫))
    - algebraMap ℝ _ (Real.sin (2 * π * ⟪x, ξ⟫)) * pseudoscalar

/-- The Clifford–Fourier transform on `ℝ³` (Ebling–Scheuermann): the Fourier
kernel `exp (-2π ⟪x, ξ⟫ ω)` multiplies from the left. -/
def cliffordFourierIntegral (f : EuclideanSpace ℝ (Fin 3) → CliffordAlgebra Q)
    (ξ : EuclideanSpace ℝ (Fin 3)) : CliffordAlgebra Q :=
  ∫ x, cliffordFourierKernel x ξ * f x

/-- Complex scalar multiplication on `Cl(3,0)` written with ring operations. -/
theorem complex_smul_eq_mul (z : ℂ) (a : CliffordAlgebra Q) :
    z • a = (algebraMap ℝ _ z.re + algebraMap ℝ _ z.im * pseudoscalar) * a := by
  rw [complex_smul_def, complexLift_apply, Algebra.smul_def]

/-- The scalar action of the Fourier character is left multiplication by the
Clifford–Fourier kernel. -/
theorem exp_smul_eq_cliffordFourierKernel_mul (x ξ : EuclideanSpace ℝ (Fin 3))
    (a : CliffordAlgebra Q) :
    Complex.exp (((-(2 * π * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I) • a
      = cliffordFourierKernel x ξ * a := by
  rw [complex_smul_eq_mul, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg, map_neg, neg_mul, ← sub_eq_add_neg, cliffordFourierKernel]

/-- The Clifford–Fourier transform is the Fourier transform of a vector-valued
function, for the complex structure on `Cl(3,0)` given by the pseudoscalar. -/
theorem cliffordFourierIntegral_eq_fourier
    (f : EuclideanSpace ℝ (Fin 3) → CliffordAlgebra Q) (ξ : EuclideanSpace ℝ (Fin 3)) :
    cliffordFourierIntegral f ξ = 𝓕 f ξ := by
  rw [Real.fourier_eq', cliffordFourierIntegral]
  congr 1 with x
  rw [show ((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I
        = ((-(2 * π * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I by norm_num,
    exp_smul_eq_cliffordFourierKernel_mul]

/-! ### Plancherel's theorem -/

/-- **Plancherel's theorem** for the Clifford–Fourier transform of Schwartz
functions `ℝ³ → Cl(3,0)`, inner product version. -/
theorem integral_inner_cliffordFourier_cliffordFourier
    (f g : 𝓢(EuclideanSpace ℝ (Fin 3), CliffordAlgebra Q)) :
    ∫ ξ, inner ℂ (cliffordFourierIntegral (⇑f) ξ) (cliffordFourierIntegral (⇑g) ξ)
      = ∫ x, inner ℂ (f x) (g x) := by
  have hf : ∀ ξ, cliffordFourierIntegral (⇑f) ξ = 𝓕 f ξ := fun ξ => by
    rw [cliffordFourierIntegral_eq_fourier, fourier_coe]
  have hg : ∀ ξ, cliffordFourierIntegral (⇑g) ξ = 𝓕 g ξ := fun ξ => by
    rw [cliffordFourierIntegral_eq_fourier, fourier_coe]
  simp_rw [hf, hg]
  exact integral_inner_fourier_fourier f g

/-- **Plancherel's theorem** for the Clifford–Fourier transform of Schwartz
functions `ℝ³ → Cl(3,0)`: the Clifford–Fourier transform preserves the
`L²` norm. -/
theorem integral_norm_sq_cliffordFourier
    (f : 𝓢(EuclideanSpace ℝ (Fin 3), CliffordAlgebra Q)) :
    ∫ ξ, ‖cliffordFourierIntegral (⇑f) ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hf : ∀ ξ, cliffordFourierIntegral (⇑f) ξ = 𝓕 f ξ := fun ξ => by
    rw [cliffordFourierIntegral_eq_fourier, fourier_coe]
  simp_rw [hf]
  exact integral_norm_sq_fourier f

/-- The Clifford–Fourier transform as a linear isometry equivalence of
`L²(ℝ³, Cl(3,0))` — the `L²` form of **Plancherel's theorem**. On Schwartz
functions it is given by `cliffordFourierIntegral`. -/
def cliffordFourierL2 :
    Lp (α := EuclideanSpace ℝ (Fin 3)) (CliffordAlgebra Q) 2 ≃ₗᵢ[ℂ]
      Lp (α := EuclideanSpace ℝ (Fin 3)) (CliffordAlgebra Q) 2 :=
  Lp.fourierTransformₗᵢ _ _

@[simp] theorem norm_cliffordFourierL2_eq
    (f : Lp (α := EuclideanSpace ℝ (Fin 3)) (CliffordAlgebra Q) 2) :
    ‖cliffordFourierL2 f‖ = ‖f‖ :=
  cliffordFourierL2.norm_map f

/-- On (the `L²` class of) a Schwartz function, `cliffordFourierL2` is computed
by the Clifford–Fourier integral. -/
theorem cliffordFourierL2_toLp (f : 𝓢(EuclideanSpace ℝ (Fin 3), CliffordAlgebra Q)) :
    cliffordFourierL2 (f.toLp 2) = ((𝓕 f).toLp 2 :) :=
  SchwartzMap.toLp_fourier_eq f

end CliffordAlgebraR3
