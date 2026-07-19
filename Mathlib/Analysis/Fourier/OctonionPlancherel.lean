/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.Algebra.Octonion
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Plancherel's theorem for the octonion Fourier transform

The (left-sided) octonion Fourier transform of a function `f : V → 𝕆` on a
finite-dimensional real inner product space `V` replaces the imaginary unit in
the Fourier kernel by the Cayley–Dickson doubling unit `ℓ` of the octonions:

`ℱ f ξ = ∫ x, exp (-2π ⟪x, ξ⟫ ℓ) * f x
       = ∫ x, (cos (2π ⟪x, ξ⟫) - sin (2π ⟪x, ξ⟫) ℓ) * f x`.

The octonions are not associative — and a fortiori not a complex algebra — but
the Fourier theory only needs a complex *module* structure on the codomain.
Left multiplication by `ℓ` squares to `-1` (`Octonion.unit_mul_unit_mul`, an
instance of the left alternative law), so `Complex.liftAux` into
`Module.End ℝ 𝕆` — where associativity lives — makes the octonions a complex
vector space. Equipping them with a compatible complex Hilbert space structure,
Plancherel's theorem and the Fourier inversion formula are inherited from the
vector-valued case.

## Main definitions

* `Octonion.octonionFourierIntegral`: the octonion Fourier transform, defined
  by the real cos/sin kernel above.
* `Octonion.octonionFourierInvIntegral`: the inverse octonion Fourier
  transform.
* `Octonion.octonionFourierL2`: the octonion Fourier transform as a linear
  isometry equivalence of `L²(V, 𝕆)`.

## Main statements

* `Octonion.octonionFourierIntegral_eq_fourier`: the octonion Fourier
  transform is the Fourier transform for the `ℓ`-complex structure.
* `Octonion.integral_norm_sq_octonionFourier`: Plancherel's theorem for
  Schwartz functions.
* `Octonion.octonionFourierInv_octonionFourier`: the Fourier inversion formula
  for Schwartz functions.

## References

* S. L. Hahn, K. M. Snopek, *The unified theory of n-dimensional complex and
  hypercomplex analytic signals*, Bull. Polish Ac. Sci. 59 (2011)
* Ł. Błaszczyk, *Octonion Fourier transform of real-valued functions of three
  variables*, J. Fourier Anal. Appl. 26 (2020)

-/

@[expose] public section

noncomputable section

open Quaternion MeasureTheory SchwartzMap Real
open scoped FourierTransform RealInnerProductSpace

namespace Octonion

/-! ### The complex structure -/

/-- Left multiplication by the doubling unit `ℓ`, as a real-linear endomorphism. -/
def unitMulHom : Module.End ℝ (Octonion ℝ) where
  toFun x := unit ℝ * x
  map_add' := mul_add _
  map_smul' r x := mul_smul_comm' r _ x

@[simp] theorem unitMulHom_apply (x : Octonion ℝ) : unitMulHom x = unit ℝ * x := rfl

theorem unitMulHom_mul_unitMulHom : unitMulHom * unitMulHom = -1 := by
  ext x : 1
  simp [Module.End.mul_apply]

/-- The real-algebra morphism `ℂ →ₐ[ℝ] Module.End ℝ 𝕆` sending `I` to left
multiplication by the doubling unit. The endomorphism algebra is associative even
though the octonions are not, which is all `Complex.liftAux` needs. -/
def complexLift : ℂ →ₐ[ℝ] Module.End ℝ (Octonion ℝ) :=
  Complex.liftAux unitMulHom unitMulHom_mul_unitMulHom

/-- The octonions are a complex vector space, `I` acting by left multiplication
by the doubling unit `ℓ`. The octonions are *not* a complex algebra: `ℓ` is not
central, but a module structure needs no commutation.

This is a scoped instance since it involves the choice of an imaginary unit. -/
scoped instance instModuleComplex : Module ℂ (Octonion ℝ) :=
  Module.compHom _ complexLift.toRingHom

theorem complex_smul_def (z : ℂ) (x : Octonion ℝ) : z • x = complexLift z x := rfl

/-- The complex scalar action, componentwise. -/
theorem complex_smul_mk (z : ℂ) (x : Octonion ℝ) :
    z • x = ⟨z.re • x.fst - z.im • star x.snd, z.re • x.snd + z.im • star x.fst⟩ := by
  rw [complex_smul_def, complexLift, Complex.liftAux_apply]
  ext <;>
    simp [Module.algebraMap_end_apply, unit_mul, sub_eq_add_neg]

scoped instance : IsScalarTower ℝ ℂ (Octonion ℝ) :=
  ⟨fun r z x => by
    rw [complex_smul_def, complex_smul_def, map_smul, LinearMap.smul_apply]⟩

scoped instance : SMulCommClass ℂ ℂ (Octonion ℝ) :=
  ⟨fun z w x => by
    rw [complex_smul_def, complex_smul_def, complex_smul_def, complex_smul_def,
      ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm z w]⟩

instance : Module.Finite ℂ (Octonion ℝ) := by
  -- pin the native real module structure (rather than the one restricted from `ℂ`)
  letI : Module ℝ (Octonion ℝ) := Octonion.instModule
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

/-! ### The Hilbert space structure -/

/-- A `ℂ`-linear equivalence of `𝕆` with a complex Euclidean space, fixing a
Hilbert space structure. (Plancherel's theorem below holds for any choice.) -/
def toEuclidean :
    Octonion ℝ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ (Octonion ℝ))) :=
  (Module.finBasis ℂ _).equivFun.trans (WithLp.linearEquiv 2 ℂ _).symm

scoped instance instNormedAddCommGroup : NormedAddCommGroup (Octonion ℝ) :=
  NormedAddCommGroup.induced _ _ toEuclidean.toLinearMap toEuclidean.injective

scoped instance instInnerProductSpace : InnerProductSpace ℂ (Octonion ℝ) :=
  InnerProductSpace.induced toEuclidean.toLinearMap

scoped instance instCompleteSpace : CompleteSpace (Octonion ℝ) :=
  FiniteDimensional.complete ℂ _

/-! ### The octonion Fourier transform -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The octonion Fourier kernel `exp (-2π ⟪x, ξ⟫ ℓ) = cos (2π ⟪x, ξ⟫) - sin (2π ⟪x, ξ⟫) ℓ`.
Defined componentwise, so it does not depend on any choice of analytic structure. -/
def octonionFourierKernel (x ξ : V) : Octonion ℝ :=
  ⟨((Real.cos (2 * π * ⟪x, ξ⟫) : ℝ) : ℍ[ℝ]), -((Real.sin (2 * π * ⟪x, ξ⟫) : ℝ) : ℍ[ℝ])⟩

/-- The inverse octonion Fourier kernel `exp (2π ⟪x, ξ⟫ ℓ)`. -/
def octonionFourierInvKernel (x ξ : V) : Octonion ℝ :=
  ⟨((Real.cos (2 * π * ⟪x, ξ⟫) : ℝ) : ℍ[ℝ]), ((Real.sin (2 * π * ⟪x, ξ⟫) : ℝ) : ℍ[ℝ])⟩

/-- The (left-sided) octonion Fourier transform. -/
def octonionFourierIntegral (f : V → Octonion ℝ) (ξ : V) : Octonion ℝ :=
  ∫ x, octonionFourierKernel x ξ * f x

/-- The inverse octonion Fourier transform. -/
def octonionFourierInvIntegral (f : V → Octonion ℝ) (ξ : V) : Octonion ℝ :=
  ∫ x, octonionFourierInvKernel x ξ * f x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The scalar action of the Fourier character is left multiplication by the
octonion Fourier kernel. -/
theorem exp_smul_eq_octonionFourierKernel_mul (x ξ : V) (a : Octonion ℝ) :
    Complex.exp (((-(2 * π * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I) • a
      = octonionFourierKernel x ξ * a := by
  rw [complex_smul_mk, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ext <;>
    simp [octonionFourierKernel, coe_mul_eq_smul, mul_coe_eq_smul, sub_eq_add_neg]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The scalar action of the inverse Fourier character is left multiplication by
the inverse octonion Fourier kernel. -/
theorem exp_smul_eq_octonionFourierInvKernel_mul (x ξ : V) (a : Octonion ℝ) :
    Complex.exp (((2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) • a
      = octonionFourierInvKernel x ξ * a := by
  rw [complex_smul_mk, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ext <;>
    simp [octonionFourierInvKernel, coe_mul_eq_smul, mul_coe_eq_smul, sub_eq_add_neg]

/-- The octonion Fourier transform is the Fourier transform of a vector-valued
function, for the complex structure given by the doubling unit. -/
theorem octonionFourierIntegral_eq_fourier (f : V → Octonion ℝ) (ξ : V) :
    octonionFourierIntegral f ξ = 𝓕 f ξ := by
  rw [Real.fourier_eq', octonionFourierIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change octonionFourierKernel x ξ * f x
    = Complex.exp (((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) • f x
  rw [show ((-2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I
        = ((-(2 * π * ⟪x, ξ⟫) : ℝ) : ℂ) * Complex.I by norm_num,
    exp_smul_eq_octonionFourierKernel_mul]

/-- The inverse octonion Fourier transform is the inverse Fourier transform of a
vector-valued function, for the complex structure given by the doubling unit. -/
theorem octonionFourierInvIntegral_eq_fourierInv (f : V → Octonion ℝ) (ξ : V) :
    octonionFourierInvIntegral f ξ = 𝓕⁻ f ξ := by
  rw [Real.fourierInv_eq', octonionFourierInvIntegral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change octonionFourierInvKernel x ξ * f x
    = Complex.exp (((2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) • f x
  rw [exp_smul_eq_octonionFourierInvKernel_mul]

/-! ### Plancherel's theorem and inversion -/

theorem octonionFourierIntegral_coe (f : 𝓢(V, Octonion ℝ)) (ξ : V) :
    octonionFourierIntegral (⇑f) ξ = 𝓕 f ξ := by
  rw [octonionFourierIntegral_eq_fourier, fourier_coe]

/-- **Plancherel's theorem** for the octonion Fourier transform of Schwartz
functions, inner product version. -/
theorem integral_inner_octonionFourier_octonionFourier (f g : 𝓢(V, Octonion ℝ)) :
    ∫ ξ, inner ℂ (octonionFourierIntegral (⇑f) ξ) (octonionFourierIntegral (⇑g) ξ)
      = ∫ x, inner ℂ (f x) (g x) := by
  simp_rw [octonionFourierIntegral_coe]
  exact integral_inner_fourier_fourier f g

/-- **Plancherel's theorem** for the octonion Fourier transform of Schwartz
functions: the octonion Fourier transform preserves the `L²` norm. -/
theorem integral_norm_sq_octonionFourier (f : 𝓢(V, Octonion ℝ)) :
    ∫ ξ, ‖octonionFourierIntegral (⇑f) ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  simp_rw [octonionFourierIntegral_coe]
  exact integral_norm_sq_fourier f

/-- **Fourier inversion** for the octonion Fourier transform of Schwartz
functions. -/
theorem octonionFourierInv_octonionFourier (f : 𝓢(V, Octonion ℝ)) (x : V) :
    octonionFourierInvIntegral (octonionFourierIntegral (⇑f)) x = f x := by
  have h : octonionFourierIntegral (⇑f) = 𝓕 (⇑f) :=
    funext fun ξ => octonionFourierIntegral_eq_fourier _ ξ
  rw [h, octonionFourierInvIntegral_eq_fourierInv, ← fourier_coe, ← fourierInv_coe,
    FourierPair.fourierInv_fourier_eq f]

/-- **Fourier inversion** for the octonion Fourier transform of Schwartz
functions, the other composition. -/
theorem octonionFourier_octonionFourierInv (f : 𝓢(V, Octonion ℝ)) (x : V) :
    octonionFourierIntegral (octonionFourierInvIntegral (⇑f)) x = f x := by
  have h : octonionFourierInvIntegral (⇑f) = 𝓕⁻ (⇑f) :=
    funext fun ξ => octonionFourierInvIntegral_eq_fourierInv _ ξ
  rw [h, octonionFourierIntegral_eq_fourier, ← fourierInv_coe, ← fourier_coe,
    FourierInvPair.fourier_fourierInv_eq f]

/-! ### `L²` theory -/

variable (V) in
/-- The octonion Fourier transform as a linear isometry equivalence of
`L²(V, 𝕆)` — the `L²` form of **Plancherel's theorem**. -/
def octonionFourierL2 :
    Lp (α := V) (Octonion ℝ) 2 ≃ₗᵢ[ℂ] Lp (α := V) (Octonion ℝ) 2 :=
  Lp.fourierTransformₗᵢ _ _

@[simp] theorem norm_octonionFourierL2_eq (f : Lp (α := V) (Octonion ℝ) 2) :
    ‖octonionFourierL2 V f‖ = ‖f‖ :=
  (octonionFourierL2 V).norm_map f

end Octonion
