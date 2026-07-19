/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# The Clifford algebra of Euclidean 3-space and its complex structure

We study `Cl(3,0)`, the Clifford algebra of `EuclideanSpace ℝ (Fin 3)` with the quadratic
form `x ↦ ⟪x, x⟫_ℝ`, known in physics as the algebra of physical space.

The pseudoscalar `ω = e₀ * e₁ * e₂` satisfies `ω * ω = -1` and is *central*
(this is special to `n ≡ 3 [MOD 4]`), hence by `Complex.liftAux` it induces an
`Algebra ℂ` structure on the Clifford algebra. This complex structure is what makes the
Clifford–Fourier transform on `ℝ³` (Ebling–Scheuermann) an instance of the ordinary
vector-valued Fourier transform; see `Mathlib/Analysis/Fourier/CliffordPlancherel.lean`.

## Main definitions

* `CliffordAlgebraR3.Q`: the norm-squared quadratic form on `EuclideanSpace ℝ (Fin 3)`.
* `CliffordAlgebraR3.pseudoscalar`: the pseudoscalar `ω`.
* `CliffordAlgebraR3.instAlgebraComplex`: the `Algebra ℂ` structure induced by `ω`
  (a scoped instance).

## Main statements

* `CliffordAlgebraR3.pseudoscalar_mul_pseudoscalar`: `ω * ω = -1`.
* `CliffordAlgebraR3.commute_pseudoscalar`: `ω` is central.

-/

@[expose] public section

noncomputable section

open CliffordAlgebra
open scoped RealInnerProductSpace

namespace CliffordAlgebraR3

/-- The norm-squared quadratic form on Euclidean 3-space. -/
def Q : QuadraticForm ℝ (EuclideanSpace ℝ (Fin 3)) :=
  LinearMap.BilinMap.toQuadraticMap (innerₗ _)

@[simp] theorem Q_apply (x : EuclideanSpace ℝ (Fin 3)) : Q x = ⟪x, x⟫ := rfl

/-- The `i`-th standard generator of Euclidean 3-space. -/
def e (i : Fin 3) : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single i 1

theorem inner_e_e_of_ne {i j : Fin 3} (h : i ≠ j) : ⟪e i, e j⟫ = 0 := by
  simp [e, EuclideanSpace.inner_single_left, h.symm]

@[simp] theorem Q_e (i : Fin 3) : Q (e i) = 1 := by
  simp [e]

theorem isOrtho_e {i j : Fin 3} (h : i ≠ j) : Q.IsOrtho (e i) (e j) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [Q_apply, real_inner_add_add_self, inner_e_e_of_ne h]
  ring

/-- The `i`-th standard generator of the Clifford algebra `Cl(3,0)`. -/
def γ (i : Fin 3) : CliffordAlgebra Q := ι Q (e i)

@[simp] theorem γ_mul_γ_self (i : Fin 3) : γ i * γ i = 1 := by
  rw [γ, ι_sq_scalar, Q_e, map_one]

theorem γ_mul_γ_of_ne {i j : Fin 3} (h : i ≠ j) : γ i * γ j = -(γ j * γ i) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_e h)

/-! The relations of `Cl(3,0)`, oriented so that repeatedly rewriting with them sorts
the indices of a product of generators (a confluent rewriting system). -/

@[simp] theorem γ_mul_γ_cancel (i : Fin 3) (x : CliffordAlgebra Q) :
    γ i * (γ i * x) = x := by
  rw [← mul_assoc, γ_mul_γ_self, one_mul]

@[simp] theorem γ10 : γ 1 * γ 0 = -(γ 0 * γ 1) := γ_mul_γ_of_ne (by decide)
@[simp] theorem γ20 : γ 2 * γ 0 = -(γ 0 * γ 2) := γ_mul_γ_of_ne (by decide)
@[simp] theorem γ21 : γ 2 * γ 1 = -(γ 1 * γ 2) := γ_mul_γ_of_ne (by decide)

@[simp] theorem γ10' (x : CliffordAlgebra Q) : γ 1 * (γ 0 * x) = -(γ 0 * (γ 1 * x)) := by
  rw [← mul_assoc, γ10, neg_mul, mul_assoc]
@[simp] theorem γ20' (x : CliffordAlgebra Q) : γ 2 * (γ 0 * x) = -(γ 0 * (γ 2 * x)) := by
  rw [← mul_assoc, γ20, neg_mul, mul_assoc]
@[simp] theorem γ21' (x : CliffordAlgebra Q) : γ 2 * (γ 1 * x) = -(γ 1 * (γ 2 * x)) := by
  rw [← mul_assoc, γ21, neg_mul, mul_assoc]

/-- The pseudoscalar `ω = e₀ e₁ e₂` of `Cl(3,0)`. -/
def pseudoscalar : CliffordAlgebra Q := γ 0 * (γ 1 * γ 2)

set_option linter.unusedSimpArgs false in
/-- The pseudoscalar of `Cl(3,0)` is a square root of `-1`. -/
@[simp] theorem pseudoscalar_mul_pseudoscalar : pseudoscalar * pseudoscalar = -1 := by
  simp only [pseudoscalar, mul_assoc, mul_neg, neg_mul, neg_neg, γ_mul_γ_cancel,
    γ10', γ20', γ21', γ10, γ20, γ21, γ_mul_γ_self]

set_option linter.unusedSimpArgs false in
/-- The pseudoscalar commutes with every generator. -/
theorem commute_pseudoscalar_γ (i : Fin 3) : Commute pseudoscalar (γ i) :=
  match i with
  | 0 => by
    unfold Commute SemiconjBy pseudoscalar
    simp only [mul_assoc, mul_neg, neg_mul, neg_neg, γ_mul_γ_cancel,
      γ10', γ20', γ21', γ10, γ20, γ21, γ_mul_γ_self, mul_one]
  | 1 => by
    unfold Commute SemiconjBy pseudoscalar
    simp only [mul_assoc, mul_neg, neg_mul, neg_neg, γ_mul_γ_cancel,
      γ10', γ20', γ21', γ10, γ20, γ21, γ_mul_γ_self, mul_one]
  | 2 => by
    unfold Commute SemiconjBy pseudoscalar
    simp only [mul_assoc, mul_neg, neg_mul, neg_neg, γ_mul_γ_cancel,
      γ10', γ20', γ21', γ10, γ20, γ21, γ_mul_γ_self, mul_one]

/-- The pseudoscalar commutes with the image of `ι`. -/
theorem commute_pseudoscalar_ι (x : EuclideanSpace ℝ (Fin 3)) :
    Commute pseudoscalar (ι Q x) := by
  have hx : (∑ i, x i • e i) = x := by
    simpa only [e, PiLp.basisFun_repr, PiLp.basisFun_apply]
      using (PiLp.basisFun 2 ℝ (Fin 3)).sum_repr x
  rw [← hx, map_sum]
  exact Commute.sum_right _ _ _ fun i _ => by
    rw [map_smul]
    exact (commute_pseudoscalar_γ i).smul_right (x i)

/-- The pseudoscalar of `Cl(3,0)` is central. -/
theorem commute_pseudoscalar (a : CliffordAlgebra Q) : Commute pseudoscalar a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => exact Algebra.commute_algebraMap_right r pseudoscalar
  | ι x => exact commute_pseudoscalar_ι x
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

/-- The real-algebra morphism `ℂ →ₐ[ℝ] Cl(3,0)` sending `I` to the pseudoscalar. -/
def complexLift : ℂ →ₐ[ℝ] CliffordAlgebra Q :=
  Complex.liftAux pseudoscalar pseudoscalar_mul_pseudoscalar

theorem complexLift_apply (z : ℂ) :
    complexLift z = algebraMap ℝ _ z.re + z.im • pseudoscalar :=
  Complex.liftAux_apply _ _ z

/-- `Cl(3,0)` is a complex algebra, with `I` acting as the pseudoscalar.

This is a scoped instance since it involves the choice of a pseudoscalar
(i.e. an orientation of `ℝ³`). -/
scoped instance instAlgebraComplex : Algebra ℂ (CliffordAlgebra Q) :=
  (complexLift.toRingHom).toAlgebra' fun z a => by
    have h : Commute (complexLift z) a := by
      rw [complexLift_apply]
      exact (Algebra.commute_algebraMap_left _ _).add_left
        ((commute_pseudoscalar a).smul_left z.im)
    exact h

/-- The complex scalar action on `Cl(3,0)` is left multiplication by `complexLift`. -/
theorem complex_smul_def (z : ℂ) (a : CliffordAlgebra Q) :
    z • a = complexLift z * a := rfl

theorem algebraMap_complex_apply (z : ℂ) :
    algebraMap ℂ (CliffordAlgebra Q) z = algebraMap ℝ _ z.re + z.im • pseudoscalar :=
  complexLift_apply z

/-- Complex scalar multiplication written with real scalars and the pseudoscalar. -/
theorem complex_smul_eq (z : ℂ) (a : CliffordAlgebra Q) :
    z • a = z.re • a + z.im • (pseudoscalar * a) := by
  rw [complex_smul_def, complexLift_apply, add_mul, smul_mul_assoc,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

scoped instance : IsScalarTower ℝ ℂ (CliffordAlgebra Q) :=
  IsScalarTower.of_algebraMap_eq' complexLift.comp_algebraMap.symm

end CliffordAlgebraR3
