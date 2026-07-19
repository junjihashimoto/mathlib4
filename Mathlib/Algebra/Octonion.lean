/-
Copyright (c) 2026 Junji Hashimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junji Hashimoto
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Octonions

We define the octonions `Octonion R` over a commutative ring `R` by the Cayley–Dickson
doubling of the quaternions: an octonion is a pair `⟨a, b⟩` of quaternions, multiplied by

`⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩`.

The octonions are *not associative*, so `Octonion R` is only a `NonUnitalNonAssocRing`
with a unit `⟨1, 0⟩` (`Octonion.one_mul`/`Octonion.mul_one` hold but there is no class
packaging them without associativity of the underlying multiplication).

The doubling unit `ℓ = ⟨0, 1⟩` satisfies `ℓ * ℓ = -1` and, crucially,
`ℓ * (ℓ * x) = -x` (`Octonion.unit_mul_unit_mul`). The latter is an instance of the left
alternative law; here it is proved by direct computation, without developing
alternativity. It makes left multiplication by `ℓ` a complex structure on the octonions,
which is what the octonion Fourier transform needs; see
`Mathlib/Analysis/Fourier/OctonionPlancherel.lean`.

## Main definitions

* `Octonion R`: the octonions over `R`.
* `Octonion.unit`: the doubling unit `ℓ`.

## TODO

* alternativity (the Moufang identities), the multiplicative norm, the `StarRing`
  structure, `NonAssocRing`.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. 39 (2002)

-/

@[expose] public section

open Quaternion

/-- The octonions over a commutative ring `R`, as pairs of quaternions
(Cayley–Dickson construction). -/
@[ext]
structure Octonion (R : Type*) [CommRing R] where
  /-- The first quaternion component. -/
  fst : ℍ[R]
  /-- The second quaternion component. -/
  snd : ℍ[R]

namespace Octonion

variable {R S : Type*} [CommRing R]

instance : Zero (Octonion R) := ⟨⟨0, 0⟩⟩
instance : Add (Octonion R) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
instance : Neg (Octonion R) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
instance : Sub (Octonion R) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
instance [SMul S ℍ[R]] : SMul S (Octonion R) :=
  ⟨fun s x => ⟨s • x.fst, s • x.snd⟩⟩

@[simp] theorem zero_fst : (0 : Octonion R).fst = 0 := rfl
@[simp] theorem zero_snd : (0 : Octonion R).snd = 0 := rfl
@[simp] theorem add_fst (x y : Octonion R) : (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem add_snd (x y : Octonion R) : (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem neg_fst (x : Octonion R) : (-x).fst = -x.fst := rfl
@[simp] theorem neg_snd (x : Octonion R) : (-x).snd = -x.snd := rfl
@[simp] theorem sub_fst (x y : Octonion R) : (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem sub_snd (x y : Octonion R) : (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem smul_fst [SMul S ℍ[R]] (s : S) (x : Octonion R) :
    (s • x).fst = s • x.fst := rfl
@[simp] theorem smul_snd [SMul S ℍ[R]] (s : S) (x : Octonion R) :
    (s • x).snd = s • x.snd := rfl

def toProd (x : Octonion R) : ℍ[R] × ℍ[R] := (x.fst, x.snd)

theorem toProd_injective : Function.Injective (toProd (R := R)) := fun x y h => by
  cases x
  cases y
  simpa [toProd, Prod.ext_iff] using h

instance : AddCommGroup (Octonion R) :=
  toProd_injective.addCommGroup toProd rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

def toProdHom : Octonion R →+ ℍ[R] × ℍ[R] where
  toFun := toProd
  map_zero' := rfl
  map_add' _ _ := rfl

instance instModule [Semiring S] [Module S ℍ[R]] : Module S (Octonion R) :=
  toProd_injective.module S toProdHom fun _ _ => rfl

variable (S) in
/-- `toProd` as a linear equivalence. -/
@[simps apply]
def toProdLinearEquiv [Semiring S] [Module S ℍ[R]] : Octonion R ≃ₗ[S] ℍ[R] × ℍ[R] where
  toFun := toProd
  invFun p := ⟨p.1, p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : Module.Finite R (Octonion R) :=
  Module.Finite.equiv (toProdLinearEquiv R).symm

/-! ### Multiplication (Cayley–Dickson) -/

instance : Mul (Octonion R) :=
  ⟨fun x y => ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩⟩

theorem mul_def (x y : Octonion R) :
    x * y = ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩ :=
  rfl

@[simp] theorem mul_fst (x y : Octonion R) :
    (x * y).fst = x.fst * y.fst - star y.snd * x.snd := rfl
@[simp] theorem mul_snd (x y : Octonion R) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := rfl

instance : One (Octonion R) := ⟨⟨1, 0⟩⟩

@[simp] theorem one_fst : (1 : Octonion R).fst = 1 := rfl
@[simp] theorem one_snd : (1 : Octonion R).snd = 0 := rfl

instance : NonUnitalNonAssocRing (Octonion R) where
  left_distrib _ _ _ := by ext <;> simp [star_add, mul_add, add_mul] <;> ring
  right_distrib _ _ _ := by ext <;> simp [mul_add, add_mul] <;> ring
  zero_mul _ := by ext <;> simp
  mul_zero _ := by ext <;> simp

protected theorem one_mul (x : Octonion R) : 1 * x = x := by ext <;> simp
protected theorem mul_one (x : Octonion R) : x * 1 = x := by ext <;> simp

theorem smul_mul_assoc' [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    [IsScalarTower S R R] (s : S) (x y : Octonion R) : (s • x) * y = s • (x * y) := by
  ext <;> simp [smul_sub, smul_add, mul_smul_comm, smul_mul_assoc]

theorem mul_smul_comm' [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    [IsScalarTower S R R] (s : S) (x y : Octonion R) : x * (s • y) = s • (x * y) := by
  ext <;>
    simp [Quaternion.star_smul, smul_sub, smul_add, mul_smul_comm, smul_mul_assoc]

/-! ### The doubling unit -/

variable (R) in
/-- The Cayley–Dickson doubling unit `ℓ = ⟨0, 1⟩` of the octonions. -/
def unit : Octonion R := ⟨0, 1⟩

@[simp] theorem unit_fst : (unit R).fst = 0 := rfl
@[simp] theorem unit_snd : (unit R).snd = 1 := rfl

@[simp] theorem unit_mul_unit : unit R * unit R = -1 := by
  ext <;> simp

theorem unit_mul (x : Octonion R) : unit R * x = ⟨-star x.snd, star x.fst⟩ := by
  ext <;> simp

/-- The left alternative law at the doubling unit: `ℓ * (ℓ * x) = (ℓ * ℓ) * x = -x`.
Proved by direct computation (the octonions are alternative, but alternativity is not
developed here). Left multiplication by `ℓ` is therefore a complex structure on the
octonions. -/
@[simp] theorem unit_mul_unit_mul (x : Octonion R) : unit R * (unit R * x) = -x := by
  ext <;> simp

end Octonion
