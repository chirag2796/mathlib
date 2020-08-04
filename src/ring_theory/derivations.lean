/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import algebra.lie_algebra
import tactic

/-!
# Derivations

This file defines derivation.

IMPORTANT: this file is just a stub to go on with some PRs in the geometry section. It only
only implements the definition of derivations in commutative algebra. This will soon change: as soon
as bimodules will be there in mathlib I will changee this file to take into account the
non-commutative case. Any development on the theory of derivations is discouraged until the
definitive definition of derivation will be implemented.
-/

open algebra ring_hom

def transitive_scalar (R : Type*) (A : Type*) (M : Type*)
  [comm_semiring R] [semiring A] [algebra R A]
  [add_comm_monoid M] [semimodule A M] : has_scalar R M :=
{ smul := λ r m, ((algebra_map R A) r) • m, }

def transitive_module (R : Type*) (A : Type*) (M : Type*)
  [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule A M] :
  semimodule R M :=
{ smul_add := λ r x y, smul_add _ _ _,
  smul_zero := λ r, smul_zero _,
  zero_smul := λ x, show algebra_map R A 0 • x = 0, by rw [map_zero, zero_smul],
  one_smul := λ x, show algebra_map R A 1 • x = x, by rw [map_one, one_smul],
  mul_smul := λ r s x, show algebra_map R A (r * s) • x =
    algebra_map R A r • algebra_map R A s • x, by rw [map_mul, mul_smul],
  add_smul := λ r s x, show algebra_map R A (r + s) • x =
    algebra_map R A r • x + algebra_map R A s • x, by rw [map_add, add_smul],
  .. transitive_scalar R A M }

@[protect_proj]
class compatible_semimodule (R : Type*) (A : Type*) [comm_semiring R] [semiring A] [algebra R A]
(M : Type*) [add_comm_monoid M] [semimodule A M] [semimodule R M] :=
(compatible_smul (r : R) (m : M) : r • m = ((algebra_map R A) r) • m)

instance algebra.to_compatible_semimodule  {R : Type*} {A : Type*} [comm_semiring R] [semiring A]
  [algebra R A] : compatible_semimodule R A A :=
⟨λ r a, by rw [smul_def]; refl⟩

section compatible_semimodule

variables {R : Type*} [comm_semiring R]
(A : Type*) [comm_semiring A] [algebra R A]
{M : Type*} [add_comm_monoid M] [semimodule A M] [semimodule R M] [compatible_semimodule R A M]
{N : Type*} [add_comm_monoid N] [semimodule A N] [semimodule R N] [compatible_semimodule R A N]

@[simp] lemma compatible_smul (r : R) (m : M) : r • m = ((algebra_map R A) r) • m :=
compatible_semimodule.compatible_smul r m

variable {A}

@[simp] lemma compatible_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
by rw [compatible_smul A r m, compatible_smul A r (a • m), ←mul_smul, mul_comm, mul_smul]

@[simp] lemma compatible_map_smul (f : M →ₗ[A] N) (r : R) (m : M) :
  f (r • m) = r • f m :=
by rw [compatible_smul A r m, linear_map.map_smul, ←compatible_smul A r (f m)]

instance : has_coe (M →ₗ[A] N) (M →ₗ[R] N) :=
⟨λ f, ⟨f.to_fun, λ x y, f.map_add' x y, λ r n, compatible_map_smul _ _ _⟩⟩

end compatible_semimodule

@[protect_proj]
structure derivation (R : Type*) (A : Type*) [comm_semiring R] [comm_semiring A]
  [algebra R A] (M : Type*) [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M]
  [compatible_semimodule R A M]
  extends A →ₗ[R] M :=
(leibniz' (a b : A) : to_fun (a * b) = a • to_fun b + b • to_fun a)

namespace derivation

section

variables {R : Type*} [comm_semiring R]
{A : Type*} [comm_semiring A] [algebra R A]
{M : Type*} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M]
[compatible_semimodule R A M]
(D : derivation R A M) {D1 D2 : derivation R A M} (r : R) (a b : A)

instance : has_coe_to_fun (derivation R A M) := ⟨_, λ D, D.to_linear_map.to_fun⟩

instance has_coe_to_linear_map : has_coe (derivation R A M) (A →ₗ[R] M) :=
  ⟨λ D, D.to_linear_map⟩

@[simp, norm_cast]
lemma coe_linear_map (f : derivation R A M) :
  ⇑(f : A →ₗ[R] M) = f := rfl

lemma coe_injective (H : ⇑D1 = D2) : D1 = D2 :=
by cases D1; cases D2; congr'; exact linear_map.coe_inj H

@[ext] theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
coe_injective $ funext H

@[simp] lemma map_add : D (a + b) = D a + D b := is_add_hom.map_add D a b
@[simp] lemma map_zero : D 0 = 0 := is_add_monoid_hom.map_zero D
@[simp] lemma map_mul : D (a * b) = a • D b + b • D a := D.leibniz' _ _
@[simp] lemma map_smul : D (r • a) = r • D a := linear_map.map_smul D r a
@[simp] lemma leibniz : D (a * b) = b • D a + a • D b := (D.leibniz' a b).trans $ add_comm _ _

@[simp] lemma map_one_eq_zero : D 1 = 0 :=
begin
  have h : D 1 = D (1 * 1) := by rw mul_one,
  rw [leibniz D 1 1, one_smul] at h, /- better way to do this? -/
  exact zero_left_cancel h,
end

@[simp] lemma map_algebra_map : D (algebra_map R A r) = 0 :=
by rw [←mul_one r, ring_hom.map_mul, map_one, ←smul_def, map_smul, map_one_eq_zero, smul_zero]

instance : add_comm_monoid (derivation R A M) :=
{ add := λ D1 D2, ⟨D1 + D2, λ a b, begin
  simp only [leibniz, linear_map.add_apply, linear_map.to_fun_eq_coe, coe_linear_map, smul_add],
  cc, end⟩,
  zero := ⟨(0 : A →ₗ[R] M), λ a b, by simp only [add_zero, linear_map.zero_apply, linear_map.to_fun_eq_coe, smul_zero]⟩,
  add_assoc := λ D E F, ext $ λ a, add_assoc _ _ _,
  zero_add := λ D, ext $ λ a, zero_add _,
  add_zero := λ D, ext $ λ a, add_zero _,
  add_comm := λ D E, ext $ λ a, add_comm _ _, }

@[priority 100]
instance derivation.Rsemimodule : semimodule R (derivation R A M) :=
{ smul := λ r D, ⟨r • D, λ a b, by simp only [linear_map.smul_apply, leibniz,
linear_map.to_fun_eq_coe, compatible_smul_comm, coe_linear_map, smul_add, add_comm],⟩,
  mul_smul := λ a1 a2 D, ext $ λ b, mul_smul _ _ _,
  one_smul := λ D, ext $ λ b, one_smul _ _,
  smul_add := λ a D1 D2, ext $ λ b, smul_add _ _ _,
  smul_zero := λ a, ext $ λ b, smul_zero _,
  add_smul := λ a1 a2 D, ext $ λ b, add_smul _ _ _,
  zero_smul := λ D, ext $ λ b, zero_smul _ _ }

instance : semimodule A (derivation R A M) :=
{ smul := λ a D, ⟨⟨λ b, a • D b,
    λ a1 a2, by rw [D.map_add, smul_add],
    λ a1 a2, by rw [D.map_smul, compatible_smul_comm]⟩,
    λ b c, by {dsimp, simp only [smul_add, leibniz, smul_comm, add_comm],}⟩,
  mul_smul := λ a1 a2 D, ext $ λ b, mul_smul _ _ _,
  one_smul := λ D, ext $ λ b, one_smul A _,
  smul_add := λ a D1 D2, ext $ λ b, smul_add _ _ _,
  smul_zero := λ a, ext $ λ b, smul_zero _,
  add_smul := λ a1 a2 D, ext $ λ b, add_smul _ _ _,
  zero_smul := λ D, ext $ λ b, zero_smul A _ }

def comp {N : Type*} [add_cancel_comm_monoid N] [semimodule A N] [semimodule R N]
  [compatible_semimodule R A N]
  (D : derivation R A M) (f : M →ₗ[A] N) : derivation R A N :=
{ to_fun := λ a, f (D a),
  map_add' := λ a1 a2, by rw [D.map_add, f.map_add],
  map_smul' := λ r a, by rw [map_smul, compatible_map_smul],
  leibniz' := λ a b, by simp only [leibniz, linear_map.map_smul, linear_map.map_add, add_comm] }

end

section

variables {R : Type*} [comm_ring R]
{A : Type*} [comm_ring A] [algebra R A]
{M : Type*} [add_comm_group M] [module A M] [module R M]
[compatible_semimodule R A M]
(D : derivation R A M) {D1 D2 : derivation R A M} (r : R) (a b : A)

@[simp] lemma map_neg : D (-a) = -D a := linear_map.map_neg D a
@[simp] lemma map_sub : D (a - b) = D a - D b := linear_map.map_sub D a b

open ring_commutator

def commutator (D1 D2 : derivation R A A) : derivation R A A :=
⟨commutator D1 D2, λ a b, by simp only [commutator, map_add, id.smul_eq_mul, linear_map.mul_app,
leibniz, linear_map.to_fun_eq_coe, coe_linear_map, linear_map.sub_apply]; ring⟩

localized "notation `⁅`x`,` y`⁆` := derivation.commutator x y" in derivation

end

end derivation
