/-
Copyright 2025 Chisomo M. Sakala

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

-- import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
-- import Mathlib.LinearAlgebra.Eigenspace.Minpoly
-- import Mathlib.LinearAlgebra.Charpoly.Basic

import Mathlib.Tactic
import Mathlib.Algebra.Module.LinearMap.Defs


def Sequence α := ℕ → α

namespace Sequence

instance : Coe R (ℕ → R) where coe := fun a _ ↦ a -- FIXME: <~~Delete. Find a way to not have to have coerce to underlying sequence definition
instance : Coe R (Sequence R) where coe := fun a _ ↦ a

instance instHAddRatSequence' [Ring R] : HAdd R (Sequence R) (Sequence R) where
  hAdd b f := by unfold Sequence at *; exact ↑b + f


instance [Ring R] : AddCommMonoid (Sequence R) := by unfold Sequence; infer_instance
instance [Ring R] : Module R (Sequence R) := by unfold Sequence; infer_instance



-- @[simp]
theorem add_fun_add [Ring R] {f g : Sequence R} {n : ℕ} : (f + g) n = f n + g n := rfl
theorem smul_fun [Ring R] {a : R} {f : Sequence R} {n : ℕ} : (a • f) n = a • f n := rfl

theorem fun_sum_order [Ring R] (g : Fin (d) → Sequence R):
    (∑ i : Fin (d), fun n ↦ g i n) = (fun n ↦ ∑ i : Fin (d), g i n) := by
  induction d with
  | zero => change _ = Function.const _ 0; simp
  | succ d' ih => funext n; simp_all [Fin.sum_univ_castSucc]


end Sequence
-- end Sequence

namespace Linear
open Sequence
-----------------------------------------

abbrev Transformation (R) [Ring R] := Sequence R →ₗ[R] Sequence R

@[simp]
abbrev Transformation.id (R) [Ring R] : Transformation (R) := LinearMap.id (R := R) (M := Sequence R)


namespace Calculus

def D.toFun' [Ring R] (f : Sequence R) : Sequence R := fun n => f (n + 1) - f n
-- simp [D.toFun', smul_fun, mul_sub]

def D [Ring R] : Transformation R where
  toFun := D.toFun'
  map_add' := by
    intro f g; funext n; induction n; all_goals simp_all [D.toFun', add_fun_add]; try grind
  map_smul' := by
    intros; funext n; induction n; all_goals simp_all [D.toFun', smul_fun, mul_sub]; try grind


def I.toFun' [Ring R] (f : Sequence R) : Sequence R
| 0 => 0
| n + 1 => I.toFun' f n + f n

def I [Ring R] : Transformation R where
  toFun := I.toFun'
  map_add' := by
    intro f g; funext n; induction n; all_goals simp_all [I.toFun', add_fun_add]; try grind
  map_smul' := by
    intros; funext n; induction n; all_goals simp_all [I.toFun', smul_fun, mul_add]; try grind



@[simp]
theorem Diff_const_eq_zero [Ring R] {b : R} : D b = (0:Sequence R) := by unfold D D.toFun'; simp; rfl

@[simp, grind]
theorem Diff_const_add_fun_eq_fun [Ring R] {b : R} (f : Sequence R) : D (b + f) = D f := by
  simp [show D (b + f) = _ from D.map_add _ f]


-- @[simp]
theorem const_mul_idseq [Ring R] {b : R} : (b • (fun (n : ℕ) ↦ n*(1:R))) = (fun (n : ℕ) ↦ (b:R)*n) := by
  funext; norm_num

-- @[simp]
theorem Intg_const_eq_zero [Ring R] {b : R} : I b = (fun (n : ℕ) ↦ b*n : Sequence R)  := by
  simp [I]; funext n
  fun_induction I.toFun' (fun _ ↦ b) n with
  | case1 => simp
  | case2 n ih => norm_num; simp [ih, mul_add]


-- #check

/- Canonical Simplex Sequence of order d -/
def Simp (d : ℕ) (R) [Ring R] : Sequence R := (·.choose d * (1:R))

theorem Intg_const_eq_zero' [Ring R] {b : R} : I b = b • Simp 1 R := by
  unfold Simp
  simp only [Nat.choose_one_right]
  rw [const_mul_idseq, Intg_const_eq_zero]

theorem Intg_const_add_fun_eq_fun [Ring R] {b : R} (f : Sequence R) :
    I (b + f) = (show Sequence _ from ((b:R)*·)) + I f := by
  simp [show I (b + f) = _ from I.map_add b f, Intg_const_eq_zero]

end Calculus
-- end Calculus



variable [Ring R] (T : Transformation R)

@[simp, grind]
theorem zero_of_zero : T 0 = 0 := by simp

@[simp, grind]
theorem smul {a : R} {f : Sequence R} : T (a • f)  = a • (T f) := by simp

-- @[simp]
-- theorem smul' {a : R} {f : Sequence R} :
--     T (fun n ↦ (a•f) n)  = fun n ↦ (a•(T f)) n := by simp

@[simp]
theorem smul'' {a : R} {f : Sequence R} : T (fun n ↦ a*(f n))  = fun n ↦ a*(T f) n := by
  change T (a • f)  = a • (T f)
  simp



@[simp, grind]
theorem Sum {f g : Sequence R} : T (f + g) = (T f) + (T g) := by simp

-- @[simp, grind]
-- theorem sum_smul {a b : R} {f g : Sequence R} : T (a • f + b • g) = (a • T f) + (b • T g) := by simp

-- theorem Sum' {f g : Sequence R} : T (fun n ↦ (f n  + g n)) = (T f) + (T g) := Sum

-- @[simp]
theorem Sum_n {d : ℕ} {f : Fin (d) → Sequence R} : T (∑ k : Fin (d), f k) = ∑ k : Fin (d), T (f k) := by simp

@[grind]
theorem iterate_linearmap {d : ℕ} : IsLinearMap R T^[d]  := by
  constructor
  · intro f g
    induction d generalizing f g
    all_goals simp; try grind
  · intro f a
    induction d generalizing f a
    all_goals simp; try grind



protected def iterate [Ring R] (T : Transformation R) (d : ℕ) : Transformation R where
  toFun := T^[d]
  map_add' := (iterate_linearmap _ ).map_add
  map_smul' := (iterate_linearmap _ ).map_smul


notation:max T_ "^["n_"]'" K_:max => @Linear.iterate K_ _ T_ n_


end Linear

------------------------ ############### END OF LINEAR ################### -----------------------

namespace Linear.Calculus
-- #check Diff_const_eq_zero
open Sequence Linear Calculus


variable [Ring R]

@[grind]
theorem D_comm (d) : D^[d]'R ∘ₗ D  = D ∘ₗ D^[d]'_ := by
  ext; apply Function.Commute.iterate_self

@[grind]
theorem Diff_rec (f : Sequence R) : D^[d + 1]'R f n  = (D^[d]'_ f (n + 1)) - (D^[d]'_ f n) := by
  change ((D.toFun'^[d] ∘ D.toFun') f) n  = (D.toFun'^[d] f) (n + 1) - (D.toFun'^[d] f) n
  have  : D.toFun'^[d] ∘ D.toFun' = D.toFun' ∘ (D.toFun'^[d] : Sequence R → Sequence R) := by
    ext; apply Function.Commute.iterate_self

  rw [this, Function.comp_apply, D.toFun']



@[grind]
theorem Diff_rec' : D^[d]'R f (n + 1) = (D^[d + 1]'_ f n) + (D^[d]'_ f n) := by grind


@[simp]
theorem D_zero : D 0 = (0 : Sequence R) := by simp

@[simp]
theorem D_zero_zero' {n : ℕ} : D 0 n = (0:R) := by simp only [D_zero]; rfl


----------------------------------------------------------------


@[simp]
theorem I_zero_zero (f : Sequence R) : I f 0 = 0 := rfl



@[simp]
theorem I_zero : I 0 = (0: Sequence R) := by simp

@[simp]
theorem I_zero_zero' {k : ℕ} : I 0 k = (0:R) := by simp; rfl






section I_D_Id
@[simp]
theorem I_D_Id_apply {f : Sequence R} : D (I f) = f := by
  simp [D, I]; funext; simp [D.toFun', I.toFun']

@[simp]
theorem I_D_Id_fun_comp : D ∘ I = @id (Sequence R) := by
  unfold Function.comp
  simp; rfl

@[simp]
theorem I_D_Id_linear_comp : D ∘ₗ I = LinearMap.id (R := R) (M := Sequence R) := by
  unfold LinearMap.comp LinearMap.id Function.comp
  simp; rfl

@[simp]
theorem I_D_Id_const_apply {c : R} {f : Sequence R} : D (c + I f) = f := by simp


@[simp]
theorem I_D_Id_const {c : R} : D ∘ ((c : Sequence R) + I ·) = id := by funext; simp

end I_D_Id



section D_I_Id
theorem D_I_Id' {f : Sequence R} : ((f 0 + I ·) ∘ D) f = f := by
  simp [I, D, Function.comp]
  funext n
  show f 0 + (I.toFun' (D.toFun' f) n)  = f n

  fun_induction I.toFun' (D.toFun' f) n generalizing f with
  | case1 => simp [I.toFun']
  | case2 n ih =>
    simp [I.toFun', D.toFun']
    simp at ih
    grind




theorem D_I_Id_fun_comp  : (fun (f: Sequence R) ↦ ((f 0 + I ·) ∘ D) f) = id := by simp only [D_I_Id']; rfl
theorem D_I_Id'''   {f : Sequence R} :  (f 0 + I ·) (D  f) = f := congrFun D_I_Id_fun_comp  ..
end D_I_Id


end Linear.Calculus
-- end Linear.Calculus
-- #min_imports
