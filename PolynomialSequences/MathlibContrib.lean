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

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.Defs

/-
Potential Contributions to Mathlib, if these theorems do not already exist
-/
theorem Fin.sum_univ_rev [AddCommMonoid M] (d : ℕ) (c : Fin (d + 1) → M) :
    ∑ k : Fin (d + 1), (c k) = ∑ k : Fin (d + 1), (c ⟨d - k, by omega⟩)  := by
  induction d with
  | zero => simp
  | succ _ ih =>
    replace ih := ih (c ⟨·, by omega⟩)
    conv => lhs; rw [Fin.sum_univ_castSucc]
    conv => rhs; rw [Fin.sum_univ_succ]
    simp [Fin.last]
    rw [add_comm]
    solve_by_elim

theorem IsLinearMap_iff_IsLinear (K : Type u) [Semiring K] {V : Type v} {W : Type w}
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W] (R : V → W)
    : IsLinearMap K R ↔ ∀ (f g : V) (a b : K), R (a • f + b • g) = (a • R f) + (b • R g) where
  mp h := by
    have _ := h.map_add
    have _ := h.map_smul
    grind
  mpr h := by
    constructor
    · intro f g
      have _ := h f g 1 1
      simp_all
    · intro a f
      have _ := h f 0 a 0
      simp_all

private theorem Nat.forall_le_iff_forall_sub {d : Nat} (p : Nat → Prop): (∀ (k : Nat) (_ : k < (d + 1)), p k ) ↔ ∀ (k : Nat), p (d - k) := by
  constructor <;> grind [Nat.sub_sub_self]


-- TODO: clean this poof up. can be shorter and simpler.
open Nat in
@[simp]
theorem Fin.sum_mul_choose_zero_above [Semiring R] (d : ℕ)  (c : Fin (d + 1) → R) : ∀ (e : Fin (d + 1)),
    ∑ k : Fin (d + 1), c k * choose 0 (e - k) * choose 0 (k - e) = c e  := by
  suffices ∀ (e : Fin (d + 1)), ∑ k : Fin (d + 1), c k * (choose 0 (e - k) * choose 0 (k - e)) = c e by grind [mul_assoc]
  suffices ∀ (e : Fin (d + 1)), ∀ (k : Fin _), (choose 0 (e - k) * choose 0 (k - e) : R) = if k = e then 1 else 0 by simp [this]
  suffices ∀ (e : ℕ), ∀ (k : ℕ), (choose 0 (e - k) * choose 0 (k - e) : R) = if k = e then 1 else 0 by
    intro e k
    rw [this e.1 k.1]
    if heq : k = e then
      simp_all
    else
      have : k.1 ≠ e.1 := by omega
      simp_all

  intro e k
  if h_eq : k = e then
    simp [h_eq]
  else
    if h_ge : k > e then
      replace h_ge : 0 < k - e := by omega
      rw [←Nat.exists_add_one_eq] at h_ge
      have ⟨m, hx⟩ := h_ge
      rw [←hx, m.choose_zero_succ]
      simp_all
    else
      have h_lt : k < e := by omega
      replace h_lt : 0 < e - k := by omega
      rw [←Nat.exists_add_one_eq] at h_lt
      have ⟨m, hx⟩ := h_lt
      rw [←hx, m.choose_zero_succ]
      simp_all


@[simp]
theorem Fin.sum_mul_choose_zero [Semiring R] (d : ℕ) (c : Fin (d + 1) → R) :
    ∑ k : Fin (d + 1), (c k) * (Nat.choose 0 (d - k)) = c ⟨d, by simp⟩  := by

  suffices ∑ k: Fin (d + 1), c k * (Nat.choose 0 (d - k)) =
    c ⟨d, by simp⟩ * (Nat.choose 0 (d - d)) by
      simp at this; assumption

  apply Finset.sum_eq_single_of_mem (ι := Fin _) ⟨d, ?_⟩

  all_goals simp
  intro ⟨k', hb⟩ _
  suffices Nat.choose 0  (d - k') = 0 by simp_all
  have := (d - k' - 1).choose_zero_succ
  grind



-- #min_imports
