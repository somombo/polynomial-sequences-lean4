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

import PolynomialSequences.MathlibContrib
import PolynomialSequences.LinearDiscreteCalculus


local infixr:80  " ᶜ "   => Nat.choose

variable [Ring R]

-- A sequence f is a polynomial sequence if it's nth term can be written a polynomial
-- in our context all coeffiecients will come from a ring (with unity but not necesarily commutative)
abbrev Sequence.Polynom (f : Sequence R) (d : ℕ) := ∃ (c : Fin (d + 1) → R),
  f = fun n ↦ ∑ k : Fin (d + 1), (c k) * nᶜk

namespace Sequence.Polynom
open Sequence Linear Calculus



theorem monomial_Intg {d : ℕ} : I (fun n ↦ nᶜd : Sequence R) = fun n ↦ ↑(nᶜ(d + 1)) := by
  simp [I]
  funext n
  fun_induction I.toFun' (fun n ↦ nᶜd : Sequence R) n with
  | case1 => simp
  | case2 n ih =>
    simp [Nat.choose]
    suffices I.toFun' (fun n ↦ nᶜd : Sequence R) n + nᶜd = nᶜ(d + 1) + nᶜd by grind
    grind

theorem monomial_Diff_base (k : ℕ) : D (fun n ↦ (nᶜk : R)) = (fun n ↦ 0ᶜ(1 - k) * nᶜ(k - 1): Sequence R) := by
  cases k with
  | zero => simp; rfl
  | succ => funext; simp [D, Nat.choose, D.toFun']

theorem monomial_Diff (k : ℕ) : D^[d]'R (fun n ↦ nᶜk) = (fun n ↦ 0ᶜ(d - k) * nᶜ(k - d) : Sequence R) := by
  induction d with
  | zero => simp [D, Linear.iterate]
  | succ e ih =>
    let rhs : Sequence R := fun n ↦ 0ᶜ(e + 1 - k) * nᶜ(k - (e + 1))
    change (D^[_]'R ∘ₗ D) (·ᶜk) = rhs
    suffices D (D^[_]'R (·ᶜk)) = rhs by simpa only [D_comm]

    simp only [ih, smul'', monomial_Diff_base]
    funext n
    suffices ((0ᶜ(e - k) * 0ᶜ(1 - (k - e))) * nᶜ(k - (e + 1)) : R) = 0ᶜ(e + 1 - k) * nᶜ(k - (e + 1)) by
      simp only [rhs]
      rw [←this, (by omega : k - (e + 1) = k - e - 1), mul_assoc]

    suffices 0ᶜ((e + 1) - k) = 0ᶜ(e - k) *  0ᶜ(1 - (k - e)) by rw [this, Nat.cast_mul]
    rw [mul_comm]
    if k > e then
      grind [Nat.choose_zero_right, Nat.sub_eq_zero_of_le]
    else
      grind [Nat.choose_eq_zero_of_lt, zero_mul]


-- FIXME: probably dont need this theorem.
theorem monomial_Diff_d_of_k_le_d {d : ℕ} (k : Fin (d + 1)) : D^[d]'R (fun n ↦ nᶜk) = (0ᶜ(d - k) : R) := by
  have : k ≤ d := by omega
  suffices D^[d]'R (fun n ↦ nᶜk) = (fun n ↦ 0ᶜ(d - k) * nᶜ(k - d) : Sequence R) by simp_all
  apply monomial_Diff

section monomial_Diff_variations

theorem monomial_Diff_e_of_k {d : ℕ} (e : Fin (d + 1)) (k : Fin (d + 1)) :
    D^[e]'R (fun n ↦ nᶜk) = (fun n ↦ (0ᶜ(e - k) : R) * nᶜ(k - e)) := by apply monomial_Diff

theorem monomial_Diff_e_of_d_sub_k {d : ℕ} (e : Fin (d + 1)) (k : Fin (d + 1)) :
    D^[e]'R (fun n ↦ nᶜ(d - k)) = (fun n ↦ 0ᶜ(k - (d - e)) * nᶜ((d - e) - k) : Sequence R) := by
  suffices D^[e]'R (fun n ↦ nᶜ(d - k)) = (fun n ↦ 0ᶜ(e - (d - k)) * nᶜ((d - k) - e) : Sequence R) by
    rwa [(by omega : (d - e) - k = (d - k) - e), (by omega : (k - (d - e)) = (e - (d - k)) )]

  exact monomial_Diff_e_of_k e ⟨d - k, by omega⟩

theorem monomial_Diff_d_sub_e_of_k {d : ℕ} (e : Fin (d + 1)) (k : Fin (d + 1)) :
    D^[d - e]'R (fun n ↦ nᶜk) = (fun n ↦ 0ᶜ((d - e) - k) * nᶜ(k - (d - e)) : Sequence R) := by
  exact monomial_Diff_e_of_k ⟨d - e, by omega⟩ k

theorem monomial_Diff_d_sub_e_of_d_sub_k {d : ℕ} (e : Fin (d + 1)) (k : Fin (d + 1)) :
    D^[d - e]'R (fun n ↦ nᶜ(d - k)) = (fun n ↦ 0ᶜ(k - e) * nᶜ(e - k) : Sequence R) := by
  suffices D^[d - e]'R (fun n ↦ nᶜ(d - k)) = (fun n ↦ 0ᶜ((d - e) - (d - k)) * nᶜ((d - k) - (d - e)) : Sequence R) by
    rwa [(by omega : (d - k) - (d - e) = e - k), (by omega : (d - e) - (d - k) = k - e)] at this
  exact monomial_Diff_e_of_k (d := d) ⟨d - e, by omega⟩ ⟨d - k, by omega⟩
end monomial_Diff_variations
-- end monomial_Diff_variations






theorem fundem1_succ.aux (f : Sequence R) {cs : List R} (hd : cs.length = d + 1)
    (h : D f = fun n ↦ ∑ k : Fin (d + 1), cs[k]'(by simp [hd]) * nᶜk)
    : f = fun n ↦ ∑ k : Fin (d + 2), (f 0 :: cs)[k]'(by simp [hd]) * nᶜk := by

  suffices f = fun n ↦ f 0 + ∑ k : Fin (d + 1), cs[k]'(by simp [hd]) * nᶜ(k + 1) by
    simp [Fin.sum_univ_succ] at this
    simpa [Fin.sum_univ_succ]

  suffices f = ↑(f 0) + (show Sequence R from fun n ↦ ∑ x : Fin (d + 1), cs[x]'(by simp [hd]) * (nᶜ(x + 1))) from this
  simp

  have _ : (fun n ↦ ∑ k : Fin (d + 1), cs[k]'(by simp [hd]) * nᶜk)
    = (∑ k : Fin (d + 1), fun n ↦ cs[k]'(by simp [hd]) * nᶜk) := by simp [fun_sum_order]
  have _ : (∑ k : Fin (d + 1), fun n ↦ cs[k]'(by simp [hd]) * (nᶜ(k + 1)))
    = (fun n ↦ ∑ k : Fin (d + 1), cs[k]'(by simp [hd]) * (nᶜ(k + 1))) := by simp [fun_sum_order]


  replace h : ((f 0 + I ·) ∘ D) f = (f 0 + I ·) (fun n ↦ ∑ k : Fin (d + 1), cs[k]'(by simp [hd]) * nᶜk) := congrArg (f 0 + I ·) h
  simp only [D_I_Id'] at h
  replace h : f = (f 0 + I ·) (∑ k : Fin (d + 1), fun n ↦ cs[k]'(by simp [hd]) * nᶜk) := by grind
  simp only [Sum_n] at h
  simp only [smul''] at h
  simp only [monomial_Intg] at h

  simp [fun_sum_order ..] at h
  change f = f 0 + fun n ↦ ∑ k : Fin (d + 1), cs[k] * nᶜ(k + 1) at h
  change f = f 0 + fun n ↦ ∑ k : Fin (d + 1), cs[k] * nᶜ(k + 1)
  grind

/- The following fundemental theorems are equvalent -/
theorem fundem1 (f : Sequence R) : (D^[d] f).Polynom 0 → f.Polynom d  := by
  have fundem1_succ (f : Sequence R) (d : ℕ) (h : (D f).Polynom d) : f.Polynom (d + 1) := by
    replace ⟨c_, h⟩ := h

    let cs := (List.ofFn c_)
    have hd : cs.length = d + 1 := by simp [cs]
    have : ∀ {k}, cs[k]'(by simp [hd]) = c_ k := by intro; apply List.getElem_ofFn

    simp [←this] at h
    constructor; apply @fundem1_succ.aux _ _ d f cs (by grind) h

  intro h
  induction d generalizing f with
  | zero => simpa only
  | succ _ ih => simp [fundem1_succ _ _ (ih (D f) h)]

theorem fundem2 (f : Sequence R) : f.Polynom d → (D^[d] f).Polynom 0  := by
  show f.Polynom d → (D^[d]'_ f).Polynom 0
  intro h
  replace ⟨c_, h⟩ := h

  let c := fun (_ : Fin 1) ↦ c_ ⟨d, by grind⟩

  suffices D^[d]'_ f = fun n ↦ ∑ k : Fin 1, (c k) * nᶜk from ⟨c, this⟩

  simp
  change D^[d]'_ f = fun _ ↦ c_ ⟨d, by grind⟩

  replace h := congrArg (D^[d]'_) h

  simp only [←fun_sum_order] at h
  have := Sum_n (f := fun k n ↦ (c_ k) * ↑(n ᶜ k))
  simp only [this] at h
  simp only [smul''] at h
  simp only [monomial_Diff_d_of_k_le_d] at h

  simp only [fun_sum_order ..] at h
  rw [Fin.sum_mul_choose_zero] at h

  assumption


theorem fundem3 {f : Sequence R} (h : f.Polynom d) :
    f = fun n ↦ ∑ k : Fin (d + 1), (D^[k] f 0) * nᶜk := by

  replace ⟨c, h⟩ := h

  suffices ∀ e, c e = (D^[e] f 0) by
    let p : Sequence R → Prop := (f = ·)
    change p (∑ k : Fin (d + 1), (D^[k] f 0) * ·ᶜk)
    replace : ∀ k, (c k * ·ᶜk) = (D^[k] f 0 * ·ᶜk) := by intros; funext; grind
    replace h : p (∑ k, (c k * ·ᶜk)) := by simpa [p, fun_sum_order (R := R)]

    simp [←fun_sum_order]
    have hsum_subst  {a b : Fin (d + 1) → Sequence R}
        (heq : ∀ k, b k = a k) : p (∑ k, b k) → p (∑ k, a k) := by grind
    apply hsum_subst <;> assumption
    -- (b := fun k n ↦ c k * nᶜk) (a := fun k n ↦ D^[k] f 0 * nᶜk) this h

  intro e

  replace h := congrArg (D^[e]'R) h


  simp only [←fun_sum_order (R := R)] at h
  have := Sum_n (R := R) (f := fun k n ↦ (c k) * ↑(n ᶜ k))
  simp only [this] at h
  clear this
  simp only [smul''] at h
  simp only [monomial_Diff_e_of_k] at h

  simp only [fun_sum_order (R := R)] at h
  replace h : D^[e] f 0 = _ := congrFun h 0


  simp [h]
  change c e = ∑ k : Fin (d + 1), (c k) * (0ᶜ(e - k) * 0ᶜ(k - e))
  suffices c e = ∑ k : Fin (d + 1), (c k) * 0ᶜ(e - k) * 0ᶜ(k - e) by grind [mul_assoc]

  simp [Fin.sum_mul_choose_zero_above]


-- Example of concrete construction of polynomial sequence
def Polyseq_mk (c₀ : R) : List R → Sequence R
| [], _ | _ , 0  => c₀
| c₁ :: cs, n + 1 => Polyseq_mk c₀ (c₁::cs) n + Polyseq_mk c₁ cs n

-- Proof that constucting a sequence this way, is indeed has a polynomial nth term with desidred degree
@[simp]
theorem Polyseq_mk_soln {c₀ : R} {cs : List R} : (Polyseq_mk c₀ cs).Polynom cs.length
:= by

  generalize hd : cs.length = d
  generalize hcc : ((c₀::cs)[·]'(by simp [hd]) : Fin (d + 1) → R ) = c

  suffices Polyseq_mk c₀ cs = fun n ↦ ∑ k : Fin (d + 1), c k * nᶜk from ⟨c, this⟩
  funext n

  fun_induction Polyseq_mk c₀ cs n generalizing d with
  | case1 n c₀ =>

    replace hd : d + 1 = 1 := by grind
    let f : Fin (d + 1) → R := fun k ↦ c k * ↑(n ᶜ ↑k)
    rw [←Fin.sum_congr' f hd.symm]
    replace hcc := congrFun hcc 0
    simpa [f]

  | case2 c₀ cs hne =>

    clear hne
    replace hcc := congrFun hcc 0
    simp at hcc

    induction d generalizing cs  with
    | zero => simp_all
    | succ d' ihd =>

      replace ihd := ihd cs.tail (by simp_all [List.length_tail]) (fun (k : Fin (d' + 1)) ↦ c k.castSucc)

      subst hcc
      simp at ihd
      rw [ihd]
      conv =>
        rhs
        rw [Fin.sum_univ_castSucc]
        simp

  | case3 c₀ c₁ cs n ih2 ih1 =>
    simp at hd
    have hd' : cs.length = d - 1 := by omega


    have h1 : d - 1 + 1  = d  := by omega
    simp_all only [List.length_cons, Fin.getElem_fin, ←hcc]


    let f : Fin d → R := fun k ↦ (c₁ :: cs)[k]'(by simp [hd]) * nᶜk
    have := Fin.sum_congr' f h1
    simp [f] at this
    rw [this]


    simp [Fin.sum_univ_succ, add_assoc]
    rw [add_comm]

    let c := fun (k : Fin d) ↦ (c₁ :: cs)[k.1]'(by simp [hd])

    calc (∑ k : Fin d, c k * nᶜk) + (∑ k : Fin d, c k * nᶜ(k + 1))
      _ = ∑ k : Fin d, ((c k * nᶜk) + (c k * nᶜ(k + 1)))  := by symm; apply Multiset.sum_map_add
      _ = ∑ k : Fin d, c k * ((nᶜk) + (nᶜ(k + 1))) := by simp [mul_add]
      _ = ∑ k : Fin d, c k * (n + 1)ᶜ(k + 1) := by simp [Nat.choose]


def xs := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

#eval Polyseq_mk (0:ℤ) [0, 0] <$> xs
#eval Polyseq_mk (11:ℤ) [] <$> xs
#eval Polyseq_mk (3:ℤ) [2] <$> xs
#eval Polyseq_mk (12:ℤ) [-1, -1] <$> xs
#eval Polyseq_mk (1:ℤ) [1, 3, 2] <$> xs
