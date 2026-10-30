-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevSimA.lean: the sumcheck over the field (`PscF`) on k
equality-weighted variables and the further variable Y, against the closed forms of LevRunA.lean:
the running claim, the weights of the own mask entries, the point by variable. `PscF` is our text of
the program's sumcheck, over the field. That the program's run, read in the field, is `PscF` is not
shown here.

Main names:
  `pr` a flat round as the pair (the scalars sent, the first element drawn).
  `poly3` a round's polynomial completed under an equality weight, at the draw.
  `claim_fin` `PscF.claimAfter` along k equality weights and Y is `Lev.finC`.
  `wts`, `walk_eq` `PscF.hidingWalk` along these variables: two powers of the draw a round, in Y's
    round 1 and two powers; the product of the polynomials psi is 1.
  `wvF`, `wcF` the places of a sumcheck's own mask entries, from the list of fresh entries in the
    order in which the program takes them.
  `rd_wts` the fresh entries zipped with these weights, read by `rdMF`, are `Lev.rowF` at these
    places.
  `byVar_ofFn` `byVarF` under the list of an order σ: coordinate t is the draw of round σ⁻¹ t.
Limits: the rounds are asked to have two scalars each and to be enough, the fresh entries to be
enough. Nothing on the program's blocks.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.Course
import Cb.Pv.KeyLookup.LevRunD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim

/-- In a list without repeats zipped with another: the member's partner is found under it. -/
theorem lookup_zip {α : Type} : ∀ (l : List ℕ) (r : List α) (j : ℕ) (hj : j < l.length) (hr : j <
    r.length),
    l.Nodup → (l.zip r).lookup l[j] = some r[j]
  | [], _, _, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | _ :: _, [], _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | a :: l, b :: r, 0, _, _, _ => by
    show ((a, b) :: l.zip r).lookup a = some b
    exact List.lookup_cons_self
  | a :: l, b :: r, j + 1, hj, hr, hn => by
    have hj' : j < l.length := Nat.lt_of_succ_lt_succ hj
    have hr' : j < r.length := Nat.lt_of_succ_lt_succ hr
    have hne : (l[j] == a) = false := by
      have : l[j] ≠ a := fun e => (List.nodup_cons.1 hn).1 (e ▸ List.getElem_mem hj')
      simpa using this
    show ((a, b) :: l.zip r).lookup l[j] = some r[j]
    rw [List.lookup_cons, hne]
    exact lookup_zip l r j hj' hr' (List.nodup_cons.1 hn).2

open OnBytes OnBytes.Slice Flat Lev

/-- a flat round as the sumcheck over the field hears it -/
def pr (r : RV GE) : List GE × GE := (r.1, r.2.headD 0)

/-- k equality weights at z, then Y -/
def wsOf {k : ℕ} (z : Fin k → GE) : List PscF.Weight :=
  (List.ofFn z).map (fun a => PscF.Weight.equality a 3) ++ [PscF.Weight.atZero 3]

theorem wsOf_zero (z : Fin 0 → GE) : wsOf z = [PscF.Weight.atZero 3] := by
  unfold wsOf
  rw [List.ofFn_zero]
  rfl

theorem wsOf_succ {k : ℕ} (z : Fin (k + 1) → GE) :
    wsOf z = PscF.Weight.equality (z 0) 3 :: wsOf fun i => z i.succ := by
  unfold wsOf
  rw [List.ofFn_succ]
  rfl

theorem two_of_len : ∀ q : List GE, q.length = 2 → q = [q.getD 0 0, q.getD 1 0]
  | [_, _], _ => rfl

/-- A round's polynomial under an equality weight, at the draw. -/
theorem poly3 (z R g : GE) (q : List GE) (h : q.length = 2) :
    PscF.polyAt ((PscF.Weight.equality z 3).complete q R) g =
      R - z * (q.getD 0 0 + q.getD 1 0) + q.getD 0 0 * g + q.getD 1 0 * g ^ 2 := by
  rw [complete_eq z 3 q R (by omega)]
  have e := two_of_len q h
  generalize q.getD 0 0 = a at e ⊢
  generalize q.getD 1 0 = b at e ⊢
  subst e
  simp only [PscF.polyAt_cons, PscF.polyAt_nil, List.sum_cons, List.sum_nil]
  ring

/-- The running claim. -/
theorem claim_fin : ∀ (k : ℕ) (z : Fin k → GE) (R : GE) (g : List (RV GE)),
    (∀ j ≤ k, (g.getD j ([], [])).1.length = 2) → k + 1 ≤ g.length →
    PscF.claimAfter (wsOf z) ((g.take (k + 1)).map pr) R = finC k z R g
  | 0, _, _, [], _, hl => absurd hl (by simp)
  | 0, z, R, v :: g, h2, _ => by
    have hv : v.1.length = 2 := h2 0 (Nat.le_refl 0)
    rw [wsOf_zero]
    show PscF.polyAt ((PscF.Weight.equality 0 3).complete v.1 R) (v.2.headD 0) = _
    rw [poly3 0 R _ v.1 hv]
    show _ = R + v.1.getD 0 0 * v.2.headD 0 + v.1.getD 1 0 * v.2.headD 0 ^ 2
    ring
  | _ + 1, _, _, [], _, hl => absurd hl (by simp)
  | k + 1, z, R, v :: g, h2, hl => by
    have hv : v.1.length = 2 := h2 0 (Nat.zero_le _)
    rw [wsOf_succ]
    show PscF.claimAfter (wsOf fun i => z i.succ) ((g.take (k + 1)).map pr)
      (PscF.polyAt ((PscF.Weight.equality (z 0) 3).complete v.1 R) (v.2.headD 0)) = _
    rw [poly3 (z 0) R _ v.1 hv, claim_fin k (fun i => z i.succ) _ g
      (fun j hj => h2 (j + 1) (Nat.succ_le_succ hj)) (Nat.le_of_succ_le_succ hl)]
    rfl

/-- the weights of the own mask entries, in the order in which the program takes them -/
def wts : ℕ → List (RV GE) → List GE
  | 0, g => PscF.powers 1 (chC g 0) 3
  | k + 1, g => PscF.powers (chC g 0) (chC g 0) 2 ++ wts k g.tail

theorem wts_ne : ∀ (k : ℕ) (g : List (RV GE)), wts k g ≠ []
  | 0, g => by
    show PscF.powers 1 (chC g 0) (2 + 1) ≠ []
    rw [PscF.powers_succ]
    exact List.cons_ne_nil _ _
  | k + 1, g => by
    show PscF.powers (chC g 0) (chC g 0) (1 + 1) ++ wts k g.tail ≠ []
    rw [PscF.powers_succ]
    exact List.cons_ne_nil _ _

/-- The walk along k equality weights and Y. -/
theorem walk_eq : ∀ (k : ℕ) (z : Fin k → GE) (g : List (RV GE)), k + 1 ≤ g.length →
    PscF.hidingWalk ((wsOf z).zip (((g.take (k + 1)).map pr).map (·.2))) = (wts k g, 1)
  | 0, _, [], hl => absurd hl (by simp)
  | 0, z, v :: g, _ => by
    rw [wsOf_zero]
    show (PscF.powers 1 (v.2.headD 0) 3, PscF.polyAt [1] (v.2.headD 0)) = _
    refine Prod.ext rfl ?_
    show (0 : GE) * v.2.headD 0 + 1 = 1
    ring
  | _ + 1, _, [], hl => absurd hl (by simp)
  | k + 1, z, v :: g, hl => by
    have ih := walk_eq k (fun i => z i.succ) g (Nat.le_of_succ_le_succ hl)
    rw [wsOf_succ]
    show PscF.hidingWalk ((PscF.Weight.equality (z 0) 3, v.2.headD 0) ::
      (wsOf fun i => z i.succ).zip (((g.take (k + 1)).map pr).map (·.2))) = _
    generalize (wsOf fun i => z i.succ).zip (((g.take (k + 1)).map pr).map (·.2)) = rest at ih ⊢
    cases rest with
    | nil => exact absurd (congrArg Prod.fst ih).symm (wts_ne k g)
    | cons p l =>
      rw [walk_two, ih]
      refine Prod.ext ?_ ?_
      · show PscF.powers (1 * v.2.headD 0) (v.2.headD 0) 2 ++ wts k g = _
        rw [_root_.one_mul]
        rfl
      · show (1 : GE) * (0 * v.2.headD 0 + 1) = 1
        ring

variable {J : Type} [DecidableEq J] (sl : Slot → J)

/-- the place of the own mask entry for the power t + 1 in round r (from round k on: Y's); for the
constant: from the fresh entries in the order of the sumcheck over the field -/
def wvF : ℕ → List Slot → ℕ → Fin 2 → J
  | 0, fr, _, t => sl (fr.getD (1 + t.val) ⟨0, 0⟩)
  | _ + 1, fr, 0, t => sl (fr.getD t.val ⟨0, 0⟩)
  | k + 1, fr, r + 1, t => wvF k (fr.drop 2) r t
def wcF : ℕ → List Slot → J
  | 0, fr => sl (fr.getD 0 ⟨0, 0⟩)
  | k + 1, fr => wcF k (fr.drop 2)

theorem one_eq (i : J) (c : GE) : Parts.one i c = Lev.one i c := rfl

/-- The row's form on the own mask entries. -/
theorem rd_wts : ∀ (k : ℕ) (g : List (RV GE)) (fr : List Slot) (j : J), 2 * k + 3 ≤ fr.length →
    rdMF sl (fr.zip (wts k g)) j = rowF k (wvF sl k fr) (wcF sl k fr) (chC g) j
  | 0, g, s0 :: s1 :: s2 :: fr, j, _ => by
    show rdMF sl ((s0 :: s1 :: s2 :: fr).zip (PscF.powers 1 (chC g 0) (2 + 1))) j = _
    rw [PscF.powers_succ, PscF.powers_succ, PscF.powers_succ, PscF.powers_zero,
      List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons, List.zip_nil_right]
    show rdMF sl [(s0, 1), (s1, 1 * chC g 0), (s2, 1 * chC g 0 * chC g 0)] j =
      Lev.one (sl s1) (chC g 0) j + Lev.one (sl s2) (chC g 0 ^ 2) j + Lev.one (sl s0) 1 j
    rw [rdMF_cons, rdMF_cons, rdMF_cons, rdMF_nil, one_eq, one_eq, one_eq]
    have p2 : (1 : GE) * chC g 0 * chC g 0 = chC g 0 ^ 2 := by ring
    rw [p2, _root_.one_mul]
    ring
  | 0, _, [], _, h => absurd h (by simp)
  | 0, _, [_], _, h => absurd h (by simp)
  | 0, _, [_, _], _, h => absurd h (by simp)
  | k + 1, g, s0 :: s1 :: fr, j, h => by
    have ih := rd_wts k g.tail fr j (by simp only [List.length_cons] at h; omega)
    show rdMF sl ((s0 :: s1 :: fr).zip (PscF.powers (chC g 0) (chC g 0) (1 + 1) ++ wts k g.tail))
        j = _
    rw [PscF.powers_succ, PscF.powers_succ, PscF.powers_zero]
    show rdMF sl ((s0, chC g 0) :: (s1, chC g 0 * chC g 0) :: fr.zip (wts k g.tail)) j =
      Lev.one (sl s0) (chC g 0) j + Lev.one (sl s1) (chC g 0 ^ 2) j +
        rowF k (wvF sl k fr) (wcF sl k fr) (fun r => chC g (r + 1)) j
    have ec : (fun r => chC g (r + 1)) = chC g.tail := by
      funext r
      cases g <;> rfl
    have p2 : chC g 0 * chC g 0 = chC g 0 ^ 2 := by ring
    rw [rdMF_cons, rdMF_cons, ih, one_eq, one_eq, ec, p2, add_assoc]
  | _ + 1, _, [], _, h => absurd h (by simp)
  | _ + 1, _, [_], _, h => absurd h (by simp)

/-- The point by variable. -/
theorem byVar_ofFn (k : ℕ) (σ : Equiv.Perm (Fin k)) (br : List GE) (hb : br.length = k) :
    byVarF br (List.ofFn fun j => (σ j).val) =
      List.ofFn fun t : Fin k => br.getD (σ.symm t).val 0 := by
  have hn : (List.ofFn fun j => (σ j).val).Nodup :=
    List.nodup_ofFn.2 (Fin.val_injective.comp σ.injective)
  unfold byVarF
  refine List.ext_getElem (by simp [hb]) fun i h1 h2 => ?_
  have hi : i < k := by simpa using h2
  have hj : (σ.symm ⟨i, hi⟩).val < (List.ofFn fun j => (σ j).val).length := by
    rw [List.length_ofFn]
    exact (σ.symm ⟨i, hi⟩).2
  have hr : (σ.symm ⟨i, hi⟩).val < br.length := by
    rw [hb]
    exact (σ.symm ⟨i, hi⟩).2
  have ho : (List.ofFn fun j => (σ j).val)[(σ.symm ⟨i, hi⟩).val] = i := by
    rw [List.getElem_ofFn]
    show (σ (σ.symm ⟨i, hi⟩)).val = i
    rw [Equiv.apply_symm_apply]
  have hl := lookup_zip (List.ofFn fun j => (σ j).val) br (σ.symm ⟨i, hi⟩).val hj hr hn
  rw [ho] at hl
  rw [List.getElem_map, List.getElem_range, hl, List.getElem_ofFn, List.getD_eq_getElem _ _ hr]
  rfl

end Lk6.Mid

#print axioms Lk6.Mid.claim_fin
#print axioms Lk6.Mid.walk_eq
#print axioms Lk6.Mid.rd_wts
#print axioms Lk6.Mid.byVar_ofFn
