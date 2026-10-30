-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsShort.lean: the parts' steps at the short sumcheck: knowledge soundness, form
and lists.

Statements and proofs. What Cb/Pv/KeyLookup/PartsK.lean, PartsForm.lean and PartsLam.lean state at
the sumcheck of Cb/Ld/LdPsc.lean is stated here at SK₀ (Cb/Pv/KeyLookup/Short0.lean), the format in
which the
constant of a round's polynomial is not sent. No honest side is named.

Main names:
  partsK_short: what is asked of the letter (D.LtK) holds at SK₀, for every D and k: no premise
    (from
    parts_ok, by SK₀_ourK).
  partsXK_short: under 1 ≤ A.m alone, (A.partsXK wP cP (SK₀ E Ex)).Know (A.jt R0 msg Mu A.Tied)
    (A.jt R0 msg Mu A.Roots).
  partsXK_form_short: Bks.FormX (A.partsXK wP cP (SK₀ E Ex)): no premise.
  partsK_lists: for every letter SK whose sumchecks at the steps have the lists [1, 2, 0] and
    [q, q - 1, 1], D.afterK SK b k has b's lists and then partsErrs k, partsVals q k.
  partsXK_errs_short, partsXK_vals_short: the lists at SK₀ are the columns c and n of lamParts
    (Cb/Pv/KeyLookup/Lam.lean): no premise.
  parts_eq0: at every step's sumcheck the weights of each variable sum to 1 (TWhole.Eq0): there is
    the further variable alone, whose "sum" is the value at 0. No premise.
  parts_shape_short: a step's rounds at SK₀ are pRound0 E, sRound (pDummy E 2), pRoundV E _: one
    scalar, two, two.

Limits: that the verifier rejects nothing is `partsXK_total_short` (Cb/Pv/KeyLookup/PartsRun.lean).

-/
import Cb.Pv.KeyLookup.Short0
import Cb.Pv.KeyLookup.PartsForm
import Cb.Pv.KeyLookup.PartsLam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.LdLkp.Kn Johnson.L5.Layers

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (D : PartsP E)

theorem partsK_short (M Wp Kc : Type) (msg : M → D.J → E) (k : ℕ) :
    D.LtK (SK₀ E Ex) Wp Kc msg k := fun l _ =>
  SK₀_ourK M Wp Kc (D.lv l).T (D.msgAt M msg l) (parts_ok D l).1 (parts_ok D l).2.2.1
    (parts_ok D l).2.2.2 (parts_ok D l).2.1

theorem partsK_form_short (k : ℕ) : D.FormK (SK₀ E Ex) k := fun l _ =>
  ⟨SK₀_passes Ex (D.lv l).T.par, SK₀_copies Ex (D.lv l).T.par⟩

/-- Every variable's weights sum to 1: there is Y alone. -/
theorem parts_eq0 (l : ℕ) : TWhole.Eq0 (D.lv l).T.par :=
  TWhole.our_eq0 (D.lv l).T fun st v hv => by
    have h : (D.lv l).T.vars st = [] := by
      cases l <;> rfl
    rw [h] at hv
    exact absurd hv List.not_mem_nil

/-- The lists of the chain, for every letter whose sumchecks have a step's lists. -/
theorem partsK_lists (SK : PscLtK E Ex) {X : Type} (b : BkK X (E × (D.lv 0).T.St) Ex)
    (e v : List ℕ) (hb : b.e.toList = e ∧ b.R.shape.chalList = v) :
    ∀ k, (∀ l < k, (SK.full (D.lv l).T.par).e.toList = [1, 2, 0] ∧
        (SK.full (D.lv l).T.par).R.shape.chalList = [Fintype.card E, Fintype.card E - 1, 1]) →
      (D.afterK SK b k).e.toList = e ++ partsErrs k ∧
        (D.afterK SK b k).R.shape.chalList = v ++ partsVals (Fintype.card E) k
  | 0, _ => by
    have e0 : partsErrs 0 = [] := rfl
    have v0 : partsVals (Fintype.card E) 0 = [] := rfl
    rw [e0, v0, List.append_nil, List.append_nil]
    exact hb
  | k + 1, h => by
    obtain ⟨h1, h2⟩ := partsK_lists SK b e v hb k fun l hl => h l (Nat.lt_succ_of_lt hl)
    obtain ⟨s1, s2⟩ := h k (Nat.lt_succ_self k)
    rw [partsErrs_succ, partsVals_succ, ← List.append_assoc, ← List.append_assoc]
    constructor
    · exact (Err.toList_app (D.afterK SK b k).e (D.stepK SK k).e).trans (by
        rw [h1]
        exact congrArg _ s1)
    · exact (Shape.chalList_append (D.afterK SK b k).R.shape (D.stepK SK k).R.shape).trans (by
        rw [h2]
        exact congrArg _ s2)

theorem parts_ll_short (l : ℕ) :
    ((SK₀ E Ex).full (D.lv l).T.par).e.toList = [1, 2, 0] ∧
      ((SK₀ E Ex).full (D.lv l).T.par).R.shape.chalList =
        [Fintype.card E, Fintype.card E - 1, 1] := by
  cases l with
  | zero => exact SK₀_ll Ex (D.lv 0).T 0 2 rfl
  | succ l => exact SK₀_ll Ex (D.lv (l + 1)).T 0 2 rfl

/-- A step's rounds at SK₀: one scalar; two (Y's constant is not sent); two values. -/
theorem parts_shape_short (l : ℕ) :
    (D.stepK (SK₀ E Ex) l).R.shape =
      [pRound0 E, sRound (pDummy E 2), pRoundV E (D.lv l).T.A] := by
  cases l <;> rfl

end

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (A : Dat E)
variable (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)

/-- Stretch 3 at the short sumcheck, by road (k): under 1 ≤ m alone. -/
theorem partsXK_short (M Wp Kc : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E)
    (Mu : A.St → (A.J → E) → Prop) (hm : 1 ≤ A.m) :
    (A.partsXK wP cP (SK₀ E Ex)).Know (A.jt R0 msg Mu A.Tied) (A.jt R0 msg Mu A.Roots) :=
  partsXK_know A wP cP _ M Wp Kc R0 msg Mu hm (partsK_short (A.partsD wP cP) M Wp Kc msg _)

theorem partsXK_form_short : Bks.FormX (A.partsXK wP cP (SK₀ E Ex)) :=
  partsXK_form A wP cP _ (partsK_form_short (A.partsD wP cP) _)

theorem partsXK_lists_short :
    (A.partsXK wP cP (SK₀ E Ex)).e.toList = partsErrs (A.m - 1) ∧
      (A.partsXK wP cP (SK₀ E Ex)).R.shape.chalList = partsVals (Fintype.card E) (A.m - 1) :=
  partsK_lists (A.partsD wP cP) (SK₀ E Ex) (mapK Ex (A.partsIn wP cP)) [] [] ⟨rfl, rfl⟩ (A.m - 1)
    fun l _ => parts_ll_short (A.partsD wP cP) l

theorem partsXK_errs_short :
    (A.partsXK wP cP (SK₀ E Ex)).e.toList = (lamParts (Fintype.card E) A.toPub).map (·.c) := by
  rw [lamParts_is, lamSteps_c]
  exact (partsXK_lists_short A wP cP).1

theorem partsXK_vals_short :
    (A.partsXK wP cP (SK₀ E Ex)).R.shape.chalList =
      (lamParts (Fintype.card E) A.toPub).map (·.n) := by
  rw [lamParts_is, lamSteps_n]
  exact (partsXK_lists_short A wP cP).2

end
end Lk6

#print axioms Lk6.partsK_short
#print axioms Lk6.partsK_form_short
#print axioms Lk6.parts_eq0
#print axioms Lk6.partsK_lists
#print axioms Lk6.parts_ll_short
#print axioms Lk6.parts_shape_short
#print axioms Lk6.partsXK_short
#print axioms Lk6.partsXK_form_short
#print axioms Lk6.partsXK_errs_short
#print axioms Lk6.partsXK_vals_short
