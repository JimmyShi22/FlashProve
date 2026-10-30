-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/KeyLookup/LamBelow.lean: round by round, the error of the lookup with parts is
covered by the error that a plan holds for that round.

OnBytes/Tie/Pv/KeyLookup/LamSpec.lean holds the lookup's own numbers, round by round, against the
planner's list of descriptions `lookupList`: the number of values of the verifier's message
(`lamS_vals`) and the count of bad values (`lamS_errs`, by the relation `BoundIs`).
OnBytes/Tie/Pv/PortKit.lean has the two relations in which the other kinds of block are held against
the planner: `Fits` (the count is the description's ratio, exactly) and `Covered` (the share of bad
values is at most the error that a plan holds). This file brings the lookup's numbers into these
two.
  `valuesOf_pv`, `bytesOf_pv`   the two files define the number of values and the bytes of a
                   description each for itself, by the same equations: they agree.
  `covered_of_fits`   a round that fits a description is covered under the scope `.once`, if its
                   verifier's message has a value and the planner's `close` has tested the
                   description (`RoundSpec.Good`): by `fits_covered` and `covered_zero`
                   (OnBytes/Tie/Pv/PortKit.lean, SealPort.lean).
  `spec_fits`, `spec_pos`   of each row of the lookup's list: count and number of values fit the
                   row's description; the number of values is not 0. `spec_fits` is `spec_err` with
                   `spec_vals`, and besides: the ratio's denominator is not 0.
  `lamS_fits`       round by round the lookup's errors and numbers of values fit `lookupList`.
  `lamS_covered`    round by round they are covered, if every description of `lookupList` is `Good`.
  `lam_good`, `lamS_covered_run`   where the planner's routine for the lookup ends well, from a
                   state with the scope `.once` and nothing open, every description of the list is
                   `Good` (the last clause of `Runs`, OnBytes/Params/PlanningLaws.lean, at
                   `lam_runs`); so there the lookup's errors are covered.
  `link_errs`, `link_vals`, `link_covered`   the link of a lookup in the library's house
                   (Cb/Pv/KeyLookup/House.lean) has the lookup's errors and rounds (by rfl); so the
                   same holds of the link.
Under: the lookup's public record is admissible; the setting's number of field elements is the
field's; `Good` where it is named.
What is not claimed: that the planner's routine ends well at any state; that a plan's rounds hold
against the target: that is the plan's own test; anything on the work of a round, or on the written
rounds. It imports files of both sides.

-/
import OnBytes.Tie.Pv.KeyLookup.LamSpec
import Cb.Pv.KeyLookup.House
import OnBytes.Tie.Pv.SealPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open OnBytes OnBytes.Params

theorem valuesOf_pv (q : ℕ) (y : RoundSpec) : Cb.Pv.valuesOf q y = valuesOf q y := by
  cases y <;> rfl

theorem bytesOf_pv (y : RoundSpec) : Cb.Pv.bytesOf y = bytesOf y := by
  cases y <;> rfl

/-- A round that fits is covered, if `close` has tested its description. -/
theorem covered_of_fits (s : Setting) (q : ℕ) (cn : ℕ × ℕ) (y : RoundSpec)
    (h : Cb.Pv.Fits q cn y) (hn : 0 < cn.2) (hg : y.Good s .once) :
    Cb.Pv.Covered s .once cn y := by
  cases y with
  | said n w e d b r a =>
      refine Cb.Pv.fits_covered s q cn n w e d b r a h hn ?_
      have h1 := hg.1
      simpa [RoundSpec.bound] using h1
  | silent n b a =>
      obtain ⟨c, m⟩ := cn
      obtain rfl : c = 0 := h.2
      exact Cb.Pv.covered_zero s .once m _
  | record a c e =>
      obtain ⟨c', m⟩ := cn
      obtain rfl : c' = 0 := h.2
      exact Cb.Pv.covered_zero s .once m _

/-- Count and number of values of a row fit the row's description. -/
theorem spec_fits (s : Setting) (S : Pub) (h : 1 < s.cardE) :
    ∀ r ∈ Lam s.cardE S, Cb.Pv.Fits s.cardE (r.c, r.n) (specOf s S r) := by
  have h0 : 0 < s.cardE := Nat.lt_of_succ_lt h
  have h1 : 0 < s.cardE - 1 := Nat.sub_pos_of_lt h
  intro r hr
  refine ⟨(valuesOf_pv _ _).trans (spec_vals s S _ r hr), ?_⟩
  revert r
  exact lam_forall s.cardE S _
    (show ∃ a b, 0 < b ∧ Bound.ratio (S.allKeys - 1) s.cardE = Bound.ratio a b ∧
        (S.allKeys - 1) * b = a * s.cardE
      from ⟨_, _, h0, rfl, rfl⟩)
    (show ∃ a b, 0 < b ∧ fieldError s 1 = Bound.ratio a b ∧ 1 * b = a * s.cardE
      from ⟨1, s.cardE, h0, rfl, rfl⟩)
    (fun g => show ∃ a b, 0 < b ∧ fieldError s (g - 1) = Bound.ratio a b ∧
        (g - 1) * b = a * s.cardE
      from ⟨g - 1, s.cardE, h0, rfl, rfl⟩)
    (fun dY => show ∃ a b, 0 < b ∧ fieldErrorNonzero s dY = Bound.ratio a b ∧
        dY * b = a * (s.cardE - 1)
      from ⟨dY, s.cardE - 1, h1, rfl, rfl⟩)
    (fun _ => show (0 : ℕ) = 0 from rfl)
    (show ∃ a b, 0 < b ∧ fieldError s S.mu = Bound.ratio a b ∧
        S.mu * s.cardE ^ (S.mu - 1) * b = a * s.cardE ^ S.mu
      from ⟨S.mu, s.cardE, h0, rfl, mul_pow_pred _ _⟩)
    (show ∃ a b, 0 < b ∧ fieldError s 1 = Bound.ratio a b ∧ 1 * b = a * s.cardE
      from ⟨1, s.cardE, h0, rfl, rfl⟩)
    (show ∃ a b, 0 < b ∧ fieldError s (S.mu + S.d) = Bound.ratio a b ∧
        (S.mu + S.d) * s.cardE ^ (S.mu + S.d - 1) * b = a * s.cardE ^ (S.mu + S.d)
      from ⟨S.mu + S.d, s.cardE, h0, rfl, mul_pow_pred _ _⟩)

/-- The verifier's message of a row has a value. -/
theorem spec_pos (S : Pub) (q : ℕ) (h : 1 < q) : ∀ r ∈ Lam q S, 0 < r.n :=
  have h0 : 0 < q := Nat.lt_of_succ_lt h
  lam_forall q S _ h0 h0 (fun _ => h0) (fun _ => Nat.sub_pos_of_lt h) (fun _ => Nat.one_pos)
    (Nat.pow_pos h0) h0 (Nat.pow_pos h0)

section
variable {E : Type} [Field E] [Fintype E] (p : ℕ) (A : Dat E) (P : Pl A) (Ex : Iop.ExtSpec)
  (s : Setting)

/-- Round by round the lookup's errors and numbers of values fit the planner's list. -/
theorem lamS_fits (hA : A.toPub.Adm p) (hq : s.cardE = Fintype.card E) :
    List.Forall₂ (Cb.Pv.Fits (Fintype.card E))
      ((A.lamS P Ex).e.toList.zip (A.lamS P Ex).R.shape.chalList)
      (lookupList s (sizeOfPub A.toPub)) := by
  obtain ⟨h1, h2⟩ := lamS_isL_adm p A P Ex hA
  rw [h1, h2, ← lam_list s A.toPub (Fintype.card E) (adm_pl hA) (adm_parts hA), List.zip_map',
    List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro r hr
  rw [← hq] at hr ⊢
  exact spec_fits s A.toPub (by rw [hq]; exact Fintype.one_lt_card) r hr

/-- Round by round they are covered, if `close` has tested every description of the list. -/
theorem lamS_covered (hA : A.toPub.Adm p) (hq : s.cardE = Fintype.card E)
    (hg : ∀ y ∈ lookupList s (sizeOfPub A.toPub), y.Good s .once) :
    List.Forall₂ (Cb.Pv.Covered s .once)
      ((A.lamS P Ex).e.toList.zip (A.lamS P Ex).R.shape.chalList)
      (lookupList s (sizeOfPub A.toPub)) := by
  have hc : 1 < s.cardE := by rw [hq]; exact Fintype.one_lt_card
  obtain ⟨h1, h2⟩ := lamS_isL_adm p A P Ex hA
  rw [← lam_list s A.toPub (Fintype.card E) (adm_pl hA) (adm_parts hA)] at hg
  rw [h1, h2, ← lam_list s A.toPub (Fintype.card E) (adm_pl hA) (adm_parts hA), List.zip_map',
    List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro r hr
  have hG := hg _ (List.mem_map_of_mem hr)
  rw [← hq] at hr
  exact covered_of_fits s s.cardE _ _ (spec_fits s A.toPub hc r hr) (spec_pos A.toPub _ hc r hr) hG

/-- Where the planner's routine for the lookup ends well, `close` has tested every description of
its list. -/
theorem lam_good (hA : A.toPub.Adm p) (st st' : PlanState) (h1 : st.set = s)
    (h2 : st.scope = .once) (h3 : st.openBytes = 0) (h4 : st.openRoots = 0)
    (h5 : st.openAnswers = 0) (hrun : planLookup (sizeOfPub A.toPub) st = .ok ((), st')) :
    ∀ y ∈ lookupList s (sizeOfPub A.toPub), y.Good s .once := by
  rw [← lam_list s A.toPub (Fintype.card E) (adm_pl hA) (adm_parts hA)]
  exact ((lam_runs s .once A.toPub (Fintype.card E) (adm_pl hA) (adm_parts hA)) st st' () h1 h2 h3
    h4 h5 hrun).2.2.2.2.2.2.2

/-- So, where that routine ends well, the lookup's errors are covered round by round. -/
theorem lamS_covered_run (hA : A.toPub.Adm p) (hq : s.cardE = Fintype.card E)
    (st st' : PlanState) (h1 : st.set = s) (h2 : st.scope = .once) (h3 : st.openBytes = 0)
    (h4 : st.openRoots = 0) (h5 : st.openAnswers = 0)
    (hrun : planLookup (sizeOfPub A.toPub) st = .ok ((), st')) :
    List.Forall₂ (Cb.Pv.Covered s .once)
      ((A.lamS P Ex).e.toList.zip (A.lamS P Ex).R.shape.chalList)
      (lookupList s (sizeOfPub A.toPub)) :=
  lamS_covered p A P Ex s hA hq (lam_good p A s hA st st' h1 h2 h3 h4 h5 hrun)

end

section
open Iop Hiop IOR Cb Cb.LdLkp Cb.LdLkp.Kn Cb.LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} (P : LdWfP E C) (K : Cut P)

/-- The link has the lookup's errors. -/
theorem link_errs (B : ∀ l, Bks (K.dat l) C.E0) (l : ℕ) :
    (lLkK P K B l).e.toList = (B l).lam1.e.toList := rfl

/-- The link has the lookup's rounds. -/
theorem link_vals (B : ∀ l, Bks (K.dat l) C.E0) (l : ℕ) :
    (lLkK P K B l).R.shape.chalList = (B l).lam1.R.shape.chalList := rfl

/-- Round by round the link's errors are covered. -/
theorem link_covered (Q : ∀ l, Pl (K.dat l)) (l p : ℕ) (s : Setting) (hA : (K.S l).Adm p)
    (hq : s.cardE = Fintype.card E)
    (hg : ∀ y ∈ lookupList s (sizeOfPub (K.S l)), y.Good s .once) :
    List.Forall₂ (Cb.Pv.Covered s .once)
      ((lLkK P K (fun l => (K.dat l).bks (Q l) (SK₀ E C.E0)) l).e.toList.zip
        (lLkK P K (fun l => (K.dat l).bks (Q l) (SK₀ E C.E0)) l).R.shape.chalList)
      (lookupList s (sizeOfPub (K.S l))) := by
  rw [link_errs, link_vals]
  exact lamS_covered p (K.dat l) (Q l) C.E0 s hA hq hg

end
end Lk6

#print axioms Lk6.covered_of_fits
#print axioms Lk6.spec_fits
#print axioms Lk6.lamS_fits
#print axioms Lk6.lamS_covered
#print axioms Lk6.lam_good
#print axioms Lk6.lamS_covered_run
#print axioms Lk6.link_covered
