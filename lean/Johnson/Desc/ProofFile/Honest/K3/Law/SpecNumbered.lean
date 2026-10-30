-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecNumbered.lean: the honest side of the kind "lookup" (K3).
Two of the seven clauses of `Numbered R` (Honest/K3/Law/SpecLawful.lean), of a course that stands at
its place and whose challenges can be sampled (`Fit R`, Honest/K3/Law/Statements.lean). The first is
conditional on one part of keys. Theorems. The other five clauses, and the seven together
(`numbered_of_fit`), stand in Honest/K3/Law/NumberedOfFit.lean.

Terms. Honest/K3/GLOSSARY.md ("course", "fit", "stage").

What is shown, by the file's sections.
  1. `theta_take`, `alpha_take`, `same_take`, `same_of_fit`: what a stage's job reads of the
     challenges in front of the stage is what the whole run's points hold.
  2. `all_len`, `draws_len`, `len_of_fit`: a challenge for every variable.

Hypotheses that remain. `hF`: `Fit R`; `hp`: one part of keys, in section 1. In the steps: `hs`,
`hk`: the stage is one of the row's, with the call k; `hn`: (in `theta_take`, `alpha_take`) the cut
reaches behind the shift's, or alpha's, round.

How the proof goes. It rests on the closed forms of `firstRound` and on the facts on a list of
challenges that is cut (Honest/K3/HeardLaw.lean; Honest/K3/Law/Index.lean), and on
Honest/K3/Law/StageFacts.lean.

Users. This file is imported by Honest/K3/Law/NumberedOfFit.lean and Honest/K3/Law/SpecMember.lean.

Limits. One part of keys. No summand and no input is read.
Instances of `Fit`: the courses of Honest/K3/Law/Members.lean (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecCourse
import Johnson.Desc.ProofFile.Honest.K3.Law.StageFacts
import Johnson.Desc.ProofFile.Honest.K3.Law.Index

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open ProofFile.Honest.SumLaw (drawsOk varsOf ownOf endRun)

variable {W : Type}

/-! ## 1 What a stage reads in front of it -/

section Take
variable (f : LFace) (v : Nat) (hp : f.parts = [v]) (front ds : List Fmt.Drawn)
include hp

theorem theta_take {n : Nat} (hn : 1 ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).theta =
      (ptsOf f front.length (front ++ ds)).theta := by
  show (if f.shifted then elemAt (front ++ ds.take n) (roundAt f front.length .shift) else zeroE) =
    (if f.shifted then elemAt (front ++ ds) (roundAt f front.length .shift) else zeroE)
  by_cases hs : f.shifted = true
  · rw [if_pos hs, if_pos hs,
      elemAt_take front ds n _ (by unfold roundAt; rw [fr_shift f v hp hs]; omega)]
  · rw [if_neg hs, if_neg hs]

theorem alpha_take {n : Nat} (hn : oAlpha f < n) :
    (ptsOf f front.length (front ++ ds.take n)).alpha =
      (ptsOf f front.length (front ++ ds)).alpha := by
  show elemAt (front ++ ds.take n) (roundAt f front.length .alpha) =
    elemAt (front ++ ds) (roundAt f front.length .alpha)
  rw [elemAt_take front ds n _ (by unfold roundAt; rw [fr_alpha f v hp]; omega)]

theorem same_take (s : Stage) (hs : s ∈ stages f) :
    SameFor f s (ptsOf f front.length (front ++ ds.take (firstRound f s)))
      (ptsOf f front.length (front ++ ds)) := by
  obtain ⟨_, c1, c2, c3, c4, c5, c6, _⟩ := o_chain f v
  cases s with
  | tie j =>
    have fr := fr_tie f v hp (tie_lt hs)
    exact ⟨theta_take f v hp front ds (by omega), alpha_take f v hp front ds (by omega)⟩
  | key i m =>
    obtain ⟨rfl, hm⟩ := key_lt hp hs
    have fr := fr_key f v hp hm
    exact ⟨theta_take f v hp front ds (by omega), alpha_take f v hp front ds (by omega),
      keyPt_take f v hp front ds (Nat.le_of_lt hm) (by omega)⟩
  | tab l =>
    have hl := tab_lt hs
    have fr := fr_tab f v hp hl
    exact ⟨theta_take f v hp front ds (by omega), alpha_take f v hp front ds (by omega),
      tabPt_take f v hp front ds (Nat.le_of_lt hl) (by omega)⟩
  | leaves =>
    have fr := fr_leaves f v hp
    exact ⟨theta_take f v hp front ds (by omega), alpha_take f v hp front ds (by omega),
      tabPt_take f v hp front ds (Nat.le_refl _) (by omega)⟩
  | bits =>
    have fr := fr_bits f v hp
    exact ⟨theta_take f v hp front ds (by omega), alpha_take f v hp front ds (by omega),
      zeroPt_take f v hp front ds (by omega)⟩
  | shift => trivial
  | alpha => trivial
  | split i => trivial
  | join => trivial
  | keyLine i m => trivial
  | tabLine l => trivial
  | zero => trivial

end Take

/-- **Conditional on `Fit R` and on one part of keys: what a stage's job reads of the challenges in
front of it is what the whole run's points hold** (`Numbered.same`). Instances of the hypotheses:
the courses of Honest/K3/Law/Members.lean (by evaluation). -/
theorem same_of_fit (R : Course W) (v : Nat) (hp : R.f.parts = [v]) (hF : Fit R) (s : Stage)
    (hs : s ∈ stages R.f) : SameFor R.f s (ptsOf R.f R.a.base (R.front s).heard) R.pts := by
  show SameFor R.f s (ptsOf R.f R.a.base (R.t.heard ++ R.ds.take (firstRound R.f s)))
    (ptsOf R.f R.a.base (R.t.heard ++ R.ds))
  rw [← hF.base]
  exact same_take R.f v hp R.t.heard R.ds s hs

/-! ## 2 A challenge for every variable -/

/-- The call in the run has as many variables as the shape. -/
theorem all_len (R : Course W) (s : Stage) :
    (R.call s).all.length = (shapeAt R.a s).all.length := by
  show (Call.all { shapeAt R.a s with
    vs := withPoints (shapeAt R.a s).vs (pointsAt R.f s (R.ptsAt s)) }).length = _
  unfold Call.all
  cases (shapeAt R.a s).ends <;> simp [withPoints_len]

/-- A stage with a call has a challenge for each of its rounds. -/
theorem draws_len (R : Course W) (hF : Fit R) {s : Stage} (hs : s ∈ stages R.f) {k : Call}
    (hk : s.call R.f = some k) :
    (R.draws s).length = 1 + (k.vs.length + (match k.ends with | none => 0 | some _ => 2)) := by
  have h1 := drawsOk_stage hF hs hk
  unfold drawsOk at h1
  have h2 := congrArg List.length (eq_of_beq h1)
  rw [entries_drawE, call_eq R s k hk] at h2
  simp only [List.length_map, List.length_cons, List.length_append, List.length_replicate,
    withPoints_len] at h2
  rw [h2]
  cases k.ends <;> simp <;> omega

/-- **Conditional on `Fit R`: a stage's sumcheck has a challenge for each variable, Y among them**
(`Numbered.len`). Instances of `Fit`: Honest/K3/Law/Members.lean (by evaluation). -/
theorem len_of_fit (R : Course W) (hF : Fit R) (s : Stage) (hs : s ∈ stages R.f) :
    (R.r s).length = (shapeAt R.a s).all.length := by
  show (((ownOf (R.draws s)).drop 1).take (R.call s).all.length).length = _
  rw [List.length_take, List.length_drop, all_len]
  have ho : (ownOf (R.draws s)).length = (R.draws s).length := by simp [ownOf, drawnE]
  rw [ho]
  cases hk : s.call R.f with
  | none =>
    have e : shapeAt R.a s = ⟨0, [], none⟩ := by
      unfold shapeAt
      rw [show s.call R.a.face = none from hk]
      rfl
    rw [e]
    simp [Call.all]
  | some k =>
    rw [draws_len R hF hs hk, shapeAt_eq R s k hk]
    unfold Call.all
    cases k.ends <;> simp

#print axioms ProofFile.Honest.K3.Law.Spec.theta_take
#print axioms ProofFile.Honest.K3.Law.Spec.alpha_take
#print axioms ProofFile.Honest.K3.Law.Spec.same_take
#print axioms ProofFile.Honest.K3.Law.Spec.same_of_fit
#print axioms ProofFile.Honest.K3.Law.Spec.all_len
#print axioms ProofFile.Honest.K3.Law.Spec.draws_len
#print axioms ProofFile.Honest.K3.Law.Spec.len_of_fit

end ProofFile.Honest.K3.Law.Spec
