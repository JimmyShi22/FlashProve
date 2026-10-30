-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/MarksAtDoor.lean

What it proves. At the state on entry to the shared chain's two proximity tests as doorOf makes it
(JobShared.lean), at every input and whatever precedes the test, whatever the readers of the key and
of the columns are: the three tests that a proximity test's door asks beside the shape hold
(stTidyB, stPlainB, claimsB: Three, MarksBehind.lean), where they hold at the fall-back; and at the
test on G_u the shape is the term doorU (endOf Q sentU) (ShapeBehind.lean), where it is the
fall-back's. With the fall-back fallU Q sentU the second needs no premise on the fall-back.
All premises are on the plan and on the fall-back, which is a parameter.

Names.
  prop_doorOf   what holds at the fall-back, and wherever the fold and the seat's way in return,
      holds at doorOf.
  three_behind_nine   the three tests at what the seat of the test on G_omega enters, wherever the
      fold over the eight and the test on G_u returns.
  three_door_U, three_door_Omega   the three tests at the two doors.
  shape_door_U, shape_door_U_fall   the shape at the test on G_u.
  not_tidy_stateOfPub   the state that holds the plan's public part and nothing else is not tidy.

By what. three_at_U, three_at_Omega, marks_behind_eight, there_behind_eight (MarksBehind.lean);
shape_at_U_plan, shape_fallU (ShapeBehind.lean); behind_fold (PubAtDoor.lean) for the codes and the
two groups' numbers; the library's foldBlocks_append_ok and foldBlocks_cons_ok
(Johnson/Desc/RunLaws.lean), step_decide (Johnson/Desc/ChainEndFold.lean), early_of_planOk and
answers_of_planOk (Johnson/Desc/K12/Law/Top.lean).

Limits.
- At the fall-back that the theorems of PubNear.lean name, stateOfPub (pubBehind Q sentU, g), the
  first of the three tests fails (not_tidy_stateOfPub): its first group has the member 0, none of
  its messages is marked as sampled, and stTidyB asks that every member is sampled. So with that
  fall-back the premise on the fall-back cannot be met, and three_door_U and three_door_Omega say
  nothing. A fall-back that meets it is not given here: fallU has the shape; whether it passes the
  three tests is an evaluation at a plan, which is not made here.
- The premise that each of the eight blocks' tests on the plan passes is asked; who shows it at a
  plan is not treated here.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- That the state on entry is the verifier's is not shown: where the fold does not return, doorOf
  gives the fall-back. At the test on G_omega that is so at every honest run, as long as a part is
  handed no opened column (JobShared.lean's limits): there three_door_Omega says no more than its
  premise on the fall-back.
- At the test on G_omega the shape is not treated here.
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ShapeBehind
import Johnson.Desc.ProofFile.Honest.K12.PubNear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts Seat.enter Seat.onGu)
open Desc.K14 (P14 St blocks first withU withOmega)
open Desc.K14.Shape (doorU)
open ProofFile.Honest.Sh (testSh)

variable {W X : Type}

/-- What holds at the fall-back, and wherever the fold and the way in return, holds at doorOf. -/
theorem prop_doorOf {S₀ : Type} (Pr : T12 → Prop) (bs : List (Block S₀ Unit)) (s₀ : W → S₀)
    (enter : S₀ → Except String T12) (cols : W → Front X → List OpenedColumn) (fall : T12) (hf : Pr fall)
    (h : ∀ w fr x t, foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) = .ok x →
      enter x.1 = .ok t → Pr t) (w : W) (fr : Front X) :
    Pr (doorOf bs s₀ enter cols fall w fr) := by
  unfold doorOf
  cases hx : foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) with
  | error _ => exact hf
  | ok x =>
    show Pr ((enter x.1).toOption.getD fall)
    cases ht : enter x.1 with
    | error _ => exact hf
    | ok t => exact h w fr x t hx ht

/-- **The three tests at what the seat of the test on G_omega enters**, wherever the fold over the
eight and the test on G_u returns. -/
theorem three_behind_nine (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (hS : Q.S.sharedSplitNeeded = true)
    (hM : Q.S.masksAhead = true) (sentU : Array OracleNotice) (hw : withU Q.S = some sentU)
    (hl : Q.codes.lengthsOk = true) (p : P12)
    (hpU : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (key : TableKey)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (x : St × List Fmt.RoundView × List OpenedColumn) (t : T12)
    (h : foldBlocks 0 (bs ++ [Seat.onGu (proximityTestKind guardedProximityTestParts p)]) (first Q.codes key) rs cols = .ok x)
    (he : Seat.enter (·.gOmega) (fun _ => none) x.1 = .ok t) : Three t := by
  obtain ⟨d8, rs', cols', h8, h9⟩ :=
    (VerifiableInference.Desc.foldBlocks_append_ok _ _ _ _ _ _).1 h
  have B := behind_fold Q bs hb hS hM sentU hw key rs cols _ h8
  obtain ⟨_, d9, k9, s9, h9⟩ := VerifiableInference.Desc.foldBlocks_cons_ok.1 h9
  simp only [foldBlocks, Except.ok.injEq] at h9
  subst h9
  obtain ⟨_, _, e9⟩ := VerifiableInference.Desc.ChainEnd.step_decide _ _ _ _ _ _ _ s9
  exact three_at_Omega p (H2K.JointK.early_of_planOk p hpU) (H2K.JointK.answers_of_planOk p hpU)
    d8 d9 _ _ e9 (by rw [B.mid.codes]; exact hl)
    (marks_behind_eight Q bs hb hp 0 key rs cols _ h8)
    (there_behind_eight Q bs hb sentU hw hS 0 _ rs cols _ h8).2
    (by rw [B.gU, B.gOmega]; decide) t he

/-- **The three tests at the door of the test on G_u.** -/
theorem three_door_U (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (hS : Q.S.sharedSplitNeeded = true)
    (sentU : Array OracleNotice) (hw : withU Q.S = some sentU) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (fall : T12) (hf : Three fall) (w : W) (fr : Front X) :
    Three (doorOf bs (fun w => first Q.codes (key w)) (Seat.enter (·.gU) (·.firstMask)) cols fall
      w fr) :=
  prop_doorOf Three _ _ _ cols fall hf
    (fun w _ x t hx ht => three_at_U Q bs hb hp sentU hw hS 0 (key w) _ _ x hx t ht) w fr

/-- **The three tests at the door of the test on G_omega.** -/
theorem three_door_Omega (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hp : ∀ b ∈ bs, b.planOk = true) (hS : Q.S.sharedSplitNeeded = true)
    (hM : Q.S.masksAhead = true) (sentU : Array OracleNotice) (hw : withU Q.S = some sentU)
    (hl : Q.codes.lengthsOk = true) (p : P12)
    (hpU : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (fall : T12) (hf : Three fall) (w : W) (fr : Front X) :
    Three (doorOf (bs ++ [Seat.onGu (proximityTestKind guardedProximityTestParts p)]) (fun w => first Q.codes (key w))
      (Seat.enter (·.gOmega) fun _ => none) cols fall w fr) :=
  prop_doorOf Three _ _ _ cols fall hf
    (fun w _ x t hx ht =>
      three_behind_nine Q bs hb hp hS hM sentU hw hl p hpU (key w) _ _ x t hx ht) w fr

/-- **The shape at the door of the test on G_u is one term of the plan**, where it is the
fall-back's. -/
theorem shape_door_U (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (sentU : Array OracleNotice)
    (hw : withU Q.S = some sentU) (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (fall : T12) (hf : testSh fall = doorU (endOf Q sentU)) (w : W) (fr : Front X) :
    testSh (doorOf bs (fun w => first Q.codes (key w)) (Seat.enter (·.gU) (·.firstMask)) cols fall
      w fr) = doorU (endOf Q sentU) :=
  prop_doorOf (fun t => testSh t = doorU (endOf Q sentU)) _ _ _ cols fall hf
    (fun w _ x t hx ht => shape_at_U_plan Q bs hb sentU hw hS 0 (key w) _ _ x hx t ht) w fr

/-- The same with the fall-back made of the term: no premise on the fall-back. -/
theorem shape_door_U_fall (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (hS : Q.S.sharedSplitNeeded = true) (sentU : Array OracleNotice)
    (hw : withU Q.S = some sentU) (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) :
    testSh (doorOf bs (fun w => first Q.codes (key w)) (Seat.enter (·.gU) (·.firstMask)) cols
      (fallU Q sentU) w fr) = doorU (endOf Q sentU) :=
  shape_door_U Q bs hb hS sentU hw key cols _ (shape_fallU Q sentU) w fr

/-- **The state that holds the plan's public part and nothing else is not tidy**: its first group
has the member 0, and no message of it is marked as sampled. -/
theorem not_tidy_stateOfPub (Q : P14) (sentU : Array OracleNotice) (g : ℕ) :
    VerifiableInference.Desc.Ground.Sh.stTidyB (stateOfPub (pubBehind Q sentU, g)).st = false := by
  cases h : VerifiableInference.Desc.Ground.Sh.stTidyB (stateOfPub (pubBehind Q sentU, g)).st with
  | false => rfl
  | true =>
    exfalso
    have hm := (VerifiableInference.Desc.Ground.Sh.tidy_of h).members 0
      { code := Q.S.fold.u.code, maskCode := Q.S.sharedMaskCode, members := #[0, sentU.size + 1]
        kept := #[false, false] } (by simp [stateOfPub, PubState.st, pubBehind]) 0 (by simp)
    obtain ⟨x, hx, hs⟩ := hm
    have hx' : (((sentU ++ withOmega Q.S).map (·.shape)).map
        fun s => ({ shape := s } : OnBytes.Oracle))[0]? = some x := hx
    rw [Array.getElem?_map] at hx'
    obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 hx'
    cases hs

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.prop_doorOf
#print axioms ProofFile.Honest.K12.Light.three_behind_nine
#print axioms ProofFile.Honest.K12.Light.three_door_U
#print axioms ProofFile.Honest.K12.Light.three_door_Omega
#print axioms ProofFile.Honest.K12.Light.shape_door_U
#print axioms ProofFile.Honest.K12.Light.shape_door_U_fall
#print axioms ProofFile.Honest.K12.Light.not_tidy_stateOfPub
