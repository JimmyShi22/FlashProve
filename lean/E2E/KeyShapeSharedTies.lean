--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeSharedTies.lean: THE KEY FILE's SHARED CHAIN ON SHAPES, IN THE GOALS' SCOPE, AT THE
DESCRIPTION THAT THE VERIFIER RUNS: the letters of E2E/KeyShapeSharedChain.lean with the guards of
E2E/KeyShapeSharedFull.lean: (B1) at every number, the run's value, the Bool that the frame's rule
asks, and the first state's shape. Statements and proofs. Sub-protocols of the verifier's and guards
on shapes: NOTHING IS SHOWN OF ANY PROVER.

  `later_sourced`, `par_sourced`: in scope the later places' numbers and the linear claim's
    parameters are the written values `PF` and `QK`.
  **`plan2_full`**: the hash build's public premises (Johnson/Desc/ProofFile/Honest/K14/Debts2.lean:
    `Plan2`) hold at `QK`. By Lean's kernel, clause by clause.
  `goes_full`, `blocksOr_eight`: small ones.
  `plan_eight`: each of the linear claim's eight passes its own test on the plan at `QK`. By Lean's
    kernel.
  `flatAt₂`, `pre_len₂`: the description's own flat list begins with the front sub-protocol and the
    eight, in the hash build's form (`FlatAt`); nine stand in front of the test on G_u.
  `like_at`, `tidy_kept`: each of the nine keeps the mark on the statement.
  **`carriesK`**: (B1) at the nine: the premise of E2E/KeyShapeSharedChain.lean's `carries_all₂`: by
    the hash build's `carries2` (Honest/K14/ShapeLaws.lean), `carries_withMark` and `eight_tidy`:
    CALLED.
  **`carries₂_sourced`**: so (B1) at every number.
  `letters₂_sourced`: in scope the letters at the description's own count are the ones whose run is
    evaluated.
  **`yes₂_sourced`**, `run₂_sourced`: the run's value and the Bool.
  **`first₂_shape`**: the first state's shape is `V0`, at every instance whose key's sizes fit.

Limits.
- (B2) IS NOT HERE, at no number. At the two proximity tests the guards ask fewer guards than the
  tests.
- That an instance's key's sizes fit is a premise of `first₂_shape`.
- The named tests on values are a letter.


-/
import E2E.KeyShapeSharedFull
import E2E.KeyShapeFirstEnd
import Johnson.Desc.ProofFile.Honest.K14.ShapeLaws
import Johnson.Desc.K14.Shape.Mark
import Johnson.AtFull.KeyBack.InScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest ProofFile.Honest.K14
open Lk6.AtPlan (keyFull)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Ground.Sh (stTidyB tidy_mark)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Key (Source LaterPlaces beforeSharedPoint sharedPar)
open _root_.Desc.K14 (P14 St withU blocks blocksOr frontBlock)
open _root_.Desc.K14.Shape (Sh2 sh2 factsB updS first_shape marked_first)
open _root_.Desc.K14.Honest (keyW Eight FlatAt Like PlanFacts)

section Scope
variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- In scope the later places' numbers are the library's written value. -/
theorem later_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) : P = PF := by
  obtain ⟨X₀, m, h0, hm, -, -, hP⟩ := hs.source
  have e := Johnson.AtFull.KeyBack.laterPlaces_in_scope scope h0 hm
  rw [hP] at e
  exact Except.ok.inj e

/-- In scope the linear claim's parameters are the written value. -/
theorem par_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) :
    sharedPar X.chains (beforeSharedPoint P) = QK := by
  rw [later_sourced hs scope]
  unfold sharedPar
  rw [sized_sourced hs scope]
  rfl

end Scope

/-! ## The public premises at the written value -/

theorem goes_full : withU QK.S = some sentUF := by
  have h : (withU QK.S).isSome = true := by decide +kernel
  unfold sentUF
  cases e : withU QK.S with
  | none => rw [e] at h; cases h
  | some a => rfl

/-- **The hash build's public premises hold at the written value.** -/
theorem plan2_full : ∃ layO, Plan2 QK sentUF layO := by
  have hB : ((layTrees QK.codes (_root_.Desc.K14.withOmega QK.par.S)).any fun l =>
      decide (l.tree.getD 0 0 < l.shapes.size) &&
        decide (l.tree.getD 1 0 ≠ l.tree.getD 0 0)) = true := by decide +kernel
  cases e : layTrees QK.codes (_root_.Desc.K14.withOmega QK.par.S) with
  | none => rw [e] at hB; cases hB
  | some l =>
    rw [e] at hB
    have hB' : (decide (l.tree.getD 0 0 < l.shapes.size) &&
        decide (l.tree.getD 1 0 ≠ l.tree.getD 0 0)) = true := hB
    rw [Bool.and_eq_true] at hB'
    exact ⟨l, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, goes_full, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, e,
      ⟨of_decide_eq_true hB'.1, of_decide_eq_true hB'.2⟩⟩, by decide +kernel, by decide +kernel⟩

/-- Each of the eight passes its own test on the plan. -/
theorem plan_eight : ∀ b ∈ blocksOr QK, b.planOk = true := by
  have h : (blocksOr QK).all (·.planOk) = true := by decide +kernel
  exact fun b hb => List.all_eq_true.1 h b hb

/-! ## The description's own list -/

theorem blocksOr_eight {Q : P14} (B : Eight Q) :
    blocksOr Q = [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] := by
  unfold blocksOr
  rw [B.made]
  rfl

/-- **The description's own flat list begins with the front sub-protocol and the eight.** -/
theorem flatAt₂ (c : Model.Verify.Chains) (P : LaterPlaces) {Q : P14}
    (e : sharedPar c (beforeSharedPoint P) = Q) (B : Eight Q) : FlatAt (flat₂ c P) c B := by
  subst e
  rw [flat₂_cut]
  unfold H2K.JointK.keySharedPre
  rw [blocksOr_eight B]
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, .mk rfl rfl rfl rfl, .mk rfl rfl rfl rfl,
    .mk rfl rfl rfl rfl, .mk rfl rfl rfl rfl, .mk rfl rfl rfl rfl, .mk rfl rfl rfl rfl,
    .mk rfl rfl rfl rfl, .mk rfl rfl rfl rfl, .mk rfl rfl rfl rfl⟩

/-- Nine stand in front of the test on G_u. -/
theorem pre_len₂ (c : Model.Verify.Chains) (P : LaterPlaces) {Q : P14}
    (e : sharedPar c (beforeSharedPoint P) = Q) (B : Eight Q) :
    (H2K.JointK.keySharedPre c P).length = 9 := by
  subst e
  unfold H2K.JointK.keySharedPre
  rw [blocksOr_eight B]
  rfl

/-- The member number b, from 1 to 8, is like one of the eight. -/
theorem like_at {Cl : Type} {Q : P14} {bs : List (Block St Cl)} {c : Model.Verify.Chains}
    {B : Eight Q} (F : FlatAt bs c B) {b : Nat} (h1 : 1 ≤ b) (h8 : b ≤ 8) {blk : Block St Cl}
    (hblk : bs[b]? = some blk) : ∃ x ∈ blocksOr Q, Like blk x := by
  rw [blocksOr_eight B]
  match b, h1, h8, hblk with
  | 1, _, _, h => exact ⟨B.b1, by simp, F.at1 h⟩
  | 2, _, _, h => exact ⟨B.b2, by simp, F.at2 h⟩
  | 3, _, _, h => exact ⟨B.b3, by simp, F.at3 h⟩
  | 4, _, _, h => exact ⟨B.b4, by simp, F.at4 h⟩
  | 5, _, _, h => exact ⟨B.b5, by simp, F.at5 h⟩
  | 6, _, _, h => exact ⟨B.b6, by simp, F.at6 h⟩
  | 7, _, _, h => exact ⟨B.b7, by simp, F.at7 h⟩
  | 8, _, _, h => exact ⟨B.b8, by simp, F.at8 h⟩

/-- **Each of the nine keeps the mark on the statement.** -/
theorem tidy_kept {Cl : Type} {bs : List (Block St Cl)} {c : Model.Verify.Chains} {B : Eight QK}
    (F : FlatAt bs c B) (ft : Nat) {b : Nat} (h8 : b ≤ 8) (blk : Block St Cl)
    (hblk : bs[b]? = some blk) (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : St) (n : Nat)
    (h : blk.step ft s rs cols = .ok (s', n)) (hT : stTidyB s.st = true) :
    stTidyB s'.st = true := by
  by_cases h0 : b = 0
  · subst h0
    have hl := F.at0 hblk
    rw [hl.step] at h
    have hd := ((VerifiableInference.Desc.step_iff ft (frontBlock c) s s' rs cols n).1 h).2.1
    have e : s = s' := Except.ok.inj hd
    rw [← e]
    exact hT
  · obtain ⟨x, hx, hl⟩ := like_at F (by omega) h8 hblk
    rw [hl.step] at h
    exact eight_tidy (ft := ft) QK x hx (plan_eight x hx) s s' rs cols n h hT

section Scope2
variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **(B1) AT THE NINE IN FRONT OF THE TEST ON G_u**, in scope. -/
theorem carriesK (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) (ft : Nat)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (b : Nat)
    (hb : b < (H2K.JointK.keySharedPre X.chains P).length) :
    Carries (flat₂ X.chains P) ft (Z₂At X.chains P gK₂ v) b := by
  obtain ⟨layO, hQ⟩ := plan2_full
  obtain ⟨B⟩ := hQ.eight
  have e := par_sourced hs scope
  have F := flatAt₂ X.chains P e B
  have h9 := pre_len₂ X.chains P e B
  have hb8 : b ≤ 8 := by omega
  intro blk hblk s rs cols s' n t hstep hg
  have hg' : gK₂ b (sh₂ s) = .ok t := by
    have q : (Z₂At X.chains P gK₂ v).g b = gK₂ b := by
      show (if b < (H2K.JointK.keySharedPre X.chains P).length then gK₂ b else _) = _
      rw [if_pos hb]
    rw [q] at hg
    exact hg
  exact carries_withMark (ft := ft) (bs := flat₂ X.chains P) (b := b) _
    (carries2 (guard := factsB QK) (upd := updS QK sentUF) (vals := v) B F hQ.facts.goes
      hQ.facts.two ft b hb8 fun _ => rfl)
    (fun blk hblk s rs cols s' n h hT => tidy_kept F ft hb8 blk hblk s rs cols s' n h hT)
    blk hblk s rs cols s' n t hstep hg'

/-- **(B1) AT EVERY NUMBER**, in scope. -/
theorem carries₂_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true) (ft : Nat)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (j : Nat) :
    Carries (flat₂ X.chains P) ft (Z₂At X.chains P gK₂ v) j :=
  carries_all₂ X.chains P gK₂ v ft (carriesK hs scope ft v) (shared_places_in_scope hs scope).1
    (shared_places_in_scope hs scope).2 j

/-- In scope the letters at the description's own count are the ones whose run is evaluated. -/
theorem letters₂_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    Z₂At X.chains P gK₂ v = Z₂ PF 9 gK₂ v := by
  obtain ⟨layO, hQ⟩ := plan2_full
  obtain ⟨B⟩ := hQ.eight
  show Z₂ P (H2K.JointK.keySharedPre X.chains P).length gK₂ v = _
  rw [pre_len₂ X.chains P (par_sourced hs scope) B, later_sourced hs scope]

/-- **The run's value**, in scope, at the letters at the description's own count. -/
theorem run₂_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    (Z₂At X.chains P gK₂ v).run 12 V0 = .ok V12 := by
  obtain ⟨layO, hQ⟩ := plan2_full
  obtain ⟨B⟩ := hQ.eight
  have h9 := pre_len₂ X.chains P (par_sourced hs scope) B
  obtain rfl := later_sourced hs scope
  show (Z₂ PF (H2K.JointK.keySharedPre X.chains PF).length gK₂ v).run 12 V0 = .ok V12
  rw [h9]
  exact run₂_full v

/-- **The Bool that the frame's rule asks**, in scope. -/
theorem yes₂_sourced (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    (Z₂At X.chains P gK₂ v).yes V0 12 = true := by
  show ((Z₂At X.chains P gK₂ v).run 12 V0).toOption.isSome = true
  rw [run₂_sourced hs scope v]
  rfl

/-- **The first state's shape**, at every instance whose key's sizes fit. -/
theorem first₂_shape (hs : KeySourced Z X N P) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription X N P).XiPub) (hk : keyFits x.key QK.par.S.fold.index = true) :
    sh₂ ((keyFileDescription X N P).start₂ x) = V0 := by
  have e : (keyFileDescription X N P).start₂ x = _root_.Desc.K14.first QK.codes x.key := by
    show _root_.Desc.K14.first X.chains.made.sized.key.codes x.key = _
    rw [sized_sourced hs scope]
    rfl
  rw [e]
  exact Prod.ext (first_shape QK x.key hk) (tidy_mark (marked_first QK.codes x.key).1)

end Scope2

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.later_sourced
#print axioms AtPublicFiles.AtFiles.Full.par_sourced
#print axioms AtPublicFiles.AtFiles.Full.goes_full
#print axioms AtPublicFiles.AtFiles.Full.plan2_full
#print axioms AtPublicFiles.AtFiles.Full.plan_eight
#print axioms AtPublicFiles.AtFiles.Full.blocksOr_eight
#print axioms AtPublicFiles.AtFiles.Full.flatAt₂
#print axioms AtPublicFiles.AtFiles.Full.pre_len₂
#print axioms AtPublicFiles.AtFiles.Full.like_at
#print axioms AtPublicFiles.AtFiles.Full.tidy_kept
#print axioms AtPublicFiles.AtFiles.Full.carriesK
#print axioms AtPublicFiles.AtFiles.Full.carries₂_sourced
#print axioms AtPublicFiles.AtFiles.Full.letters₂_sourced
#print axioms AtPublicFiles.AtFiles.Full.run₂_sourced
#print axioms AtPublicFiles.AtFiles.Full.yes₂_sourced
#print axioms AtPublicFiles.AtFiles.Full.first₂_shape
