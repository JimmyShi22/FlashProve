-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.TopH
import Johnson.Desc.K12.Law.CondReads
import Johnson.Desc.K12.Law.PlacesNums
import Johnson.Top.H0.StepLaws.StepLaws
/-
Johnson/Desc/K12/Law/PubOfStep.lean: pubOk AT A PROXIMITY TEST's PLACE, TWICE: AT THE RUN's OWN CODES, from a yes of the block's step; AT PUBLIC CODES, from a closed member and four equations on the place. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  pub_of_step: k12_guards (Law/TopH.lean: of the DECISION's yes) CARRIED TO THE STEP: planOk · (proximityTestKind guardedProximityTestParts p).step ft t rs cols = .ok (t', n) ⇒ p.nums.free = t.roots ∧ pubOk p t.st.codes = true: guards (f) and (p), read off the STEP's yes AT THE RECORD IN FRONT OF THE BLOCK.
  pub_of_seat: the same behind a way in: (Block.inside enter (proximityTestKind guardedProximityTestParts p) leave).step … s … = .ok … ⇒ ∃ t, enter s = .ok t ∧ ….
  pub_public: at a place made by proximityTestParametersAt place x whose block passes its test on the plan: pubOk q K = true at a closed place q, and x's stages · work · written rounds and the place's idx are q's ⇒ pubOk (proximityTestParametersAt place x) K = true: NO RUN, NO RECORD.
OVER: step_iff | inside_step (Johnson/Top/H0/StepLaws/StepLaws.lean) · our k12_guards (Law/TopH.lean) · early_of_planOk (Law/Top.lean) · our pubOk_reads (Law/CondReads.lean) · nums_of_planOk (Law/PlacesNums.lean).
WHY TWO: a law that speaks of all transcripts cannot hang on one run's record: it takes the public form; what is said of a run takes the run's. THAT THE RUN's CODES ARE THE PUBLIC ONES IS SAID BY NEITHER.


-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok)

/-- **Guards (f) and (p), off the step's yes, at the record in front of the block.** -/
theorem pub_of_step (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (ft : Nat) (t t' : T12)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step ft t rs cols = .ok (t', n)) :
    p.nums.free = t.roots ∧ H2K.Pub.pubOk p t.st.codes = true := by
  obtain ⟨_, hd, _⟩ := (step_iff _ _ _ _ _ _ _).1 h
  obtain ⟨h1, h2, _⟩ := k12_guards p (early_of_planOk p hp) t t' _ _ hp hd
  exact ⟨h1, h2⟩

/-- **Behind a way in.** -/
theorem pub_of_seat {S : Type} (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ft : Nat) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat)
    (h : (Block.inside enter (proximityTestKind guardedProximityTestParts p : Blk') leave).step ft s rs cols = .ok (s', n)) :
    ∃ t, enter s = .ok t ∧ p.nums.free = t.roots ∧ H2K.Pub.pubOk p t.st.codes = true := by
  obtain ⟨t, t', he, h2, _⟩ := (inside_step _ _ _ _ _ _ _ _ _).1 h
  exact ⟨t, he, pub_of_step p hp ft t t' rs cols n h2⟩

/-- **At public codes: no run, no record.** -/
theorem pub_public {Cl : Type} (place : Place) (x : H2U.PlaceNums) (q : P12) (K : Codes)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place x) : Block T12 Cl).planOk = true)
    (hq : H2K.Pub.pubOk q K = true) (hs : x.nums.stages = q.nums.stages)
    (hw : x.nums.work = q.nums.work)
    (hW : H2K.Pub.writtenOf x.nums = H2K.Pub.writtenOf q.nums)
    (hi : (H2U.proximityTestParametersAt place x).idx = q.idx) : H2K.Pub.pubOk (H2U.proximityTestParametersAt place x) K = true := by
  have hn := H2K.Made.nums_of_planOk place x hp
  exact (H2K.Pub.pubOk_reads K (by rw [hn]; exact hs) (by rw [hn]; exact hw)
    (by rw [hn]; exact hW) hi).trans hq

end H2K.JointK

#print axioms H2K.JointK.pub_of_step
#print axioms H2K.JointK.pub_of_seat
#print axioms H2K.JointK.pub_public
