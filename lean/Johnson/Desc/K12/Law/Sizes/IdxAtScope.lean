-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/IdxAtScope.lean: UNDER THE PREMISE THAT THE STAGES OF THE FIRST CHAIN's
LAST TEST ARE THE TYPED LIST szLFull: the index (for each stage the numbers of its two codes) of the
four places of the kind K12 that are made off a plan sized as at the full size is the closed
places', and the proof's lists of codes are the closed `codesFull`.

That premise (hL below) hangs, in scope, on a premise on the layout file that is proved nowhere
(LastAtScope.lean). It stands under the index of ALL FOUR places: Params.proofSized numbers the
codes through the four tests in a row, the last test's first, so the numbers at the three later
tests hang on the last test's stages. A closed control at the end of section 3 shows it.
Main names:
  `nosOf`: the two codes' numbers of each stage of a test.
  `proofSized_batch`, `tests_of_proofSized`: in what proofSized returns the four tests are the four
    sized lists, numbered one after the other from no codes; the codes are those after the fourth.
    General: no scope, no size. Over `linSized_tests` (OnBytes/Params/Fit/StagesFew.lean),
    `linSized_parts` (LinParts.lean) and `proofSized_parts` (SizedParts.lean).
  `later_idx`, `places_idx`: what placesLater and placesOfMade lay as the index. General.
  `idx_of_planOk`: a made place at which the test on the plan says yes has that index.
  `nos_LFull`, `nos_UFull`, `nos_OFull`, `nos_WFull`, `codes_full`: five closed statements, by the
    kernel.
  `IdxFull M`: five equations of fields of what the planner has made with closed terms.
  `idxFull_of_configure`: from `AtFull made`, hL and configure's yes.
  `idx_L_of_full`, `idx_U_of_full`, `idx_O_of_full`, `idx_W_of_full`: THE STATEMENTS.
Limits: hL is a premise. One direction: from a configure and a placesOfMade that return. That the
codes K of a record in front of a test are the proof's lists of codes is not said. The full size
only. Nothing on soundness. Nothing on hiding.
-/
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.K12.Law.PlacesNums
import OnBytes.Params.Fit.StagesFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Params Johnson.G.OfPlan
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Member
open H2U (placesOfMade placesLater laterOfProof mkPlace Places4 PlaceNums Later3 LaterArgs cutOn
  testCutAt cutTestL TestCut proximityTestParametersAt noP12)

/-- The two codes' numbers of each stage. -/
def nosOf (l : List IoppStage) : List (Nat × Nat) := l.map fun s => (s.code, s.maskCode)

/-! ## 1. The numbering, along the planner's text -/

/-- proofSized's text with the codes named that linSized is handed: those after the numbering of the
last test's stages. -/
theorem proofSized_batch {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    ∃ (L : LinLines) (T : TableSize),
      linSized (settingOf l) L T (ioppStages z.last.stages {}).2 = some (z.batch, z.codes) := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, hl, h⟩ := opt_bind h
  obtain ⟨stages, hs, h⟩ := opt_bind h
  obtain ⟨T, hT, h⟩ := opt_bind h
  split at h
  rename_i last codes1 he
  replace h := opt_guard h
  obtain ⟨⟨batch, codes2⟩, hb, h⟩ := opt_bind h
  cases h
  have e : (ioppStages stages {}).2 = codes1 := congrArg Prod.snd he
  rw [← e] at hb
  exact ⟨_, T, hb⟩

/-- **In what proofSized returns the four tests are the four sized lists, numbered one after the
other from no codes: the last test's first; and the codes are those after the fourth.** -/
theorem tests_of_proofSized {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    z.request.last = (ioppStages z.last.stages {}).1 ∧
      z.batch.shape.testU = (ioppStages z.batch.folded.stages (ioppStages z.last.stages {}).2).1 ∧
      z.batch.shape.testOmega = (ioppStages z.batch.omega.stages
        (ioppStages z.batch.folded.stages (ioppStages z.last.stages {}).2).2).1 ∧
      z.batch.shape.testOwn = (ioppStages z.batch.own.stages (ioppStages z.batch.omega.stages
        (ioppStages z.batch.folded.stages (ioppStages z.last.stages {}).2).2).2).1 ∧
      z.codes = (ioppStages z.batch.own.stages (ioppStages z.batch.omega.stages
        (ioppStages z.batch.folded.stages (ioppStages z.last.stages {}).2).2).2).2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hl, _, _⟩ := proofSized_parts h
  obtain ⟨L, T, hB⟩ := proofSized_batch h
  obtain ⟨t1, t2, t3, _⟩ := linSized_tests hB
  obtain ⟨_, _, _, _, _, _, stU, stO, stW, _, _, _, _, _, _, _, eF, eO, eW, _, _, _, _, _, _, _, _,
    ec⟩ := linSized_parts hB
  refine ⟨hl, t1, t2, t3, ?_⟩
  rw [eF, eO, eW]
  exact ec

/-! ## 2. What the makers of places lay as the index -/

theorem cutOn_stages {es : List Fmt.Entry} {ch i : Nat} {st : List IoppStage} {t : TestCut}
    (h : cutOn es ch i st = some t) : t.stages = st := by
  unfold cutOn at h
  dsimp only at h
  split at h
  · cases h
  · rw [← Option.some.inj h]

theorem testCutAt_stages {C : Configured} {ch i : Nat} {st : List IoppStage} {t : TestCut}
    (h : testCutAt C ch i st = some t) : t.stages = st := by
  unfold testCutAt at h
  obtain ⟨P, _, h⟩ := opt_bind h
  dsimp only at h
  replace h := opt_guard h
  rw [← Option.some.inj h]

/-- A step that refuses where there is nothing has returned: there was something. -/
theorem get_ok {α : Type} {x : Option α} {e : String} {v : α}
    (h : (match x with
      | some v => (Except.ok v : Except String α)
      | none => throw e) = .ok v) : x = some v := by
  cases x with
  | none => cases h
  | some a =>
    cases h
    rfl

theorem bind_cut {o : Option Nat} {es : List Fmt.Entry} {ch : Nat} {st : List IoppStage}
    {t : TestCut} (h : (o.bind fun i => cutOn es ch i st) = some t) : t.stages = st := by
  obtain ⟨i, _, hi⟩ := Option.bind_eq_some_iff.1 h
  exact cutOn_stages hi

/-- What placesLater lays as the index of its three places. -/
theorem later_idx (A : LaterArgs) (X : Later3) (h : placesLater A = .ok X) :
    X.U.idx = nosOf A.batch.shape.testU ∧
      (∀ o, X.O = some o → o.idx = nosOf A.batch.shape.testOmega) ∧
      X.W.idx = nosOf A.batch.shape.testOwn := by
  unfold placesLater at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals
    first
    | (cases h; done)
    | skip
  all_goals
    cases h
    have hU : ((H2U.batPlaces A.es1)[0]?.bind fun i => cutOn A.es1 1 i A.batch.shape.testU) =
        some _ := get_ok (by assumption)
    have hW : ((H2U.batPlaces A.es2)[0]?.bind fun i => cutOn A.es2 2 i A.batch.shape.testOwn) =
        some _ := get_ok (by assumption)
    refine ⟨congrArg nosOf (bind_cut hU), ?_, congrArg nosOf (bind_cut hW)⟩
    intro o ho
    first
    | (cases ho
       exact congrArg nosOf (bind_cut (by assumption)))
    | cases ho

/-- **What placesOfMade lays as the index of the proof file's four places**: the numbers of the four
tests' stages in the planner's sized record. -/
theorem places_idx (m : Made) (X : Places4) (h : placesOfMade m = .ok X) :
    X.L.idx = nosOf m.p.chains.made.sized.proof.request.last ∧
      X.U.idx = nosOf m.p.chains.made.sized.proof.batch.shape.testU ∧
      (∀ o, X.O = some o → o.idx = nosOf m.p.chains.made.sized.proof.batch.shape.testOmega) ∧
      X.W.idx = nosOf m.p.chains.made.sized.proof.batch.shape.testOwn := by
  unfold placesOfMade at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i tL hL
      split at h
      · cases h
      · rename_i X3 hX3
        split at h
        · cases h
        · cases h
          have hc : cutTestL m.p.chains.made = some tL := get_ok hL
          unfold cutTestL at hc
          obtain ⟨_, _, hc⟩ := opt_bind hc
          obtain ⟨_, _, hc⟩ := opt_bind hc
          exact ⟨congrArg nosOf (testCutAt_stages hc), later_idx _ X3 hX3⟩

/-- A place at which the block's test on the plan says yes has the index that it was made of. -/
theorem idx_of_planOk (place : Place) (x : PlaceNums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place x) : Block T12 Unit).planOk = true) :
    (proximityTestParametersAt place x).idx = x.idx := by
  unfold proximityTestParametersAt at hp ⊢
  split
  · rename_i hc
    rw [if_pos hc] at hp
    exact absurd hp (by simp [proximityTestKind, noP12])
  · rename_i hc
    rw [if_neg hc] at hp
    split
    · rfl
    · rename_i ho
      rw [ho] at hp
      exact absurd hp (by simp [proximityTestKind, noP12])

/-! ## 3. Closed: the four typed lists, numbered in a row -/

/-- The last test's stages, numbered from no codes. -/
def noL : List IoppStage × Codes := ioppStages szLFull {}

/-- Then the folded row's. -/
def noU : List IoppStage × Codes := ioppStages szUFull noL.2

/-- Then Omega's. -/
def noO : List IoppStage × Codes := ioppStages szOFull noU.2

/-- Then the request's own test's. -/
def noW : List IoppStage × Codes := ioppStages szWFull noO.2

theorem nos_LFull : nosOf noL.1 = piLFull.idx := by decide +kernel

theorem nos_UFull : nosOf noU.1 = piUFull.idx := by decide +kernel

theorem nos_OFull : nosOf noO.1 = piOFull.idx := by decide +kernel

theorem nos_WFull : nosOf noW.1 = piWFull.idx := by decide +kernel

/-- The codes after the fourth numbering are the closed lists. -/
theorem codes_full : noW.2 = codesFull := by decide +kernel

/-- A control: numbered from no codes, the folded row's stages do not get the closed place's index:
it hangs on the last test's stages. -/
theorem nos_UFull_hangs : nosOf (ioppStages szUFull {}).1 ≠ piUFull.idx := by decide +kernel

/-! ## 4. From what the planner has made -/

/-- **The four tests' numbers and the proof's codes are as at the full size**: five equations of
fields of M with closed terms. -/
structure IdxFull (M : Configured) : Prop where
  L : nosOf M.sized.proof.request.last = piLFull.idx
  U : nosOf M.sized.proof.batch.shape.testU = piUFull.idx
  O : nosOf M.sized.proof.batch.shape.testOmega = piOFull.idx
  W : nosOf M.sized.proof.batch.shape.testOwn = piWFull.idx
  codes : M.sized.proof.codes = codesFull

/-- **From configure's yes, where the sizes are the full size's and the last test's stages are the
typed list.** Of configure's yes only this is read: the proof's sizes are what proofSized returns
(configure_proof_sizes, OnBytes/Plan/PlanListsProof.lean); so the lines l are a free letter. -/
theorem idxFull_of_configure {l : Lines} {shapes : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (A : AtFull made) (hL : made.sized.proof.last.stages = szLFull)
    (hc : configure l shapes cfg bits = .ok made) : IdxFull made := by
  obtain ⟨t0, t1, t2, t3, t4⟩ := tests_of_proofSized (configure_proof_sizes hc).1
  rw [hL] at t0
  rw [hL, A.U] at t1
  rw [hL, A.U, A.O] at t2
  rw [hL, A.U, A.O, A.W] at t3 t4
  exact ⟨by rw [t0]; exact nos_LFull, by rw [t1]; exact nos_UFull, by rw [t2]; exact nos_OFull,
    by rw [t3]; exact nos_WFull, t4.trans codes_full⟩

section
variable {m : Made} (I : IdxFull m.p.chains.made) {X : Places4} (h : placesOfMade m = .ok X)
include I h

theorem idx_L_of_full : X.L.idx = piLFull.idx := (places_idx m X h).1.trans I.L

theorem idx_U_of_full : X.U.idx = piUFull.idx := (places_idx m X h).2.1.trans I.U

theorem idx_O_of_full (o : PlaceNums) (ho : X.O = some o) : o.idx = piOFull.idx :=
  ((places_idx m X h).2.2.1 o ho).trans I.O

theorem idx_W_of_full : X.W.idx = piWFull.idx := (places_idx m X h).2.2.2.trans I.W

end

end H2K.Sizes

#print axioms H2K.Sizes.tests_of_proofSized
#print axioms H2K.Sizes.places_idx
#print axioms H2K.Sizes.idx_of_planOk
#print axioms H2K.Sizes.nos_UFull_hangs
#print axioms H2K.Sizes.codes_full
#print axioms H2K.Sizes.idxFull_of_configure
#print axioms H2K.Sizes.idx_L_of_full
#print axioms H2K.Sizes.idx_U_of_full
#print axioms H2K.Sizes.idx_O_of_full
#print axioms H2K.Sizes.idx_W_of_full
