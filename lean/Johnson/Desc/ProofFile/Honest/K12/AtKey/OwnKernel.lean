-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnKernel.lean: the public lines at the key file's own test, BY
THE KERNEL's OWN EVALUATION (`decide +kernel`): what OwnGuards.lean asks the evaluator first.

  `plan_own`     the test on the plan (`planPlaysB`): no tree sent in front, the fresh table come
                 earlier. `plan_own_fresh`, `plan_own_one`: controls: the other word on the fresh table;
                 one tree in front
  `form_own`     the test for `FormPub` (`formPubB`)
  `stages_own`   two stages or more; k = h + g at the first
  `early_own`    the masks are sent ahead
  `planPlays_own`   so `PlanPlays` at every job at the place whose fresh table has come earlier
  `planB_own`    the plan's half at three trees, at the key's codes
  `depths_own`, `opens_own`   the trees' depths; the declared openings are the term's, at the three sources
                 taken over and no tree sent in front. `opens_own_depth`, `opens_own_sent`: controls
  `toTest`, `lineB`   the test's own shape of the last chain's shape; the lines on it as one Bool: the statement
                 is tidy; `frontFiveB`; `manyFitsS`; three trees; the group is there and has not begun
  `membersB`, `omegaB`   the own group's three members by number; Omega is sampled behind the shared chain's
                 ninth block
  `closedB`, `closed_own`, `own_closed`   the run on shapes from the chain's first shape over the first two
                 blocks returns, and the lines hold behind it
  `closed_bent`  control: at the next group the lines do not hold
  `lines_of_line`, `tidy_of_line`, `group_of_line`   what `lineB` says
  `msgB`, `msg_own`, `idx_own`   W's message holds two notices, the first sampled; the index masks' has an answer
  `written_own`  the chain's numbers of the test at the written later places are the written place

Limits. It reads the plan alone: no run, no half, no job of the key. That the chain has sent no tree in
front of the test is OwnSeat.lean's `trees_own`. `piKWFull` is a written place: that a file's place
is this one is not said here. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnLinesGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc.K12
open H2K.Member (piKWFull)
open H2K.Pub (sgOf)
open ProofFile.Honest.Sh (TestSh thinOf)
open ProofFile.Honest.K12.Light (manyFitsS tsLenOf)
open ProofFile.Honest.K12.AtProof (treesW placeW)
open AtPublicFiles.AtFiles (Sh₃ ZW CF)
open AtPublicFiles.AtFiles.Full (X0 PF V9 V12)
open AtPublicFiles.KeyLay (pWK)

variable {W X : Type}

/-- The test on the plan at the own test. -/
theorem plan_own : planPlaysB piKWFull false 0 = true := by decide +kernel

/-- Control: the other word on the fresh table. -/
theorem plan_own_fresh : planPlaysB piKWFull true 0 = false := by decide +kernel

/-- Control: one tree in front. -/
theorem plan_own_one : planPlaysB piKWFull false 1 = false := by decide +kernel

/-- The test for `FormPub`. -/
theorem form_own : formPubB piKWFull = true := by decide +kernel

/-- The masks are sent ahead. -/
theorem early_own : piKWFull.early = true := by decide +kernel

/-- Two stages or more, and k = h + g at the first. -/
theorem stages_own : ∃ s t rest, piKWFull.nums.stages = s :: t :: rest ∧
    s.k = (sgOf s).h + (sgOf s).g := by
  have h2 : 2 ≤ piKWFull.nums.stages.length := by decide +kernel
  have hk : (piKWFull.nums.stages.headD default).k =
      (sgOf (piKWFull.nums.stages.headD default)).h +
        (sgOf (piKWFull.nums.stages.headD default)).g := by decide +kernel
  cases hh : piKWFull.nums.stages with
  | nil =>
    rw [hh] at h2
    simp at h2
  | cons a l =>
    cases l with
    | nil =>
      rw [hh] at h2
      simp at h2
    | cons b r =>
      rw [hh] at hk
      exact ⟨a, b, r, rfl, hk⟩

/-- **`PlanPlays` at every job at the place whose fresh table has come earlier.** -/
theorem planPlays_own (J : TestJob W X) (hJ : J.p = piKWFull) (hfr : J.fresh.isNone = false)
    (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: rest) :
    PlanPlays J s rest 0 :=
  planPlays_of_B J s rest hst 0 (by
    rw [hJ, hfr]
    exact plan_own)

/-- The plan's half at three trees, at the key's codes. -/
theorem planB_own : planB piKWFull CF 3 = true := by decide +kernel

/-- The trees' depths. -/
theorem depths_own : (treesW piKWFull).map (·.1) = [13, 22, 22] := by decide +kernel

/-- The declared openings are the term's. -/
theorem opens_own : opensOwn [13, 22, 22] takenOwn 0 = true := by decide +kernel

/-- Control: another order of the depths. -/
theorem opens_own_depth : opensOwn [22, 13, 22] takenOwn 0 = false := by decide +kernel

/-- Control: one tree sent in front. -/
theorem opens_own_sent : opensOwn [13, 22, 22] takenOwn 1 = false := by decide +kernel

/-- The test's own shape of the last chain's shape. -/
def toTest (a : Sh₃) : TestSh := ⟨a.1, a.2.own, .nothing, a.2.mask⟩

/-- **The lines on the shape in front of the test.** -/
def lineB (a : Sh₃) : Bool :=
  a.2.tidy && frontFiveB piKWFull CF (toTest a) &&
    manyFitsS piKWFull msOwn (treesW piKWFull) (thinOf (toTest a)) &&
    decide (tsLenOf piKWFull (thinOf (toTest a)) = 3) &&
    ((toTest a).core.st.groups[(toTest a).g]?).any fun G => !G.inRun

/-- The own group's members: message 0, the last message but one of the first chain, Omega's copy. -/
def membersB (a b : Sh₃) : Bool :=
  ((toTest b).core.st.groups[(toTest b).g]?).any fun G =>
    G.members == [0, a.1.st.oracles.length - 2, a.1.st.oracles.length]

/-- Omega is sampled behind the shared chain's ninth block. -/
def omegaB : Bool :=
  (V9.1.core.st.oracles[(AtPublicFiles.AtFiles.sharedOf V12).omega]?).any (·.sampled)

/-- The run from the chain's first shape over the first two blocks, and the lines behind it. -/
def closedB : Bool :=
  match X0 with
  | some a =>
    match ZW.run 2 a with
    | .ok b => lineB b && membersB a b && omegaB
    | .error _ => false
  | none => false

/-- **The lines hold.** By the kernel. -/
theorem closed_own : closedB = true := by decide +kernel

/-- Control: at the next group the lines do not hold. -/
theorem closed_bent : (shapeAtOwn.map fun a => lineB (a.1, { a.2 with own := a.2.own + 1 })) =
    some false := by decide +kernel

/-- **The terms.** -/
theorem own_closed : ∃ A₀ A₂ : Sh₃, X0 = some A₀ ∧ ZW.run 2 A₀ = .ok A₂ ∧ lineB A₂ = true ∧
    membersB A₀ A₂ = true ∧ omegaB = true := by
  have h := closed_own
  unfold closedB at h
  cases h₀ : X0 with
  | none =>
    rw [h₀] at h
    cases h
  | some a =>
    rw [h₀] at h
    have h' : (match ZW.run 2 a with
      | .ok b => lineB b && membersB a b && omegaB
      | .error _ => false) = true := h
    cases h₂ : ZW.run 2 a with
    | error e =>
      rw [h₂] at h'
      cases h'
    | ok b =>
      rw [h₂] at h'
      have h'' : (lineB b && membersB a b && omegaB) = true := h'
      simp only [Bool.and_eq_true] at h''
      exact ⟨a, b, rfl, h₂, h''.1.1, h''.1.2, h''.2⟩

theorem lines_of_line {a : Sh₃} (h : lineB a = true) :
    (frontFiveB piKWFull CF (toTest a) &&
      manyFitsS piKWFull msOwn (treesW piKWFull) (thinOf (toTest a)) &&
      decide (tsLenOf piKWFull (thinOf (toTest a)) = 3)) = true := by
  unfold lineB at h
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1.1.2, h.1.1.2⟩, h.1.2⟩

theorem tidy_of_line {a : Sh₃} (h : lineB a = true) : a.2.tidy = true := by
  unfold lineB at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem group_of_line {a : Sh₃} (h : lineB a = true) :
    ∃ G, (toTest a).core.st.groups[(toTest a).g]? = some G ∧ G.inRun = false := by
  unfold lineB at h
  simp only [Bool.and_eq_true] at h
  have h' := h.2
  cases hG : (toTest a).core.st.groups[(toTest a).g]? with
  | none =>
    rw [hG] at h'
    cases h'
  | some G =>
    rw [hG] at h'
    have e : (!G.inRun) = true := h'
    exact ⟨G, rfl, by simpa using e⟩

/-- W's message at the written shape: two notices, the first sampled. -/
def msgB : Bool :=
  (OnBytes.linMessageW AtPublicFiles.AtFiles.SF).any fun m =>
    m.size == 2 && (m.toList.head?.any fun n => n.shape.answers != 0)

/-- By the kernel. -/
theorem msg_own : msgB = true := by decide +kernel

/-- The index masks' message has an answer. By the kernel. -/
theorem idx_own : Lk6.AtPlan.keyFull.once.input.shape.answers ≠ 0 := by decide +kernel

/-- The chain's numbers of the test at the written later places are the written place. -/
theorem written_own : pWK PF = piKWFull := by
  first
    | decide +kernel
    | rfl

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.plan_own
#print axioms ProofFile.Honest.K12.AtKey.plan_own_fresh
#print axioms ProofFile.Honest.K12.AtKey.plan_own_one
#print axioms ProofFile.Honest.K12.AtKey.form_own
#print axioms ProofFile.Honest.K12.AtKey.early_own
#print axioms ProofFile.Honest.K12.AtKey.stages_own
#print axioms ProofFile.Honest.K12.AtKey.planPlays_own
#print axioms ProofFile.Honest.K12.AtKey.planB_own
#print axioms ProofFile.Honest.K12.AtKey.depths_own
#print axioms ProofFile.Honest.K12.AtKey.opens_own
#print axioms ProofFile.Honest.K12.AtKey.opens_own_depth
#print axioms ProofFile.Honest.K12.AtKey.opens_own_sent
#print axioms ProofFile.Honest.K12.AtKey.closed_own
#print axioms ProofFile.Honest.K12.AtKey.closed_bent
#print axioms ProofFile.Honest.K12.AtKey.own_closed
#print axioms ProofFile.Honest.K12.AtKey.lines_of_line
#print axioms ProofFile.Honest.K12.AtKey.tidy_of_line
#print axioms ProofFile.Honest.K12.AtKey.group_of_line
#print axioms ProofFile.Honest.K12.AtKey.msg_own
#print axioms ProofFile.Honest.K12.AtKey.idx_own
#print axioms ProofFile.Honest.K12.AtKey.written_own
