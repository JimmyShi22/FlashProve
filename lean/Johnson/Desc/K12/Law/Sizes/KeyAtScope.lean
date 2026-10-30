-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/KeyAtScope.lean: for the three later places of the proximity test in a
key file (the tests on the folded row's group, on Omega's group and on the own group): which fields
of the three places' numbers are read off the planner's sizes alone, and what they are at the full
size. Statements and proofs; no definition.

Why. The key file's description is made of the structure `Made` that `Key.madeAt X lay cfg` returns
(Johnson/Desc/Key/Road.lean) at public parameters X that are handed in. The three places' numbers
are `Key.laterPlaces m` (Johnson/Desc/Key/Places.lean). The library has the sizes of a key's blocks
at the full size as one typed value (`keyFull`, Johnson/Goal/PlanValues/KeySizedReturns.lean).
Main names.
  `atFull_of_chains`, `set_of_madeAt`: at `Key.madeAt`'s return, at public parameters as at the full
    size (`PubFull`, StageSizesAtScope.lean), the setting of all sizes is `setAt`.
  `keyTestCut_stages`, `cut_of_do`: a cut hands back the stages that it is given.
  `later_fields`: GENERAL IN m, by the text of `Key.laterPlaces`: at each of the three places seven
    fields are read off the sizes alone: the stages, the rows, the work, whether the first fold's
    mask is the test's own, THE NUMBERS OF THE STAGES' CODES, the answers, whether the masks come
    early.
  `testFirsts_trees`, `key_later_more`: the chain at each place; at the shared chain's two places
    the first tree's number is 0; the first group at the folded row's place.
  `later_of_full`: where the key's sizes are `keyFull` and the setting is `setAt`, the seven fields
    are closed terms in these two.
Who pays `later_of_full`'s first premise. Not this file. At what `Model.Verify.planned` and `madeOf`
return the library has it in scope (`key_eq_at_scope`, `made_eq_at_scope`,
Johnson/Goal/PlanValues/KeyFullAtScope.lean). At `Key.madeAt`'s return no file that this one imports
shows it: here it is a premise.
What it is not. Not said of a place: where its rounds begin, the trees of its first opening, the
roots in front, the first tree's number at the own test's place, the first group at two places, and
whether the plan has a place for Omega's test: these are read off the plans and the sendings. The
first chain's own test (on the ranges' group) is not here. Nothing says that `madeAt` or
`laterPlaces` returns at any files. No law and no bound. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Desc.Key.NoCfgLive
import Johnson.Desc.Key.Places
import OnBytes.Model.Fit.PlannedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify
open H2K.Member

/-! ## 1. The setting of all sizes -/

/-- Of what `chainsOf` returns at a public part as at the full size, at any layout file and digest:
the proof's sizes are as at the full size. -/
theorem atFull_of_chains {X : OnBytes.Model.Verify.Public} (P : PubFull X)
    {lay : Option ByteArray} {c : ByteArray} {ch : OnBytes.Model.Verify.Chains}
    (h : OnBytes.Model.Verify.chainsOf X lay c = .ok ch) : AtFull ch.made := by
  obtain ⟨_, shapes, hs, hc, _, _⟩ := OnBytes.Model.Verify.chainsOf_parts h
  obtain ⟨_, _, rl, _, _, he⟩ := OnBytes.Model.Verify.shapesOf_sub hs
  exact atFull_of_public P hc he

/-- **At what `Key.madeAt` returns: the setting of all sizes is the typed one.** -/
theorem set_of_madeAt {X : OnBytes.Model.Verify.Public} (P : PubFull X) {lay cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (h : VerifiableInference.Desc.Key.madeAt X lay cfg = .ok m) :
    m.p.chains.made.sized.set = setAt :=
  (atFull_of_chains P (VerifiableInference.Desc.Key.madeAt_chains h)).set

/-! ## 2. What the three places' numbers read of the sizes -/

/-- The cut hands back the stages that it is given. -/
theorem keyTestCut_stages {C : Configured} {ch i : ℕ} {st : List IoppStage} {t : H2U.TestCut}
    (h : VerifiableInference.Desc.Key.keyTestCut C ch i st = some t) : t.stages = st := by
  unfold VerifiableInference.Desc.Key.keyTestCut at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    rfl

/-- The same behind the choice of the batching round. -/
theorem cut_of_do {C : Configured} {ch k : ℕ} {st : List IoppStage} {t : H2U.TestCut}
    (h : (do
      let a ← VerifiableInference.Desc.Key.keyBatchRounds C ch
      let b ← a[k]?
      VerifiableInference.Desc.Key.keyTestCut C ch b st) = some t) :
    t.stages = st := by
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
  exact keyTestCut_stages h

/-- **The fields of the three later places that are read off the sizes alone**, general in m: by the
text of `Key.laterPlaces`. z := m.p.chains.made.sized.key; σ := m.p.chains.made.sized.set. -/
theorem later_fields {m : Johnson.G.OfPlan.Made} {P : VerifiableInference.Desc.Key.LaterPlaces}
    (h : VerifiableInference.Desc.Key.laterPlaces m = .ok P) :
    (P.U.nums.stages = m.p.chains.made.sized.key.once.folded.stages.map H2U.stageNums ∧
      P.U.nums.rows = m.p.chains.made.sized.key.once.shape.fold.index.answers +
        m.p.chains.made.sized.key.once.shape.fold.columns + 1 +
        2 * m.p.chains.made.sized.set.samples ∧
      P.U.nums.work = m.p.chains.made.sized.set.workOf .query
        (if m.p.chains.made.sized.key.once.lines.oneTime then .once else .shared) ∧
      P.U.nums.ownMask = !m.p.chains.made.sized.key.once.shape.masksAhead ∧
      P.U.idx = m.p.chains.made.sized.key.once.shape.testU.map (fun s => (s.code, s.maskCode)) ∧
      P.U.answers = m.p.chains.made.sized.set.samples ∧
      P.U.early = m.p.chains.made.sized.key.once.shape.choice.masksRide) ∧
    (P.W.nums.stages = m.p.chains.made.sized.key.once.own.stages.map H2U.stageNums ∧
      P.W.nums.rows = 2 + 3 * m.p.chains.made.sized.set.samples ∧
      P.W.nums.work = m.p.chains.made.sized.set.workOf .query
        (if m.p.chains.made.sized.key.once.lines.oneTime then .once else .request) ∧
      P.W.nums.ownMask = !m.p.chains.made.sized.key.once.shape.masksAhead ∧
      P.W.idx = m.p.chains.made.sized.key.once.shape.testOwn.map (fun s => (s.code, s.maskCode)) ∧
      P.W.answers = m.p.chains.made.sized.set.samples ∧
      P.W.early = m.p.chains.made.sized.key.once.shape.choice.masksRide) ∧
    ∀ nO, P.O = some nO →
      nO.nums.stages = m.p.chains.made.sized.key.once.omega.stages.map H2U.stageNums ∧
      nO.nums.rows = 1 + 2 * m.p.chains.made.sized.set.samples ∧
      nO.nums.work = m.p.chains.made.sized.set.workOf .query
        (if m.p.chains.made.sized.key.once.lines.oneTime then .once else .shared) ∧
      nO.nums.ownMask = true ∧
      nO.idx = m.p.chains.made.sized.key.once.shape.testOmega.map (fun s => (s.code, s.maskCode)) ∧
      nO.answers = m.p.chains.made.sized.set.samples ∧
      nO.early = m.p.chains.made.sized.key.once.shape.choice.masksRide := by
  unfold VerifiableInference.Desc.Key.laterPlaces at h
  obtain ⟨Fs, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨tU, hU, h⟩ := exc_bind h
  obtain ⟨tW, hW, h⟩ := exc_bind h
  obtain rfl : _ = P := Except.ok.inj h
  have eU : tU.stages = m.p.chains.made.sized.key.once.shape.testU := by
    split at hU
    · rename_i v hv
      obtain rfl : v = tU := Except.ok.inj hU
      exact cut_of_do hv
    · cases hU
  have eW : tW.stages = m.p.chains.made.sized.key.once.shape.testOwn := by
    split at hW
    · rename_i v hv
      obtain rfl : v = tW := Except.ok.inj hW
      exact cut_of_do hv
    · cases hW
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩, ?_⟩
  · show tU.stages.map _ = _
    rw [eU]
  · show tW.stages.map _ = _
    rw [eW]
  · intro nO hO
    dsimp only at hO
    split at hO
    · rename_i tO fO hv _
      obtain rfl := Option.some.inj hO
      refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
      show tO.stages.map _ = _
      rw [cut_of_do hv]
    · cases hO

/-- What `testFirsts` says of the first tree's number at the two places of the shared chain. -/
theorem testFirsts_trees {m : Johnson.G.OfPlan.Made} {Fs : VerifiableInference.Desc.Key.TestFirsts}
    (h : VerifiableInference.Desc.Key.testFirsts m = .ok Fs) :
    Fs.U.2 = 0 ∧ ∀ fO, Fs.O = some fO → fO.2 = 0 := by
  unfold VerifiableInference.Desc.Key.testFirsts at h
  obtain ⟨t0, _, h⟩ := exc_bind h
  obtain ⟨t1, _, h⟩ := exc_bind h
  obtain ⟨t2, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨u, _, h⟩ := exc_bind h
  obtain ⟨w, _, h⟩ := exc_bind h
  obtain rfl : _ = Fs := Except.ok.inj h
  refine ⟨rfl, fun fO hO => ?_⟩
  dsimp only at hO
  split at hO
  · obtain ⟨x, _, e⟩ := Option.map_eq_some_iff.1 hO
    rw [← e]
  · cases hO

/-- **Four fields more**: the chain, and at the shared chain's two places the first tree's number.
-/
theorem key_later_more {m : Johnson.G.OfPlan.Made} {P : VerifiableInference.Desc.Key.LaterPlaces}
    (h : VerifiableInference.Desc.Key.laterPlaces m = .ok P) :
    (P.U.chain = 2 ∧ P.U.nums.firstTree = 0 ∧ P.U.firstGroup = 2) ∧ P.W.chain = 3 ∧
      ∀ nO, P.O = some nO → nO.chain = 2 ∧ nO.nums.firstTree = 0 := by
  unfold VerifiableInference.Desc.Key.laterPlaces at h
  obtain ⟨Fs, hF, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨tU, _, h⟩ := exc_bind h
  obtain ⟨tW, _, h⟩ := exc_bind h
  obtain rfl : _ = P := Except.ok.inj h
  obtain ⟨f1, f2⟩ := testFirsts_trees hF
  refine ⟨⟨rfl, f1, rfl⟩, rfl, fun nO hO => ?_⟩
  dsimp only at hO
  split at hO
  · rename_i tO fO _ hf
    obtain rfl := Option.some.inj hO
    exact ⟨rfl, f2 fO hf⟩
  · cases hO

/-! ## 3. At the full size -/

/-- **So at the full size these fields are closed terms**: in the typed sizes of a key and the typed
setting. -/
theorem later_of_full {m : Johnson.G.OfPlan.Made} {P : VerifiableInference.Desc.Key.LaterPlaces}
    (hk : m.p.chains.made.sized.key = Lk6.AtPlan.keyFull) (hset : m.p.chains.made.sized.set = setAt)
    (h : VerifiableInference.Desc.Key.laterPlaces m = .ok P) :
    (P.U.nums.stages = Lk6.AtPlan.keyFull.once.folded.stages.map H2U.stageNums ∧
      P.U.nums.rows = Lk6.AtPlan.keyFull.once.shape.fold.index.answers +
        Lk6.AtPlan.keyFull.once.shape.fold.columns + 1 +
        2 * setAt.samples ∧
      P.U.nums.work = setAt.workOf .query
        (if Lk6.AtPlan.keyFull.once.lines.oneTime then .once else .shared) ∧
      P.U.nums.ownMask = !Lk6.AtPlan.keyFull.once.shape.masksAhead ∧
      P.U.idx = Lk6.AtPlan.keyFull.once.shape.testU.map (fun s => (s.code, s.maskCode)) ∧
      P.U.answers = setAt.samples ∧
      P.U.early = Lk6.AtPlan.keyFull.once.shape.choice.masksRide) ∧
    (P.W.nums.stages = Lk6.AtPlan.keyFull.once.own.stages.map H2U.stageNums ∧
      P.W.nums.rows = 2 + 3 * setAt.samples ∧
      P.W.nums.work = setAt.workOf .query
        (if Lk6.AtPlan.keyFull.once.lines.oneTime then .once else .request) ∧
      P.W.nums.ownMask = !Lk6.AtPlan.keyFull.once.shape.masksAhead ∧
      P.W.idx = Lk6.AtPlan.keyFull.once.shape.testOwn.map (fun s => (s.code, s.maskCode)) ∧
      P.W.answers = setAt.samples ∧
      P.W.early = Lk6.AtPlan.keyFull.once.shape.choice.masksRide) ∧
    ∀ nO, P.O = some nO →
      nO.nums.stages = Lk6.AtPlan.keyFull.once.omega.stages.map H2U.stageNums ∧
      nO.nums.rows = 1 + 2 * setAt.samples ∧
      nO.nums.work = setAt.workOf .query
        (if Lk6.AtPlan.keyFull.once.lines.oneTime then .once else .shared) ∧
      nO.nums.ownMask = true ∧
      nO.idx = Lk6.AtPlan.keyFull.once.shape.testOmega.map (fun s => (s.code, s.maskCode)) ∧
      nO.answers = setAt.samples ∧
      nO.early = Lk6.AtPlan.keyFull.once.shape.choice.masksRide := by
  have e := later_fields h
  rw [hk, hset] at e
  exact e


end H2K.Sizes

#print axioms H2K.Sizes.atFull_of_chains
#print axioms H2K.Sizes.set_of_madeAt
#print axioms H2K.Sizes.later_fields
#print axioms H2K.Sizes.key_later_more
#print axioms H2K.Sizes.later_of_full
