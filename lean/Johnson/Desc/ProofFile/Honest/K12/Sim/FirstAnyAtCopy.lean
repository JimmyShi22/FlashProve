-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstAnyAtCopy.lean: `any_at_place`
(Sim/FirstAnyAtPlace.lean) at the place at which the description of a copy's file (the entry file,
which holds the link proof) seats its proximity test: at every job at that place, for all public
files in the goals' scope, and so at the goals' two named sets.

What is stated. First what plays the head's part: the verifier's decision on the copy's file is the
run of one written description, `copyDesc`, at the keys written of the two records; that
description passes its tests on the plan. Then the first stage's number of fold rounds at the seated
place; that there is a job and a simulators' job of the sort spoken of, at all types (made-up ones:
Sim/FirstAnyWitness.lean); and for every job J at the place which says that the first fold's fresh
table has come earlier, and every simulators' job with the same two public letters: all that
`any_at_place` concludes, at the description's own list of sub-protocols and at a written list of
challenges, with the count of scalars as a conjunct. Nothing stands under "there is" in front: the
description and the place are closed terms.

  `copyDesc`     the description: `Desc.K15.linkDescriptionAt` at the typed parameters `frP`
                 (Johnson/Desc/Link/LinkDesc.lean, LinkWritten.lean; Johnson/Desc/K15/TypedP.lean)
  `pCopy`        the seated place: `Desc.K15.p12Of frP` (Johnson/Desc/K15/HsemSays.lean)
  `dsCopy`       a list of challenges, written by hand: each is one field element, the same one
  `k_copy`, `facts_copy`   the first stage's number of fold rounds; the seven public tests
                 `PlaceFacts` at the seated place itself: six evaluated by Lean's kernel, the
                 block's test on the plan from the library's `planOk_full`
  `place_copy`, `six_off`, `find_copy`   the place's address; none of the six sub-protocols in
                 front of the test stands at it (kernel); so the first sub-protocol of the list at
                 that address is the test's, with the declared rounds and oracle messages of the
                 test's own block
  `named_in_scope`   both named sets are in scope
  `first_any_in_scope_copy`, `first_any_at_named_copy`   the statements

By what. `K15_sits_keys` (Johnson/Goal/Conditions/EntrySits.lean), `planOk_full`
(Johnson/Desc/Link/LinkWrittenMade.lean), `test_planOk` (Johnson/Desc/K15/HsemOf.lean),
`descV_planOk` (Johnson/Desc/K15/SendOwnLaw.lean), `flat_split`
(Johnson/Prover/Link/FormWalks.lean), `place_of_k12`, `place_of_p12At`
(Johnson/Desc/K12/Law/SharedPlaces.lean), `inScope_full`, `inScope_gap`
(Johnson/Goal/Files/ScopeExample.lean), `job_there`, `sims_there` (Sim/FirstAnyWitness.lean).
`maxRecDepth` is raised at the evaluations, as at the other places.

Limits.
- The frame's run (Johnson/Desc/ProofFile/Honest/Frame.lean) plays a description of three chains.
  This description has one chain, and its form as a description of three chains
  (`OneChainFileDescription.asFile`, Johnson/Desc/Link/OneChainFileDescription.lean) is never run. So there is no play by which a
  state of a run could be reached here.
- The library holds a statement on the whole link protocol, this test within it, in its own frame
  (Johnson/LinkSim/), with a prover and a simulator written out. This file's sentence is on a part
  of that protocol, in another frame. Nothing here relates the two.
- No job is typed at the place. "At every job at the place" says nothing on whether any job there is
  the prover's. The job that is shown to be there is made up: empty state, rows 0, no tree. Who owns
  the fresh table that came earlier is not named: the job's field is any address.
- The link proof is the committer's, made once for each copy (Johnson/LinkSim/Spec.lean's head). The
  frame's two ways of giving a side its input (`Face`) take inputs of the forms `Local` and
  `Common`, which Frame.lean writes for the prover of a file of three chains.
- The typed parameters `frP` were copied by a program out of a print (TypedP.lean's limits). The
  description's plan is its own blocks' declared rounds; only their entries are held against the
  written plan (`linkRoundsMatchPlan`, LinkWritten.lean's head).
- The full size alone: at the smaller written lines the decision says no to all. There is no
  negative test at this place.
- All limits of Sim/FirstAnyAtPlace.lean stand; among them: the state on entry is any function; the
  parts of `proverSideOfProximityTest`, not the guarded halves; the spender's half; the front lists no column and no
  root; one list of challenges, written by hand; the first member alone: it is not the frame's field
  `exact` at that side, which speaks of every member; "every job" takes in jobs of which the
  sentence says nothing of any run, and no book is asked. `testOn` and `testBud` ask nothing at the
  first member.
- No file of this folder states a security property by itself. Nothing on completeness, soundness or
  hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyWitness
import Johnson.Goal.Conditions.EntrySits
import Johnson.Goal.Files.ScopeExample
import Johnson.Prover.Link.FormWalks
import Johnson.Desc.K15.HsemOf
import Johnson.Desc.K15.SendOwnLaw
import Johnson.Desc.K12.Law.SharedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block OneChainFileDescription)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (laidOf)
open ProofFile.Honest.Small (ExactMember)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (linkDecisionAtFiles)
open _root_.Desc.K15 (St frP p12Of linkDescriptionAt linkDeclaredRounds linkRoundsMatchPlan linkProtocolChain testBlock frontBlock blocksOrV)
open OnBytes (TableKey)
open OnBytes.Params (recordPlan)
open OnBytes.Slice (keyOf NZ)

/-! ## 1 The description, the place, a written list of challenges -/

/-- The copy's file's description, at the typed parameters. -/
def copyDesc : OneChainFileDescription (TableKey × TableKey) := linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)

/-- The place at which it seats its proximity test. -/
def pCopy : P12 := p12Of frP

/-- Ten challenges, each of one field element. -/
def dsCopy : List Fmt.Drawn := List.replicate 10 ⟨[(1, 0, 0)], [], [], none⟩

/-! ## 2 The public tests, at the seated place itself -/

set_option maxRecDepth 100000 in
theorem k_copy : (pCopy.nums.stages.headD default).k = 8 := by decide +kernel

theorem plan_copy : (proximityTestKind guardedProximityTestParts pCopy : Block T12 Unit).planOk = true :=
  _root_.Desc.K15.test_planOk frP _ _
    (_root_.Desc.K15.descV_planOk frP _ _ _root_.Desc.K15.planOk_full)

set_option maxRecDepth 100000 in
theorem form_copy : formPubB pCopy = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem enough_copy : firstLen pCopy.nums.stages ≤ (laidOf pCopy).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tab_copy : tabB pCopy false = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem count_copy :
    (laidOf pCopy).length = firstLen pCopy.nums.stages + restLen pCopy.nums.stages := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem quiet_copy :
    quietB (((laidOf pCopy).take (firstLen pCopy.nums.stages)).map (·.1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem draws_copy :
    drawsFit (((laidOf pCopy).take (firstLen pCopy.nums.stages)).map (·.1)) dsCopy = true := by
  decide +kernel

theorem facts_copy : PlaceFacts pCopy dsCopy :=
  ⟨plan_copy, form_copy, enough_copy, tab_copy, count_copy, quiet_copy, draws_copy⟩

/-! ## 3 The test's sub-protocol in the description's list -/

theorem place_copy : pCopy.place = ⟨1, none, 6, .K12⟩ := by
  unfold pCopy p12Of
  cases _root_.Desc.K15.numsOf frP with
  | none => rfl
  | some x => exact H2K.JointK.place_of_p12At _ x

set_option maxRecDepth 100000 in
/-- None of the six sub-protocols in front of the test stands at the test's place. -/
theorem six_off :
    ((frontBlock frP :: blocksOrV frP).all fun b => b.place != ⟨1, none, 6, .K12⟩) = true := by
  decide +kernel

/-- The first sub-protocol of the description's list at the test's place. -/
theorem find_copy :
    ∃ b : Block St Unit,
      (copyDesc.chain.blocksInOrder.find? fun b => b.place == pCopy.place) = some b ∧
      b.place = pCopy.place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts pCopy : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts pCopy : Block T12 Unit).oracles := by
  have hb : (testBlock frP).place = pCopy.place := H2K.JointK.place_of_k12 guardedProximityTestParts pCopy
  refine ⟨{ testBlock frP with planOk := (testBlock frP).planOk && (testBlock frP).hasNoClaimsAndNothingAfter }, ?_, hb,
    rfl, rfl⟩
  have h0 : ((frontBlock frP :: blocksOrV frP).map
      (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter })).find?
      (fun b => b.place == pCopy.place) = none := by
    rw [List.find?_eq_none]
    intro b hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
    have h := List.all_eq_true.1 six_off a ha
    rw [place_copy]
    simpa using h
  show ((linkProtocolChain frP).blocksInOrder.find? fun b => b.place == pCopy.place) = _
  rw [Johnson.Prover.Link.flat_split, List.find?_append, h0]
  simp [hb]

/-! ## 4 The statements -/

local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **For all public files in scope, what plays the head's part first: at every job at the place of
the copy's file's proximity test.** -/
theorem first_any_in_scope_copy (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.InScope Z = true) :
    linkDecisionAtFiles (asDescriptionFiles Z) = (fun rr V => copyDesc.run
                          (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) V) ∧
    copyDesc.planOk = true ∧
    (pCopy.nums.stages.headD default).k = 8 ∧
    (∀ W X Pb : Type, (∃ J : TestJob W X, J.p = pCopy ∧ J.fresh.isNone = false) ∧
      ∃ Js : SimJob Pb, Js.p = pCopy ∧ Js.own = false) ∧
    ∀ (V W X Pb : Type) (J : TestJob W X) (Js : SimJob Pb),
      J.p = pCopy → J.fresh.isNone = false → Js.p = pCopy → Js.own = false →
      FirstPub J Js ∧
      (∀ fs : List (Fall St), ∃ σ : Side St Unit V W X Pb,
        testSide copyDesc.chain.blocksInOrder J Js fs = some σ) ∧
      ∀ (fs : List (Fall St)) (σ : Side St Unit V W X Pb),
        testSide copyDesc.chain.blocksInOrder J Js fs = some σ →
        σ.fits = true ∧
        σ.members = [firstMember J Js, restMember J Js] ∧
        (∀ (φ : Face V W Pb) (chain firstTree : ℕ), ExactMember φ σ chain firstTree
          (testOn φ J Js) (testBud Js) (firstMember J Js)) ∧
        firstMember J Js ∈ σ.members ∧
        ∀ (φ : Face V W Pb) (chain firstTree : ℕ)
          (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
          (asks : List (List (List ℕ))),
          testOn φ J Js (firstMember J Js) ca m (bareFront chain m) ∧
          m.seen = (bareFront chain m).seen ∧
          drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) dsCopy = true ∧
          testBud Js (firstMember (V := V) J Js).number dsCopy asks ∧
          (bareFront chain m).holds chain firstTree ((firstMember (V := V) J Js).rounds.map (·.1))
            dsCopy = true ∧
          (firstMember J Js).part.stopAt (φ.sees m.st.input) m.loc dsCopy ≠ some .hid ∧
          (∀ c, ∃ l, σ.shows φ (firstMember J Js) c m dsCopy asks = some l ∧ scalars l = 17 ∧
            columns l = 0) ∧
          (Prob.unif (Cs (firstMember (V := V) J Js).part.takes ×
              CsAll (firstMember (V := V) J Js).part.spends)).map
              (fun c => σ.shows φ (firstMember J Js) (c.1, c.2, ca) m dsCopy asks) =
            (Prob.unif (Cs (firstMember (V := V) J Js).sim.takes)).map fun c =>
              (firstMember J Js).tells φ c m.st.input (bareFront chain m) dsCopy asks := by
  refine ⟨FlashProve.K15_sits_keys hZ, _root_.Desc.K15.planOk_full, k_copy,
    fun W X Pb => ⟨job_there W X pCopy, sims_there Pb pCopy⟩, fun V W X Pb J Js hJ hfr hs ho => ?_⟩
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_copy
  obtain ⟨a1, a2, a3⟩ := any_at_place (V := V) J Js (hJ ▸ facts_copy) _ b (by rw [hJ]; exact hf)
    (by rw [hJ]; exact hpl) (by rw [hJ]; exact hr) (by rw [hJ]; exact hor) hfr (hs.trans hJ.symm)
    ho
  refine ⟨a1, a2, fun fs σ hσ => ?_⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := a3 fs σ hσ
  refine ⟨b1, b2, b3, b4, fun φ chain firstTree ca m asks => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := b5 φ chain firstTree ca m asks
  refine ⟨c1, c2, c3, c4, c5, c6, fun c => ?_, c8⟩
  obtain ⟨l, l1, l2, l3⟩ := c7 c
  refine ⟨l, l1, ?_, l3⟩
  have e : J.s₀.k = 8 := by
    show (J.p.nums.stages.headD default).k = 8
    rw [hJ]
    exact k_copy
  rw [l2, e]

/-- Both named sets of public files are in scope. -/
theorem named_in_scope (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) : VerifierAndGoals.InScope Z = true := by
  rcases hZ with rfl | rfl
  · exact VerifierAndGoals.inScope_full
  · exact VerifierAndGoals.inScope_gap

/-- **At either named set of public files: the same.** -/
theorem first_any_at_named_copy (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) :
    linkDecisionAtFiles (asDescriptionFiles Z) = (fun rr V => copyDesc.run
                          (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) V) ∧
    copyDesc.planOk = true ∧
    (pCopy.nums.stages.headD default).k = 8 ∧
    (∀ W X Pb : Type, (∃ J : TestJob W X, J.p = pCopy ∧ J.fresh.isNone = false) ∧
      ∃ Js : SimJob Pb, Js.p = pCopy ∧ Js.own = false) ∧
    ∀ (V W X Pb : Type) (J : TestJob W X) (Js : SimJob Pb),
      J.p = pCopy → J.fresh.isNone = false → Js.p = pCopy → Js.own = false →
      FirstPub J Js ∧
      (∀ fs : List (Fall St), ∃ σ : Side St Unit V W X Pb,
        testSide copyDesc.chain.blocksInOrder J Js fs = some σ) ∧
      ∀ (fs : List (Fall St)) (σ : Side St Unit V W X Pb),
        testSide copyDesc.chain.blocksInOrder J Js fs = some σ →
        σ.fits = true ∧
        σ.members = [firstMember J Js, restMember J Js] ∧
        (∀ (φ : Face V W Pb) (chain firstTree : ℕ), ExactMember φ σ chain firstTree
          (testOn φ J Js) (testBud Js) (firstMember J Js)) ∧
        firstMember J Js ∈ σ.members ∧
        ∀ (φ : Face V W Pb) (chain firstTree : ℕ)
          (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
          (asks : List (List (List ℕ))),
          testOn φ J Js (firstMember J Js) ca m (bareFront chain m) ∧
          m.seen = (bareFront chain m).seen ∧
          drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) dsCopy = true ∧
          testBud Js (firstMember (V := V) J Js).number dsCopy asks ∧
          (bareFront chain m).holds chain firstTree ((firstMember (V := V) J Js).rounds.map (·.1))
            dsCopy = true ∧
          (firstMember J Js).part.stopAt (φ.sees m.st.input) m.loc dsCopy ≠ some .hid ∧
          (∀ c, ∃ l, σ.shows φ (firstMember J Js) c m dsCopy asks = some l ∧ scalars l = 17 ∧
            columns l = 0) ∧
          (Prob.unif (Cs (firstMember (V := V) J Js).part.takes ×
              CsAll (firstMember (V := V) J Js).part.spends)).map
              (fun c => σ.shows φ (firstMember J Js) (c.1, c.2, ca) m dsCopy asks) =
            (Prob.unif (Cs (firstMember (V := V) J Js).sim.takes)).map fun c =>
              (firstMember J Js).tells φ c m.st.input (bareFront chain m) dsCopy asks :=
  first_any_in_scope_copy Z (named_in_scope Z hZ)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.copyDesc
#print axioms ProofFile.Honest.K12.Light.pCopy
#print axioms ProofFile.Honest.K12.Light.dsCopy
#print axioms ProofFile.Honest.K12.Light.k_copy
#print axioms ProofFile.Honest.K12.Light.plan_copy
#print axioms ProofFile.Honest.K12.Light.form_copy
#print axioms ProofFile.Honest.K12.Light.enough_copy
#print axioms ProofFile.Honest.K12.Light.tab_copy
#print axioms ProofFile.Honest.K12.Light.count_copy
#print axioms ProofFile.Honest.K12.Light.quiet_copy
#print axioms ProofFile.Honest.K12.Light.draws_copy
#print axioms ProofFile.Honest.K12.Light.facts_copy
#print axioms ProofFile.Honest.K12.Light.place_copy
#print axioms ProofFile.Honest.K12.Light.six_off
#print axioms ProofFile.Honest.K12.Light.find_copy
#print axioms ProofFile.Honest.K12.Light.first_any_in_scope_copy
#print axioms ProofFile.Honest.K12.Light.named_in_scope
#print axioms ProofFile.Honest.K12.Light.first_any_at_named_copy
