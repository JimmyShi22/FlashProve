-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/OwnAnyAtPlace.lean: the first member of a proximity test whose
first fold sends its own fresh table, at every job at a place. General in the place, in the list of
sub-protocols and in the job. It is Sim/FirstAnyAtPlace.lean at the other case of the first fold,
with the record `MeetsAt` of Sim/MeetsOwnAtHead.lean. It imports Mathlib.

What is stated. Let a place pass nine public tests (`PlaceFactsOwn`), and let the first sub-protocol
of a list that stands at the place have the declared rounds and oracle messages of the test's own
block. Then for every job J at that place which says that the fold sends its own table, and every
simulators' job with the same two public values: `FirstPubOwn` (Sim/ExactFirstOwn.lean) holds;
`testSide` (Sim/Row.lean) returns a side off the list, at all falls; whatever side it returns passes
`Side.fits` and has just the two members that are written out; the frame's sentence `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean) holds at the first, at `testOn` and `testBud`; and
at every state of a run, at the front made of it, at the written challenges and at every list of
positions that passes `budFirst`: `MeetsAt`: the sentence's six hypotheses, that what the member
shows is something, and the equation.

  `PlaceFactsOwn`   the nine tests: a record of premises, defined here; lemmas conclude it
                 (`facts_KO`, Sim/KeyPlaceFactsOwn.lean), no top statement does; all nine are
                 Booleans or numbers on the place and the written list
  `firstPubOwn_any`   `FirstPubOwn` at every such job
  `madeJobOwn`, `madeSimsOwn`, `job_there_own`, `sims_there_own`   there is such a job, and such a
                 simulators' job, at every place and all types: made-up ones (empty state, rows 0,
                 no tree)
  `own_at_place`   the statement

By what. `exact_first_job` (Sim/ExactFirstOwn.lean), `exact_bud`, `budBoth_of_testBud`
(Sim/FirstPubOwnAtHead.lean), `meetsAt_of_exact`, `testBud_own` (Sim/MeetsOwnAtHead.lean),
`members_of_seat` (Sim/ExactSide.lean), `fits_of` (Sim/FirstSeatAtHead.lean), `zip_laid`
(PlaysK12.lean), `shows_first` (Sim/ShowsFirst.lean), `formPub_of_B` (FormPubAt.lean),
`tablesFitB_eq` (Sim/FirstPubAtHead.lean), and `testOn_first`, `seen_bareFront`, `holds_of_quiet`,
`stop_first` (Sim/MeetsAtHead.lean).

Limits.
- "At every job at the place" says nothing on whether any job there is the prover's. Nor does it
  settle the state on entry: every job's `rec₀` is handed no opened column (the limits of
  Test.lean).
- The bound `budFirst` (Sim/Row.lean) is a premise that is spent: every asked position lies below 2
  ^ Z.a, and at most Z.r different ones are asked. It is shown at no list of positions that the
  frame lays: which rounds of a file read the fold's own tree is not treated here.
- The state of a run is any: none is shown to be one that a play reaches. The front lists no column
  and no root; it could not serve the test's second member.
- It is shown at no job that is played. It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of
  halves with a guard in front.
- The parts and their random values are defined in Test.lean, Parts.lean and Coins.lean of
  Johnson/Desc/ProofFile/Honest/K12/. What the parts send is that folder's own `testAll`; how far it
  is tied to the library's `bodyAll` (Johnson/Prover/Link/BodyAll.lean) is said in the limits of
  Test.lean.
- The part's own values are sampled anew in the equation. `restPart` (Parts.lean) states a carried
  run for the whole fresh table; nothing here says that a book deals the first part's own values to
  it, and nothing here joins the two members.
- The first member alone. It is not the frame's field `exact` at the side, which speaks of every
  member.
- No file of this folder states a security property by itself. Nothing on completeness, soundness or
  hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsOwnAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (laidOf)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-! ## 1 The public tests on a place -/

/-- **Nine public tests on a place whose first fold sends its own table.** ds: a written list of
challenges. -/
structure PlaceFactsOwn (p : P12) (ds : List Fmt.Drawn) : Prop where
  plan : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true
  form : formPubB p = true
  enough : firstLen p.nums.stages ≤ (laidOf p).length
  tab : tabB p true = true
  points : (p.nums.stages.headD default).Z.a ≤ 32
  count : (laidOf p).length = firstLen p.nums.stages + restLen p.nums.stages
  quiet : quietB (((laidOf p).take (firstLen p.nums.stages)).map (·.1)) = true
  draws : drawsFit (((laidOf p).take (firstLen p.nums.stages)).map (·.1)) ds = true
  len : ds.length = firstLen p.nums.stages

theorem firstPubOwn_any {ds : List Fmt.Drawn} (J : TestJob W X) (Js : SimJob Pb)
    (F : PlaceFactsOwn J.p ds) (hfr : J.fresh.isNone = true) (hs : Js.p = J.p)
    (ho : Js.own = true) : FirstPubOwn J Js :=
  ⟨hs, ho, F.form, F.enough, by rw [tablesFitB_eq, hfr]; exact F.tab, F.points⟩

/-- A made-up job at the place p whose first fold sends its own table. -/
def madeJobOwn (W X : Type) (p : P12) : TestJob W X :=
  ⟨p, [], none, fun _ _ => noState, fun _ _ _ => zeroPS, fun _ _ _ _ => []⟩

/-- A made-up simulators' job at the place p. -/
def madeSimsOwn (Pb : Type) (p : P12) : SimJob Pb := ⟨p, true, fun _ _ => noState, []⟩

theorem job_there_own (W X : Type) (p : P12) :
    ∃ J : TestJob W X, J.p = p ∧ J.fresh.isNone = true := ⟨madeJobOwn W X p, rfl, rfl⟩

theorem sims_there_own (Pb : Type) (p : P12) : ∃ Js : SimJob Pb, Js.p = p ∧ Js.own = true :=
  ⟨madeSimsOwn Pb p, rfl, rfl⟩

/-! ## 2 The statement -/

/-- **At every job at the place.** -/
theorem own_at_place {ds : List Fmt.Drawn} (J : TestJob W X) (Js : SimJob Pb)
    (F : PlaceFactsOwn J.p ds) (bs : List (Block S Cl)) (b : Block S Cl)
    (hf : (bs.find? fun b => b.place == J.p.place) = some b) (hpl : b.place = J.p.place)
    (hr : b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor : b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hfr : J.fresh.isNone = true) (hs : Js.p = J.p) (ho : Js.own = true) :
    FirstPubOwn J Js ∧
    (∀ fs : List (Fall S), ∃ σ : Side S Cl V W X Pb, testSide bs J Js fs = some σ) ∧
    ∀ (fs : List (Fall S)) (σ : Side S Cl V W X Pb), testSide bs J Js fs = some σ →
      σ.fits = true ∧
      σ.members = [firstMember J Js, restMember J Js] ∧
      (∀ (φ : Face V W Pb) (chain firstTree : ℕ), ExactMember φ σ chain firstTree
        (testOn φ J Js) (testBud Js) (firstMember J Js)) ∧
      firstMember J Js ∈ σ.members ∧
      ∀ (φ : Face V W Pb) (chain firstTree : ℕ)
        (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
        (asks : List (List (List ℕ))), budFirst Js.s₀ asks = true →
        MeetsAt φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) ca m
          (bareFront chain m) ds asks := by
  have T := firstPubOwn_any J Js F hfr hs ho
  obtain ⟨s, t, rest, hst⟩ : ∃ s t rest, J.p.nums.stages = s :: t :: rest := by
    have hform := F.form
    unfold formPubB at hform
    cases hs' : J.p.nums.stages with
    | nil => rw [hs'] at hform; cases hform
    | cons a l =>
      cases l with
      | nil => rw [hs'] at hform; cases hform
      | cons b' r => exact ⟨a, b', r, rfl⟩
  refine ⟨T, fun fs => ?_, fun fs σ hσ => ?_⟩
  · unfold testSide Side.seated
    exact ⟨_, by rw [hf]; rfl⟩
  · have hσ' := hσ
    unfold testSide Side.seated at hσ'
    rw [hf] at hσ'
    obtain rfl := Option.some.inj hσ'
    have hmem : (⟨b, testPairs J Js, fallOf fs J.p.place⟩ : Side S Cl V W X Pb).members =
        [firstMember J Js, restMember J Js] := by
      refine members_of_seat _ _ Js fs _ hσ ?_ s t rest hst F.count
      show b.rounds.zip b.oracles = _
      rw [hr, hor]
      exact zip_laid J.p F.plan
    have hE : ∀ (φ : Face V W Pb) (chain firstTree : ℕ), ExactMember φ
        (⟨b, testPairs J Js, fallOf fs J.p.place⟩ : Side S Cl V W X Pb) chain firstTree
        (testOn φ J Js) (testBud Js) (firstMember J Js) := fun φ chain firstTree =>
      exact_bud (fun ds asks hb => budBoth_of_testBud Js ds asks hb)
        (exact_first_job φ _ J Js chain firstTree _ hfr T)
    refine ⟨fits_of J Js hs b _ hpl F.plan hr hor s t rest hst F.count, hmem, hE,
      by rw [hmem]; exact List.mem_cons_self, fun φ chain firstTree ca m asks hb => ?_⟩
    refine meetsAt_of_exact (hE φ chain firstTree) ca m (bareFront chain m) ds asks
      (testOn_first φ J Js ca m (bareFront chain m)) (seen_bareFront chain m) F.draws
      (testBud_own Js ds asks hb)
      (holds_of_quiet (bareFront chain m) chain firstTree _ ds F.quiet)
      (stop_first (V := V) J Js (φ.sees m.st.input) m.loc ds) fun c => ?_
    rw [shows_first φ _ J Js s t rest m (byNo ds) ds
      ⟨hst, T.enough, (formPub_of_B _ s t rest hst T.form).sorts, T.tables, F.len,
        fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩ c asks]
    rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.PlaceFactsOwn
#print axioms ProofFile.Honest.K12.Light.firstPubOwn_any
#print axioms ProofFile.Honest.K12.Light.madeJobOwn
#print axioms ProofFile.Honest.K12.Light.madeSimsOwn
#print axioms ProofFile.Honest.K12.Light.job_there_own
#print axioms ProofFile.Honest.K12.Light.sims_there_own
#print axioms ProofFile.Honest.K12.Light.own_at_place
