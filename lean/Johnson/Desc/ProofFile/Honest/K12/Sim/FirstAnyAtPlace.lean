-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstAnyAtPlace.lean: the first member of a proximity test,
where the first fold's fresh table has come earlier, at every job at a place. General in the place,
in the list of sub-protocols and in the job.

What is stated. Let a place pass seven public tests (`PlaceFacts`), and let the first sub-protocol
of a list that stands at the place have the declared rounds and oracle messages of the test's own
block. Then for every job J at that place which says that the table has come earlier, and every
simulators' job with the same two public letters: `FirstPub` (Sim/ExactFirst.lean) holds; `testSide`
(Sim/Row.lean) returns a side off the list, at all falls; whatever side it returns passes
`Side.fits` and has just the two members that are written out; the frame's sentence `ExactMember`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean) holds at the first, at `testOn` and `testBud`; and
at every state of a run, at the front made of it (`bareFront`, Sim/MeetsAtHead.lean) and at the
written challenges, the sentence's six hypotheses hold, what the member shows is something, with 2 k
+ 1 scalars and no list of columns, and the equation holds.

  `PlaceFacts`, `facts_carry`   the seven tests: a record of premises, defined here: lemmas
                 conclude it, no top statement does; all seven are Booleans or numbers on the place.
                 They carry over between two places with the same stages and the same `thinOf`
  `firstPub_any`   `FirstPub` at every such job
  `any_at_place`   the statement. Its four premises on the sub-protocol b (it is the first of the
                 list at the place; its place; its declared rounds; its oracle messages) are public
                 facts on the description's list

Why every job. `FirstPub` reads of a job its place and whether it says that the table has come
earlier, and nothing else (`tablesFitB_eq`, Sim/FirstPubAtHead.lean). The job's state function,
rows, trees and members are variables.

By what. `exact_first` (Sim/ExactFirst.lean), `first_count` (Sim/FirstCount.lean), `members_of_seat`
(Sim/ExactSide.lean), `fits_of` (Sim/FirstSeatAtHead.lean), `zip_laid` (PlaysK12.lean), and the four
lemmas on what asks nothing at this member, with `seen_bareFront` (Sim/MeetsAtHead.lean).

Limits.
- "At every job at the place" says nothing on whether any job there is the prover's. Who owns the
  fresh table that came earlier is not named: the job's field is any address.
- Among "every job" are jobs whose list of members names the very message whose run the part spends,
  and jobs whose `rows₀` reads beyond its members. The sentence holds there as typed, the spent run
  sampled anew and the carried runs fixed, and says nothing of any run. No book is asked here; the
  frame's own test on a book (`ProverCoinCounts.clauses`, Honest/Frame.lean) refuses the first kind.
- The state on entry is any function: nothing says that it is the verifier's state.
- It is shown at no job that is played.
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of the guarded halves (PartsByJob.lean).
- What the parts send is `testAll` (Johnson/Desc/ProofFile/Honest/K12/Test.lean), cut into parts in
  Parts.lean, over the random values of Coins.lean, both beside it. How far `testAll` is tied to the
  library's `bodyAll` is said in Test.lean's limits.
- It is the spender's half: the 2 k + 1 spent values are sampled anew in the equation. Where else in
  a run these values are meant to stand, in their sender's tree and in what the second part carries,
  is joined to this by nothing here.
- Of the sentence's six hypotheses four ask nothing at this member; two say something: the run has
  shown what the front shows, and the challenges have the declared form. The front lists no column
  and no root; it could not serve the second member. No state of a run is shown to be one that a
  play reaches.
- The first member alone. It is not the frame's field `exact` at the side, which speaks of every
  member.
- No file of this folder states a security property by itself. Nothing on completeness, soundness or
  hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ThinOfReads
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstCount
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstSeatAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (laidOf)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-! ## 1 The public tests on a place -/

/-- **Seven public tests on a place.** ds: a written list of challenges. -/
structure PlaceFacts (p : P12) (ds : List Fmt.Drawn) : Prop where
  plan : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true
  form : formPubB p = true
  enough : firstLen p.nums.stages ≤ (laidOf p).length
  tab : tabB p false = true
  count : (laidOf p).length = firstLen p.nums.stages + restLen p.nums.stages
  quiet : quietB (((laidOf p).take (firstLen p.nums.stages)).map (·.1)) = true
  draws : drawsFit (((laidOf p).take (firstLen p.nums.stages)).map (·.1)) ds = true

theorem facts_carry {p q : P12} {ds : List Fmt.Drawn} (hst : p.nums.stages = q.nums.stages)
    (hT : thinOf p = thinOf q) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true)
    (F : PlaceFacts q ds) : PlaceFacts p ds := by
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [formPubB_reads hst hT]
    exact F.form
  · rw [hst, length_congr hT]
    exact F.enough
  · rw [tabB_reads hst hT]
    exact F.tab
  · rw [length_congr hT, hst]
    exact F.count
  · rw [List.map_take, decls_thin, hT, ← decls_thin, ← List.map_take, hst]
    exact F.quiet
  · rw [List.map_take, decls_thin, hT, ← decls_thin, ← List.map_take, hst]
    exact F.draws

theorem firstPub_any {ds : List Fmt.Drawn} (J : TestJob W X) (Js : SimJob Pb)
    (F : PlaceFacts J.p ds) (hfr : J.fresh.isNone = false) (hs : Js.p = J.p)
    (ho : Js.own = false) : FirstPub J Js :=
  ⟨hs, ho, F.form, F.enough, by rw [tablesFitB_eq, hfr]; exact F.tab⟩

/-! ## 2 The statement -/

local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **At every job at the place.** -/
theorem any_at_place {ds : List Fmt.Drawn} (J : TestJob W X) (Js : SimJob Pb)
    (F : PlaceFacts J.p ds) (bs : List (Block S Cl)) (b : Block S Cl)
    (hf : (bs.find? fun b => b.place == J.p.place) = some b) (hpl : b.place = J.p.place)
    (hr : b.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor : b.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hfr : J.fresh.isNone = false) (hs : Js.p = J.p) (ho : Js.own = false) :
    FirstPub J Js ∧
    (∀ fs : List (Fall S), ∃ σ : Side S Cl V W X Pb, testSide bs J Js fs = some σ) ∧
    ∀ (fs : List (Fall S)) (σ : Side S Cl V W X Pb), testSide bs J Js fs = some σ →
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
        drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) ds = true ∧
        testBud Js (firstMember (V := V) J Js).number ds asks ∧
        (bareFront chain m).holds chain firstTree ((firstMember (V := V) J Js).rounds.map (·.1))
          ds = true ∧
        (firstMember J Js).part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid ∧
        (∀ c, ∃ l, σ.shows φ (firstMember J Js) c m ds asks = some l ∧
          scalars l = 2 * J.s₀.k + 1 ∧ columns l = 0) ∧
        (Prob.unif (Cs (firstMember (V := V) J Js).part.takes ×
            CsAll (firstMember (V := V) J Js).part.spends)).map
            (fun c => σ.shows φ (firstMember J Js) (c.1, c.2, ca) m ds asks) =
          (Prob.unif (Cs (firstMember (V := V) J Js).sim.takes)).map fun c =>
            (firstMember J Js).tells φ c m.st.input (bareFront chain m) ds asks := by
  have T := firstPub_any J Js F hfr hs ho
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
    refine ⟨fits_of J Js hs b _ hpl F.plan hr hor s t rest hst F.count, hmem,
      fun φ chain firstTree => exact_first φ _ J Js chain firstTree _ _ hfr T,
      by rw [hmem]; exact List.mem_cons_self, fun φ chain firstTree ca m asks => ?_⟩
    have h1 := testOn_first φ J Js ca m (bareFront chain m)
    have h2 := seen_bareFront chain m
    have h3 : drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) ds = true := F.draws
    have h4 : testBud Js (firstMember (V := V) J Js).number ds asks := testBud_first Js ho ds asks
    have h5 := holds_of_quiet (bareFront chain m) chain firstTree
      ((firstMember (V := V) J Js).rounds.map (·.1)) ds F.quiet
    have h6 := stop_first (V := V) J Js (φ.sees m.st.input) m.loc ds
    exact ⟨h1, h2, h3, h4, h5, h6, fun c => first_count φ _ J Js hfr T m ds h3 asks c,
      exact_first φ _ J Js chain firstTree (testOn φ J Js) (testBud Js) hfr T ca m
        (bareFront chain m) ds asks h1 h2 h3 h4 h5 h6⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.PlaceFacts
#print axioms ProofFile.Honest.K12.Light.facts_carry
#print axioms ProofFile.Honest.K12.Light.firstPub_any
#print axioms ProofFile.Honest.K12.Light.any_at_place
