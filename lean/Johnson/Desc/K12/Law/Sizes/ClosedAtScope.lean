-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/ClosedAtScope.lean: what a caller of the law of a proximity test (the
kind K12) lays at a closed place, `ClosedL` (Johnson/Desc/K12/Coin/LawAtLight.lean), at three of the
four places that are made off a plan whose sized record is the full size's, by carrying the closed
members over.

`ClosedL π r ch b₁ b₂ T` has five fields. What each reads of the place π:
  `plan`: the whole of π. Here a premise.
  `chain`: the stages and the written rounds.
  `joh`: the stages alone.
  `bat`: the first stage and the first written round.
  `place`: the chain, the rows, the first free own number, the written rounds, and the rounds that
    the block declares: of every tree that is opened its depth and its source.
No field reads the index of π or a record's codes.
Main names:
  `johOk_reads`, `batPriceOk_reads`, `rdsAt_reads`, `placeOk_reads`: three tests with code at two
    places that agree in what the tests read give one answer.
  `opensOf_rds`, `ownLabelsFreeB_reads`: the like for the test on the labels of the first switch's
    trees (Coin/GameAt.lean): under the test on the plan it reads nothing of the place's oracle
    messages.
  `first_reads`: THE TREES OF THE TEST's GROUP, WHOLE, are read off the declared rounds: over
    `MasksFixed.made` (Johnson/Desc/K12/Law/MasksFixed.lean) at both places. `firstNe_reads`,
    `ownLabelsB_reads`: two more tests on the plan (Law/FirstNe.lean, Coin/FirstBook.lean).
  `ClosedL.of_reads`: so `ClosedL` goes over from a place q to a place π, general in both. No scope.
  `chain_of_planOk`: a made place at which the test on the plan says yes lies on its chain.
  `closedL_U_of_full`, `closedL_O_of_full`, `closedL_W_of_full`: THE STATEMENTS: `ClosedL` at
    `proximityTestParametersAt P X.U` and its like, at the closed radii `rUFull` and the closed members' own letters.
  `labels_UFull`, `labels_U_of_full`: the test on the labels says yes at the folded row's place.
  `first_U_of_full`, `first_O_of_full`, `first_W_of_full`: the group's trees at the made places.
  `nums_U_of_full`, `nums_O_of_full`: ALL SEVEN NUMBERS of the made place are the closed place's.
    NOT SAID: an equation of whole places: the address, the index, the oracle messages, «before»,
    «early» and the answers lie outside the numbers. Not the own test's place: its first tree's
    number hangs on the first chain's roots.
The premises, all: `AtFull m.p.chains.made` (StageSizesAtScope.lean); `placesOfMade m = .ok X`; the
block's test on the plan at the place; and THREE NAMED PREMISES that hang on the plans' rounds and
sendings, not on sizes: the made place's written rounds, the rounds that its numbers give, and its
first free own number are the closed member's.
That `rUFull` and its like are the planner's own radii at the place's stages is said beside this, in
PlacesAtScope.lean (`place_U_of_full`, third clause): `ClosedL` does not ask it.
Limits: the closed members' limits stand (Coin/LawAtFull.lean, Law/CondMembersFull.lean). THE PLACE
OF THE FIRST CHAIN's LAST TEST IS NOT HERE: its rows are joined to nothing yet. `AtFull` has no
member by theorem. The full size only. Nothing on soundness of a verifier. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LawAtFull
import Johnson.Desc.K12.Coin.LawAtLight
import Johnson.Desc.K12.Law.Sizes.PlacesAtScope
import Johnson.Desc.K12.Law.Sizes.MoreAtScope
import Johnson.Desc.K12.Law.FirstTreeOfMade
import Johnson.Desc.K12.Law.StepGroups
import Johnson.Desc.K12.Law.MasksPlan
import Johnson.Desc.K12.Law.FirstNe
import Johnson.Desc.K12.Coin.FirstBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open OnBytes OnBytes.Params Johnson.G.OfPlan
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (ClosedL ChainAt ownLabelsFreeB ownLabelsB)
open VerifiableInference.Desc.K12.Coin.At (closed_UFull closed_OFull closed_WFull TUFull TOFull
  TWFull)
open H2K.Pub (writtenOf johOk johAll batPriceOk batAtB)
open H2K.Member (rdsAt wsAt r0At openOk opensOk placeOk piUFull piOFull piWFull rUFull rOFull
  rWFull)
open H2K.Made (nums_of_planOk places_firstTree MasksFixed ownTold firstNe masksFixed_of_planOk)
open H2K.First (opensOf)
open H2U (placesOfMade Places4 PlaceNums proximityTestParametersAt noP12)

/-! ## 1. What three tests read -/

/-- The test on the Johnson radii reads the stages alone. -/
theorem johOk_reads {π q : P12} (r : Fmt.M1.Stage → ℕ) (hs : π.nums.stages = q.nums.stages) :
    johOk π r = johOk q r := by
  unfold johOk johAll
  rw [hs]

/-- The test on the price of "BAT" reads the first stage and the first written round. -/
theorem batPriceOk_reads {π q : P12} (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (hs : π.nums.stages = q.nums.stages) (hW : writtenOf π.nums = writtenOf q.nums) :
    batPriceOk π r k = batPriceOk q r k := by
  unfold batPriceOk batAtB
  rw [hs, hW]

/-- Where both blocks' tests on the plan say yes and the numbers give the same rounds, the blocks
declare the same rounds. -/
theorem rdsAt_reads {π q : P12} (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hq : (proximityTestKind guardedProximityTestParts q : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums π.nums = H2U.roundsOfNums q.nums) : rdsAt π = rdsAt q := by
  have a := k12_rounds guardedProximityTestParts π hp
  have b := k12_rounds guardedProximityTestParts q hq
  rw [hR, b] at a
  exact (Option.some.inj a).symm

/-- The test on a place reads the chain, the declared rounds, the written rounds, the rows and the
first free own number. -/
theorem placeOk_reads {π q : P12} (ch b₁ b₂ : ℕ) (T : List (Fmt.TreeSource × ℕ))
    (hc : π.place.chain = q.place.chain) (hD : rdsAt π = rdsAt q)
    (hW : writtenOf π.nums = writtenOf q.nums) (h1 : π.nums.rows = q.nums.rows)
    (h5 : π.nums.free = q.nums.free) : placeOk π ch b₁ b₂ T = placeOk q ch b₁ b₂ T := by
  have w : wsAt π = wsAt q := by
    unfold wsAt
    rw [hW]
  have r0 : r0At π = r0At q := by
    unfold r0At
    rw [h1]
  have o : openOk π T = openOk q T := by
    funext x
    obtain ⟨sh, s⟩ := x
    cases s with
    | own n => simp only [openOk, h5, w]
    | taken c s => rfl
  unfold placeOk opensOk
  rw [hc, hD, w, r0, o, h5]

/-- Where the block's test on the plan says yes, what the first switch's two declared rounds open is
read off the rounds that the block declares. -/
theorem opensOf_rds (p : P12) (k : ℕ) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) :
    opensOf p k = ((((rdsAt p).drop 1).drop (1 + k)).take 2).flatMap (·.opens) := by
  have e : rdsAt p = (H2K.JointK.laidOf p).map (·.1) := H2K.Sw.k12_rounds guardedProximityTestParts p hp
  rw [e]
  unfold opensOf H2K.JointK.laidOf
  rw [← List.map_drop, ← List.map_drop, ← List.map_take, List.flatMap_map]

/-- The test on the labels of the first switch's trees reads the first stage, the declared rounds,
the first tree's number and the first free own number. -/
theorem ownLabelsFreeB_reads {π q : P12} (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hq : (proximityTestKind guardedProximityTestParts q : Block T12 Unit).planOk = true) (hs : π.nums.stages = q.nums.stages)
    (hD : rdsAt π = rdsAt q) (h6 : π.nums.firstTree = q.nums.firstTree)
    (h5 : π.nums.free = q.nums.free) : ownLabelsFreeB π = ownLabelsFreeB q := by
  unfold ownLabelsFreeB
  rw [hs]
  cases q.nums.stages with
  | nil => rfl
  | cons a rest =>
    simp only
    rw [opensOf_rds π a.k hp, opensOf_rds q a.k hq, hD, h6, h5]

/-- **The trees of the test's group, whole, are read off the declared rounds**: two places at which
the block's test on the plan says yes, with one first stage, one own mask and the same declared
rounds, have the same list. -/
theorem first_reads {π q : P12} (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hq : (proximityTestKind guardedProximityTestParts q : Block T12 Unit).planOk = true) (hs : π.nums.stages = q.nums.stages)
    (hm : π.nums.ownMask = q.nums.ownMask) (hD : rdsAt π = rdsAt q) :
    π.nums.first = q.nums.first := by
  have Mp := masksFixed_of_planOk π hp
  have Mq := masksFixed_of_planOk q hq
  obtain ⟨a, b, rest, _, _, e1, _, _, o1⟩ := Mp.made
  obtain ⟨a', b', rest', _, _, e2, _, _, o2⟩ := Mq.made
  obtain ⟨rfl, _⟩ := List.cons.inj (e1.symm.trans (hs.trans e2))
  have e : π.nums.first ++ ownTold π.nums = q.nums.first ++ ownTold q.nums := by
    rw [← o1, ← o2, opensOf_rds π a.k hp, opensOf_rds q a.k hq, hD]
  have hl : (ownTold π.nums).length = (ownTold q.nums).length := by
    cases hb : q.nums.ownMask with
    | false =>
      have hb' := hm.trans hb
      simp [ownTold, hb, hb']
    | true =>
      obtain ⟨_, _, x1⟩ := Mp.own (hm.trans hb)
      obtain ⟨_, _, x2⟩ := Mq.own hb
      rw [x1, x2]
      rfl
  exact (List.append_inj' e hl).1

/-- The test that no tree of the group is the first fold's own mask's reads the group's trees and
the first free own number. -/
theorem firstNe_reads {π q : P12} (hf : π.nums.first = q.nums.first)
    (h5 : π.nums.free = q.nums.free) : firstNe π = firstNe q := by
  unfold firstNe
  rw [hf, h5]

/-- The test on the labels without the clause on the first free own number. -/
theorem ownLabelsB_reads {π q : P12} (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hq : (proximityTestKind guardedProximityTestParts q : Block T12 Unit).planOk = true) (hs : π.nums.stages = q.nums.stages)
    (hD : rdsAt π = rdsAt q) (h6 : π.nums.firstTree = q.nums.firstTree) :
    ownLabelsB π = ownLabelsB q := by
  unfold ownLabelsB
  rw [hs]
  cases q.nums.stages with
  | nil => rfl
  | cons a rest =>
    simp only
    rw [opensOf_rds π a.k hp, opensOf_rds q a.k hq, hD, h6]

/-! ## 2. From a place to a place -/

/-- **`ClosedL` goes over to a place that agrees with a closed one in what its fields read**, where
the block's test on the plan, which reads more, says yes. -/
theorem ClosedL.of_reads {π q : P12} {r : Fmt.M1.Stage → ℕ} {ch b₁ b₂ : ℕ}
    {T : List (Fmt.TreeSource × ℕ)} (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hs : π.nums.stages = q.nums.stages) (hW : writtenOf π.nums = writtenOf q.nums)
    (hR : H2U.roundsOfNums π.nums = H2U.roundsOfNums q.nums) (h1 : π.nums.rows = q.nums.rows)
    (h5 : π.nums.free = q.nums.free) (hc : π.place.chain = q.place.chain)
    (C : ClosedL q r ch b₁ b₂ T) : ClosedL π r ch b₁ b₂ T :=
  ⟨hp, ChainAt.congr hs hW C.chain,
    (placeOk_reads ch b₁ b₂ T hc (rdsAt_reads hp C.plan hR) hW h1 h5).trans C.place,
    (johOk_reads r hs).trans C.joh, (batPriceOk_reads r 128 hs hW).trans C.bat⟩

/-- A place at which the block's test on the plan says yes lies on the chain that it was made for.
-/
theorem chain_of_planOk (place : Place) (x : PlaceNums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place x) : Block T12 Unit).planOk = true) :
    (proximityTestParametersAt place x).place.chain = x.chain := by
  unfold proximityTestParametersAt at hp ⊢
  split
  · rename_i hc
    rw [if_pos hc] at hp
    exact absurd hp (by simp [proximityTestKind, noP12])
  · rename_i hc
    rw [if_neg hc] at hp
    have e : place.chain = x.chain := by simpa using hc
    split
    · exact e
    · rename_i ho
      rw [ho] at hp
      exact absurd hp (by simp [proximityTestKind, noP12])

/-- Two records of a place's numbers with the same seven fields are one. -/
theorem nums_ext {N M : H2U.TestNums} (h1 : N.rows = M.rows) (h2 : N.work = M.work)
    (h3 : N.stages = M.stages) (h4 : N.ownMask = M.ownMask) (h5 : N.first = M.first)
    (h6 : N.free = M.free) (h7 : N.firstTree = M.firstTree) : N = M := by
  cases N
  cases M
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- At the closed place of Omega's test no tree of the group is the own mask's. -/
theorem firstNe_OFull : firstNe piOFull = true := by decide +kernel

/-- The closed place of the folded row's test passes the test on the labels. -/
theorem labels_UFull : ownLabelsFreeB piUFull = true := by decide +kernel

/-! ## 3. At the places that are made off a plan sized as at the full size

The address P is a free letter. Where P lies on another chain than the place was made for, proximityTestParametersAt
lays an empty place, at which the test on the plan fails: so hp says that P lies on that chain
(`chain_of_planOk`), and MoreAtScope.lean says which chain that is. -/

section
variable {m : Made} (A : AtFull m.p.chains.made) {X : Places4} (h : placesOfMade m = .ok X)
  (P : Place)
include A h

/-- **The folded row's place.** -/
theorem closedL_U_of_full
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P X.U) : Block T12 Unit).planOk = true)
    (hW : writtenOf X.U.nums = writtenOf piUFull.nums)
    (hR : H2U.roundsOfNums X.U.nums = H2U.roundsOfNums piUFull.nums)
    (h5 : X.U.nums.free = piUFull.nums.free) :
    ClosedL (proximityTestParametersAt P X.U) rUFull 1 0 0 TUFull := by
  have hn := nums_of_planOk P X.U hp
  refine ClosedL.of_reads hp ?_ ?_ ?_ ?_ ?_ ?_ closed_UFull.light
  · rw [hn]
    exact (place_U_of_full A h).1
  · rw [hn]
    exact hW
  · rw [hn]
    exact hR
  · rw [hn]
    exact (more_U_of_full A h).1
  · rw [hn]
    exact h5
  · rw [chain_of_planOk P X.U hp]
    exact (more_U_of_full A h).2.2.2.2

/-- **Omega's place, where there is one.** -/
theorem closedL_O_of_full (o : PlaceNums) (ho : X.O = some o)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P o) : Block T12 Unit).planOk = true)
    (hW : writtenOf o.nums = writtenOf piOFull.nums)
    (hR : H2U.roundsOfNums o.nums = H2U.roundsOfNums piOFull.nums)
    (h5 : o.nums.free = piOFull.nums.free) :
    ClosedL (proximityTestParametersAt P o) rOFull 1 0 0 TOFull := by
  have hn := nums_of_planOk P o hp
  refine ClosedL.of_reads hp ?_ ?_ ?_ ?_ ?_ ?_ closed_OFull.light
  · rw [hn]
    exact (place_O_of_full A h o ho).1
  · rw [hn]
    exact hW
  · rw [hn]
    exact hR
  · rw [hn]
    exact (more_O_of_full A h o ho).1
  · rw [hn]
    exact h5
  · rw [chain_of_planOk P o hp]
    exact (more_O_of_full A h o ho).2.2.2.2

/-- **The place of the request's own test.** -/
theorem closedL_W_of_full
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P X.W) : Block T12 Unit).planOk = true)
    (hW : writtenOf X.W.nums = writtenOf piWFull.nums)
    (hR : H2U.roundsOfNums X.W.nums = H2U.roundsOfNums piWFull.nums)
    (h5 : X.W.nums.free = piWFull.nums.free) :
    ClosedL (proximityTestParametersAt P X.W) rWFull 2 83 2 TWFull := by
  have hn := nums_of_planOk P X.W hp
  refine ClosedL.of_reads hp ?_ ?_ ?_ ?_ ?_ ?_ closed_WFull.light
  · rw [hn]
    exact (place_W_of_full A h).1
  · rw [hn]
    exact hW
  · rw [hn]
    exact hR
  · rw [hn]
    exact (more_W_of_full A h).1
  · rw [hn]
    exact h5
  · rw [chain_of_planOk P X.W hp]
    exact (more_W_of_full A h).2.2.2.2

/-- **The test on the labels of the first switch's trees, at the folded row's place.** The first
tree's number is 0 there at every plan (FirstTreeOfMade.lean). -/
theorem labels_U_of_full
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P X.U) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums X.U.nums = H2U.roundsOfNums piUFull.nums)
    (h5 : X.U.nums.free = piUFull.nums.free) : ownLabelsFreeB (proximityTestParametersAt P X.U) = true := by
  have hn := nums_of_planOk P X.U hp
  refine (ownLabelsFreeB_reads hp closed_UFull.plan ?_ ?_ ?_ ?_).trans labels_UFull
  · rw [hn]
    exact (place_U_of_full A h).1
  · refine rdsAt_reads hp closed_UFull.plan ?_
    rw [hn]
    exact hR
  · rw [hn]
    exact (places_firstTree m X h).2.1
  · rw [hn]
    exact h5

/-! ### The trees of the test's group, and so all seven numbers -/

theorem first_U_of_full
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P X.U) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums X.U.nums = H2U.roundsOfNums piUFull.nums) :
    X.U.nums.first = piUFull.nums.first := by
  have hn := nums_of_planOk P X.U hp
  rw [← hn]
  refine first_reads hp closed_UFull.plan ?_ ?_ (rdsAt_reads hp closed_UFull.plan ?_)
  · rw [hn]
    exact (place_U_of_full A h).1
  · rw [hn]
    exact (more_U_of_full A h).2.1
  · rw [hn]
    exact hR

theorem first_O_of_full (o : PlaceNums) (ho : X.O = some o)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P o) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums o.nums = H2U.roundsOfNums piOFull.nums) :
    o.nums.first = piOFull.nums.first := by
  have hn := nums_of_planOk P o hp
  rw [← hn]
  refine first_reads hp closed_OFull.plan ?_ ?_ (rdsAt_reads hp closed_OFull.plan ?_)
  · rw [hn]
    exact (place_O_of_full A h o ho).1
  · rw [hn]
    exact (more_O_of_full A h o ho).2.1
  · rw [hn]
    exact hR

theorem first_W_of_full
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P X.W) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums X.W.nums = H2U.roundsOfNums piWFull.nums) :
    X.W.nums.first = piWFull.nums.first := by
  have hn := nums_of_planOk P X.W hp
  rw [← hn]
  refine first_reads hp closed_WFull.plan ?_ ?_ (rdsAt_reads hp closed_WFull.plan ?_)
  · rw [hn]
    exact (place_W_of_full A h).1
  · rw [hn]
    exact (more_W_of_full A h).2.1
  · rw [hn]
    exact hR

/-- **All seven numbers of the folded row's place are the closed place's.** Outside them lie the
address, the index, the oracle messages, «before», «early» and the answers: no equation of whole
places is said. -/
theorem nums_U_of_full
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P X.U) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums X.U.nums = H2U.roundsOfNums piUFull.nums)
    (h5 : X.U.nums.free = piUFull.nums.free) : X.U.nums = piUFull.nums :=
  nums_ext (more_U_of_full A h).1 (place_U_of_full A h).2.1
    (place_U_of_full A h).1 (more_U_of_full A h).2.1
    (first_U_of_full A h P hp hR) h5 ((places_firstTree m X h).2.1)

/-- **All seven numbers of Omega's place are the closed place's.** -/
theorem nums_O_of_full (o : PlaceNums) (ho : X.O = some o)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt P o) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums o.nums = H2U.roundsOfNums piOFull.nums)
    (h5 : o.nums.free = piOFull.nums.free) : o.nums = piOFull.nums :=
  nums_ext (more_O_of_full A h o ho).1 (place_O_of_full A h o ho).2.1
    (place_O_of_full A h o ho).1 (more_O_of_full A h o ho).2.1
    (first_O_of_full A h P o ho hp hR) h5 ((places_firstTree m X h).2.2.1 o ho)

end

end H2K.Sizes

#print axioms H2K.Sizes.ClosedL.of_reads
#print axioms H2K.Sizes.closedL_U_of_full
#print axioms H2K.Sizes.closedL_O_of_full
#print axioms H2K.Sizes.closedL_W_of_full
#print axioms H2K.Sizes.ownLabelsFreeB_reads
#print axioms H2K.Sizes.labels_U_of_full
#print axioms H2K.Sizes.first_reads
#print axioms H2K.Sizes.firstNe_OFull
#print axioms H2K.Sizes.nums_U_of_full
#print axioms H2K.Sizes.nums_O_of_full
