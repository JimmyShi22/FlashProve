-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlaysAtPlan.lean: the kind "the code switch" (K2): THE HALF OF
THE KIND's ONE LOT PLAYS AT THE KIND's OWN SUB-PROTOCOL, AT THE PLAN's OWN NUMBERS: at a place of
the lot, where the lot's `numsAt` (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) returns the numbers N,
every sub-protocol whose rounds and oracle messages are those of the kind at these numbers
(`IM.k2P`, Johnson/IMR/K2Seat.lean) meets THREE of the four equations that `lot_plays`
(Honest/K2/Law/Plays.lean) asks of it: its first, second and fourth; THE THIRD, ON THE ANSWERS, IS
LEFT AS ONE NAMED PUBLIC TEST. One definition, that test; statements with their proofs.

  `place_codes`     a place's codes are the planner's
  `place_shapes`    THE SECOND EQUATION: the oracle messages that the numbers state beneath the
                    first round's roots have the lengths and widths of the honest sending's trees
  `answersFit`      THE TEST THAT IS LEFT, with code: the honest sending has as many answers as the
                    numbers state
  `plays_at_plan`   THE LAW, at two challenges
  `plays_at_plan_fit`   THE LAW AT `Good.plays`' OWN TERM (Honest/Side.lean): at every list of
                    challenges that the sub-protocol's rounds can draw

By: `lot_plays` · `place_nums` (Honest/K2/Law/SentIsBlocks.lean) · `zipIdx_fst`
(Honest/K2/Law/SwitchFrame.lean) · `draws_two` (Honest/K2/Law/ExactProof.lean) · `filter_cut`
(Johnson/Desc/K2/Honest/Returns/ItemsFit.lean) · the library's `treesMade_eq`
(Johnson/Desc/Own/TreesAgree.lean) and `numsAt_codes` (Johnson/P1K2R/HstInScope.lean). Two steps are
`omega`, two `simp only` at the definitions named there.

Limits. `answersFit` IS A PREMISE, PAID NOWHERE HERE: the numbers state the samples times the number
of sampled messages; the sending has the sum of the sampled messages' answers. The five other public
tests of `lot_plays` stay premises too, and "`numsAt` returns". THAT THE DESCRIPTION's SUB-PROTOCOL
AT THE PLACE HAS THESE ROUNDS AND ORACLE MESSAGES IS A PREMISE (two equations on b): of the kind's
own block at these numbers they hold by its text. On returning alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Plays
import Johnson.Desc.ProofFile.Honest.K2.Law.SentIsBlocks
import Johnson.Desc.K2.Honest.Returns.ItemsFit
import Johnson.Desc.Own.TreesAgree
import Johnson.IMR.K2Seat
import Johnson.P1K2R.HstInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Oracle Place)
open VerifiableInference.Desc.First.K2 (At rounds)
open VerifiableInference.Desc.K2.Honest.Returns (filter_cut)

variable {X W₀ Rc Xi Tr S Cl : Type}

/-- A place's codes are the planner's. -/
theorem place_codes {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G) :
    p.sizes.codes = P.z.codes := by
  cases hs : spotsOf Z.cuts with
  | none =>
    simp only [switchPlaces, hP, hs] at hp
    cases hp
  | some sps =>
    simp only [switchPlaces, hP, hs] at hp
    obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hp
    rfl

/-- **The oracle messages that the numbers state have the shapes of the honest sending's trees.** -/
theorem place_shapes {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    {N : P1K2.Nums} (hN : P1K2.numsAt P p.place.link = some N) :
    (P1K2.oraclesAt N.grp N.codes N.sent).map (fun o => (o.logLength, o.words)) =
      treeShapes p.sizes.codes (switchSent p.sizes p.others) := by
  rw [place_nums hP hp hN, P1K2.numsAt_codes hN, place_codes hP hp]
  unfold P1K2.oraclesAt treeShapes
  rw [VerifiableInference.Desc.Own.treesMade_eq]
  cases OnBytes.layTrees P.z.codes (switchSent p.sizes p.others) with
  | none => rfl
  | some lay =>
    show (lay.shapes.toList.zipIdx.map _).map _ = lay.shapes.toList.map _
    rw [List.map_map]
    exact zipIdx_fst (fun t : OnBytes.TreeShape => (t.logN, t.mainWidth + t.maskWidth)) _ 0

/-- **THE TEST THAT IS LEFT**: the honest sending has as many answers as the numbers state. -/
def answersFit (p : SwitchPlace) (N : P1K2.Nums) : Bool :=
  (sendingPar p.sizes.codes (switchSent p.sizes p.others)).answers == N.answers

/-- **THE HALF OF THE KIND's ONE LOT PLAYS AT THE KIND's OWN SUB-PROTOCOL.** -/
theorem plays_at_plan {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    {N : P1K2.Nums} (hN : P1K2.numsAt P p.place.link = some N)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub)
    (a : Place) (nm : String) (st : At) (b : Block S Cl)
    (hb₁ : b.rounds = rounds (IM.k2P Z a nm st N))
    (hb₂ : b.oracles = [(IM.k2P Z a nm st N).sent, []])
    (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt lay segs) p).parts)
    (x₁ x₂ : Fmt.Drawn) (m : Mid (Local W₀ Rc Xi Tr) X)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (ha : answersFit p N = true)
    (hc : closingOk freshTable (segs.take p.link) p = true)
    (hq : publicOk D lay p (segs.take p.link) m.st.input.x = true) :
    ∃ y, play ((switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt lay segs) p).steps b v c) [x₁, x₂] [] m = .ok y := by
  refine lot_plays D readers lay segs p b _ _ _ _ (by rw [hb₁, hb₂]; rfl) v c x₁ x₂ m hs hr hf
    ?_ (place_shapes hP hp hN) ?_ rfl hc hq
  · show (Fmt.Entry.cut _).filter (· != .root) = []
    rw [filter_cut]
    show List.replicate 0 Fmt.Item.answer ++
      List.replicate ((32 * N.roots - 24 * 0 - 32 * N.roots) / 24) Fmt.Item.e = []
    have z : (32 * N.roots - 24 * 0 - 32 * N.roots) / 24 = 0 := by omega
    rw [z]
    rfl
  · show (Fmt.Entry.cut _).filter (· != .root) = _
    rw [filter_cut, beq_iff_eq.1 ha]
    show List.replicate N.answers Fmt.Item.answer ++
      List.replicate ((24 * N.answers - 24 * N.answers - 32 * 0) / 24) Fmt.Item.e = _
    have z : (24 * N.answers - 24 * N.answers - 32 * 0) / 24 = 0 := by omega
    rw [z]
    exact List.append_nil _

/-- **The same at every list of challenges that the sub-protocol's rounds can draw**: the second
clause of `Good.plays` (Honest/Side.lean) at its own term. -/
theorem plays_at_plan_fit {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    {N : P1K2.Nums} (hN : P1K2.numsAt P p.place.link = some N)
    (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub)
    (a : Place) (nm : String) (st : At) (b : Block S Cl)
    (hb₁ : b.rounds = rounds (IM.k2P Z a nm st N))
    (hb₂ : b.oracles = [(IM.k2P Z a nm st N).sent, []])
    (v : Option (Local W₀ Rc Xi Tr))
    (c : RowCoins (switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt lay segs) p).parts)
    (ds : List Fmt.Drawn) (hd : drawsFit b.rounds ds = true) (m : Mid (Local W₀ Rc Xi Tr) X)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (ha : answersFit p N = true)
    (hc : closingOk freshTable (segs.take p.link) p = true)
    (hq : publicOk D lay p (segs.take p.link) m.st.input.x = true) :
    ∃ y, play ((switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt lay segs) p).steps b v c) ds [] m = .ok y := by
  rw [hb₁] at hd
  obtain ⟨x₁, x₂, rfl, _⟩ := draws_two _ _ ds hd
  exact plays_at_plan hP hp hN D readers lay segs a nm st b hb₁ hb₂ v c x₁ x₂ m hs hr hf ha hc hq

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.place_codes
#print axioms ProofFile.Honest.K2.Law.place_shapes
#print axioms ProofFile.Honest.K2.Law.answersFit
#print axioms ProofFile.Honest.K2.Law.plays_at_plan
#print axioms ProofFile.Honest.K2.Law.plays_at_plan_fit
