-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K2Rounds.lean: THE CODE SWITCH's LOT's SECOND ROW (ProofFile.k2Pure,
Johnson/Desc/ProofFile/Lots/PureLots.lean): WHAT THE LOT's BLOCKS DECLARE. Each block of the lot has
no round, or its declared rounds are the list that the written table `listAt`
(Johnson/AtFull/Rounds/ListAt.lean) bears at the name of the place at which the block stands. AT
HYPOTHESES BY FIELD on what the lot reads of the public part and of the ground. NO OPENING, NO PIN
«in scope» IS SPENT. NO BLOCK IMPORTS THIS FILE.
  p2Ft · p2Of_ft     the first row's p2Of (K2Row.lean) reads of the public part one number alone,
                     the number of the chain's first tree: here it is an argument. The kind's own
                     text of its two rounds (`rounds`, Johnson/Top/H0/Tw/K2C/Kind.lean) is
                     CALLED at it; it is not typed again
  pureAt_rounds      where the lot's maker makes a block at a place, the block stands at that place
                     and declares the kind's two rounds at the place's numbers
  k2_lot_rounds      THE GENERAL LAW, without a hypothesis: a block of the lot has no round, or it
                     stands at a place that has its numbers and declares the kind's two rounds at
                     them. So the rounds read the table of steps, prepOf's return and the number of
                     the chain's first tree, and nothing else
  k2ListsOk          the test: at every place that has its numbers, and every place of the table
                     that is the same place, the kind's rounds are the table's list at the name
  k2_lists_closed    THE CLOSED FACT, BY LEAN's KERNEL, at the written places, the written sizes and
                     the number 0: the test says yes. One fact for all 25 lists
  k2_made_count · k2_made_names    NONE IS DROPPED: 25 places have their numbers, and their names,
                     in order, are the names of all the written places of the kind. So the test's
                     outer «all» runs over every place of the kind · k2_made_names_none: a negative
                     fact: without the numbers it is not so
  k2_lists_tree_one · k2_lists_swapped · k2_lists_bent_trees    NEGATIVE FACTS, BY THE KERNEL: with
                     the number 1 for 0 · with two switches' names exchanged in the table · with the
                     first link's trees struck from the numbers: the test says no
  k2_lists_prep      THE ROW under hs, hP (prepOf's return is the written one) and hF (the number
                     is 0)
  k2_lists_spots     THE ROW under the first row's hs, hz, t1 … t5, which pay hP (prep_at), and hF
  first_tree_made    hF, where the public part is made by the plain road
  k2_lists_made      THE ROW with hF paid so
  k2_two_rounds · k2_lists_whole    under the first row's hH besides: every block of the lot
                     declares the table's list: «no round» is barred by the first row
WHAT STAYS OWED, BY FIELD: hs (the places are the written ones) · hz (the sizes are the written
ones) · t1 … t5. Neither hH nor hK of the first row is spent by the row itself.
LIMITS. THE ROW ALONE LETS EVERY BLOCK BE WITHOUT A ROUND: what bars that is the first row (two
rounds at all 25 places, under hH): k2_lists_whole says so. Without hH that is no figure of speech:
at «H:2» the block is mute, and so without a round, where the head's link's letters are lacking.
That any public part and ground meet the hypotheses together is shown nowhere here: THE ROW MAY BE
IDLE; THERE IS NO EXAMPLE. (Johnson/IMR/SendsPinned.lean's prep_pinned derives the five equations
of «tied» and hz where the public part and the blank records are made and a test on the made plan
accepts: it is not called here. For hs no such law is known to this file.) The table was cut by a
program out of written values that were printed off a run of the planner (ListAt.lean's own head):
it is no independent witness.
The full size alone. No soundness is claimed.

-/
import Johnson.AtFull.Desc.Lots.K2Row
import Johnson.AtFull.Rounds.ListAt
import Johnson.Desc.ProofFile.Law.PlainMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K2
open P1K2
open OnBytes OnBytes.Model OnBytes.Params OnBytes.Plan
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Sk (skel)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind rounds finishPlace headOpened headPlanOk)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.AtFull.Desc (spotsWritten)
open Johnson.AtFull.Rounds (listAt)

/-- p2Of, with the number of the chain's first tree as an argument. -/
def p2Ft (ft : Nat) (sp : Spot) (n : Nums) : P2 :=
  { name := sp.name, place := sp.place, stands := standsOf sp, grp := n.grp
    firstTree := ft, samples := n.samples
    work₁ := n.work₁, roots := n.roots, seeds := n.seeds, nonZero := n.nonZero
    work₂ := n.work₂, answers := n.answers, positions := n.positions, logN := n.logN
    sent := oraclesAt n.grp n.codes n.sent, read := n.read }

theorem p2Of_ft (Z : Pub) (sp : Spot) (n : Nums) : p2Of Z sp n = p2Ft Z.P.firstTree sp n := rfl

/-- Where the maker makes a block: its place and its rounds. -/
theorem pureAt_rounds (Z : Pub) (G : Ground) (x : Spot × Nums) {b : Block S Unit}
    (h : pureAt (fun _ _ => some none) G (x.1, p2Of Z x.1 x.2) = some b) :
    b.place = x.1.place ∧ b.rounds = rounds (p2Ft Z.P.firstTree x.1 x.2) := by
  revert h
  unfold pureAt
  have hs : (p2Of Z x.1 x.2).stands = standsOf x.1 := rfl
  simp only [hs]
  cases standsOf x.1 with
  | finish =>
    intro h
    obtain rfl : _ = b := Option.some.inj h
    exact ⟨rfl, rfl⟩
  | head =>
    cases x.1.place.link with
    | none =>
      intro h
      have h' : (none : Option (Block S Unit)) = some b := h
      cases h'
    | some l =>
      simp only [Option.bind_some]
      cases pureLetters G l with
      | none =>
        intro h
        have h' : (none : Option (Block S Unit)) = some b := h
        cases h'
      | some HP =>
        intro h
        obtain rfl : _ = b := Option.some.inj h
        exact ⟨rfl, rfl⟩
  | link =>
    cases x.1.place.link with
    | none =>
      intro h
      have h' : (none : Option (Block S Unit)) = some b := h
      cases h'
    | some l =>
      intro h
      obtain rfl : _ = b := Option.some.inj h
      exact ⟨rfl, rfl⟩

/-- **THE GENERAL LAW.** -/
theorem k2_lot_rounds (Z : Pub) (G : Ground) : ∀ b ∈ (ProofFile.k2Pure Z).blocks G,
    b.rounds = [] ∨ ∃ x ∈ ((spotsOf Z.cuts).map fun l => madeW l (prepOf Z G)).getD [],
      b.place = x.1.place ∧ b.rounds = rounds (p2Ft Z.P.firstTree x.1 x.2) := by
  intro b hb
  have e : (ProofFile.k2Pure Z).blocks G =
      (pureTable (fun _ _ => some none) Z G).map (fun b => b.retype) ++ [] := rfl
  rw [e, List.append_nil] at hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
  unfold pureTable purePlaces pureSpots at hc
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hc
  have hm : ((spotsOf Z.cuts).map (p2All Z G)).getD [] =
      (((spotsOf Z.cuts).map fun l => madeW l (prepOf Z G)).getD []).map
        fun x => (x.1, p2Of Z x.1 x.2) := by
    cases spotsOf Z.cuts with
    | none => rfl
    | some l => exact p2All_made Z G l
  rw [hm, List.find?_map]
  cases hf : (((spotsOf Z.cuts).map fun l => madeW l (prepOf Z G)).getD []).find?
      ((fun x : Spot × P2 => x.1.name == sp.name) ∘ fun x => (x.1, p2Of Z x.1 x.2)) with
  | none => exact Or.inl rfl
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    cases hp : pureAt (fun _ _ => some none) G (x.1, p2Of Z x.1 x.2) with
    | none =>
      refine Or.inl ?_
      show ((pureAt (fun _ _ => some none) G (x.1, p2Of Z x.1 x.2)).getD
        (pureMute sp _)).rounds = []
      rw [hp]
      rfl
    | some b =>
      refine Or.inr ⟨x, hx, ?_, ?_⟩
      · show ((pureAt (fun _ _ => some none) G (x.1, p2Of Z x.1 x.2)).getD
          (pureMute sp _)).place = x.1.place
        rw [hp]
        exact (pureAt_rounds Z G x hp).1
      · show ((pureAt (fun _ _ => some none) G (x.1, p2Of Z x.1 x.2)).getD
          (pureMute sp _)).rounds = _
        rw [hp]
        exact (pureAt_rounds Z G x hp).2

/-- The test: at every place that has its numbers, and every place of the table of places that is
the same place, the kind's two rounds are T's list at the name. -/
def k2ListsOk (sps : List Spot) (Pq : Option Prep) (ft : Nat)
    (T : String → List Fmt.DeclaredRound) : Bool :=
  (madeW sps Pq).all fun x => sps.all fun p =>
    !(p.place == x.1.place) || decide (rounds (p2Ft ft x.1 x.2) = T p.name)

/-! ## Closed facts, by the kernel -/

set_option maxRecDepth 1000000 in
theorem k2_made_count : (madeW spotsWritten (prepW proofSizedFull)).length = 25 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- None is dropped: the places that have their numbers are all the written places of the kind. -/
theorem k2_made_names : (madeW spotsWritten (prepW proofSizedFull)).map (·.1.name) =
    (spotsWritten.filter fun p => p.place.kind == .K2).map (·.name) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem k2_made_names_none : (madeW spotsWritten none).map (·.1.name) ≠
    (spotsWritten.filter fun p => p.place.kind == .K2).map (·.name) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **THE CLOSED FACT.** -/
theorem k2_lists_closed : k2ListsOk spotsWritten (prepW proofSizedFull) 0 listAt = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The number of the chain's first tree turned: 1 for 0. -/
theorem k2_lists_tree_one : k2ListsOk spotsWritten (prepW proofSizedFull) 1 listAt = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Two switches' names exchanged in the table: their lists have two rounds each, and differ. -/
theorem k2_lists_swapped : k2ListsOk spotsWritten (prepW proofSizedFull) 0
    (fun n => listAt (if n == "A1:1" then "G2:1" else if n == "G2:1" then "A1:1" else n)) =
      false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The first link's trees struck from the numbers. -/
theorem k2_lists_bent_trees : k2ListsOk spotsWritten bentTrees 0 listAt = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k2_two_rounds : k2SkelW.all (fun k => k.nRounds == 2) = true := by decide +kernel

/-! ## The row -/

/-- **THE ROW, under what the rounds read.** -/
theorem k2_lists_prep {Zq : Pub} {G : Ground} (hs : spotsOf Zq.cuts = some spotsWritten)
    (hP : prepOf Zq G = prepW proofSizedFull) (hF : Zq.P.firstTree = 0) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, ∀ p ∈ spotsWritten, p.place = b.place →
      b.rounds = [] ∨ b.rounds = listAt p.name := by
  intro b hb p hp hpb
  rcases k2_lot_rounds Zq G b hb with h0 | ⟨x, hx, hxp, hxr⟩
  · exact Or.inl h0
  · rw [hs, hP] at hx
    simp only [Option.map_some, Option.getD_some] at hx
    have c := k2_lists_closed
    unfold k2ListsOk at c
    have k := List.all_eq_true.1 (List.all_eq_true.1 c x hx) p hp
    have hpe : (p.place == x.1.place) = true := beq_iff_eq.2 (hpb.trans hxp)
    rw [hpe] at k
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at k
    refine Or.inr ?_
    rw [hxr, hF]
    exact k

/-- **THE ROW, under the first row's hypotheses by field.** -/
theorem k2_lists_spots {Zq : Pub} {G : Ground} (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) (hF : Zq.P.firstTree = 0) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, ∀ p ∈ spotsWritten, p.place = b.place →
      b.rounds = [] ∨ b.rounds = listAt p.name :=
  k2_lists_prep hs (prep_at hz t1 t2 t3 t4 t5) hF

/-- Where the plain road makes the public part, the first chain takes over no tree. -/
theorem first_tree_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zq : Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Zq) : Zq.P.firstTree = 0 := by
  have hP : Zq.P = ProofFile.plainStarts.par Zq.first :=
    (ProofFile.Law.pubBy_fields
      (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Zq from hZ)).2.2.2.2.1
  rw [hP]
  rfl

/-- **THE ROW, where the plain road makes the public part.** -/
theorem k2_lists_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zq : Pub} {G : Ground}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Zq) (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, ∀ p ∈ spotsWritten, p.place = b.place →
      b.rounds = [] ∨ b.rounds = listAt p.name :=
  k2_lists_spots hs hz t1 t2 t3 t4 t5 (first_tree_made hZ)

/-- Beside the first row: no block of the lot is without a round. -/
theorem k2_lists_whole {Zq : Pub} {G : Ground} (hs : spotsOf Zq.cuts = some spotsWritten)
    (hz : Zq.p.chains.made.sized.proof = proofSizedFull)
    (t1 : proofSizedFull.request = G.first.shape) (t2 : proofSizedFull.codes = G.first.codes)
    (t3 : Zq.s₀.st.codes = proofSizedFull.codes)
    (t4 : Zq.s₀.check.frame.shape = proofSizedFull.request)
    (t5 : proofSizedFull.set.samples = Zq.P.samples) (hF : Zq.P.firstTree = 0)
    (hH : (pureLetters G 24).map headPlanOk = some true) :
    ∀ b ∈ (ProofFile.k2Pure Zq).blocks G, ∀ p ∈ spotsWritten, p.place = b.place →
      b.rounds = listAt p.name := by
  intro b hb p hp hpb
  rcases k2_lists_spots hs hz t1 t2 t3 t4 t5 hF b hb p hp hpb with h0 | h
  · exfalso
    have hk : skel b ∈ k2SkelW := by
      rw [← k2_row_spots hs hz t1 t2 t3 t4 t5 hH]
      exact List.mem_map_of_mem hb
    have h2 : ((skel b).nRounds == 2) = true := List.all_eq_true.1 k2_two_rounds _ hk
    have h3 : b.rounds.length = 2 := eq_of_beq h2
    rw [h0] at h3
    exact absurd h3 (by simp)
  · exact h

end Johnson.AtFull.Lots.K2

#print axioms Johnson.AtFull.Lots.K2.p2Of_ft
#print axioms Johnson.AtFull.Lots.K2.pureAt_rounds
#print axioms Johnson.AtFull.Lots.K2.k2_lot_rounds
#print axioms Johnson.AtFull.Lots.K2.k2_made_count
#print axioms Johnson.AtFull.Lots.K2.k2_made_names
#print axioms Johnson.AtFull.Lots.K2.k2_made_names_none
#print axioms Johnson.AtFull.Lots.K2.k2_lists_closed
#print axioms Johnson.AtFull.Lots.K2.k2_lists_tree_one
#print axioms Johnson.AtFull.Lots.K2.k2_lists_swapped
#print axioms Johnson.AtFull.Lots.K2.k2_lists_bent_trees
#print axioms Johnson.AtFull.Lots.K2.k2_two_rounds
#print axioms Johnson.AtFull.Lots.K2.k2_lists_prep
#print axioms Johnson.AtFull.Lots.K2.k2_lists_spots
#print axioms Johnson.AtFull.Lots.K2.first_tree_made
#print axioms Johnson.AtFull.Lots.K2.k2_lists_made
#print axioms Johnson.AtFull.Lots.K2.k2_lists_whole
