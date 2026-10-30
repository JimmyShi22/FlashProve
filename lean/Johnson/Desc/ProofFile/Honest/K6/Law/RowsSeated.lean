-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/RowsSeated.lean: CONDITIONAL. NOT a law on a distribution of
its own, NOT `plays`, NOT `acc`, and NO evaluation at a description: THE SEAT AND THE LOT's OWN
ROWS, BROUGHT TO ONE SET OF LETTERS. Honest/K6/Law/RowsIn.lean lays the rows of the sub-protocol
"the output head's own rounds" at the places of the blocks that the lot seats and at the public
numbers `headParAt G`; Honest/K6/Law/RowAtHead.lean pays the seat at a written place and at the
numbers of the library's public data. Nothing tied the two.

  1  `seatB_of_members_at`   the seat's test with code (`headSeatB`, Honest/K6/Law/Row.lean) says
     yes wherever what the door asks of the list holds: with `members_at_of_seatB`: it says just
     that
  2  `headLotPlaces`, `headLotSeatB`   THE TEST AT THE LOT's OWN ROWS, WITH CODE, on a chain's list,
     the public part and the segments' built data alone: the lot lays a row; at each row's place the
     seat's test says yes, AND A MEMBER STANDS THERE
     `headSLotAt_places`, `places_test`, `headLotSeatB_iff`   the places are the rows'; a line on
     lists; the test in the rows' own words
  3  `head_lot_members_at`, `seated_isSome`, `head_lot_seated`, `head_good_lot`   where the test
     says yes: at each row's place what the door asks of the list holds; each row of the lot has a
     side, at whatever falls; the structure `HeadSeated` holds of it; and, under the Bool on the
     book, `Good` at every `pre`, at A := False and whatever B, at the row's own On and bud
  4  `head_first_flat`, `head_ground_at_head`, `head_member_at_head`, `head_lot_at_head`,
     `head_lotSeatB_at_head`, `head_good_lot_at_head`   UNDER THE LIBRARY's ONE HYPOTHESIS AT THE
     FULL SIZE (`P5J.AtMgA`), at the ground that the description's maker lays, which is there, AND
     UNDER THE NAMED PUBLIC PREMISE `headFitsB`: a member stands at K6's place; the lot lays one
     row, at that place and at the library's numbers; the test of 2 says yes at the description's
     first chain; so 3 there

All definitions have code.

Called. `headSLot_rows`: Honest/K6/Law/RowsIn.lean. `head_good_all`: Honest/K6/Law/GoodRowSum.lean.
`members_at_of_seatB`, `headSeated_of_seatB`: Honest/K6/Law/Row.lean. `head_seated_at_head`:
Honest/K6/Law/RowAtHead.lean. `headSeated_is`: Honest/K6/Cut.lean. `member_is`:
Honest/K6/Law/MemberIs.lean. `P4.k6_member_at_mg`: Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean.
`IM.k6_of`: Johnson/IMR/K6Seat.lean. `IM.Open.blank`, `IM.Open.W`: Johnson/IMR/SeatOpen.lean. TYPED
ANEW, AND WHY: `head_first_flat`: one line by unfolding; the frame's threads have it
(Honest/Thread/FirstSits.lean: `head_flat`) in a file that this one need not import ·
`seated_isSome`: near the frame's `side_isSome_of_any` (Honest/Thread/Rows.lean), which speaks of a
row with letters, without falls, and ends in `isSome`; here: `Side.seated` itself, at whatever
falls, with the side named. Of the folder Johnson/Goal/ nothing is named here.

Limits. THIS FILE EVALUATES `headLotSeatB` AT NO LIST: its yes at the description's first chain
(`head_lotSeatB_at_head`) is a theorem under the hypothesis and `headFitsB`. In 4: THE HYPOTHESIS IS
A PREMISE: the format's second hash function (`OnBytes.secondHashFunction`), the full size alone, in the goals' scope;
met under four premises on the three public files (Honest/K6/Law/RowAtHead.lean:
`head_seated_at_files`). `headFitsB Zp G = true` IS A PREMISE TOO: named tests on public numbers;
nothing here shows it. The Bool on the book is a premise: this file evaluates it at no book. In
`head_good_lot` and `head_good_lot_at_head` `plays` and `acc` are met for nothing (A := False) and
`fresh` holds by an empty list: of such a term the frame's rule reads `fits`, `exact` and `fresh`.
All that the Limits of Honest/K6/Law/GoodRow.lean and GoodRowSum.lean say holds here: the spender's
half alone; one part at a time. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Cut
import Johnson.Desc.ProofFile.Honest.K6.Law.RowsIn
import Johnson.Desc.ProofFile.Honest.K6.Law.RowAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Claim Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds (Head.Par Head.parOf Head.seatedClaims)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open ProofFile.Honest.Small

variable {St Cm X W₀ Rc Tr : Type}

/-! ## 1 The seat's test says just what the door asks -/

/-- CONDITIONAL. Where every member of the list at the place has the declared rounds and no oracle
message, the seat's test says yes. The converse is `members_at_of_seatB`. -/
theorem seatB_of_members_at {bs : List (Block St Cm)} {p : Head.Par} {at_ : Place}
    (h : ∀ b ∈ bs, b.place = at_ → b.rounds = p.rounds ∧ b.oracles = p.rounds.map fun _ => []) :
    headSeatB bs p at_ = true := by
  unfold headSeatB
  refine List.all_eq_true.2 fun b hb => ?_
  by_cases hp : b.place = at_
  · obtain ⟨hr, ho⟩ := h b hb hp
    simp only [hp, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.all_eq_true, List.isEmpty_iff]
    refine ⟨⟨hr, ?_⟩, fun o ho' => ?_⟩
    · rw [ho, hr, List.length_map]
    · rw [ho] at ho'
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 ho'
      rfl
  · rw [bne_iff_ne.2 hp, Bool.true_or]

/-! ## 2 The test at the lot's own rows -/

/-- **The places at which the lot lays its rows**: of the public part and the segments' built data
alone: those of the blocks that the lot seats, where the test on the public numbers says yes; else
none. -/
def headLotPlaces (Z : Pub) (G : Ground) : List Place :=
  if headFitsB Z G then (P4.k6Hear Z G).map (·.place) else []

/-- **THE SEAT's TEST AT THE LOT's OWN ROWS, WITH CODE**: the lot lays a row; and at each row's
place every member of the chain's list that stands there has the rounds that the verifier's text
declares at `headParAt G` and no oracle message, AND A MEMBER STANDS THERE. On public data alone. -/
def headLotSeatB (bs : List (Block St Cm)) (Z : Pub) (G : Ground) : Bool :=
  !(headLotPlaces Z G).isEmpty &&
    (headLotPlaces Z G).all fun a => headSeatB bs (headParAt G) a && bs.any fun b => b.place == a

/-- The places are the rows'. No premise. -/
theorem headSLotAt_places (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub) (G : Ground) :
    ((headSLotAt (Rc := Rc) (X := X) cells weights).rows Z G).map (·.place) =
      headLotPlaces Z G := by
  unfold headSLotAt headSLot headLotPlaces
  by_cases hf : headFitsB Z G = true
  · simp only [hf, if_true, List.map_map]
    exact List.map_congr_left fun _ _ => rfl
  · simp only [hf, if_false, Bool.false_eq_true, List.map_nil]

/-- A line on lists: a test on the rows' places, asked of the places or of the rows. No premise. -/
theorem places_test {V W Y Pb : Type} (g : Place → Bool) :
    ∀ rows : List (Unlettered V W Y Pb),
      (!(rows.map (·.place)).isEmpty && (rows.map (·.place)).all g) = true ↔
        rows ≠ [] ∧ (rows.all fun r => g r.place) = true
  | [] => ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd rfl h.1⟩
  | a :: l => by
    rw [List.all_map]
    exact ⟨fun h => ⟨List.cons_ne_nil a l, (Bool.and_eq_true_iff.1 h).2⟩,
      fun h => Bool.and_eq_true_iff.2 ⟨rfl, h.2⟩⟩

/-- **The test in the rows' own words.** No premise. -/
theorem headLotSeatB_iff (bs : List (Block St Cm)) (cells : Tr → Cells) (weights : W₀ → Weights)
    (Z : Pub) (G : Ground) :
    headLotSeatB bs Z G = true ↔
      (headSLotAt (Rc := Rc) (X := X) cells weights).rows Z G ≠ [] ∧
      (((headSLotAt (Rc := Rc) (X := X) cells weights).rows Z G).all fun r =>
        headSeatB bs (headParAt G) r.place && bs.any (·.place == r.place)) = true := by
  unfold headLotSeatB
  rw [← headSLotAt_places (Rc := Rc) (X := X) cells weights Z G]
  exact places_test _ _

/-! ## 3 Where the test says yes -/

/-- CONDITIONAL. **What the door asks of the list, AT THE LOT's OWN ROWS**: at each place at which
the lot lays a row every member of the list that stands there has the declared rounds and no oracle
message: the premise of `head_good_row` and of `head_bud_share` (Honest/K6/Law/RowsIn.lean). -/
theorem head_lot_members_at {bs : List (Block St Cm)} {Z : Pub} {G : Ground}
    (h : headLotSeatB bs Z G = true) :
    ∀ a ∈ headLotPlaces Z G, ∀ b ∈ bs, b.place = a →
      b.rounds = (headParAt G).rounds ∧ b.oracles = (headParAt G).rounds.map fun _ => [] := by
  intro a ha
  unfold headLotSeatB at h
  have h2 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 a ha
  exact members_at_of_seatB (Bool.and_eq_true_iff.1 h2).1

/-- CONDITIONAL. Where a member stands at the place, the side is there, at whatever falls. -/
theorem seated_isSome {V W Y Pb : Type} {bs : List (Block St Cm)} {a : Place}
    (h : (bs.any fun b => b.place == a) = true) (row : List (Part V W Y × Sim Pb))
    (fs : List (Fall St)) : ∃ σ, Side.seated bs a row fs = some σ := by
  obtain ⟨c, hc, hp⟩ := List.any_eq_true.1 h
  refine Option.isSome_iff_exists.1 ?_
  unfold Side.seated
  rw [Option.isSome_map]
  exact List.find?_isSome.2 ⟨c, hc, hp⟩

/-- CONDITIONAL. **Each row of the lot is seated**: it has a side over the list, at whatever falls,
and the structure `HeadSeated` holds of that side, at the row's own place and numbers. -/
theorem head_lot_seated {bs : List (Block St Cm)} {Z : Pub} {G : Ground}
    (h : headLotSeatB bs Z G = true) (cells : Tr → Cells) (weights : W₀ → Weights)
    (fs₀ : List (Fall St)) :
    ∀ r ∈ (headSLotAt (Rc := Rc) (X := X) cells weights).rows Z G,
      ∃ σ₀, Side.seated bs r.place r.row fs₀ = some σ₀ ∧
        HeadSeated σ₀ (headWit' cells weights Z G) (headParAt G) r.place := by
  intro r hr
  have ha := List.all_eq_true.1
    ((headLotSeatB_iff (Rc := Rc) (X := X) bs cells weights Z G).1 h).2 r hr
  obtain ⟨hs, hm⟩ := Bool.and_eq_true_iff.1 ha
  obtain ⟨b, _, rfl⟩ := headSLot_rows hr
  obtain ⟨σ₀, hσ⟩ := seated_isSome hm
    (headUnlettered (X := X) (headWit' cells weights Z G) (headParAt G) b.place).row fs₀
  exact ⟨σ₀, hσ, headSeated_of_seatB hσ hs⟩

/-- CONDITIONAL. **`Good` at each row of the lot**, at the side that `Side.seated` lays over the
list AT WHATEVER FALLS, at A := False and whatever B, at the row's own On and bud. `plays` and `acc`
ARE MET FOR NOTHING THERE; `fresh` HOLDS BY AN EMPTY LIST. `pre` is a free letter: the term stands
at every `pre`. -/
theorem head_good_lot {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    {bs : List (Block St Cm)} {Z : Pub} {G : Ground} (h : headLotSeatB bs Z G = true)
    (cells : Tr → Cells) (weights : W₀ → Weights) (fs₀ : List (Fall St)) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat)
    (B : Coins Bk → St → Mid (Local W₀ Rc Inst Tr) X → Env → Prop)
    (hB : ∀ a ∈ headLotPlaces Z G, ((List.range 8).all fun i => noneSpent Bk ⟨a, i⟩) = true) :
    ∀ r ∈ (headSLotAt (Rc := Rc) (X := X) cells weights).rows Z G,
      ∃ σ₀, Side.seated bs r.place r.row fs₀ = some σ₀ ∧
        Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) B r.On r.bud := by
  intro r hr
  obtain ⟨σ₀, hσ, hS⟩ := head_lot_seated h cells weights fs₀ r hr
  have hp : r.place ∈ headLotPlaces Z G := by
    rw [← headSLotAt_places (Rc := Rc) (X := X) cells weights Z G]
    exact List.mem_map_of_mem hr
  obtain ⟨b, _, rfl⟩ := headSLot_rows hr
  exact ⟨σ₀, hσ, head_good_all φ hS Bk ord chain firstTree B (hB _ hp)⟩

/-! ## 4 Under the library's one hypothesis at the full size -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The description's first chain is cF. By unfolding. No premise. -/
theorem head_first_flat (o : ProofFile.SecondHashFunctionArgument) : (P5J.F0T o Zp Np cF).first.blocksInOrder = cF.blocksInOrder := rfl

/-- CONDITIONAL. **The ground is there**: under the hypothesis the description's maker lays one. -/
theorem head_ground_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G := by
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  exact ⟨Bs.G₀, O.blank⟩

/-- CONDITIONAL. **A member of the description's first chain stands at K6's place.** -/
theorem head_member_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder.any fun b => b.place == IM.k6Place) = true := by
  obtain ⟨b, e, M⟩ := P4.k6_member_at_mg h.toAtMg
  exact List.any_eq_true.2 ⟨b, List.mem_of_getElem? e, beq_iff_eq.2 (member_is M).1⟩

/-- CONDITIONAL. **THE TWO SETS OF LETTERS ARE ONE**: at the ground that the description's maker
lays, where the test on the public numbers says yes: the lot lays its rows at K6's place alone, and
`headParAt` there is the term at the library's public data. -/
theorem head_lot_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : headFitsB Zp G = true) :
    headLotPlaces Zp G = [IM.k6Place] ∧
      headParAt G = (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨_, _, b', ms, _, _, hms, hsc, _, hsz, _, _⟩ := IM.k6_of h.scope h.reads O
  have hk : P4.k6Hear Zp Bs.G₀ = [b'] := by
    unfold P4.k6Hear
    rw [hms, hsz]
    show (Head.seatedClaims Bs.G₀.W 24 ms).toList = [b']
    rw [hsc]
    rfl
  refine ⟨?_, ?_⟩
  · unfold headLotPlaces
    rw [if_pos hf, hk]
    show [b'.place] = [IM.k6Place]
    rw [(headSeated_is hsc).1]
    rfl
  · have eW : Bs.G₀.W = P5J.At.X Zp := O.W
    unfold headParAt
    rw [eW]
    rfl

/-- CONDITIONAL. **THE LOT's ROW IS SEATED UNDER THE HEAD AND `headFitsB`'s YES**: the test at the
lot's own rows says yes at the description's first chain: under the one hypothesis and the named
public premise. -/
theorem head_lotSeatB_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : headFitsB Zp G = true) :
    headLotSeatB cF.blocksInOrder Zp G = true := by
  obtain ⟨hp, hn⟩ := head_lot_at_head h hG hf
  unfold headLotSeatB
  rw [hp, hn, show ([IM.k6Place] : List Place).isEmpty = false from rfl]
  simp only [Bool.not_false, Bool.true_and, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  exact ⟨seatB_of_members_at (head_seated_at_head h), head_member_at_head h⟩

/-- CONDITIONAL. **`Good` at each row of the lot, over the description's first chain**, at whatever
falls, at A := False and whatever B, at the row's own On and bud: under the one hypothesis, the
named public premise and the Bool on the book. `plays` and `acc` ARE MET FOR NOTHING THERE; `fresh`
HOLDS BY AN EMPTY LIST. (The letter r in the end is a row of the lot; the r in h is the run.) `pre`
is a free letter: the term stands at every `pre`. -/
theorem head_good_lot_at_head {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (φ : Face (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) Inst)
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (hf : headFitsB Zp G = true)
    (cells : Tr → Cells) (weights : W₀ → Weights) (fs₀ : List (Fall P5J.TS)) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat)
    (B : Coins Bk → P5J.TS → Mid (Local W₀ Rc Inst Tr) X → Env → Prop)
    (hB : ((List.range 8).all fun i => noneSpent Bk ⟨IM.k6Place, i⟩) = true) :
    (headSLotAt (Rc := Rc) (X := X) cells weights).rows Zp G ≠ [] ∧
    ∀ r ∈ (headSLotAt (Rc := Rc) (X := X) cells weights).rows Zp G,
      ∃ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀ ∧
        Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) B r.On r.bud := by
  have hy := head_lotSeatB_at_head h hG hf
  refine ⟨((headLotSeatB_iff (Rc := Rc) (X := X) cF.blocksInOrder cells weights Zp G).1 hy).1, ?_⟩
  refine head_good_lot φ hy cells weights fs₀ Bk ord chain firstTree B fun a ha => ?_
  rw [(head_lot_at_head h hG hf).1] at ha
  obtain rfl : a = IM.k6Place := List.mem_singleton.1 ha
  exact hB

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.seatB_of_members_at
#print axioms ProofFile.Honest.K6.headSLotAt_places
#print axioms ProofFile.Honest.K6.places_test
#print axioms ProofFile.Honest.K6.headLotSeatB_iff
#print axioms ProofFile.Honest.K6.head_lot_members_at
#print axioms ProofFile.Honest.K6.seated_isSome
#print axioms ProofFile.Honest.K6.head_lot_seated
#print axioms ProofFile.Honest.K6.head_good_lot
#print axioms ProofFile.Honest.K6.head_first_flat
#print axioms ProofFile.Honest.K6.head_ground_at_head
#print axioms ProofFile.Honest.K6.head_member_at_head
#print axioms ProofFile.Honest.K6.head_lot_at_head
#print axioms ProofFile.Honest.K6.head_lotSeatB_at_head
#print axioms ProofFile.Honest.K6.head_good_lot_at_head
#print axioms ProofFile.Honest.K6.headLotPlaces
#print axioms ProofFile.Honest.K6.headLotSeatB
