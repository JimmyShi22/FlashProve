--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/SimulatorShare.lean: what the sub-protocol "the output head's
own rounds" (kind K6) hands in for the zero knowledge of the online honest prover, stated at what the
honest prover's maker (`onlineProverFromPublicFiles`, Honest/AtPure.lean) returns: at its description, its book of coins
and its ground, with no premise left on the book, on the block's declared rounds or on the place.
General in the filling and in the types of the index and of the stored tables' randomness.

Words. The hypothesis: `P5J.AtMgA`, the library's one hypothesis on the proof file's description at
the full size. A fall (`Fall`, Honest/Side.lean): a public test for an event at which a sub-protocol
may reject an honest run; `exact` and `fresh` read none. A and B: the two conditions of `Good` before
and after the place, which whoever joins the rows sets. A row without letters (`Unlettered`): a place,
its parts with their simulators, On and bud, and no A or B. "A conclusion's form": a definition that
is meant to stand at the end of a theorem and claims nothing by itself. A border: the place between two
members of a chain's flat list, by the number of the member behind it. The payer: the files of this
folder that work on completeness (Honest/K6/Term/Statements.lean). (P1): that the book of coins lends a
side its runs, so that the frame's set-up routine returns at its member.

WHAT IT IS NOT.
  * IT NAMES NO PROVER. `HeadSimulatorShare` reads of the maker's return its public part, ground,
    description and book, and never its prover's sides; it holds at every filling and every reader of
    the index. That the honest prover's side at K6's place is this row is another statement:
    Honest/K6/Term/SimulatorAtTheHonestProver.lean.
  * NOT zero knowledge, NOT hiding, of anything. One part's law at a time, all else fixed before the
    coins; NO JOINT LAW of the eight parts, and none with any other kind's.
  * NOT the playing and NOT the verifier's acceptance: `Good` stands here at A := False, where its
    fields `plays` and `acc` hold emptily. `Owed` (Honest/Owed.lean) is the structure of hypotheses
    from which the frame goes on. What stands here is K6's clause of the premise hand₁ of the rule
    that ends in `Owed`: THREE OF THE FIVE FIELDS of K6's part of `Owed.good` (fits, exact, fresh).
    `Owed.good` asks `Good` at the list's own A and B: `plays` and `acc` there are unpaid; at lists
    made mute (`Sides.mute`, Honest/Law/Rule/Mute.lean) they ask nothing. WITH `acc` MUTED, NOTHING IN `Owed`
    SHOWS THAT A RUN EVER CALLS K6's PARTS: that has to come from acceptance at the same description, book,
    prover and lists (Honest/Law/OwedAtRun.lean, its second limit). Of `Owed.owed` it gives the
    rule's premises for the clauses On and bud, not its two returns (that the book hands the carried
    runs and that the walk has a state at the part); and NOTHING of `Owed.runs`.
  * OF THE BOOK IT READS ONE TEST. The fields `fits` and `exact` of `Good` do not read the book: the law
    in `exact` is over the runs that the part itself states. `fresh` reads it, and holds by an empty
    list. So "at the maker's book" adds to the library's law just this: no entry spends a coin of K6's.
    THAT THE BOOK LENDS K6's TEN RUNS, under these names and counts, marked as spent, sharing no coin,
    is not said here: Honest/K6/Law/LendsAtBook.lean (`k6_row_is_lent`), StretchAtBook.lean.
  * AT A ZERO CHALLENGE NOTHING IS SAID, AND NOTHING STOPS THE PART. A masked sumcheck sends each end
    value plus a challenge times a mask entry. At that challenge 0 parts 2, 5, 6 and 7 would send
    2 + 4 + 2 + 2 end values bare, and part 7's are made of the head's matrix, which is of the index.
    0 IS NO CHALLENGE THAT THE ROUND CAN DRAW: the verifier's own declared round "PSC Y" marks its one
    element as never 0, and the verifier's general step refuses a view in which it is 0. So `exact` is
    not asked there: `drawsFit` asks that rule (`drawsMarkedNonzeroHaveNonzeroWords`; Honest/K6/Term/BetaIsNeverZero.lean). That at
    every value of the verifier's randomness the challenges are such as the rounds can draw is a
    theorem of other authors: `due_atFiles` (E2E/BridgePaidAtFiles.lean), at the description at which
    the prover plays; its one premise on the declared rounds is paid by `nonZero_atFiles`
    (E2E/BridgeNonZero.lean). A statement over the verifier's randomness takes that theorem at each
    value; it is no debt of this kind's.
  * NOT the owner's sentence. K6's parts own no coin. What they send is masked by entries of the
    segment's mask row (how: Honest/K6/Term/OwedBeside.lean, (i)), whose owner is another kind's
    sender. That these entries are uniform and independent of what that owner shows is the field
    `fresh` at THAT owner, which is not shown here. Behind
    K6 the same entries are carried by later parts, each of which owes its own `exact` at every
    fixed carried run.
  * The field `fresh` holds here by an empty list: no entry of the book spends a coin of K6's.
  * On := True: nothing is asked of the state before a part, because `exact` holds at every state.
    So no test can show this On false. bud bears no load either: K6 sends no table, and the library's
    `exact` holds at every bud. `budBites` shows only that
    the bud that is written is not "always true".
  * The honest-verifier form: all challenges are fixed before the coins.
  * CONDITIONAL on the library's one hypothesis at the full size (`P5J.AtMgA`) and on the maker's
    return. Nothing in this file shows that either can be met. Under two tests on the public files
    Honest/K6/Term/SimulatorAtTheHonestProver.lean has both, by two theorems of other authors.

  `head_rounds_send_no_seed`   no declared round of the kind is a round "SEND seed"
  `noneSpent_of_spentBy_nil`   the test on the book, from the frame's list
  `head_noneSpent_at_maker`    at the book that the maker returns no entry spends a coin of K6's
  `headSided_cases`, `headSided_coins`   the row's eight pairs, one by one; their counts of coins
  `HeadSimulatorShare`         the share, field by field
  `headSimulatorShare_at_maker`   it holds at what the maker returns
  `HeadSimulatorShare.hand`, `.budDebt`, `.onDebt`, `.onFromS`   the forms in which the frame's rules take it
-/
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.BookOwners
import Johnson.Desc.ProofFile.Honest.Thread.OnSaid
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute
import Johnson.Desc.ProofFile.Honest.K6.Law.RowsSeatedAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.WindowNumbers
import Johnson.Desc.ProofFile.Honest.K6.Law.SpendsWritten
import Johnson.Desc.ProofFile.Honest.K6.Term.RowThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.Kinds
open ProofFile.Honest.Small

/-! ## 1 The book -/

/-- **No declared round of the kind is a round "SEND seed".** No premise. -/
theorem head_rounds_send_no_seed (p : Head.Par) :
    ∀ z ∈ p.rounds, z.entry.name ≠ "SEND seed" := by
  intro z hz
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hz
  letI := p.sizes
  show R.name ≠ "SEND seed"
  simp only [Head.rounds, Norm.rounds, FinalNorm.rounds, drawPoint.rounds, drawJoin.rounds,
    sendThenBatch.rounds, level.rounds, sumcheck.rounds, List.mem_append, List.mem_cons,
    List.mem_replicate, List.not_mem_nil, or_false] at hR
  simp only [or_assoc] at hR
  rcases hR with rfl | rfl | h | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl |
    rfl | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl
  case inr.inr.inl =>
    have hN0 : Norm.lNI = 0 := rfl
    rw [hN0] at h
    simp at h
  all_goals (dsimp only; decide)

/-- Where no part spends a coin of the part at o, the test `noneSpent` says yes. -/
theorem noneSpent_of_spentBy_nil {B : ProverCoinCounts} {o : Addr} (h : ∀ q, B.spentBy o q = []) :
    noneSpent B o = true := by
  refine List.all_eq_true.2 fun e he => ?_
  cases hx : (e.once && e.owner == o) with
  | false => rfl
  | true =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hx
    have hm : e ∈ B.spentBy o e.spender := by
      unfold ProverCoinCounts.spentBy
      refine List.mem_filter.2 ⟨he, ?_⟩
      simp [h1, h2]
    rw [h e.spender] at hm
    cases hm

variable {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h; the maker returns. **At the book that the maker returns no entry
spends a coin of one of K6's eight parts.** General in the filling. -/
theorem head_noneSpent_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ((List.range 8).all fun i => noneSpent A.B ⟨IM.k6Place, i⟩) = true := by
  obtain ⟨b, hb, hp⟩ := List.any_eq_true.1 (head_member_at_head h)
  have hp' : b.place = IM.k6Place := beq_iff_eq.1 hp
  have hr := (head_seated_at_head h b hb hp').1
  refine List.all_eq_true.2 fun i _ => noneSpent_of_spentBy_nil fun q => ?_
  have hs := bookWhole_spent_nil (K14.atPure_book_at_head h hA) (k6_placesOk_at_head h) (b := b) hb
    (by rw [hr]; exact head_rounds_send_no_seed _) i q
  rw [hp'] at hs
  exact hs

/-! ## 2 The share -/

/-- **What the kind K6 hands in, at a return of the maker.** `weights`: the reader of the index, by
public part. The rows are those of `headSimulatorLot weights` (Honest/K6/Term/RowThrough.lean) at the
returned public part and ground. A definition: a conclusion's form. -/
structure HeadSimulatorShare (weights : Pub → W₀ → Weights) (returned : OnlineProverWithDescription W₀ Rc Cells X₀ X) :
    Prop where
  /-- the lot lays one row, at K6's place -/
  oneRow : ((headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G).map
    (·.place) = [IM.k6Place]
  /-- a sub-protocol of the returned description's first chain stands at that place -/
  seated : (returned.F.first.blocksInOrder.any fun b => b.place == IM.k6Place) = true
  /-- the returned book passes its own tests at the returned description: among them, that no coin
  stands in two entries that spend it, and that a coin which a part spends is handed to no part in
  front of it -/
  book : returned.B.word returned.F = none
  /-- `Good` at the row's side over the returned description's first chain, at the returned book, at
  every list of falls and every `pre`: its fields `fits`, `exact`, `fresh`. At A := False: `plays` and
  `acc` hold emptily. `fits` and `exact` do not read the book -/
  good : ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G,
    ∀ (falls : List (Fall returned.F.S₁)) σ,
      Side.seated returned.F.first.blocksInOrder r.place r.row falls = some σ →
      ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
        (after : Coins returned.B → returned.F.S₁ → Mid (Local W₀ Rc Inst Cells) X → Env → Prop),
        Good pre .own σ returned.B (orderOf returned.F) 0 0 (fun _ _ _ _ => False) after r.On r.bud
  /-- the condition before a part asks nothing -/
  on : ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G,
    ∀ u ca m front, r.On u ca m front
  /-- the condition on the positions read holds at every reader of trees, number and challenges -/
  bud : ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G,
    ∀ (falls : List (Fall returned.F.S₁)) σ,
      Side.seated returned.F.first.blocksInOrder r.place r.row falls = some σ →
      ∀ u ∈ σ.members, ∀ (tree : Nat → List Nat) (n : Nat) (ds : List Fmt.Drawn),
        r.bud u.number ds (asksFrom tree (u.rounds.map (·.2.length)) n)
  /-- and it is false at one position. It bears no load: K6 sends no table -/
  budBites : ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G,
    ∀ j ds, ¬ r.bud j ds [[[0]]]
  /-- no part has a stop of either sort -/
  noStop : ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G,
    ∀ q ∈ r.row, (∀ loc ds, q.1.bad loc ds = none) ∧ ∀ v loc ds, q.1.hid v loc ds = none
  /-- no part has a coin of its own, and none is handed a run to carry -/
  noOwnCoin : ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G,
    ∀ q ∈ r.row, q.1.takes = ⟨0, 0⟩ ∧ q.1.carries = []
  /-- each simulator takes as many coins as its part spends -/
  coinsAlike : ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G,
    ∀ q ∈ r.row, q.2.takes.f = 0 ∧ (q.1.spends.map (·.2.f)).sum = 0 ∧
      q.2.takes.e = (q.1.spends.map (·.2.e)).sum
  /-- each simulator's output is a function of its own coins alone -/
  simulatorsReadCoinsAlone :
    ∀ r ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G,
    ∀ q ∈ r.row, ∀ pub pub' front front' ds ds' asks asks' c,
      q.2.tell pub front ds asks c = q.2.tell pub' front' ds' asks' c

/-- A row of the lot, written out. -/
theorem headSimulatorLot_rows {weights : Pub → W₀ → Weights} {Zq : Pub} {G : Ground}
    {r : Unlettered (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X Inst}
    (hr : r ∈ (headSimulatorLot weights).rows Zq G) :
    ∃ a, r = headUnlettered (headWit' id (weights Zq) Zq G) (headParAt G) a := by
  obtain ⟨b, _, e⟩ := headSLot_rows (fits := headFitsB) (wit := headWit' id (weights Zq)) hr
  exact ⟨b.place, e⟩

/-- CONDITIONAL: the hypothesis h. **The lot lays one row**: the row without letters at the filling's
reader, at the library's public numbers, at K6's place. -/
theorem headSimulatorLot_one_row (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (weights : Pub → W₀ → Weights) :
    (headSimulatorLot (Rc := Rc) (X := X) weights).rows Zp G =
      [headUnlettered (headWit' id (weights Zp) Zp G)
        (Head.parOf (P5J.At.X Zp).hS (Head.Law.workOf (P5J.At.X Zp))) IM.k6Place] := by
  have hp : ((headSimulatorLot (Rc := Rc) (X := X) weights).rows Zp G).map (·.place) =
      [IM.k6Place] :=
    (headSLotAt_places (Rc := Rc) (X := X) id (weights Zp) Zp G).trans (head_lot_under_head h hG).1
  cases hrows : (headSimulatorLot (Rc := Rc) (X := X) weights).rows Zp G with
  | nil =>
    rw [hrows] at hp
    cases hp
  | cons r t =>
    rw [hrows] at hp
    cases t with
    | cons r' t' =>
      have hl := congrArg List.length hp
      simp at hl
    | nil =>
      obtain ⟨a, e⟩ := headSimulatorLot_rows (weights := weights) (Zq := Zp) (G := G) (r := r)
        (by rw [hrows]; exact List.mem_cons_self ..)
      have ha : r.place = IM.k6Place := (List.cons.inj hp).1
      rw [e] at ha
      have ha' : a = IM.k6Place := ha
      rw [e, ha', (head_lot_under_head h hG).2]

/-- The eight pairs of a row, one by one. -/
theorem headSided_cases (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place)
    {Q : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X × Sim Inst → Prop}
    (quiet : ∀ i, Q ((quietPart : Part Unit HeadAsk Unit).lift (fun _ => ()) wit (fun _ => ())
      (fun x _ => x), quietSim ⟨at_, i⟩))
    (scalars : ∀ name n vals i, Q ((scalarsPart name n vals : Part Unit HeadAsk Unit).lift
      (fun _ => ()) wit (fun _ => ()) (fun x _ => x), scalarsSim ⟨at_, i⟩ n))
    (sum : ∀ name endName (J : SumJob HeadAsk Unit) i, Q ((sumPart name endName J :
      Part Unit HeadAsk Unit).lift (fun _ => ()) wit (fun _ => ()) (fun x _ => x),
      sumSim ⟨at_, i⟩ J.shape)) :
    ∀ q ∈ headSided (X := X) wit p at_, Q q := by
  intro q hq
  simp only [headSided, headRow, headParts, headSims, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact quiet _
  · exact scalars _ _ _ _
  · exact sum _ _ _ _
  · exact quiet _
  · exact scalars _ _ _ _
  · exact sum _ _ _ _
  · exact sum _ _ _ _
  · exact sum _ _ _ _

/-- Each of the row's simulators takes as many coins as its part spends: none of the base field; of
the extension field none, 9, 7, and at a masked sumcheck in n variables with `lead` claimed sums and
`ends` end values lead + (2 n + 3) + ends. No premise. -/
theorem headSided_coins (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    ∀ q ∈ headSided (X := X) wit p at_, q.2.takes.f = 0 ∧ (q.1.spends.map (·.2.f)).sum = 0 ∧
      q.2.takes.e = (q.1.spends.map (·.2.e)).sum := by
  have hsum : ∀ lead n ends : Nat,
      runOf (pointShape lead n ends) = ownRun (pointShape lead n ends) + (ends + 0) := by
    intro lead n ends
    have h1 : runOf (pointShape lead n ends) = (scalarsOf (pointShape lead n ends)).sum := by
      unfold runOf
      rw [← List.sum_eq_foldl]
    rw [h1, scalarsOf_point, k6_ownRun_point]
    simp [List.sum_replicate]
    omega
  intro q hq
  simp only [headSided, headRow, headParts, headSims, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, hsum _ _ _⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, hsum _ _ _⟩
  · exact ⟨rfl, rfl, hsum _ _ _⟩
  · exact ⟨rfl, rfl, hsum _ _ _⟩

/-- CONDITIONAL: the hypothesis h; the maker returns. **THE SHARE HOLDS AT WHAT THE MAKER RETURNS**,
at every filling and every reader of the index. -/
theorem headSimulatorShare_at_maker (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (weights : Pub → W₀ → Weights) :
    HeadSimulatorShare weights A := by
  have hB := head_noneSpent_at_maker h hA
  have hW := (atPure_tests hA).1
  have hG₀ := (atPure_ok hA).2.1
  obtain ⟨G, B, H, rd, rw', rfl⟩ := atPure_is h.laid hA
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G := hG₀
  refine
    { oneRow := ?_, seated := head_member_at_head h, book := hW, good := ?_, on := ?_, bud := ?_
      budBites := ?_, noStop := ?_, noOwnCoin := ?_, coinsAlike := ?_
      simulatorsReadCoinsAlone := ?_ }
  · exact (headSLotAt_places (Rc := Rc) (X := X) id (weights Zp) Zp G).trans
      (head_lot_under_head h hG).1
  · intro r hr falls σ hσ pre after
    obtain ⟨σ₀, hσ₀, g⟩ := (head_good_lot_under_head (pre := pre) .own h hG id (weights Zp) falls B
      (orderOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) 0 0 after hB).2 r hr
    obtain rfl : σ₀ = σ := Option.some.inj (hσ₀.symm.trans hσ)
    exact g
  · intro r hr u ca m front
    obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
    trivial
  · intro r hr falls σ hσ u hu tree n ds
    obtain ⟨σ₀, hσ₀, hS⟩ := head_lot_seated (Rc := Rc) (X := X) (head_lotSeatB_under_head h hG) id
      (weights Zp) falls r hr
    obtain rfl : σ₀ = σ := Option.some.inj (hσ₀.symm.trans hσ)
    obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
    exact head_bud hS u hu tree n ds
  · intro r hr j ds hb
    obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
    have hb' : (([[[0]]] : List (List (List Nat))).all (·.isEmpty)) = true := hb
    exact absurd hb' (by decide)
  · intro r hr
    obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
    exact headSided_cases _ _ _ (fun _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩)
      (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩)
      (fun _ _ _ _ => ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩)
  · intro r hr
    obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
    exact headSided_cases _ _ _ (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ _ => ⟨rfl, rfl⟩)
      (fun _ _ _ _ => ⟨rfl, rfl⟩)
  · intro r hr
    obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
    exact headSided_coins _ _ _
  · intro r hr
    obtain ⟨a, rfl⟩ := headSimulatorLot_rows hr
    exact headSided_cases _ _ _ (fun _ _ _ _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-! ## 3 The forms in which the frame's rule takes it -/

section
variable {weights : Pub → W₀ → Weights} {returned : OnlineProverWithDescription W₀ Rc Cells X₀ X}

/-- **What the rule asks of `Good`** (`file_owed_rows`, Honest/Thread/Rows.lean: hand₁) at every list
with letters whose place, parts, On and bud are a row's of the lot: whatever its letters A and B. -/
theorem HeadSimulatorShare.hand (s : HeadSimulatorShare weights returned)
    (L : Lettered returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Cells)
      (Local W₀ Rc Inst Cells) X Inst)
    (hL : L.bare ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G)
    (falls : List (Fall returned.F.S₁)) :
    ∀ σ, L.side returned.F.first.blocksInOrder falls = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf returned.F 0) returned.F.first.blocksInOrder L.place) .own σ
        returned.B (orderOf returned.F) 0 0 A' B' L.On L.bud :=
  fun σ hσ => ⟨_, _, s.good L.bare hL falls σ hσ _ fun _ _ _ _ => False⟩

/-- **K6's part of `Owed.good`, whole, at such a list made mute** (`Lettered.mute`,
Honest/Law/Rule/Mute.lean: its A and B set to "never", where `plays` and `acc` ask nothing): in the form
in which `Owed.good` asks it, with what the field holds beside A and B. It adds nothing to `.hand`. With
`acc` muted, nothing in `Owed` shows that a run ever calls K6's parts. -/
theorem HeadSimulatorShare.goodAtMute (s : HeadSimulatorShare weights returned)
    (L : Lettered returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Cells)
      (Local W₀ Rc Inst Cells) X Inst)
    (hL : L.bare ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G)
    (falls : List (Fall returned.F.S₁)) (base : List VerifiableInference.Desc.OpenedColumn) (skip : Nat) :
    (L.mute.withField 0 0 returned.F.first.blocksInOrder base skip).goodAt (earlierOf returned.F 0) .own
      returned.F.first.blocksInOrder (orderOf returned.F) 0 0 falls :=
  goodAt_mute (s.hand L hL falls)

/-- **The first chain's clause of `BudDebts`** (Honest/Law/OwedRule.lean: bud₁) at such a list, to its
letter. -/
theorem HeadSimulatorShare.budDebt (s : HeadSimulatorShare weights returned)
    (L : Lettered returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Cells)
      (Local W₀ Rc Inst Cells) X Inst)
    (hL : L.bare ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G) :
    ∀ σ, L.side returned.F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      returned.F.first.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due returned.F = true →
      L.bud u.number ((ρ.first.drop n).take u.rounds.length)
        (asksFrom (treeAsks returned.F ρ 0) (u.rounds.map (·.2.length))
          (((rowsOfChain returned.F.first.blocksInOrder).take n).map (·.2.length)).sum) :=
  fun σ hσ u hu _ _ _ _ _ _ _ => s.bud L.bare hL [] σ hσ u hu _ _ _

/-- **The end of the first chain's clause of `OnDebts`** at such a list: at every member, carried
runs, state and front. -/
theorem HeadSimulatorShare.onDebt (s : HeadSimulatorShare weights returned)
    (L : Lettered returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Cells)
      (Local W₀ Rc Inst Cells) X Inst)
    (hL : L.bare ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G) :
    ∀ u ca m front, L.On u ca m front :=
  s.on L.bare hL

/-- **The form in which the rule `file_owed_rows` takes On** (`OnFromS`, Honest/Thread/OnSaid.lean), at
such a list: at every thread, every clause `Said`, every border and every `len`. It asks nothing,
because On asks nothing. -/
theorem HeadSimulatorShare.onFromS (s : HeadSimulatorShare weights returned)
    (L : Lettered returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Cells)
      (Local W₀ Rc Inst Cells) X Inst)
    (hL : L.bare ∈ (headSimulatorLot (Rc := Rc) (X := X) weights).rows returned.Z returned.G)
    (T : Thread returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Cells)
      (Local W₀ Rc Inst Cells) X Inst)
    (Said : Nat → Coins returned.B → Mid (Local W₀ Rc Inst Cells) X → Prop) (b : Nat)
    (len : Nat → Nat → Nat) : OnFromS T Said L b len :=
  fun _ _ u _ _ m _ ca front _ _ _ => s.on L.bare hL u ca m front

end

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.head_rounds_send_no_seed
#print axioms ProofFile.Honest.K6.noneSpent_of_spentBy_nil
#print axioms ProofFile.Honest.K6.head_noneSpent_at_maker
#print axioms ProofFile.Honest.K6.HeadSimulatorShare
#print axioms ProofFile.Honest.K6.headSimulatorLot_rows
#print axioms ProofFile.Honest.K6.headSided_cases
#print axioms ProofFile.Honest.K6.headSided_coins
#print axioms ProofFile.Honest.K6.headSimulatorLot_one_row
#print axioms ProofFile.Honest.K6.headSimulatorShare_at_maker
#print axioms ProofFile.Honest.K6.HeadSimulatorShare.hand
#print axioms ProofFile.Honest.K6.HeadSimulatorShare.goodAtMute
#print axioms ProofFile.Honest.K6.HeadSimulatorShare.budDebt
#print axioms ProofFile.Honest.K6.HeadSimulatorShare.onDebt
#print axioms ProofFile.Honest.K6.HeadSimulatorShare.onFromS
