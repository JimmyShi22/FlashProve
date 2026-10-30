-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/LendsAtTheTerm.lean: at the prover that onlineProverFromPublicFiles returns at the filling
onlineProverPartsInUse, the book lends each side of the kind K2, the code switch, its runs.

  switch_names, switch_cut   the names of the kind's two rounds, and how the book's maker cuts them:
                             one part of two rounds
  partClear, rowClear, spenderClear   three tests: an address of the kind has a part number below n
  rows_clear, entries_clear  by Lean's kernel: no row of the first chain's written table and no
                             entry of the written book names a part of the kind beyond part 0
  rows_can_fail, entries_can_fail   the two tests say no at the bound 0: rows and spenders of the
                             kind stand in these lists
  k2_book_at_member          at a member of the kind the maker's book has that cut, and no row and
                             no entry beyond the side's one part
  lendRow_of_part, switch_row_lent   where the book lends the part, it lends the side's row
  switch_side_pays           the kind's half at a place of the plan pays
  k2Lends                    every side of the kind pays
  switch_places_written      by Lean's kernel: the written list has 25 places, all different
  k2_sides_there             so k2Lends speaks of something: at 25 different places a block stands,
                             and the search in the prover's list finds the kind's half

Limits. The library's head and the maker's return are premises. The two tests at the written lists
are evaluations in Lean's kernel. The lending is lend_at_pure's. Nothing here says what a part sends
or that a verifier accepts.
-/
import AtFullSide.K2.FoundAtTheTerm
import AtFullSide.K2.LendAtPure
import AtFullSide.K14.MakersBookOne
import AtFullSide.K14.RawAtTheBookAtHead
import AtFullSide.K14.RawBookRowsWritten
import AtFullSide.K14.RawEntriesKit
import AtFullSide.K14.RawReturnsWritten
import AtFullSide.K14.BookWholeWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.BlockAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysSeated
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.Unfolds.SplitOn
import Johnson.Unfolds.SliceFoldl

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Term
open VerifiableInference.Desc (Block Chain KindName Place)
open VerifiableInference.Desc.First.K2 (P2 rounds)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open AtFullSide.K14 (rawAheadW rawSegW rawRowsFirstW rawAll_whole rawBook_same
  rawBookRows_written bookRaw_returns_written bookWhole_returns_raw makers_book_one)

/-! ## 1 The cut of the kind's rounds -/

/-- The names of the kind's two rounds. -/
theorem switch_names (q : P2) :
    (rounds q).map (·.entry.name) = ["SEND seed", "LOC"] := rfl

/-- **The book's maker cuts the kind's two rounds as one part of two.** -/
theorem switch_cut : cutOfNames KindName.K2 ["SEND seed", "LOC"] = [2] := by
  decide +kernel

/-! ## 2 The written lists name no part of the kind beyond part 0 -/

/-- The test: an address of the kind has a part number below n. -/
def partClear (n : Nat) (a : Addr) : Bool :=
  decide (a.place.kind = KindName.K2 → a.part < n)

/-- The test at a row of a table. -/
def rowClear (n : Nat) (e : Addr × Due) : Bool := partClear n e.1

/-- The test at the spender of an entry. -/
def spenderClear (n : Nat) (e : Ahead) : Bool := partClear n e.spender

/-- What the test's yes says. -/
theorem part_below {n : Nat} {a : Addr} (h : partClear n a = true)
    (hk : a.place.kind = KindName.K2) : a.part < n := by
  have t : a.place.kind = KindName.K2 → a.part < n := of_decide_eq_true h
  exact t hk

set_option maxRecDepth 1000000 in
/-- **No row of the first chain's written table names a part of the kind beyond part 0.** -/
theorem rows_clear : rawRowsFirstW.all (rowClear 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the bound 0 the test says no, so a row of the kind stands in the table. -/
theorem rows_can_fail : rawRowsFirstW.all (rowClear 0) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **No entry of the written book names a spender of the kind beyond part 0.** -/
theorem entries_clear : rawAheadW.all (spenderClear 1) = true := by
  refine rawAll_whole (spenderClear 1) (by decide +kernel) ?_ (by decide +kernel)
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- A control: at the bound 0 the test says no, so a spender of the kind stands among the
entries. -/
theorem entries_can_fail : rawSegW.all (spenderClear 0) = false := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-! ## 3 The maker's book at a member of the kind -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)} {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **At a member of the kind the maker's book has the kind's cut, and no row and no entry beyond
one part.** -/
theorem k2_book_at_member (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {b : Block TS ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hk : b.place.kind = KindName.K2) {q : P2} (hr : b.rounds = rounds q) :
    A.B.cuts.lookup b.place = some [2] ∧
      (A.B.rowsOf 0).any (fun e => e.1.place == b.place && decide (1 ≤ e.1.part)) = false ∧
      A.B.ahead.any (fun e => e.spender.place == b.place && decide (1 ≤ e.spender.part)) =
        false := by
  obtain ⟨B, -, hW, -, ha, hall⟩ := makers_book_one h
  obtain ⟨eB, -⟩ := hall _ _ _ _ _ P A hA
  rw [eB]
  obtain ⟨W, hRaw⟩ := bookRaw_returns_written
  have eW : B = W := rawBook_same h.scope h.laid (bookWhole_returns_raw W hRaw) hW
  have eR : B.rowsOf 0 = rawRowsFirstW := by
    have e0 : B.rowsOf 0 = B.first := by
      first
        | rfl
        | simp [Book.rowsOf]
    rw [e0, eW]
    exact (rawBookRows_written _ W hRaw).1
  have hp : (F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hbF : b ∈ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := hb
  have hcut : partsCut b = [2] := by
    unfold partsCut
    rw [hk, hr]
    exact (congrArg (cutOfNames KindName.K2) (switch_names q)).trans switch_cut
  have hlen : b.rounds.length = 2 := congrArg List.length hr
  have hne : b.rounds ≠ [] := by
    intro e
    rw [e] at hlen
    simp at hlen
  refine ⟨(bookWhole_cut_first hW hp hbF hne).trans (congrArg some hcut), ?_, ?_⟩
  · refine List.any_eq_false.2 fun e he hq => ?_
    rw [eR] at he
    rw [Bool.and_eq_true] at hq
    have hkp : e.1.place.kind = KindName.K2 := by
      rw [beq_iff_eq.1 hq.1]
      exact hk
    have h1 := part_below (a := e.1) (List.all_eq_true.1 rows_clear e he) hkp
    have h2 := of_decide_eq_true hq.2
    omega
  · refine List.any_eq_false.2 fun e he hq => ?_
    rw [ha] at he
    rw [Bool.and_eq_true] at hq
    have hkp : e.spender.place.kind = KindName.K2 := by
      rw [beq_iff_eq.1 hq.1]
      exact hk
    have h1 := part_below (a := e.spender) (List.all_eq_true.1 entries_clear e he) hkp
    have h2 := of_decide_eq_true hq.2
    omega

/-! ## 4 The lending of the side's row -/

section Row
variable {V W Y W₁ Rc₁ Xi Tr₁ : Type}

/-- Where the book lends a part, it lends the row of that one part. -/
theorem lendRow_of_part (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Place) (Q : Part V W Y) {c : Q.Coins}
    (h : lendPart Bk rows look ⟨a, 0⟩ Q = .ok c) :
    ∃ row, lendRow Bk rows look a [Q] 0 = .ok row := by
  refine ⟨(c, ()), ?_⟩
  first
    | (rw [lendRow, h]; rfl)
    | rw [lendRow, h]

/-- **Where the book lends the kind's part, it lends the row of the kind's half.** -/
theorem switch_row_lent (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Place) (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₁ Rc₁ Xi Tr₁ → Readers) (closing : Closing) (p : SwitchPlace)
    {c : (switchPart Sd p.sizes p.others p.foldVars p.carries).Coins}
    (h : lendPart Bk rows look ⟨a, 0⟩ (switchPart Sd p.sizes p.others p.foldVars p.carries) =
      .ok c) :
    ∃ row, lendRow Bk rows look a (switchHalf (X := Y) Sd D readers closing p).parts 0 =
      .ok row :=
  lendRow_of_part Bk rows look a _
    ((lendPart_lift Bk rows look ⟨a, 0⟩ (switchPart Sd p.sizes p.others p.foldVars p.carries)
      (fun _ => ()) (switchWit D readers closing p) (fun _ => ()) fun (y : Y) _ => y).trans h)

/-! ## 5 The side pays -/

/-- **The kind's half at a place of the plan pays, at the maker's book.** -/
theorem switch_side_pays (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {p : SwitchPlace}
    (hp : p ∈ switchPlaces Zp Bs.G₀) (D : RowDataOf Xi)
    (readers : Local W₁ Rc₁ Xi Tr₁ → Readers) (closing : Closing) :
    SidePays A.B 0 cF.blocksInOrder (switchHalf (X := Y) (coreSender freshTable) D readers closing p) := by
  have hpl : (F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hn₀ : ((F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hpl)).1).1
  have hn : (cF.blocksInOrder.map (·.place)).Nodup := hn₀
  obtain ⟨blk, mem, -⟩ := k2_member_at_head h O hp
  obtain ⟨Pp, n, nm, st, before, after, -, -, -, ⟨epl, hr, ho⟩, -, -⟩ :=
    k2_block_at_head h O hp mem
  have hbm : blk ∈ cF.blocksInOrder := List.mem_of_getElem? mem
  have hkind : blk.place.kind = KindName.K2 := by
    rw [epl]
    exact switchPlaces_kind hp
  obtain ⟨c1, c2, c3⟩ := k2_book_at_member h hA hbm hkind hr
  have hlen : blk.rounds.length = 2 := congrArg List.length hr
  have hol : blk.oracles.length = 2 := congrArg List.length ho
  have hg : (switchHalf (X := Y) (coreSender freshTable) D readers closing p).rounds = 2 := by
    first
      | rfl
      | simp [Placed.rounds, switchHalf, switchPart, Part.lift]
  have hcuts : (switchHalf (X := Y) (coreSender freshTable) D readers closing p).parts.map
      (·.moves.length) = [2] := by
    first
      | rfl
      | simp [switchHalf, switchPart, Part.lift]
  obtain ⟨c₀, hc⟩ := lend_at_pure h O hA p hp (default : Coins A.B)
  obtain ⟨row, hrow⟩ := switch_row_lent (Y := Y) A.B (A.B.rowsOf 0)
    ((default : Coins A.B).look 0) p.place (coreSender freshTable) D readers closing p hc
  refine sidePays_of_tests A.B 0 cF.blocksInOrder _ fun b hb hbp => ?_
  have hbp' : b.place = p.place := hbp
  have eb : b = blk := List.inj_on_of_nodup_map hn hb hbm (hbp'.trans epl.symm)
  rw [eb]
  exact ⟨hol.trans hlen.symm, hg.trans hlen.symm, c1.trans (congrArg some hcuts.symm), c2, c3,
    default, row, by rw [epl]; exact hrow⟩

end Row

/-! ## 6 The sides of the kind at the maker's prover -/

/-- **The book lends the kind's sides**, at the prover that the maker returns at the filling. -/
theorem k2Lends {W₁ : Type} (I : WiderIn W₁) (S : OnBytes.HonestTrace.Sz) (Oo : OnlineProverArguments)
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {A : OnlineProverWithDescription W₁ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Oo) =
      .ok A) :
    KindPays A.B 0 cF.blocksInOrder A.H.first KindName.K2 := by
  intro g hg hk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨p, hp, rfl⟩ := k2_side_is I OnBytes.secondHashFunction S Oo O hA hg hk
  exact switch_side_pays h O hA hp _ _ _

/-! ## 7 The sides stand there -/

set_option maxRecDepth 1000000 in
/-- **The written list of the kind's places has 25 members, all different.** -/
theorem switch_places_written : placesW.length = 25 ∧ (placesW.map (·.place)).Nodup := by
  decide +kernel

/-- **At 25 different places a block of the chain stands, and the search in the maker's first list
finds the kind's half by name.** -/
theorem k2_sides_there {W₁ : Type} (I : WiderIn W₁) (S : OnBytes.HonestTrace.Sz) (Oo : OnlineProverArguments)
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {A : OnlineProverWithDescription W₁ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Oo) =
      .ok A) :
    (switchPlaces Zp Bs.G₀).length = 25 ∧ ((switchPlaces Zp Bs.G₀).map (·.place)).Nodup ∧
      ∀ p ∈ switchPlaces Zp Bs.G₀, (∃ b ∈ cF.blocksInOrder, b.place = p.place) ∧
        (A.H.first.find? fun g => g.place == p.place) =
          some (switchHalf (coreSender freshTable) (withSwitchData S (K1.lotData S) Zp Bs.G₀)
            (fun w : Local W₁ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩)
            (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p) := by
  have e := places_at_head h.toAtMg O
  refine ⟨by rw [e]; exact switch_places_written.1, by rw [e]; exact switch_places_written.2,
    fun p hp => ⟨?_, k2_found I OnBytes.secondHashFunction S Oo O hA hp⟩⟩
  obtain ⟨blk, mem, epl⟩ := k2_member_at_head h O hp
  exact ⟨blk, List.mem_of_getElem? mem, epl⟩

end AtFullSide.K2.Term

#print axioms AtFullSide.K2.Term.switch_names
#print axioms AtFullSide.K2.Term.switch_cut
#print axioms AtFullSide.K2.Term.part_below
#print axioms AtFullSide.K2.Term.rows_clear
#print axioms AtFullSide.K2.Term.rows_can_fail
#print axioms AtFullSide.K2.Term.entries_clear
#print axioms AtFullSide.K2.Term.entries_can_fail
#print axioms AtFullSide.K2.Term.k2_book_at_member
#print axioms AtFullSide.K2.Term.lendRow_of_part
#print axioms AtFullSide.K2.Term.switch_row_lent
#print axioms AtFullSide.K2.Term.switch_side_pays
#print axioms AtFullSide.K2.Term.k2Lends
#print axioms AtFullSide.K2.Term.switch_places_written
#print axioms AtFullSide.K2.Term.k2_sides_there
