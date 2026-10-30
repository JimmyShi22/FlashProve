-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Law/SidePaysK13.lean: the side of the kind K13 (the members'
batching), as the lot `k13Lot` lays it, pays in the sense of `SidePays`
(Honest/Law/ReadyOfSides.lean) at the book of any return of the maker `onlineProverFromPublicFiles`, the filling a free
variable. Statements with their proofs; no definition.

  `k13_moves`           the numbers of moves of the kind's two parts: 1 and 1 + kCol
  `k13_lends_at_book`   h, hW ⊢ at a member at the kind's place the book's lending returns at the
                        kind's row, at every run's coins
  `sidePays_k13`        **h, hA ⊢ the side pays**, at every view and every run's coins

By. `chainSteps_side` (Honest/Law/ReadyOfParts.lean), whose premises are paid so: the lists' lengths
by `k13_member_fields` (Honest/K13/AtMember.lean); the rounds by `rounds_of_cut`; the book's cut by
`bookWhole_cut_first` and `k13_partsCut_of`; no row and no entry beyond the parts by
`bookWhole_tests_at`; the lending by `k13_lendRow_of_lists` (Honest/K13/LendRowOfFit.lean) with the
facts on the written book (AtFullSide/K14/RawMineAtK13.lean). That the return's book is the book's
maker's at the head's own sendings is `atPure_book_at_head` (Honest/K14/AtPureBookAtHead.lean). The
last step follows the proof of `k13_lendRow_at_head` (AtFullSide/K13/LendRowAtHead.lean), whose
statement is worded in terms of a thread's variables, which play no part here.

Limits.
  * h and hA are premises.
  * What is paid is that `chainSteps` returns at the member. Nothing here says that a part plays, or
    that a verifier accepts.
  * Nothing is said on what is lent: `lendRow` returns, and no more.
  * The law on the lending rests on closed facts on the written book that Lean's kernel evaluated.
  * The full size and the format's second hash function alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K13.Plays
import Johnson.Desc.ProofFile.Honest.K13.AtMember
import Johnson.Desc.ProofFile.Honest.K13.PlanPartsAtM3
import Johnson.Desc.ProofFile.Honest.K13.GuardsAtM3
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.Desc.ProofFile.Honest.Small.StepsOfBook
import Johnson.Desc.ProofFile.Honest.Small.RoundsOfCut
import AtFullSide.K13.LendRowAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block FileDescription Place Chain)
open VerifiableInference.Desc.K13 (battRounds whereOf Where)
open P5J (AtMgA TS)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.K14 (planAlike_at_head)
open AtFullSide.K14 (rawDueAtK13 rawSpentEAtK13_part0 rawSpentEAtK13_part1 rawCarryAtK13)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The numbers of moves of the kind's two parts. -/
theorem k13_moves {W₀ Rc Xi Tr X : Type} (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) :
    (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile p).parts.map (·.moves.length) =
      [1, 1 + p.lin.kCol] := by
  show [(quietPart : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).moves.length,
    ((k13Sum p).moves.map _).length] = _
  rw [List.length_map, k13Sum_moves]
  rfl

/-- **At a member at the kind's place the book's lending returns at the kind's row, at every run's
coins.** What it returns is bound by that equation alone. Conditional: h; hW: the book's maker
returns Bk at the head's own three lists. -/
theorem k13_lends_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk)
    {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hbp : b.place = ⟨1, none, 3, .K13⟩)
    {W₀ Rc Xi Tr X : Type} (weights : W₀ → Weights) (pile : PileOf Xi) (k : Coins Bk) :
    ∃ c, lendRow Bk (Bk.rowsOf 0) (k.look 0) b.place
      (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile (whereOf Zp)).parts 0 = .ok c := by
  have A := planAlike_at_head h
  have hs : Zp.made.proof = proofSendsFull :=
    VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
      (VerifiableInference.Desc.K1.pin1_atAll h)
  have hw := bookWhole_word hW
  rw [hs] at hW
  have hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk := by
    rw [mergesByName_alike A.first, bookWhole_planAlike A]
    exact hW
  have hk : k13Place (whereOf Zp) = ⟨1, none, 3, .K13⟩ := rfl
  have hcol : (whereOf Zp).lin.kCol = 18 := m3_kCol h
  rw [hbp, ← hk]
  refine k13_lendRow_of_lists (F := (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) weights pile (whereOf Zp) hw
    (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk) ?_ ?_ ?_ ?_ ?_ k
  · rw [hk, ← hbp]
    exact List.mem_map.2 ⟨b, hb, rfl⟩
  · intro j hj
    rw [hk]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h0 | rfl
    · obtain rfl : j = 0 := Nat.lt_one_iff.1 h0
      exact (rawDueAtK13 hB).1
    · exact (rawDueAtK13 hB).2
  · rw [hk]
    exact rawSpentEAtK13_part0 hB
  · rw [hk, rawSpentEAtK13_part1 hB, hcol]
    rfl
  · intro j _
    rw [hk]
    exact rawCarryAtK13 hB j

/-- **The side of the kind K13 pays, at the book of any return of the maker**, at every view and every
run's coins. The filling is a free variable, and the side's own types and arguments are free: the law
reads of the return its book alone. It is not acceptance. Conditional: h; hA. -/
theorem sidePays_k13 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {W₁ Rc₁ Xi Tr₁ X₁ : Type}
    (weights : W₁ → Weights) (pile : PileOf Xi) :
    SidePays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (proverSideOfClaimCombination (Rc := Rc₁) (Tr := Tr₁) (X := X₁) weights pile (whereOf Zp)) := by
  have hW := ProofFile.Honest.K14.atPure_book_at_head h hA
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  intro b hb hbg hs hf v k
  have hpl : b.place = ⟨1, none, 3, .K13⟩ := hbg
  have hbF : b ∈ cF.blocksInOrder := hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hr, ho⟩ := k13_member_fields O hbF hpl
  have hcut : partsCut b = [1, 1 + (whereOf Zp).lin.kCol] := k13_partsCut_of hr hbg
  have hmv := k13_moves (Rc := Rc₁) (Tr := Tr₁) (X := X₁) weights pile (whereOf Zp)
  have hne : b.rounds ≠ [] := by
    rw [hr]
    exact List.cons_ne_nil _ _
  have hc : A.B.cuts.lookup b.place =
      some ((proverSideOfClaimCombination (Rc := Rc₁) (Tr := Tr₁) (X := X₁) weights pile
        (whereOf Zp)).parts.map (·.moves.length)) := by
    rw [hmv, ← hcut]
    exact bookWhole_cut_first hW hp hb hne
  have hnames : ∀ q ∈ b.rounds, q.entry.name = "BAT-sigma" ∨ q.entry.name = "PSC epsilon" ∨
      q.entry.name = "PSC round" := by
    intro q hq
    rw [hr] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Or.inl rfl
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inr (Or.inl rfl)
      · obtain rfl := List.eq_of_mem_replicate hq
        exact Or.inr (Or.inr rfl)
  obtain ⟨t1, t2⟩ := bookWhole_tests_at hW hp hb
    (fun q hq e => by
      rcases hnames q hq with e' | e' | e' <;> exact absurd (e'.symm.trans e) (by decide))
    (fun q hq e => by
      rcases hnames q hq with e' | e' | e' <;> exact absurd (e'.symm.trans e) (by decide))
    (n := 2) (by rw [hcut]; exact Nat.le_refl 2)
  obtain ⟨c, hc'⟩ := k13_lends_at_book h hW hbF hpl (Rc := Rc₁) (Tr := Tr₁) (X := X₁) weights pile k
  exact ⟨_, chainSteps_side A.B (A.B.rowsOf 0) (k.look 0) v b hs _ hf
    (by rw [ho, hr, List.length_replicate, battRounds_length])
    (rounds_of_cut (by rw [hmv, hcut])) hc t1 t2 c hc'⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_moves
#print axioms ProofFile.Honest.K13.k13_lends_at_book
#print axioms ProofFile.Honest.K13.sidePays_k13
