-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/Law/SidePaysK7.lean: the side of the kind K7 (the next token), as the
lot `replyLot` lays it, pays in the sense of `SidePays` (Honest/Law/ReadyOfSides.lean) at the book of
any return of the maker `onlineProverFromPublicFiles`, the filling a free variable. Statements with their proofs; no
definition.

  `k7_member_at_head`   under the head number 338 of the first chain stands at the kind's place
  `k7_member_rounds`    a member at that place has the kind's one round
  `k7_lends_at_book`    h, hW ⊢ at such a member the book's lending returns at the kind's row, at every
                        run's coins
  `sidePays_k7`         **h, hA ⊢ the side pays**, at every view and every run's coins

By. `chainSteps_side` (Honest/Law/ReadyOfParts.lean): the lists' lengths by `planOk_all` and
`shaped_parts`; the rounds by `rounds_of_cut`; the book's cut by `bookWhole_cut_first`; no row and no
entry beyond the part by `bookWhole_tests_at`; the lending by `lendPart_of_fit`
(Honest/BookLends.lean) with the facts on the written book (AtFullSide/K14/RawAtK7.lean). The return's
book is the book's maker's at the head's own sendings by `atPure_book_at_head`.

Limits.
  * h and hA are premises.
  * What is paid is that `chainSteps` returns at the member. Nothing here says that a part plays, or
    that a verifier accepts. The side's own limits hold (Honest/K7.lean): it does not keep the range
    of the asked token, and at a request whose last position is not covered the last test asks more.
  * The law on the lending rests on closed facts on the written book that Lean's kernel evaluated.
  * The full size and the format's second hash function alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K7
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.BookWholeAlike
import Johnson.Desc.ProofFile.Honest.BookLends
import Johnson.Desc.ProofFile.Honest.Small.CutOfBook
import Johnson.Desc.ProofFile.Honest.Small.StepsOfBook
import Johnson.Desc.ProofFile.Honest.Small.RoundsOfCut
import Johnson.Desc.ProofFile.Honest.Thread.File
import Johnson.Desc.ProofFile.Honest.Law.Data
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.IMR.FirstSeats
import Johnson.IMR.TokAtReach
import AtFullSide.K14.RawAtK7

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K7
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.Kinds (Reply.rounds)
open P5J (AtMgA TS)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.K14 (planAlike_at_head)
open AtFullSide.K14 (rawDueAtK7 rawSpentEAtK7 rawCarryAtK7)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head number 338 of the first chain stands at the kind's place.** Conditional: h. -/
theorem k7_member_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∃ blk, cF.blocksInOrder[338]? = some blk ∧ blk.place = IM.k7Place := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, e1, e2, hj, -⟩ := IM.k7_sits h.scope h.reads O
  have q := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by decide) 0] at q
  exact ⟨b, q, IM.joined_place hj⟩

/-- **A member at the kind's place has the kind's one round.** Conditional: h. -/
theorem k7_member_rounds (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {b : Block TS ProofFile.Cl}
    (hb : b ∈ cF.blocksInOrder) (hbp : b.place = IM.k7Place) : b.rounds = Reply.rounds := by
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hn : ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b', e1, e2, hj, -⟩ := IM.k7_sits h.scope h.reads O
  have hm : b' ∈ cF.blocksInOrder := by
    have q := IM.hear_at_flat e1 e2
    exact List.mem_of_getElem? q
  obtain rfl : b = b' :=
    List.inj_on_of_nodup_map hn hb hm (hbp.trans (IM.joined_place hj).symm)
  rw [hj.rounds]
  rfl

/-- **At a member at the kind's place the book's lending returns at the kind's row, at every run's
coins.** What it returns is bound by that equation alone. Conditional: h; hW: the book's maker
returns Bk at the head's own three lists. -/
theorem k7_lends_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk)
    {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hbp : b.place = IM.k7Place)
    {W₀ Rc Tr X : Type} (k : Coins Bk) :
    ∃ c, lendRow Bk (Bk.rowsOf 0) (k.look 0) b.place
      [(replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)] 0 = .ok c := by
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
  obtain ⟨c0, e0⟩ := lendPart_of_fit (F := P5J.F0T OnBytes.secondHashFunction Zp Np cF)
    (V := Local W₀ Rc Inst Tr) (W := Local W₀ Rc Inst Tr) (Y := X) (p := replyPart) hw
    (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk) (Or.inl rfl)
    (a := ⟨IM.k7Place, 0⟩) (by
      rw [← hbp]
      exact List.mem_map.2 ⟨b, hb, rfl⟩)
    (rawDueAtK7 hB).symm (by rw [rawSpentEAtK7 hB]; rfl) (rawCarryAtK7 hB) k
  refine ⟨(c0, ()), ?_⟩
  rw [hbp]
  simp only [lendRow]
  rw [e0]
  rfl

/-- **The side of the kind K7 pays, at the book of any return of the maker**, at every view and every
run's coins. The filling is a free variable, and the side's own types and parameter are free: the law
reads of the return its book alone. It is not acceptance. Conditional: h; hA. -/
theorem sidePays_k7 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {W₁ Rc₁ Tr₁ X₁ : Type} (V : Nat) :
    SidePays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (replyHalf (W₀ := W₁) (Rc := Rc₁) (Tr := Tr₁) (X := X₁) 24 1 V) := by
  have hW := ProofFile.Honest.K14.atPure_book_at_head h hA
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨sh1, -, -⟩ := planOk_all h.laid.planOk
  intro b hb hbg hs hf v k
  have hpl : b.place = IM.k7Place := hbg
  have hbF : b ∈ cF.blocksInOrder := hb
  have hr := k7_member_rounds h hbF hpl
  have hcut : partsCut b = [1] := by
    unfold partsCut
    rw [hr, hpl]
    rfl
  have hne : b.rounds ≠ [] := by
    rw [hr]
    exact List.cons_ne_nil _ _
  have hc : A.B.cuts.lookup b.place =
      some ((replyHalf (W₀ := W₁) (Rc := Rc₁) (Tr := Tr₁) (X := X₁) 24 1 V).parts.map
        (·.moves.length)) := by
    have e : (replyHalf (W₀ := W₁) (Rc := Rc₁) (Tr := Tr₁) (X := X₁) 24 1 V).parts.map
        (·.moves.length) = [1] := rfl
    rw [e, ← hcut]
    exact bookWhole_cut_first hW hp hb hne
  have hname : ∀ q ∈ b.rounds, q.entry.name = "REPLY" := by
    intro q hq
    rw [hr] at hq
    obtain rfl := List.mem_singleton.1 hq
    rfl
  obtain ⟨t1, t2⟩ := bookWhole_tests_at hW hp hb
    (fun q hq e => absurd ((hname q hq).symm.trans e) (by decide))
    (fun q hq e => absurd ((hname q hq).symm.trans e) (by decide))
    (n := 1) (by rw [hcut]; exact Nat.le_refl 1)
  obtain ⟨c, hc'⟩ := k7_lends_at_book h hW hbF hpl (W₀ := W₁) (Rc := Rc₁) (Tr := Tr₁) (X := X₁) k
  exact ⟨_, chainSteps_side A.B (A.B.rowsOf 0) (k.look 0) v b hs _ hf
    (shaped_parts (sh1 b hb).2).1 (rounds_of_cut (by rw [hcut]; rfl)) hc t1 t2 c hc'⟩

end ProofFile.Honest.K7

#print axioms ProofFile.Honest.K7.k7_member_at_head
#print axioms ProofFile.Honest.K7.k7_member_rounds
#print axioms ProofFile.Honest.K7.k7_lends_at_book
#print axioms ProofFile.Honest.K7.sidePays_k7
