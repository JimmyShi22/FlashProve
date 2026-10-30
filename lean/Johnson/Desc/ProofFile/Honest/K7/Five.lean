-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/Five.lean: the next token's member (kind K7, number 338 of the first
chain) at the thread of `lettersHead` with `keeps` := `kpBy fHeadJ`, the other letters free but `carryX`,
`b₀` and `Rd`: the four statements that the member owes at its border and its test on values, in one
theorem.

  `no_rider_339`   no clause of `csHead` speaks at border 339
  `k7_at_338`, `k7_both`   closed tests: the place at number 338; what stays open past the member
  `k7_keeps_at_head`   the accepting step gives the clause of `fHeadJ`
  `k7_ridesPast_at_head`   `RidesPastS` at the member, item by item
  `K7Five`, `k7_five_at_head`   all of it, at the thread of `lettersHead` with the first chain's values

The premises on the honest prover are three. `hhalf`: its look-up at the place finds the kind's half.
`hq`: at a valid input the script's token is the number of the asked reply, which is of the form that the
state's reader reads. `hv`: at a valid input the asked reply is a token of the vocabulary. The fifth
statement is here the test on values, by the schema of the run on shapes: `AcceptedS` at the first chain is
no house's. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.AtExchange
import Johnson.Desc.ProofFile.Honest.K7.AtHead
import Johnson.Desc.ProofFile.Honest.K7.AtValues
import Johnson.Desc.ProofFile.Honest.Thread.K7CarryCell
import Johnson.Desc.ProofFile.Honest.Thread.ReplyKeptPaid
import Johnson.Desc.ProofFile.Honest.Thread.HokFoldF
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsWhole
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Place KindName OpenedColumn)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.Desc.Reply (isToken)
open Johnson.AtFull.Shape
open P5J (AtMgA CellsM TS)

/-- **No clause of the table of riders speaks at border 339.** -/
theorem no_rider_339 {W : Type} (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (v : W) (s : TS) :
    ridersOf (csHead ν st R) 339 v s := by
  intro c hc hl hh
  exfalso
  simp only [csHead, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hc
  rcases hc with (((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, hl', rfl⟩) | ⟨g, hg, rfl⟩) |
    ⟨g, hg, rfl⟩
  all_goals (dsimp only [riderHead, riderAtt] at hl hh; omega)

set_option maxRecDepth 1000000 in
/-- The place at number 338. -/
theorem k7_at_338 : P5J.At.ps[338]? = some IM.k7Place := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- What is open on both sides of the member. -/
theorem k7_both : ((IM.openAt P5J.At.links P5J.At.ps 338).filter fun i =>
    (IM.openAt P5J.At.links P5J.At.ps 339).contains i) =
    [Item.unmarked, Item.pinW, Item.pile, Item.constr 24 .idn, Item.constr 24 .rider,
      Item.constr 24 .small, Item.pinI, Item.carry 23, Item.pinKept 23] := by
  decide +kernel

theorem k7_both_mem {i : VerifiableInference.Desc.First.Item}
    (h : i ∈ [Item.unmarked, Item.pinW, Item.pile, Item.constr 24 .idn, Item.constr 24 .rider,
      Item.constr 24 .small, Item.pinI, Item.carry 23, Item.pinKept 23]) :
    i = Item.unmarked ∨ i = Item.pinW ∨ i = Item.pile ∨ i = Item.constr 24 .idn ∨
      i = Item.constr 24 .rider ∨ i = Item.constr 24 .small ∨ i = Item.pinI ∨ i = Item.carry 23 ∨
      i = Item.pinKept 23 := by
  simpa using h

set_option maxRecDepth 1000000 in
/-- The item `wrow` is not open at the border. -/
theorem k7_no_wrow : Item.wrow ∉ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
    (FirstRows.rows P5J.At.links P5J.At.ps) 338 := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  {ν : Nat} {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
  (w : Local W₀ Rc ProofFile.Inst Tr) {Bs : ProofFile.PureBase}
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **The accepting step gives the clause of `fHeadJ`.** -/
theorem k7_keeps_at_head (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {blk : Block TS ProofFile.Cl} (hblk : (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.bs[338]? = some blk)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    {s' : TS} (hA : ThrS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread Said 338 k s m E)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.Stepped blk k s m E ds y cols s') :
    (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.keeps 338 s s' := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  obtain ⟨b, hb, hp1, -⟩ := k7_at_flat h.scope h.reads O
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk)
  have hlen : 338 < (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.bs.length := by
    have e : cF.blocksInOrder.length = 358 := head_len h
    show 338 < cF.blocksInOrder.length
    omega
  have A1 := fHead_hK_whole h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w Said hB 338 hlen b hblk k s m E ds y cols s' hA hd hS
  have A2 := formsBehind_of_form h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w k7_at_338
    (K7.k7_form_behindS h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) _ w Said b hblk k s m E ds y cols s' hA hd hS)
  have A3 := head_hbook_paid h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w Said hB 338 hlen b hblk k s m E ds y cols s' hA hd hS
  have A4 := head_hreply_paid h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w Said hB 338 hlen b hblk k s m E ds y cols s' hA hd hS
  rw [hp1] at A1 A3 A4
  refine (head_keeps h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w k7_at_338 s s').2 ?_
  exact (kpBy_at _ (p := IM.k7Place) rfl s s').2 ⟨⟨⟨⟨⟨A1, A2⟩, trivial⟩, A3⟩, A4⟩, trivial⟩

/-- **What stays open past the member stays true.** -/
theorem k7_ridesPast_at_head :
    RidesPastS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread Said 338 := by
  refine ridesPastS_shares _ _ fun i hi h1 h2 => ?_
  have hb : 338 < 358 := by omega
  have hp := k7_at_338
  have hk : IM.k7Place.kind = KindName.K7 := rfl
  have hnf : IM.k7Place.kind ≠ KindName.frame := by decide
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w hb hi h1 (by
    intro e
    subst e
    exact k7_no_wrow hi)
  have hm : i ∈ (IM.openAt P5J.At.links P5J.At.ps 338).filter fun j =>
      (IM.openAt P5J.At.links P5J.At.ps 339).contains j :=
    List.mem_filter.2 ⟨ho, List.contains_iff_mem.2 ho'⟩
  rw [k7_both] at hm
  rcases k7_both_mem hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cellI_of_H h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cellH_of_G h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cell_unmarked h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said hp hnf))
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cellI_of_H h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cellH_of_G h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cell_pinW h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said 338))
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cellI_of_H h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cellH_pile h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said hb hp (.inr (.inl hk)))
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cellI_of_H h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cellH_of_G h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said
      (cell_constr4 h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said 338 24 (by decide)))
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cellI_of_H h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cellH_of_G h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said
      (cell_constr4 h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said 338 24 (by decide)))
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cellI_of_H h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cellH_of_G h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said
      (cell_constr4 h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said 338 24 (by decide)))
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cellI_of_H h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cellH_of_G h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cell_pinI h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said hb hp hnf))
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cell_carry_k7_exact h H Q test item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀
      P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
      (VerifiableInference.Desc.K13.whereOf Zp) Said hb hp hk hi h1
  · exact cellJ_of_I h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said <| cellI_of_H h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said (cellH_of_G h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) Said
      (head_ridesPastAtS_mono h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd
        (ridersOf (csHead ν st R))
        (kpBy (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
          (VerifiableInference.Desc.K13.whereOf Zp))) w
        (kpBy (fHeadG Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
          (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD))
        (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
        (ridesPastAtS_of _ _ (pinKept_cell_k7 h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂
          339 Vd (ridersOf (csHead ν st R))
          (fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
            (VerifiableInference.Desc.K13.whereOf Zp)) w rfl hp hk 23))))

/-- **The member's five at its border.** A definition, meant as a hypothesis. -/
structure K7Five {S Cl V W Xx Pb : Type} {Bk' : ProverCoinCounts} (T : Thread Bk' S Cl V W Xx Pb)
    (Said' : Nat → Coins Bk' → Mid W Xx → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Prop where
  plays : PlaysS T Said' 338
  behind : BehindS T Said' 338
  exchange : ExchangeS T Said' 338
  ridesPast : RidesPastS T Said' 338
  values : ValuesJ T Said' J Zs fall 338

/-- **THE MEMBER's FIVE AT THE FIRST CHAIN's VALUES.** -/
theorem k7_five_at_head (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {Vh : Nat}
    (hhalf : H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Vh))
    (hq : ∀ v : Local W₀ Rc ProofFile.Inst Tr, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.valid v →
      Q.tok v = v.x.asked.c0.toNat ∧ OnBytes.Model.ofNat v.x.asked.c0.toNat = v.x.asked)
    (hv : ∀ v : Local W₀ Rc ProofFile.Inst Tr, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread.valid v →
      isToken Bs.G₀.W.hS.V v.x.asked = true)
    (J : Nat → TS → Prop) (g : Nat → ShA → Except String ShA)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    K7Five (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread Said J (firstZA g (Tab.vals Zp Bs.G₀)) fall := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  obtain ⟨blk, x₀, fs, f, K, Dm⟩ := k7_stands_of_open h.scope h.reads O (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w).thread rfl hhalf
  have hw := hw_of_script h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w hq
  refine ⟨k7_playsS Said K,
    k7_behind_at_head h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w Said K Dm
      (fun v s => no_rider_339 ν st R v s)
      (fun k s m E ds y cols s' hA hd hS =>
        k7_keeps_at_head h H Q test item n₁ n₂ Vd w Said hB K.member hA hd hS),
    (exchangeS_iff _ _).2 fun j hj =>
      k7_exchange_cell h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w Said hhalf hw 338 IM.k7Place k7_at_338 rfl j hj,
    k7_ridesPast_at_head h H Q test item n₁ n₂ Vd w Said,
    reply_values Zp Bs.G₀ K hv Said J g fall⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.no_rider_339
#print axioms ProofFile.Honest.FirstThread.k7_at_338
#print axioms ProofFile.Honest.FirstThread.k7_both
#print axioms ProofFile.Honest.FirstThread.k7_no_wrow
#print axioms ProofFile.Honest.FirstThread.k7_keeps_at_head
#print axioms ProofFile.Honest.FirstThread.k7_ridesPast_at_head
#print axioms ProofFile.Honest.FirstThread.K7Five
#print axioms ProofFile.Honest.FirstThread.k7_five_at_head
