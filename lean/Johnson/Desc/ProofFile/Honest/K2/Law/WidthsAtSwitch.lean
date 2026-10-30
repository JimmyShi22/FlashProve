-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/WidthsAtSwitch.lean: the kind "the code switch" (K2): "THE
WIDTHS" WHOLE (the premise hW of `switch_playsS`, Honest/K2/Law/PlaysScript.lean) AT EACH SWITCH OF
THE PLAN, WITHOUT `PlayedTo`: at the first thread's letters at the library's head where the Script
is the joined one, at K1's jobs (52, by `k1MembersW_length`; the proof meets 51 of them): for each
tree in the switch's list `read`, at each stand at the switch's number, the thread's table has the
width that the list states. Two definitions; one closed fact by evaluation in Lean's kernel, with
two controls; two laws: joins of calls.

  `treeIn`, `sendersB`, `sendersW`   BY LEAN's KERNEL: each tree that a written switch reads was
                    sent by the switch in front, by K1's opening or by one of K1's later members,
                    in front of the switch; two controls: at number 0, and with every tree's
                    number out of every span, it says no. No control bends the link's clause
  `tree_span`       a tree in a member's span is that member's tree number τ
  `widths_at_switch`   THE CLAUSE AT ALL TREES

By, ours: `width_at_join`, `frontPairsW`, `frontSeatsW`, `roots_at_front` (WidthAtJoin.lean) ·
`width_k1_read_at_join` (ReadTold.lean) · `k2_member_at_head`, `k2_block_at_head`, `numsW_at_head`;
of other authors: `byNo_at_head` (Honest/Thread/JoinAtHead.lean) · `mem_k1MembersW`,
`mem_k1Members`, `later_plan_head` (Honest/K1/Law/LotsAtAll.lean, LotsAtHead.lean,
LotJobsAtHead.lean) · sealed: `six_at_head`, `toldOf_of_cut`, `places_at_head`, `treesTo_at_head` ·
`told_succ_at` (Johnson/Desc/First/ToldSucc.lean) · `lentCut_isSome` (Honest/K1/ScriptAtLaw.lean) ·
`k1_two_inScope`, `k1_fifty_inScope` (Honest/K1/Law/MemberInScope.lean).

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING
MEETS THEM THE LAW HOLDS EMPTILY. PREMISES, EACH WITH ITS KNOWN PAYER, NOT CALLED HERE: F and hin
(`joinFit_full`, AtFullSide/K2/JoinFitFull.lean) · hcoins (`coins_at_head`,
Honest/Thread/JoinAtHead.lean, at the book that `onlineProverFromPublicFiles` returns) · hlend (`own_hands_at_book`,
AtFullSide/K2/OwnHandsAtTheBook.lean, at the book under the head) · hcl (`closing_at_head`,
Honest/K2/Law/ClosingAtHead.lean) · hv: `publicOk` at the run's input w under Vd, AT EVERY SWITCH:
the debt `switch_playsS_at` asks it at its one switch; that is all that ties a stand's input to w
here: the thread's field valid. THE BOOK Bk IS A LETTER: one book meets hcoins and hlend at the book
of `onlineProverFromPublicFiles`, WHERE IT YIELDS: `coins_at_head` (held by its statement: no ride has joined it here)
and `lend_at_pure` (AtFullSide/K2/LendAtPure.lean), not called here: that `onlineProverFromPublicFiles` yields is a heavy
premise of both. A CLOSED FACT BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. On a table's
width: nothing on what it holds. A run's coins stand under "for all". NOT IN FRONT OF A LAW OVER
COINS. The full size and the format's second hash function alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.WidthAtJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.ReadTold
import Johnson.Desc.ProofFile.Honest.Thread.JoinAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.MemberInScope
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.First.ToldSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First (treesTold told_succ_at)
open VerifiableInference.Desc.First.K2Ties (toldFull toldOf_of_cut)
open VerifiableInference.Desc.K2.Honest.Returns (six_at_head)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open IM (k2P)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (lentCut lentCut_isSome bookCovers dueR k1MembersW mem_k1MembersW mem_k1Members
  PlaceIn SendJob k1_two_inScope k1_fifty_inScope later_plan_head)

/-- Tree number u lies in member b's span, by the written list. -/
def treeIn (b u : Nat) : Bool :=
  decide (treesTold toldFull b ≤ u) && decide (u < treesTold toldFull (b + 1))

/-- **The test**, at the written plan: who sent each tree that a switch reads. cap: the number under
which the sender must stand: the switch's own. sh: added to each tree's number: 0, but for a
control. -/
def sendersB (cap : SwitchPlace → Nat) (sh : Nat) : Bool :=
  placesW.all fun p => (numsW p.place.link).any fun n => n.read.all fun t =>
    (frontPairsW.any fun x =>
      x.2.1 == p.place.link && treeIn x.2.2 (t.1 + sh) && decide (x.2.2 < cap p)) ||
    (treeIn 2 (t.1 + sh) && decide (2 < cap p)) ||
    (List.range 25).any fun l => [false, true].any fun d =>
      treeIn (K1.noL l d) (t.1 + sh) && decide (K1.noL l d < cap p)

set_option maxRecDepth 1000000 in
/-- **Its yes, and two controls**: at number 0 it says no; with the trees' numbers out of every span
it says no. -/
theorem sendersW : sendersB switchNo 0 = true ∧ sendersB (fun _ => 0) 0 = false ∧
    sendersB switchNo 100000 = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)} {p : SwitchPlace}
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Xj Xo : Type}
  {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn Xj} {own₀ : Xo}
  {Oth : Others Bk (Local W₀ Rc ProofFile.Inst Tr)} {D : RowDataOf ProofFile.Inst}
  {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {rest : Nat → TreeLot Bk (Local W₀ Rc ProofFile.Inst Tr)}

/-- **A tree in a member's span is that member's tree number τ.** -/
theorem tree_span (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) {b u : Nat} {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[b]? = some blk) (hu : treeIn b u = true) :
    ∃ τ, u = treesTold toldFull b + τ ∧ τ < blk.oracles.flatten.length := by
  have e : toldFull = cF.blocksInOrder.map fun x => x.oracles.flatten := (toldOf_of_cut hcut).symm
  have hl : toldFull[b]? = some blk.oracles.flatten := by
    rw [e, List.getElem?_map, hb]
    rfl
  have hs := (told_succ_at toldFull b _ hl).1
  unfold treeIn at hu
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hs] at hu
  exact ⟨u - treesTold toldFull b, by omega, by omega⟩

/-- **"THE WIDTHS", WHOLE, AT A SWITCH OF THE PLAN, WITHOUT `PlayedTo`**, in the premise's own form,
at the joined Script of K1's 52 jobs. NOT IN FRONT OF A LAW OVER COINS. -/
theorem widths_at_switch (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (no : Place → Nat)
    (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀)) Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n)
    (hcoins : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀),
      dueAt (Bk.rowsOf 0) ⟨x.2.P.place, 0⟩ = dueR x.2.P x.2.ride)
    (hlend : ∀ p' ∈ switchPlaces Zp Bs.G₀, ∀ k : Coins Bk,
      ∃ c₀, lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨p'.place, 0⟩
        (switchPart (coreSender freshTable) p'.sizes p'.others p'.foldVars p'.carries) = .ok c₀)
    (hcl : ∀ p' ∈ switchPlaces Zp Bs.G₀,
      closingOk freshTable ((segmentsOf Zp Bs.G₀).take p'.link) p' = true)
    (hv : Vd w → ∀ p' ∈ switchPlaces Zp Bs.G₀,
      publicOk D Bs.G₀.first.layout p' ((segmentsOf Zp Bs.G₀).take p'.link) w.x = true) :
    ∀ t ∈ n.read, ∀ k s m E,
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀)) Oth) test carryX item n₁ n₂ b₀ Vd
        Rd Kp w).thread Said (switchNo p) k s m E →
      ((lettersHead h H (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀)) Oth) test carryX item n₁ n₂ b₀ Vd
        Rd Kp w).thread.tableAt (.own t.1) k m).2.words = t.2.2 := by
  intro t ht k s m E hT
  obtain ⟨-, hcut, -⟩ := six_at_head h.toAtMg O
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have k1case : ∀ x ∈ byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀),
      (∀ blk, cF.blocksInOrder[x.1]? = some blk →
        blk.oracles = VerifiableInference.Desc.K1.oracles x.2.P) →
      treeIn x.1 t.1 = true → x.1 < switchNo p →
      ((lettersHead h H (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀)) Oth) test carryX item n₁ n₂ b₀ Vd
        Rd Kp w).thread.tableAt (.own t.1) k m).2.words = t.2.2 := by
    intro x hx hsh hu hlt
    obtain ⟨blk, hblk, -⟩ := F.found x hx
    have hs := hsh blk hblk
    obtain ⟨τ, e, hτ⟩ := tree_span hcut hblk hu
    have hlen : τ < x.2.P.trees.length := by
      rw [hs] at hτ
      simpa [VerifiableInference.Desc.K1.oracles] using hτ
    have e' : t.1 = treesTo cF.blocksInOrder x.1 + τ := by
      rw [treesTo_at_head h.toAtMg O]
      exact e
    have hcov : bookCovers Bk 0 ⟨x.2.P.place, 0⟩ (dueR x.2.P x.2.ride) = true := by
      unfold bookCovers
      rw [hcoins x hx]
      simp
    have hsome := (lentCut_isSome k 0 (by omega) ⟨x.2.P.place, 0⟩ (dueR x.2.P x.2.ride)).trans hcov
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hsome
    exact width_k1_read_at_join h.toAtMg O hp hP hn ht F cells tok _ rfl rfl rfl rfl hx hblk hs
      (List.getElem?_eq_getElem hlen) e' Said hlt hT hc
  have w1 := List.all_eq_true.1 sendersW.1 p hpW
  rw [numsW_at_head h.toAtMg O hP, hn] at w1
  simp only [Option.any_some] at w1
  have a := List.all_eq_true.1 w1 t ht
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at a
  rcases a with (⟨x, hx, ⟨e1, hu⟩, hlt⟩ | ⟨hu, hlt⟩) | ⟨l, hl, d, -, hu, hlt⟩
  · have a1 := beq_iff_eq.1 (List.all_eq_true.1 frontSeatsW.1 x hx)
    have m1 : x.2.2 ∈ (placesW.filter fun q => q.place.link == x.1).map switchNo := by
      rw [a1]
      exact List.mem_singleton.2 rfl
    obtain ⟨p', hp'f, hno⟩ := List.mem_map.1 m1
    obtain ⟨hp'W, hl'⟩ := List.mem_filter.1 hp'f
    have hl'' : p'.place.link = x.1 := beq_iff_eq.1 hl'
    have hp' : p' ∈ switchPlaces Zp Bs.G₀ := by
      rw [places_at_head h.toAtMg O]
      exact hp'W
    obtain ⟨blk', mem', -⟩ := k2_member_at_head h O hp'
    obtain ⟨Pp₁, n₀, nm', st', -, -, hP₁, hn₀, -, ⟨-, -, ho⟩, -, -⟩ :=
      k2_block_at_head h O hp' mem'
    obtain rfl : Pp₁ = Pp := Option.some.inj (hP₁.symm.trans hP)
    have hn' : P1K2.numsAt Pp₁ x.1 = some n₀ := by
      rw [← hl'']
      exact hn₀
    have mem'' : cF.blocksInOrder[x.2.2]? = some blk' := by
      rw [← hno]
      exact mem'
    obtain ⟨τ, e, hτ⟩ := tree_span hcut mem'' hu
    have e' : t.1 = treesTo cF.blocksInOrder x.2.2 + τ := by
      rw [treesTo_at_head h.toAtMg O]
      exact e
    have hroots := roots_at_front h.toAtMg O hx hP hn'
    have hj : τ < n₀.roots := by
      rw [ho] at hτ
      have q : τ < (P1K2.oraclesAt n₀.grp n₀.codes n₀.sent).length := by
        simpa [k2P] using hτ
      omega
    obtain ⟨c₀, hc⟩ := hlend p' hp' k
    exact width_at_join h O hx hp' hl'' F hin cells tok H test carryX item n₁ n₂ b₀ Vd Rd Kp w
      Said hP hn' (by rw [e1]; exact hn) ht hj e' hlt hT c₀ hc (hcl p' hp')
      (by
        obtain ⟨ew, hV⟩ : m.st.input = w ∧ Vd m.st.input := by
          have q := hT.1.2.2.2.2.2.2
          exact ⟨q.1, q.1 ▸ q.2⟩
        rw [ew]
        exact hv (ew ▸ hV) p' hp')
  · have hx : ((2 : Nat), headJ₂ (X := Xo) Zp Bs.G₀ no Dt) ∈
        byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀) := by
      rw [byNo_at_head h O no Dt Dd]
      exact mem_k1MembersW.2 (Or.inl (mem_k1Members.2 (Or.inl rfl)))
    exact k1case _ hx (fun blk hb => (k1_two_inScope h.scope h.reads O hb).1.2.2) hu hlt
  · have hl25 : l < 25 := List.mem_range.1 hl
    have hx : (K1.noL l d, headJl (X := Xo) Zp Bs.G₀ no Dt l d) ∈
        byNo cF.blocksInOrder (k1Jobs (X := Xo) no Dt Dd Zp Bs.G₀) := by
      rw [byNo_at_head h O no Dt Dd]
      exact mem_k1MembersW.2 (Or.inl (mem_k1Members.2 (Or.inr ⟨l, hl25, d, rfl⟩)))
    refine k1case _ hx (fun blk hb => ?_) hu hlt
    rw [show (headJl (X := Xo) Zp Bs.G₀ no Dt l d).P = K1.parL Zp Bs.G₀ l d from
      later_plan_head Zp Bs.G₀ l d _ _]
    exact (k1_fifty_inScope h.scope h.reads O hl25 d hb).1.2.2

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.treeIn
#print axioms ProofFile.Honest.K2.Law.sendersB
#print axioms ProofFile.Honest.K2.Law.sendersW
#print axioms ProofFile.Honest.K2.Law.tree_span
#print axioms ProofFile.Honest.K2.Law.widths_at_switch
