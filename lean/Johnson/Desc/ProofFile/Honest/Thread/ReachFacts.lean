-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ReachFacts.lean: THE LIBRARY's FACTS ON EVERY REACHED STATE
(`FoldFacts`, Johnson/Desc/First/FoldFacts.lean: 26 fields), AT THE STATES AT WHICH THE FIRST
CHAIN's THREAD STANDS AT THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean). Lemmas;
no definition.

WHY A FILE OF OURS. The library's own value of the structure at the head (`P5J.foldFacts_at_head'`,
Johnson/P5J/FoldJ3Whole.lean) asks that "reached" be reached BY THE WRAPPED MEMBERS' STEPS (each
with a test on the shown words laid in front: Johnson/Desc/Sound/ChainRule.lean's `below`). The
thread's clause (X) gives the fold over the members' OWN steps, which is weaker: from the wrapped to
the raw there is a lemma (`reach_raw`), not back. But each field's own payer stands at the RAW reach
or the raw fold: the library's term (`Meaning.K2.foldFacts_of_rest`, Johnson/IMR/AtReachFits.lean)
calls twenty of them through that lemma; for the six that are stated at the wrapped reach their
authors have a raw lemma beside.

  1  `foldFacts_raw`   THE STRUCTURE WHOLE AT THE HEAD's CLOSED TERM, general in Y, Rch and at_,
     under "what is reached is reached by the members' own steps": 26 calls, each of a sealed lemma,
     and the library's own rewriting of the data (`P5J.foldW_is`, `linksW_at`, `placesW_at`:
     Johnson/P5J/FoldJ3.lean)
  2  `thr_reach`   the thread at a border gives the raw reach there, at the input's instance's
     public part
  3  `foldFacts_thr`   **THE STRUCTURE AT Rch := "the thread stands here"**, under the head alone
  4  `thr_back_head`, `thr_back_keeps`   one step back (Honest/Thread/ReachBack.lean) at the head;
     what the member in front lays, by its kind's clause of `keeps`, where that clause follows from
     a yes

THE SIX. pileMasks: `LPFK9.masks_reached` · pileWithin, oneRow: `LPFK9.within_reached` · tidy:
`Meaning.K2.tidy_at_open_raw` · room, roomEarly: `P1L20.room_at_fill`, `P1L20.roomEarly_at_fill`.

THE THREE PUBLIC TESTS. `foldFacts_raw` keeps them as premises, as the library's own value does: hl
(the list of seats is laid) · hs (the start's test on the index masks' ledger) · hB (the planner's
sendings are the written places' own). UNDER THE HEAD EACH IS A SEALED THEOREM: `P5J.laid_at_head`
(Johnson/P5J/ReadsTestsAtHead.lean: the list is the written one, LFull) · `P5J.startB_at_head`
(Johnson/P5J/StartAtHead.lean) · `P5J.sendsB_of_madeRow` at `P5J.madeRow_at_head`
(Johnson/P5J/FoldJ3.lean, AtMgRAtHead.lean). SO `foldFacts_thr` HAS NO PREMISE BUT THE HEAD. (The
first of the three payers was named to us by an author in another thread of this project.)

HOW IT IS CALLED. (foldFacts_thr h H Q …).‹field› b (pub, s) ⟨hb, k, m, E, hT, rfl⟩ hmark …,
where hmark : s.failed = none is the thread's form (`head_form`).

Limits. THE FULL SIZE ALONE, and the format's second hash function alone. The library's head has a member at
the name under four premises on the public files (the seal's `P5J.head_exists_at_name`); this file
does not call it; no member of the head together with the thread's sentence is shown. `lettersHead`
is without code: no test with code reaches the thread itself. IT PAYS NOTHING OF ITS OWN: every
field is a sealed lemma's. Each field is fenced to a state without a mark. None is one of the
library's goals. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack
import Johnson.P5J.FoldJ3Whole
import Johnson.P5J.StartAtHead
import Johnson.P5J.ReadsTestsAtHead
import Johnson.P5J.AtMgRAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 The structure at the raw reach -/

/-- **`FoldFacts` AT THE HEAD's CLOSED TERM, AT WHAT IS REACHED BY THE MEMBERS' OWN STEPS.** -/
theorem foldFacts_raw (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {Y : Type} (Rch : ℕ → Y → Prop)
    (at_ : Y → ProofFile.InstPub × TS)
    (hRch : ∀ k a, Rch k a → Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (at_ a))
    {L : VerifiableInference.Desc.K12.Door.Laid} (hl : P5J.At.laid? Zp = some L)
    (hs : VerifiableInference.Desc.First.FillP1.startB Zp
      (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1) (P5J.At.N Zp cF).indexNo =
        true)
    (hB : P5J.SendsB Zp) :
    FoldFacts Rch at_ (P5J.At.foldD Zp cF L) P5J.At.reqW P5J.At.links P5J.At.ps := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := P5J.flat_ok h
  have hF := h.laid.planOk
  have hf := Meaning.K2.fold_of_rch hRch
  have F : FoldFacts Rch at_ (P5J.At.foldW Zp cF L) P5J.At.reqW IM.linksW IM.placesW :=
    { bookInOrder := Meaning.K2.bookInOrder_field O hp Rch at_ hRch
      seatsCarried := IM.seatsCarried_field h.scope h.reads O Rch at_ hf hF (P5J.sends_at O hB) hl
      bookFits := Meaning.K2.bookFits_field O hp Rch at_ hRch
      msgShapes := IM.msgShapes_field h.scope h.reads O Rch at_ hf hF (P5J.sends_at O hB)
      weightsOk := fun k a hr _ => Meaning.K2.weights_at_open O hp 0 k (at_ a) (hRch k a hr)
      pileMasks := fun k a hr _ => LPFK9.masks_reached h.scope h.reads O k (at_ a) (hRch k a hr)
      pileWithin := fun k a hr _ => (LPFK9.within_reached O hp k (at_ a) (hRch k a hr)).1
      oneRow := fun k a hr _ => (LPFK9.within_reached O hp k (at_ a) (hRch k a hr)).2
      tidy := fun k a hr hm =>
        Meaning.K2.tidy_at_open_raw h.laid.value hF O k (at_ a) (hRch k a hr) hm
      codes := Meaning.K2.codes_field h.scope h.reads O hp Rch at_ hRch
      shape := Meaning.K2.shape_field h.scope h.reads O hp Rch at_ hRch
      layout := Meaning.K2.layout_field h.scope h.reads O hp Rch at_ hRch
      liveShape := Meaning.K2.liveShape_field h.scope h.reads O hp Rch at_ hRch
      liveLayout := Meaning.K2.liveLayout_field h.scope h.reads O hp Rch at_ hRch
      groups := Meaning.K2.groups_field h.scope h.reads O hp Rch at_ hRch
      liveGroups := Meaning.K2.liveGroups_field h.scope h.reads O hp Rch at_ hRch
      frameShape := Meaning.K2.frameShape_field h.scope h.reads O hp Rch at_ hRch
      frameGroups := Meaning.K2.frameGroups_field h.scope h.reads O hp Rch at_ hRch
      ownIs := Meaning.K2.ownIs_field h.scope h.reads O Rch at_ hRch
      groupIs := Meaning.K2.groupIs_field h.scope h.reads O Rch at_ hf
      frameIs := Meaning.K2.frameIs_paid h.scope h.reads O (IM.blocksOk_of_planOk O hF)
        (P5J.At.N₀ Zp cF) Zp.made.p.built.links Rch at_ hf
      rowsSent := Meaning.K2.rowsSent_field O hp Rch at_ hf fun k a hr =>
        let ⟨_, _, _, _, f⟩ := hf k a hr; Meaning.K2.bookHas_fold h.scope h.reads O hp f
      reqIs := fun k a hr hm => Meaning.K2.req_at_open O hp 0 k (at_ a) (hRch k a hr) hm
      replyNat := IM.replyNat_field h.scope h.reads O Rch at_ hRch
      room := fun k a p m hr hm hq => P1L20.room_at_fill h.scope h.reads O hp hRch hs k a p m hr hm
        (Meaning.K2.placesW_linksFull ▸ hq)
      roomEarly := fun k a p m hr hm hq => P1L20.roomEarly_at_fill h.scope h.reads O hp hRch hs k a
        p m hr hm (Meaning.K2.placesW_linksFull ▸ hq) }
  rw [P5J.foldW_is, P5J.linksW_at, P5J.placesW_at] at F
  exact F

/-! ## 2 and 3 At the thread -/

/-- **THE THREAD AT A BORDER GIVES THE RAW REACH THERE.** -/
theorem thr_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s m E) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (m.st.input.x.pub, s) :=
  thr_reach_of (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (ProofFile.startS Zp)
    m.st.input.x.pub hb (fun _ h0 => h0) hT

/-- **`FoldFacts` AT "THE THREAD STANDS HERE".** A statement is a public part and a state of the
verifier's; it is reached at b where b is a border of the chain and the thread stands there at that
state, at some run's coins, at an input whose instance has that public part. -/
theorem foldFacts_thr (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) :
    FoldFacts (fun b (a : ProofFile.InstPub × TS) => b ≤ cF.blocksInOrder.length ∧
        ∃ (k : Coins Bk) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env),
          Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k a.2 m E ∧
            m.st.input.x.pub = a.1)
      (fun a => a) (P5J.At.foldD Zp cF VerifiableInference.Desc.K13.Law.LFull) P5J.At.reqW
      P5J.At.links P5J.At.ps := by
  refine foldFacts_raw h.toAtMg _ _ (fun b a hr => ?_) (P5J.laid_at_head h.toAtMg)
    (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  obtain ⟨hb, k, m, E, hT, e⟩ := hr
  have hR := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  rw [e] at hR
  exact hR

/-! ## 4 One step back -/

/-- **ONE STEP BACK, AT THE HEAD.** -/
theorem thr_back_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b + 1 ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (b + 1) k s' m E) :
    ∃ s blk, cF.blocksInOrder[b]? = some blk ∧ Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (m.st.input.x.pub, s) ∧
      StepYes 0 blk s s' :=
  thr_back (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (ProofFile.startS Zp)
    m.st.input.x.pub hb (fun _ h0 => h0) hT

/-- **WHAT THE MEMBER IN FRONT LAYS IS HAD RIGHT BEHIND IT**: where its kind's clause of `keeps`
follows from a yes of the member (hK), that clause holds from some state that is reached in front of
it to the state at the border. -/
theorem thr_back_keeps (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b + 1 ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (b + 1) k s' m E)
    (hK : ∀ blk, cF.blocksInOrder[b]? = some blk → ∀ t t', StepYes 0 blk t t' → Kp blk.place t t') :
    ∃ s blk, cF.blocksInOrder[b]? = some blk ∧ Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (m.st.input.x.pub, s) ∧
      Kp blk.place s s' := by
  obtain ⟨s, blk, hblk, hr, hy⟩ :=
    thr_back_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  exact ⟨s, blk, hblk, hr, hK blk hblk s s' hy⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.foldFacts_raw
#print axioms ProofFile.Honest.FirstThread.thr_reach
#print axioms ProofFile.Honest.FirstThread.foldFacts_thr
#print axioms ProofFile.Honest.FirstThread.thr_back_head
#print axioms ProofFile.Honest.FirstThread.thr_back_keeps
