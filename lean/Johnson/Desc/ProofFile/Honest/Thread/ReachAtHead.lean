-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ReachAtHead.lean: FROM THE PAIR OF THE FIRST CHAIN's THREAD AT
THE LIBRARY's HEAD (`lettersHead`, Honest/Thread/FirstHead.lean) AND "EVERY WORD THAT THE ROUNDS
SEEN SHOW IS BELOW THE PRIME" (`SaidOk`, Honest/Thread/SaidOk.lean) TO THE LIBRARY's OWN "REACHED"
AT THE DESCRIPTION's FIRST CHAIN (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean): reached by the steps
of the members UNDER `below`. The thread alone gives the reach by the members' own steps
(`thr_reach`, Honest/Thread/ReachFacts.lean), which is weaker. Three statements: one call of
`reach_below` (Honest/Thread/SaidOk.lean), an unfolding, a pairing. No definition.

  `thrS_reach_below`   the pair at a border gives `Reach` over the members under `below`
  `thrS_rchAt`   the same as `RchAt`, at whatever stands beside the statement's first half
     (it is not read)
  `thrS_rch`   with "typed" as a premise: the head's own condition beside the first table's promise

HOW FAR IT REACHES, AND NO FURTHER. The head's own condition (`P5J.AtMg.rch`,
Johnson/P5J/FourAtMg.lean) is `RchAt` AND "the public part is a typed instance's"
(`P5J.AtMg.typed`): the second is a premise here: no clause of the thread says it. THE LIBRARY's
LAWS AT THE HEAD THAT SPEAK OF "REACHED" (for one `P5J.ok0_layers_hd`, Johnson/P5J/K09AreadyHd.lean)
TAKE MORE THAN THAT CONDITION: the table's promise at the library's own meaning and at the frame's
strings (`onTR`, Johnson/Desc/First/Link/Law/LinkTiedR.lean), at a border of their own naming.
NOTHING HERE GIVES THESE; NONE OF THESE LAWS IS CALLED HERE.

FOR THE FIRST TWO: NO PREMISE BUT THE PAIR AND THAT b IS A BORDER OF THE CHAIN. `reach_below`'s one
premise on a letter (the stored columns' words are below the prime) holds of `Prover.storedWords` by
make (`storedWords_lt`, Honest/Law/Run.lean). The letter's own debt is paid at every member, general
in the kind (`saidNext_ok`): the authors of no kind owe it.

Limits. THE FULL SIZE ALONE, and the format's second hash function alone. The library's head has a member at
the name under four premises on the public files (the seal's `P5J.head_exists_at_name`); this file
does not call it; no member of the head together with the thread's sentence is shown. `lettersHead`
is without code: no test with code reaches the thread itself. None is one of the library's goals.
This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Top.H0.Walk.ReachAt
import Johnson.P5J.FourAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.Sound (MsgT below)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE PAIR AT A BORDER GIVES THE REACH BY THE WRAPPED MEMBERS' STEPS.** -/
theorem thrS_reach_below (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m
      E) :
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) b (m.st.input.x.pub, s) :=
  reach_below (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ProofFile.startS Zp) m.st.input.x.pub hb (fun _ h0 => h0)
    (fun v i p u hu => storedWords_lt H v.w₀ v.rc i p u hu) hT

/-- **THE SAME AS THE LIBRARY's "REACHED" AT THE DESCRIPTION.** y: what stands beside: it is not
read. -/
theorem thrS_rchAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Str : Type} (y : Str) {b : Nat} {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m
      E) :
    RchAt (F0T OnBytes.secondHashFunction Zp Np cF) b ((m.st.input.x.pub, s), y) :=
  thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT

/-- **THE HEAD's OWN CONDITION BESIDE THE FIRST TABLE's PROMISE**, at the public part of a typed
member of the instances. -/
theorem thrS_rch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk b k s m
      E)
    (ht : h.toAtMg.typed m.st.input.x.pub) : ∀ y, h.toAtMg.rch b ((m.st.input.x.pub, s), y) :=
  fun y => ⟨thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w y hb hT, ht⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.thrS_reach_below
#print axioms ProofFile.Honest.FirstThread.thrS_rchAt
#print axioms ProofFile.Honest.FirstThread.thrS_rch
