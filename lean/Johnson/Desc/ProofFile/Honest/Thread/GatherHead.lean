-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherHead.lean: `owesS_first` (Gather.lean) at the first
chain's invariant at the full size (`lettersHead`, FirstHead.lean), where the parameter `Rd` is a
list of rider clauses (`ridersOf cs`, Riders.lean) and `Kp` is given kind by kind (`kpBy f`,
KeepsBy.lean). Two columns become more concrete. `keeps` at a sub-protocol is the clause `f` of the
kind of its place. The part of `rides` that is not a rider clause says that from border `b₀` on the
state holds the reply that the instance asks about. No definition.

  1  `owesS_head`   the lemma. The parameters are named `L`, with an equation, to keep it readable

Limits.
  * A conditional lemma on this folder's own definitions. `cs`, `f`, the script `Q` and the prover
    `H` are arguments. Nothing shows that a hypothesis holds at any sub-protocol.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Gather
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (samplesHeld)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`OwesS` at the first chain's invariant at the full size, from the seven columns.** -/
theorem owesS_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
    (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      s'.failed = none ∧
      IM.XK L.N L.links L.ps (P1K2.EQ L.mgP L.links L.ps (L.pubOf m.st.input.x)) (b + 1) s' =
        true ∧
      samplesHeld L.N L.mgP (IM.openAt L.links L.ps (b + 1)) (L.pubOf m.st.input.x, s') = true ∧
      ∀ q ∈ P1K2.pubAt L.mgP L.links L.ps (b + 1), L.mgP.pubP q (L.pubOf m.st.input.x, s'))
    (hK : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      f blk.place.kind blk.place s s')
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hst : ∀ b, b < L.thread.bs.length → ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi →
      StaysBy L.thread b c)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ cs, c.lo = b + 1 → LaysAtS L.thread Said b c)
    (hX : ∀ b, b < L.thread.bs.length → ∀ i ∈ (L.thread.row b).owes,
      ExchangeAtS L.thread Said b i)
    (hR : ∀ b, b < L.thread.bs.length → ∀ i ∈ L.thread.opened b, i ∉ (L.thread.row b).shuts →
      i ∉ (L.thread.row b).owes → RidesPastAtS L.thread Said b i) : OwesS L.thread Said := by
  subst hL
  exact owesS_first _ Said
    (R₀ := fun c v s => b₀ ≤ c → s.out.reply = some v.x.asked)
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs (kpBy f) w) hP hF
    (fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
      (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) f w hblk rfl s s').2
        (hK b hb blk hblk k s m E ds y cols s' hA hd hS))
    h₀ hst hl hX hR

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.owesS_head
