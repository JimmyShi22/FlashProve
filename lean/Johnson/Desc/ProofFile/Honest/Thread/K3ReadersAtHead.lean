-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K3ReadersAtHead.lean: what the readers of a segment answer
before the lookup on that segment's digits (kind K3) they answer after it, at the first chain's
invariant at `lettersHead`. A call of the lemma of the authors of kind K3,
`P5J.k3_digits_readers_head_on` (Johnson/P5J/K03ReadersHeadAsk.lean), which takes the table's
condition at the border, no mark of failure, "the state is reached" and the sub-protocol's accepting
step. The invariant before the step gives the first three (its part `Form`; `thr_reach`,
ReachFacts.lean). No definition.

The conclusion is the hypothesis `Fwd` of the lemmas on the open item `forms m k r`
(FormsLater.lean), at every such item that is open on both sides of the sub-protocol.

  1  `k3_readers_behind`   from the invariant (`Thr`) and the step (`Stepped`). At the output head's
     segment one hypothesis more: the state is reached by the sub-protocols with the test on the
     words in front (`hB`)
  2  `k3_readers_behindS`   from the invariant together with what has been said (`ThrS` at
     `SaidOk`), which gives `hB` (`thrS_reach_below`, ReachAtHead.lean)

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas take the sub-protocol's step. The condition `RidesPastAt` has the clause of `keeps`
    alone: to serve there, the conclusion has to be a part of that clause.
  * `Fwd` says nothing where the reader gives no answer before the step. At some items the table
    names no run, and the conclusion is empty.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.P5J.K03ReadersHeadAsk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT below)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- What the readers answer before the lookup on the digits of segment `l` they answer after it, at
the runs of every item `forms` that is open on both sides. -/
theorem k3_readers_behind {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[VerifiableInference.OnPublicFiles.k3K l true]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (VerifiableInference.OnPublicFiles.k3K l true) k s m E)
    (hB : l = 24 → Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp)
      (VerifiableInference.OnPublicFiles.k3K l true) (m.st.input.x.pub, s))
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') (mm kk : Nat) (ρ : String)
    (ho : Item.forms mm kk ρ ∈ IM.openAt IM.linksW IM.placesW
      (VerifiableInference.OnPublicFiles.k3K l true))
    (ho' : Item.forms mm kk ρ ∈ IM.openAt IM.linksW IM.placesW
      (VerifiableInference.OnPublicFiles.k3K l true + 1)) :
    ∀ p ∈ h.𝔇.runs mm kk ρ, Fwd (h.𝔇.Rd mm) p.1 p.2 s s' := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hF, -, -, -, -⟩ := hT'
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hb : VerifiableInference.OnPublicFiles.k3K l true ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hR := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  exact P5J.k3_digits_readers_head_on h hl hblk
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP rfl rfl rfl
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N noStrs m.st.input.x.pub 0 hR h0 hF.2
    hB hyes mm kk ρ ho ho'

/-- The same from the invariant together with what has been said. -/
theorem k3_readers_behindS {l : Nat} (hl : l < 25) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[VerifiableInference.OnPublicFiles.k3K l true]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (VerifiableInference.OnPublicFiles.k3K l true) k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') (mm kk : Nat) (ρ : String)
    (ho : Item.forms mm kk ρ ∈ IM.openAt IM.linksW IM.placesW
      (VerifiableInference.OnPublicFiles.k3K l true))
    (ho' : Item.forms mm kk ρ ∈ IM.openAt IM.linksW IM.placesW
      (VerifiableInference.OnPublicFiles.k3K l true + 1)) :
    ∀ p ∈ h.𝔇.runs mm kk ρ, Fwd (h.𝔇.Rd mm) p.1 p.2 s s' :=
  k3_readers_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl hblk hT.1
    (fun _ => thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1) hT)
    hS mm kk ρ ho ho'

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k3_readers_behind
#print axioms ProofFile.Honest.FirstThread.k3_readers_behindS
