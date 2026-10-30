-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFHeadW.lean: `fHead_hst` (FHeadStaysAll.lean) and
`owesS_fHeadF` (GatherFHead.lean) without their hypothesis `hW : rngWrittenB = true`. That
hypothesis is a test without a free variable on the written table of stretches. `rngWritten_holds`
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RngWrittenHolds.lean) of the authors of K3's lemmas
proves it. Their proof rests on two evaluations by the kernel (`decide +kernel`) at written lists,
each with a control beside it. No definition.

  1  `fHead_hst_paid`   the column `hst` at `csHead` and `fHead`
  2  `owesS_fHeadF_paid`   `OwesS` at `csHead` and `fHeadF`

What `owesS_fHeadF_paid` leaves as hypotheses.
  * `hP`, `hF`, `h₀`, `hl`, `hX`: five columns of `owesS_head_form` (GatherHeadForm.lean), as they
    stand there.
  * `hok`: an item that is open, that the row neither closes nor has in `owes`, and that the table
    `rideOkF` admits at the place, passes over the sub-protocol.
  * `hB`: it names what `ProofFile.baseOf` returns at the public part (HeadBase.lean: it does return).
  * `hσ`: the argument `st` of `csHead` at segment 24 survives whatever `K11Keeps` allows.

Limits.
  * `OwesS` is the form of a hypothesis of the rule. Nothing here shows that a run accepts.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K3.Law.AtThr (rngWritten_holds)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The column `hst` at `csHead` and `fHead`**, under `AtMgA` and `hσ` alone. -/
theorem fHead_hst_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (G : ProofFile.Ground) (take : Nat → Bool) (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP)
    (p12 : VerifiableInference.Desc.K12.P12) (P13 : VerifiableInference.Desc.K13.Where)
    (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat} {st : Nat → TS → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps P11 s s' → st 24 s → st 24 s') :
    ∀ b, ∀ c ∈ csHead ν st R, c.lo ≤ b → b + 1 ≤ c.hi →
      StaysBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread b c :=
  fHead_hst h H Q test carryX item n₁ n₂ b₀ Vd Rd G take P11 p12 P13 w rngWritten_holds hσ

/-- **`OwesS` at the first chain's invariant at the full size**, at `csHead` and `fHeadF`. -/
theorem owesS_fHeadF_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadF Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (h₀ : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      b₀ ≤ b + 1 → s'.out.reply = some m.st.input.x.asked)
    (hl : ∀ b, b < L.thread.bs.length → ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS L.thread Said b c)
    (hX : ∀ b, b < L.thread.bs.length → ∀ i ∈ (L.thread.row b).owes,
      ExchangeAtS L.thread Said b i)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p → i ∈ L.thread.opened b →
      i ∉ (L.thread.row b).shuts → i ∉ (L.thread.row b).owes → rideOkF p i = true →
      RidesPastAtS L.thread Said b i) : OwesS L.thread Said :=
  owesS_fHeadF h H Q test carryX item n₁ n₂ b₀ Vd w Said hB rngWritten_holds hσ hL hP hF h₀ hl hX
    hok

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_hst_paid
#print axioms ProofFile.Honest.FirstThread.owesS_fHeadF_paid
