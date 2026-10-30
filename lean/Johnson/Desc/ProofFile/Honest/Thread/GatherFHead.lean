-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherFHead.lean: the hypothesis `OwesS` (PaysS.lean) of the
rule for a whole file, at the first chain's invariant at the full size, with three of its eight
columns brought down to smaller hypotheses. `owesS_head_form` (GatherHeadForm.lean) gives `OwesS`
from eight columns, with the rider clauses and the family `f` of `keeps` as arguments. Here the
rider clauses are `csHead` (CsHead.lean) and `f` is `fHeadF` (FHeadF.lean). The column `hK` comes
from `fHead_hK_whole` (FHeadKeepsWhole.lean) and `head_hK_forms` (FHeadF.lean). The column `hst`
comes from `fHead_hst` (FHeadStaysAll.lean), carried over by `head_staysBy_mono` (KeepsMono.lean).
The column `hR` is asked only at the combinations of a place and an item that the table `rideOkF`
(Law/NoHouse/RideOkFrame.lean) admits. No definition.

  1  `owesS_fHeadF`   the lemma

What it leaves as hypotheses.
  * `hP`, `hF`, `h₀`, `hl`, `hX`: five columns of `owesS_head_form`, as they stand there.
  * `hok`: an item that is open, that the row neither closes nor has in `owes`, and that the table
    admits at the place, passes over the sub-protocol.
  * `hB`: `ProofFile.baseOf` returns at the public part. `hW`: a test without a free variable on the
    written table of stretches (FHeadStaysAll.lean says why it is not proved). `hσ`: the argument
    `st` of `csHead` at segment 24 survives whatever `K11Keeps` allows.

Limits.
  * `OwesS` is the form of a hypothesis of the rule. Nothing here shows that a run accepts.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherHeadForm
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsWhole
import Johnson.Desc.ProofFile.Honest.Thread.FHeadStaysAll
import Johnson.Desc.ProofFile.Honest.Thread.KeepsMono
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.RideOkFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K3.Law.AtThr (rngWrittenB)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`OwesS` at the first chain's invariant at the full size**, at `csHead` and `fHeadF`. -/
theorem owesS_fHeadF (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hW : rngWrittenB = true)
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
      RidesPastAtS L.thread Said b i) : OwesS L.thread Said := by
  subst hL
  exact owesS_head_form h H Q test carryX item n₁ n₂ b₀ Vd (csHead ν st R)
    (fHeadF Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) w Said rfl hP hF
    (head_hK_forms h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said _ hF
      (fHead_hK_whole h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hB))
    h₀
    (fun b _ c hc h1 h2 => head_staysBy_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
      (kpBy_fHeadF _ _ _ _ _ _)
      (fHead_hst h H Q test carryX item n₁ n₂ b₀ Vd _ _ _ _ _ _ w hW hσ b c hc h1 h2))
    hl hX
    (head_hR_of_cellsF h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hok)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.owesS_fHeadF
