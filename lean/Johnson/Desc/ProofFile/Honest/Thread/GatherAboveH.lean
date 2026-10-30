-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/GatherAboveH.lean: `OwesS` at the first chain's invariant at
the full size (`owesS_fHeadHS`, GatherFramesS.lean) once more, for every condition `keeps` :=
`kpBy f` that implies `kpBy fHeadH` and holds after every accepted step. No definition.

  1  `owesS_aboveHS`   `owesS_fHeadHS` with `kpBy f` in the place of `kpBy fHeadH`, under two
     hypotheses more: `hle` (`kpBy f` implies `kpBy fHeadH`) and `hKf` (the column `hK` of the
     gathering at `f`: after an accepted step from the invariant, `f` holds at the sub-protocol's
     place). `hB` is not asked: `owesS_fHeadHS` spends it on the column `hK` alone. `hF` is asked at
     `SaidOk`, as in `owesS_fHeadHS`; here `hSaid` is spent on that alone
  2  `owesS_fHeadHS_of_above`   a control: the statement of `owesS_fHeadHS`, by one call at
     `f := fHeadH`
  3  `owesS_fHeadIS`   the statement of `owesS_fHeadHS` at `fHeadI` (FHeadI.lean), by one call. The
     column `hK` is paid by `fHeadG_hK`, `head_hbook_paid` and `head_hreply_paid`
     (ReplyKeptPaid.lean)

How it was made. The three statements are that of `owesS_fHeadHS`, changed by a program. The proof
of `owesS_aboveHS` is that of `owesS_fHeadHS` with `hKf` in the place of the pair that pays the
column `hK`, and `hle` at the end of the chain of implications for the riders.

Limits.
  * Those of GatherFramesH.lean and GatherFramesS.lean: conditional lemmas on this folder's own
    definitions. `PlaysS`, the forms, the layings, the exchanges and `hok` are hypotheses.
  * Nothing says that the invariant is entered or holds at any run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.GatherFramesS
import Johnson.Desc.ProofFile.Honest.Thread.ReplyKeptPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`OwesS` at every `keeps` that implies `kpBy fHeadH` and holds after every accepted step.** The
column `hF` is asked at `SaidOk`. -/
theorem owesS_aboveHS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase}
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    (f : KindName → Place → TS → TS → Prop)
    (hle : ∀ p s s', kpBy f p s s' →
      kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) p s s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy f) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2)
    (hKf : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' →
      f blk.place.kind blk.place s s')
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
  exact owesS_head_form h H Q test carryX item n₁ n₂ b₀ Vd (csHead ν st R) f w Said rfl hP
    (fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
      hF b hb blk hblk k s m E ds y cols s' (thrS_mono _ hSaid hA) hd hS)
    hKf h₀
    (fun b _ c hc h1 h2 => head_staysBy_mono h H Q test carryX item n₁ n₂ b₀ Vd _ _ w _
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s'
        (kpBy_fHeadG _ _ _ _ _ _ p s s' (kpBy_fHeadH _ _ _ _ _ _ p s s' (hle p s s' hk))))
      (fHead_hst_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ _ _ _ _ w hσ b c hc h1 h2))
    hl hX
    (head_hR_of_cellsF h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hok)

/-- A control: `owesS_fHeadHS` (GatherFramesS.lean), statement for statement. -/
theorem owesS_fHeadHS_of_above (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
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
  exact owesS_aboveHS h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hσ
    (fHeadH Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) (fun _ _ _ hk => hk) rfl hP hF
    (fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨fHeadG_hK h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hB hF b hb blk hblk k s m E ds y cols s'
          (thrS_mono _ hSaid hA) hd hS,
        head_hbook_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩)
    h₀ hl hX hok

/-- `owesS_fHeadHS` at `fHeadI`. -/
theorem owesS_fHeadIS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {ν : Nat}
    {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hσ : ∀ s s', Johnson.Desc.First.ForkMerge.Returns.K11Keeps (K11.parOf Zp Bs.G₀) s s' →
      st 24 s → st 24 s')
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull)
      P5J.At.Tok MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadI Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD)) w)
    (hP : ∀ b, b < L.thread.bs.length → PlaysS L.thread Said b)
    (hF : ∀ b, b < L.thread.bs.length → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread SaidOk b k s m E → drawsFit blk.rounds ds = true →
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
  exact owesS_aboveHS h H Q test carryX item n₁ n₂ b₀ Vd w Said hSaid hσ
    (fHeadI Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) h.𝔇.pubD) (kpBy_fHeadI _ _ _ _ _ _) rfl hP hF
    (fun b hb blk hblk k s m E ds y cols s' hA hd hS =>
      ⟨⟨fHeadG_hK h H Q test carryX item n₁ n₂ b₀ Vd _ _ w hB hF b hb blk hblk k s m E ds y cols s'
          (thrS_mono _ hSaid hA) hd hS,
        head_hbook_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩,
        head_hreply_paid h H Q test carryX item n₁ n₂ b₀ Vd _ _ w Said hB b hb blk hblk k s m E ds
          y cols s' hA hd hS⟩)
    h₀ hl hX hok

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.owesS_aboveHS
#print axioms ProofFile.Honest.FirstThread.owesS_fHeadHS_of_above
#print axioms ProofFile.Honest.FirstThread.owesS_fHeadIS
