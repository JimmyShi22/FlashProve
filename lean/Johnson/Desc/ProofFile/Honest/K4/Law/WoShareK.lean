-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoShareK.lean

What is here, and why. Law/WoOf.lean, Law/WoTies.lean, Law/WoAtStand.lean and Law/WoShare.lean
type the reader rw at d.lay.lk column bits. THE LIBRARY's OWN READER AT ITS FULL-SIZE STRUCTURE
(`MgData.rw13`, Johnson/Desc/Sound/MgAll.lean) IS TYPED AT ANOTHER TERM, P13.lin.kCol: the two are
equal by a public fact alone, so none of those statements can be called at that reader as they
stand. Here is the share of Exchange at the pending row's item at a reader typed at any kC, under
that equation; the library takes the same equation as a hypothesis where it meets the same seam
(Johnson/Desc/Sound/MgAt/K11.lean). A definition, and statements with their proofs: a
substitution, then a call.

  `K4WeightsTieK`: the second tie on the witness (`K4WeightsTieAt`, Law/WoTies.lean) at a reader
      typed at any kC. This defines a hypothesis.
  `k4_wo_share_k`: ShareAt T At b [iWo].
  `k4_exchangeAtS_wo_k`: ExchangeAtS T Said b iWo.

Limits. CONDITIONAL THROUGHOUT, as Law/WoShare.lean, whose hypotheses these statements take, with
one more: hkC: the number kC of column bits at which the reader rw of the pile of pending rows is
typed is the layout's. No example of the hypotheses together is known; at a thread none of whose
steps accepts the statements hold emptily. Nothing on soundness, on completeness or on any other
property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading WsShape wsLayOf)
open OnBytes.Model.Layer (Own)
open OnBytes.Road (Wm)
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.First.FillP1 (PileWit PubData)
open VerifiableInference.Desc.K13.Law (lowBits)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

/-- **The witness's matrix is M**, at a reader typed at any number kC of column bits. This defines a
hypothesis; the definition claims nothing. -/
def K4WeightsTieK {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk First.S Claim V W X Pb)
    (d : PubData) {nR kC : Nat} (rw : T.P × First.S → T.Wt → PileWit nR kC) (k : Coins Bk)
    (y : Mid W X) (s' : First.S) (M : Wm Cb.Gl.E) : Prop :=
  nR ≤ 2 ^ d.lin.kRow ∧ (∀ j, nR ≤ j → ∀ C, M j C = 0) ∧
    ∀ ds' (i : Fin nR) (C : Nat), C < 2 ^ kC →
      (rw (T.seat k y s') (T.wit k y.st.input (y.st.heard ++ ds'))).mat i (lowBits kC C) = M i C

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **THE SHARE OF `Exchange` AT THE PENDING ROW's ITEM, AT A READER TYPED AT ANY kC.** CONDITIONAL:
on every hypothesis named. -/
theorem k4_wo_share_k {iWo : T.ι} {d : PubData} {nR kC : Nat} (hkC : kC = d.lay.lk)
    {rw : T.P × First.S → T.Wt → PileWit nR kC} {mL : Nat} (Tb : K4WoTable T iWo d rw mL)
    (hAt : ∀ k s m E, At k s m E → Thr T b k s m E)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, At k s m E → K4LookTieAt look Q s m)
    (hTok : ∀ k s m E, At k s m E → K4TokensTieAt tokens s m)
    (hAsk : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      ∃ (P₀ : OnBytes.Model.Layer.Pub) (o₀ : Own), KeptAsks p s s' P₀ o₀)
    {s₀ : WsShape} {p3 : Bool} {lk : ℕ} (hws : wsLayOf s₀ p3 lk = .ok Q.P.wsLay)
    (hlay : d.lay = Q.P.wsLay)
    (hIx : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      ∀ c name endName (cp : SumCoins name endName (mergeSum Q)),
        lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
          (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c →
        SumAt c (k0 Q.g + 15) name endName (mergeSum Q) cp →
        K4IndexTieAt T rw k y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)))
    (hWt : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      K4WeightsTieK T d rw k y.2 s'
        (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w)) :
    ShareAt T At b [iWo] := by
  subst hkC
  exact k4_wo_share_of_stand Tb hAt hSeat hSit hMask hLook hTok hAsk hws hlay hIx hWt

/-- **In the threads' own form, at the pair of the thread's sentence and what has been said.**
CONDITIONAL: as `k4_wo_share_k` at At := ThrS T Said b. -/
theorem k4_exchangeAtS_wo_k (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    {iWo : T.ι} {d : PubData} {nR kC : Nat} (hkC : kC = d.lay.lk)
    {rw : T.P × First.S → T.Wt → PileWit nR kC} {mL : Nat} (Tb : K4WoTable T iWo d rw mL)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, ThrS T Said b k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, ThrS T Said b k s m E → K4LookTieAt look Q s m)
    (hTok : ∀ k s m E, ThrS T Said b k s m E → K4TokensTieAt tokens s m)
    (hAsk : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      ∃ (P₀ : OnBytes.Model.Layer.Pub) (o₀ : Own), KeptAsks p s s' P₀ o₀)
    {s₀ : WsShape} {p3 : Bool} {lk : ℕ} (hws : wsLayOf s₀ p3 lk = .ok Q.P.wsLay)
    (hlay : d.lay = Q.P.wsLay)
    (hIx : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      ∀ c name endName (cp : SumCoins name endName (mergeSum Q)),
        lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) (k4Place Q)
          (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts 0 = .ok c →
        SumAt c (k0 Q.g + 15) name endName (mergeSum Q) cp →
        K4IndexTieAt T rw k y.2 s' (Reading.gl.val ((endRun cp).getD 0 zeroE)))
    (hWt : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      K4WeightsTieK T d rw k y.2 s'
        (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w)) :
    ExchangeAtS T Said b iWo :=
  (shareAt_said T Said b iWo).1
    (k4_wo_share_k hkC Tb (fun _ _ _ _ hT => hT.1) hSeat hSit hMask hLook hTok hAsk hws hlay hIx
      hWt)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_wo_share_k
#print axioms ProofFile.Honest.K4.k4_exchangeAtS_wo_k
