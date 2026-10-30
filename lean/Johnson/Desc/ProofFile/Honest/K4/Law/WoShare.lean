-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoShare.lean

What is here. The share of a thread's debt Exchange at the pending row's item, at the member of the
layers' own rounds (kind K4), in one statement; and that statement in the threads' own form from the
pair of the thread's sentence and what has been said. Statements with their proofs: calls of
Law/Keeps.lean, Law/Wo.lean, Law/WoOf.lean, Law/WoJoin.lean, Law/WoAtStand.lean,
Law/RunsAtStand.lean, Law/SharesIs.lean and of the library's `unitOK_of_layout`
(Johnson/Road/FormsKeysWLay.lean).

  `lay_of_own`: where the state's reading own? returns o, a layers' segment is open and holds o.
  `units_of_layout`: every unit of a layout that wsLayOf returns passes the library's test UnitOK.
  `k4_wo_share_of_stand`: ShareAt T At b [iWo].
  `k4_exchangeAtS_wo_of_stand`: ExchangeAtS T Said b iWo.

Limits. CONDITIONAL THROUGHOUT; no example of the hypotheses together is known; at a thread none
of whose steps accepts the statements hold emptily. They speak only where At holds. No hypothesis
names the library's full-size structure or a plan's facts; the seat's public test (`K4Seated`'s
field fits) is spent: at shapes that do not fit nothing is said. HYPOTHESES, BY NAME: the table's
parameters at the item (`K4WoTable`) · At gives the thread's sentence · the seat (`K4Seated`,
`K4Sits`) · three of the ties of Law/ScriptAt.lean at At's states (the mask; what the lookup has
sampled; the tokens) · the library's seven conditions on the states in front and behind
(`KeptAsks`), from which Law/RunsAtStand.lean has that the two runs return · hws: the public
data's layout of the weights is what the verifier's own maker `wsLayOf` returns (THE SAME
HYPOTHESIS AS IN Law/TermsPubOf.lean, there at p3 := true: one debt, not two) · hlay: the data's
layout is the public data's · THE TWO TIES ON THE WITNESS of Law/WoTies.lean at every state behind
the step: nothing shows either of any thread. Equations between machine words and their readings.
THE READER rw OF THE PILE OF PENDING ROWS IS TYPED HERE AT d.lay.lk COLUMN BITS; the library's own
reader at its full-size structure is typed at another term for that number, equal to it by a
public fact alone: SO THESE STATEMENTS CANNOT BE CALLED AT THAT READER AS THEY STAND: the forms to
call are Law/WoShareK.lean (general in the number of column bits) and, at the first chain's
thread, Law/WoHead.lean and Law/WoTop.lean. Nothing on soundness, on completeness or on any other
property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.RunsAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.Keeps
import Johnson.Desc.ProofFile.Honest.K4.Law.SharesIs
import Johnson.Road.FormsKeysWLay
import Johnson.Road.K4.InT.ReaderAtK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading WsUnit WsShape WsLay wsLayOf)
open OnBytes.Model.Layer (Own)
open OnBytes.Road (UnitOK unitOK_of_layout)
open OnBytes.Desc.First.K4 (Par k0 seatS)
open OnBytes.Desc.First.K4.InT (segAt_lay)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.First (LayOwn)
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.First.FillP1 (PileWit PubData)
open ProofFile.Honest.SumLaw (SumCoins endRun)
open ProofFile.Honest.K4.SlotsOwn (SumAt)

/-- Where the reading own? returns, a layers' segment is open and holds what it returns. The library
has this statement too (`OnBytes.Road.K4.InT.lay_of_own`, Johnson/Road/K4/InT/WinsReached.lean); it
is typed again here because that file's imports reach modules under Johnson/Goal/, which this file's
do not. -/
theorem lay_of_own {s : First.S} {o : Own} (h : s.own? = some o) :
    ∃ a : LayOwn, s.here = .lay a ∧ a.own = some o := by
  unfold First.S.own? at h
  split at h
  · rename_i a ha
    exact ⟨a, ha, h⟩
  · cases h

/-- The units of a layout that the verifier's own maker returns pass the library's test. -/
theorem units_of_layout {s₀ : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s₀ p3 lk = .ok lay) :
    ∀ (i : ℕ) (u : WsUnit), lay.U[i]? = some u → UnitOK lay.lk u := by
  obtain ⟨h1, h2⟩ := unitOK_of_layout h
  intro i u hu
  rw [h1]
  exact (h2 u (Array.mem_of_getElem? hu)).1

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **THE SHARE OF `Exchange` AT THE PENDING ROW's ITEM.** CONDITIONAL: on every hypothesis named.
hIx: the first tie on the witness, at the reading of the first end coin of whatever the lent row
hands the merge's part. hWt: the second, at the matrix of the honest input's weights. -/
theorem k4_wo_share_of_stand {iWo : T.ι} {d : PubData} {nR : Nat}
    {rw : T.P × First.S → T.Wt → PileWit nR d.lay.lk} {mL : Nat} (Tb : K4WoTable T iWo d rw mL)
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
      K4WeightsTieAt T d rw k y.2 s'
        (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w)) :
    ShareAt T At b [iWo] := by
  refine k4_wo_share Tb (k4_woHolds_of_asks fun blk hblk k s m E ds y cols s' hA hd hS ds' => ?_)
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  obtain ⟨-, _, _, o, -, -, ho, -⟩ := k4_keeps hdec
  obtain ⟨a', ha', ho'⟩ := lay_of_own ho
  obtain ⟨A, hseg, _, _⟩ := segAt_lay ha'
  obtain ⟨_, _, Ak⟩ := hAsk blk hblk k s m E ds y cols s' hA hd hS
  have Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o :=
    ⟨hSeat blk hblk, hSit, Ak.sized, hMask k s m E hA, hS, hseg, ho⟩
  obtain ⟨_, F₁, _, _, _, _, _, h1, hb, _⟩ := stand_runs Z Ak
  exact k4WoAsks_stand Z (hAt k s m E hA) (hLook k s m E hA) (hTok k s m E hA) h1 hb
    (units_of_layout hws) hlay
    (left_of_own ha' ho') (hIx blk hblk k s m E ds y cols s' hA hd hS)
    (hWt blk hblk k s m E ds y cols s' hA hd hS) ds'

/-- **In the threads' own form, at the pair of the thread's sentence and what has been said.**
CONDITIONAL: as `k4_wo_share_of_stand` at At := ThrS T Said b. -/
theorem k4_exchangeAtS_wo_of_stand (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    {iWo : T.ι} {d : PubData} {nR : Nat}
    {rw : T.P × First.S → T.Wt → PileWit nR d.lay.lk} {mL : Nat} (Tb : K4WoTable T iWo d rw mL)
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
      K4WeightsTieAt T d rw k y.2 s'
        (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w)) :
    ExchangeAtS T Said b iWo :=
  (shareAt_said T Said b iWo).1
    (k4_wo_share_of_stand Tb (fun _ _ _ _ hT => hT.1) hSeat hSit hMask hLook hTok hAsk hws hlay hIx
      hWt)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.lay_of_own
#print axioms ProofFile.Honest.K4.units_of_layout
#print axioms ProofFile.Honest.K4.k4_wo_share_of_stand
#print axioms ProofFile.Honest.K4.k4_exchangeAtS_wo_of_stand
