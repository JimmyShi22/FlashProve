-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/Units.lean: ONE TABLE, AND ONE COMPILED RUN, OF THE TOKEN SIDE AGAINST THE
SCHEME's OWN TERM BEHIND ONE DRAW FROM THE SCHEME's OWN LIST OF COINS, as two algorithms with the
same run under every rule for answering queries (Same, Johnson/TokenSide2/Same.lean). From
Spec.sameTab and Spec.sameRun (Johnson/TokenSide/SpecSame.lean), which are hypotheses here (they are
proved in Johnson/TokenSide2/SameTab.lean and Johnson/TokenSide/TieRun.lean), and the laws on the
honest side's coins (SaltsLaw, RunLaw, Johnson/WholeKey/CoinLaws.lean).

Lemmas of one step of a proof. This file states no goal of the release. The token programs are a
device of that step and stand in no statement on the scheme.

The two statements of Johnson/TokenSide/SpecSame.lean compare the token side with a family in coins
ω that have coordinates. The scheme draws its coins by one draw from a list. The way from the one
to the other: the scheme hands on its coins cut to a window (cutS, dress,
Johnson/WholeKey/Defs.lean); the law says how the window is distributed; and the free bits within
the window are coins with coordinates (tabLens, runLens, Johnson/TokenSide2/LensBits.lean). The step
from the list to the free bits is coinsFirst_of_saltsLaw and coinsFirst_of_runLaw
(Johnson/CoinsTie/Run.lean).

  same_tab   a table.
  same_run   a compiled run.

-/
import Johnson.TokenSide2.Same
import Johnson.TokenSide2.LensBits

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.CoinsTie

/-- **One table**: the token side's, against one draw of salts and the scheme's builder. -/
theorem same_tab (hT : Spec.sameTab) {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type}
    {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (h : HonestSide lam L Bd aT aL)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
    (hs : SaltsLaw h.sl (2 ^ W.depth) tl.preE tl.frE) (bd : Bd) (i : I) (r : L.EncodingRandomness)
    (vs : List Bits) :
    Same (fun p : TabT lam L Bd aT aL × List Bits => p.1.toK (fun u => p.2.getD u []) tl.preE)
      (fun p => vs <+: p.2 ∧ TreeOK tl.frE W.depth p.2 p.1.tree)
      (plainOf (tabT W S h tl bd i r) vs)
      (.sample h.sl.n fun b => tabO W S bd i r (cutS (2 ^ W.depth) (h.sl.e b))) := by
  have hTie := hT W S h tl bd i r (tabLens (2 ^ W.depth) tl.frE (fu := inferInstance)) 0 false 0 vs
    fun j hj => ⟨rfl, rfl, rfl, hj⟩
  refine Same.ofFirst hTie.toPost fun σ hd s => ?_
  refine CoinsFirst.of_enum (prog := fun sl => tabO W S bd i r (cutS (2 ^ W.depth) sl))
    (coinsFirst_of_saltsLaw hs
      (prog' := fun f => tabO W S bd i r
        (cutS (2 ^ W.depth) fun j => if hj : j < 2 ^ W.depth then f ⟨j, hj⟩ else []))
      (fun sl => ?_) ?_) σ hd s
  · refine congrArg (tabO W S bd i r) (funext fun j => ?_)
    unfold cutS
    by_cases hj : j < 2 ^ W.depth
    · rw [if_pos hj, if_pos hj]
      beta_reduce
      rw [dif_pos hj]
    · rw [if_neg hj, if_neg hj]
  · have e1 : (fun u : Fin (2 ^ W.depth) → Fin tl.frE → Bool => tabO W S bd i r
          (cutS (2 ^ W.depth) fun j =>
            if hj : j < 2 ^ W.depth then tl.preE ++ List.ofFn (u ⟨j, hj⟩) else [])) =
        fun ω => tabO W S bd i r (cutS (2 ^ W.depth) fun j => tl.preE ++
          (tabLens (2 ^ W.depth) tl.frE (fu := inferInstance)).get ω 0 false 0 j) :=
      funext fun u => congrArg (tabO W S bd i r) (funext fun j => by
        unfold cutS
        by_cases hj : j < 2 ^ W.depth
        · rw [if_pos hj, if_pos hj]
          beta_reduce
          rw [dif_pos hj, tabLens_get u hj]
        · rw [if_neg hj, if_neg hj])
    rw [e1]
    exact CoinsFirst.inst hTie.coinsFirst

/-- **One compiled run**: the token side's, against one draw of coins, the scheme's dressing of
them, the compiled prover, and what is handed out of its outcome. -/
theorem same_run (hR : Spec.sameRun) {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (t : Tag) {Y : Type}
    {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xtK : ℕ → TreeK lam L) (xt : ℕ → TreeT lam L)
    (preX : Bits) (st : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits)
    (cap : ℕ → ℕ) (stop : Rho Q.loc.shape → Bool) (e : Enum (Coins lam L)) (rtail : ℕ → Bits)
    (nR nK nJ : ℕ) (fill : Bits) (vs : List Bits)
    (hl : RunLaw e nR nK nJ ln.sFS ln.fr ln.rs ln.dq ln.pad ln.slot)
    (hrs : ln.rsw = rtail ln.slot) (hok : wq.OKG)
    (hfit : FitsWin nR nK nJ Q.loc.shape Q.ann wq.sh 0) (hx : ExtTie wq.ext xtK xt preX vs) :
    Same (fun p : Option (OneProtocolProof lam Q) × List Bits => p.1) (fun p => vs <+: p.2)
      (plainOf (proveC t Q wq embS embP xin cms x y xt preX st ln pre cap stop) vs)
      (.sample e.n fun a =>
        (proveX t Q wq embS embP xin cms x y xtK st (dress pre rtail nR nK nJ fill (e.e a))
          cap).bind
          fun r => .pure (shown stop r)) := by
  have hTie := hR t Q wq embS embP xin cms x y xtK xt preX st ln pre cap stop
    (runLens ln nR nK nJ fill (fu := inferInstance)) vs hok
    (coversRun_inWin ln nR nK nJ _ _ _ hfit) hx
  refine Same.ofFirst hTie.toPost fun σ hd s => ?_
  refine CoinsFirst.of_enum
    (prog := fun co => (proveX t Q wq embS embP xin cms x y xtK st
      (dress pre rtail nR nK nJ fill co) cap).bind fun r => .pure (shown stop r))
    (coinsFirst_of_runLaw hl
      (prog' := fun w => (proveX t Q wq embS embP xin cms x y xtK st
        (ofWin ln.pad ln.slot pre ln.rsw nR nK nJ fill w) cap).bind fun r => .pure (shown stop r))
      (fun co hp hs => ?_) ?_) σ hd s
  · rw [dress_eq_ofWin pre rtail nR nK nJ fill co hp hs, hrs]
  · have e1 : (fun u : RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq =>
          (proveX t Q wq embS embP xin cms x y xtK st
            (ofWin ln.pad ln.slot pre ln.rsw nR nK nJ fill (windowBits u)) cap).bind
            fun r => OComp.pure (shown stop r)) =
        fun ω => (proveX t Q wq embS embP xin cms x y xtK st
          (coRun (runLens ln nR nK nJ fill (fu := inferInstance)) pre ω) cap).bind
            fun r => OComp.pure (shown stop r) :=
      funext fun u => by rw [coRun_runLens]
    rw [e1]
    exact CoinsFirst.inst hTie.coinsFirst

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.same_tab
#print axioms OnBytes.TokenSide.same_run
