-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Units.lean: THE TWO UNITS OF THE TOKEN SIDE IN MODE I, AGAINST THE PLAIN PARTS THAT
LAY LATE, the secret coins drawn from the scheme's own enumerations just before the part. Theorems
with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

  tabStep    the making of a table (tabT, Johnson/TokenSide/Whole.lean) in mode I, its table read
             off the store and the oracle's table exchanged, has the law of tabInward
             (Johnson/LateSide/Need.lean). From every state.
  bind_dress a draw from an enumeration with the law RunLaw, dressed by the scheme, against uniform
             bits read through runLens (Johnson/TokenSide2/LensBits.lean): under any law that
             follows.
  extTie_toK the external strings' trees read off the store are tied to the trees with tokens.
  runStep    a compiled run (proveC, Johnson/TokenRules/Chunks.lean) in mode I has the law of: the
             run's coins from their enumeration, dressed; then lateProof
             (Johnson/LateWorld/Defs.lean). From a state that meets RunGood
             (Johnson/LateSide/Run.lean).
tabStep goes the way of runLate (Johnson/LateSide/Run.lean), without an end.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateSide.Run
import Johnson.LateSide.Need
import Johnson.TokenSide2.Units
import Johnson.TokenSide2.SameTab
import Johnson.TokenRel.Release

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open OnBytes.LateWorld
open _root_.Compile.DeferRun (Marks qa keep)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

/-! ## A table -/

section Tab
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)

/-- **The making of a table in mode I.** -/
theorem tabStep (hs : SaltsLaw h.sl (2 ^ W.depth) tl.preE tl.frE) (i : I) (r : L.EncodingRandomness)
    (hR : RoutedT W (tabT W S h tl h.b₀ i r)) (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    ((tabT W S h tl h.b₀ i r).run true D).map
        (fun v => (v.1.toK (fun u => v.2.vals.getD u []) tl.preE,
          Table.via (ghost W) v.2.table)) =
      tabInward W S h i r (Table.via (ghost W) D.table) := by
  have eA : ((tabT W S h tl h.b₀ i r).run true D).map
      (fun v => (v.1.toK (fun u => v.2.vals.getD u []) tl.preE, Table.via (ghost W) v.2.table)) =
      (((tabT W S h tl h.b₀ i r).run true D).map keep).map fun k =>
        (k.1.1.toK (fun u => k.1.2.getD u []) tl.preE, Table.via (ghost W) k.2.1) := by
    rw [PMF.map_comp]
    rfl
  rw [eA, DeferRun.modeI_defer_at mkTable _ D
    (TokenRules.marksTab I X lam L Bd aT aL W S h tl h.b₀ i r D.vals)]
  have eC : (erase (tabT W S h tl h.b₀ i r) D.vals).runDefer mkTable D.table (D.evs.map qa) =
      ((erase (tabT W S h tl h.b₀ i r) D.vals).runDefer mkTable D.table []).map fun o =>
        (o.1, (o.2.1, D.evs.map qa ++ o.2.2)) := by
    have := OComp.interp_defer_shift mkTable Handler.lazy
      (erase (tabT W S h tl h.b₀ i r) D.vals) D.table (D.evs.map qa) []
    rwa [List.append_nil] at this
  have eD := runDefer_plainOf W mkTable hR D.vals (Table.via (ghost W) D.table) []
  rw [via_via_ghost, List.map_nil, runDefer_plain_tab] at eD
  rw [eC, ← eD, PMF.map_comp, PMF.map_comp]
  have eS := (same_tab sameTab W S h tl hs h.b₀ i r D.vals).run _
    (Handler.defer mkTab Handler.lazy) (Table.via (ghost W) D.table, [])
  have eN : tabInward W S h i r (Table.via (ghost W) D.table) =
      ((OComp.sample h.sl.n fun b =>
        tabO W S h.b₀ i r (cutS (2 ^ W.depth) (h.sl.e b))).interp
          (Handler.defer mkTab Handler.lazy) (Table.via (ghost W) D.table, [])).map fun o =>
        (o.1, o.2.1) := by
    rw [OComp.interp_sample, PMF.map_bind]
    rfl
  rw [eN, eS, PMF.map_comp]
  refine congrArg (fun f => PMF.map f _) (funext fun o => ?_)
  show (o.1.1.toK (fun u => o.1.2.getD u []) tl.preE,
    Table.via (ghost W) (Table.via (ghost W) o.2.1)) = _
  rw [via_via_ghost]
  rfl

end Tab

/-! ## A compiled run -/

section Run
variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A draw from an enumeration, dressed by the scheme, against uniform bits read through runLens. -/
theorem bind_dress {γ : Type} (F : Coins lam L → PMF γ) (e : Enum (Coins lam L)) (ln : RunLen lam L)
    (pre : ℕ → Bool → Bits → Bits) (rtail : ℕ → Bits) (nR nK nJ : ℕ) (fill : Bits)
    {fu : Fintype (RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq)}
    (hpad : ∀ a, (e.e a).pad = ln.pad) (hslot : ∀ a, (e.e a).slot = ln.slot)
    (hlaw : (unif (Fin (e.n + 1))).map (fun a => windowOf nR nK nJ (e.e a)) =
      (@unif _ fu _).map windowBits)
    (hrs : ln.rsw = rtail ln.slot) :
    ((unif (Fin (e.n + 1))).bind fun a => F (dress pre rtail nR nK nJ fill (e.e a))) =
      (@unif _ fu _).bind fun u => F (coRun (runLens ln nR nK nJ fill (fu := fu)) pre u) := by
  have e1 : (fun a => F (dress pre rtail nR nK nJ fill (e.e a))) =
      (fun w => F (ofWin ln.pad ln.slot pre ln.rsw nR nK nJ fill w)) ∘
        fun a => windowOf nR nK nJ (e.e a) :=
    funext fun a => by
      rw [dress_eq_ofWin pre rtail nR nK nJ fill (e.e a) (hpad a) (hslot a), hrs]
      rfl
  have e2 : (fun u => F (coRun (runLens ln nR nK nJ fill (fu := fu)) pre u)) =
      (fun w => F (ofWin ln.pad ln.slot pre ln.rsw nR nK nJ fill w)) ∘ windowBits :=
    funext fun u => by
      rw [coRun_runLens]
      rfl
  rw [e1, e2, ← PMF.bind_map, ← PMF.bind_map, hlaw]

variable (W : QueryLayout lam L) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preX : Bits)
  (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ)
  (stop : Rho Q.loc.shape → Bool)

/-- The external strings' trees read off the store are tied to the trees with tokens. -/
theorem extTie_toK {K : ℕ} {D : DSt (typedOracleFamily lam K L)} {E' : ExtSpec} (we : WireE E')
    (hT : ∀ k, TreeOKT D [] (xt k)) :
    ExtTie we (fun k => (xt k).toK (fun w => D.vals.getD w []) preX) xt preX D.vals :=
  fun p => ⟨rfl, rfl, fun a ha => ((hT _) a (List.mem_of_getElem? ha)).1⟩

/-- **A compiled run in mode I**, its coins from their enumeration. -/
theorem runStep (e : Enum (Coins lam L)) (rtail : ℕ → Bits) (nR nK nJ : ℕ) (fill : Bits)
    (hl : RunLaw e nR nK nJ ln.sFS ln.fr ln.rs ln.dq ln.pad ln.slot) (hrs : ln.rsw = rtail ln.slot)
    (hfit : FitsWin nR nK nJ Q.loc.shape Q.ann wq.sh 0) {bl bf : ℕ}
    {sd : (t : Tag) → FbIn lam L t → Prop} {D : DSt (typedOracleFamily lam W.K L)}
    (hD : RunGood W Q wq xt preX ln bl bf sd D)
    (hR : RoutedT W (hashT t Q wq embS embP xin cms x σ ln pre cap)) (hW : wq.OKG) :
    ((proveC t Q wq embS embP xin cms x y xt preX σ ln pre cap stop).run true D).map
        (fun v => (v.1, Table.via (ghost W) v.2.table)) =
      (unif (Fin (e.n + 1))).bind fun a => lateProof t Q wq embS embP xin cms x y
        (fun k => (xt k).toK (fun w => D.vals.getD w []) preX) cap stop σ
        (dress pre rtail nR nK nJ fill (e.e a)) (Table.via (ghost W) D.table) := by
  refine Eq.trans ?_ (bind_dress (fun co => lateProof t Q wq embS embP xin cms x y
    (fun k => (xt k).toK (fun w => D.vals.getD w []) preX) cap stop σ co
    (Table.via (ghost W) D.table)) e ln pre rtail nR nK nJ fill hl.pad hl.slot hl.law hrs).symm
  exact runLate W t Q wq embS embP xin cms x y xt preX σ ln pre cap stop _ TokenRel.release hD hR hW
    (coversRun_inWin ln nR nK nJ _ _ _ hfit) (extTie_toK xt preX wq.ext hD.tree)

end Run

end OnBytes.LateSide

#print axioms OnBytes.LateSide.tabStep
#print axioms OnBytes.LateSide.runStep
