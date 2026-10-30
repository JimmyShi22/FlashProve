-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide2/Sess.lean: A SESSION OF THE TOKEN CHALLENGER, IN THE MODE IN WHICH MARKED
EVALUATIONS ARE DEFERRED, IS A SESSION OF THE PLAIN CHALLENGER THAT LAYS LATE: the proof of
Spec.sessLate (Johnson/LateSide/Good.lean).

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

The token program of a session (proveWT, Johnson/TokenSide/Whole.lean) draws a place and the
strategy's coins, and runs the compiled prover's twin on the copy at that place. The plain side
(lateBatch, Johnson/LateWorld/Defs.lean) draws a place, the strategy's coins and the compiled run's
coins, and runs the compiled prover's chain with its late queries deferred. Draw by draw
(SimAt.sample, Compile/DeferRun/Sim.lean):
  no copy at the place   both sides reply the same fixed proof and leave the table alone; the plain
                         side's third draw is not read;
  a copy at the place    the compiled run in mode I is the plain run at coins from their enumeration
                         (runStep, Johnson/LateSide/Units.lean); the invariant is kept (holdsRun,
                         Johnson/TokenRel/Holds.lean); the store only grows.

-/
import Johnson.LateSide.Good

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open OnBytes.HopSide OnBytes.LateWorld OnBytes.TokenRel
open _root_.Compile.GlueB (GCall GIn GAdm ownPf)
open _root_.Compile.DeferRun (SimAt)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

section Plain
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
  (h : HonestSide lam L Bd aT aL)

theorem lateAt_noCopy (isk : Isk lam L Bd aT aL) (x : X) (j : ℕ) (κ : h.KB)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) (T : Tb W) (e : isk.copies[j]? = none) :
    lateAt W cA r₀ h isk x ⟨j, κ, co⟩ T = PMF.pure (⟨j, h.nm j, none⟩, T) := by
  unfold lateAt
  simp only [e]

theorem lateAt_copy (isk : Isk lam L Bd aT aL) (x : X) (j : ℕ) (κ : h.KB)
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) (T : Tb W) (t : TabK lam L Bd aT aL)
    (e : isk.copies[j]? = some t) :
    lateAt W cA r₀ h isk x ⟨j, κ, co⟩ T =
      (lateBA W cA r₀ (fun _ => t.tree) (h.dressB (h.rvB κ) co) h.capB t.tree.root x
        (L.recOf isk.i t.r t.seed) (L.encodeIndex isk.i t.r) (h.st.stopB isk.i t.r t.seed x (h.nm j))
        (h.st.B isk.i t.r t.seed x (h.nm j) κ) T).map fun o => (⟨j, h.nm j, o.1⟩, o.2) := by
  unfold lateAt
  simp only [e]

/-- The plain side of a session, draw by draw. -/
theorem lateBatch_draws (isk : Isk lam L Bd aT aL) (T : Tb W) (x : X) :
    lateBatch W cA r₀ h isk T [(x, (), true)] =
      (unif (Fin (h.M + 1))).bind fun j => (unif (Fin (h.kB.n + 1))).bind fun c =>
        (unif (Fin (h.coB.n + 1))).bind fun e =>
          (lateAt W cA r₀ h isk x ⟨j.val, h.kB.e c, h.coB.e e⟩ T).map fun a => ([a.1], a.2) := by
  show ((coinsP W h).runLazy T).bind _ = _
  unfold coinsP
  simp only [OComp.runLazy, PMF.bind_bind, PMF.pure_bind]

end Plain

/-- **A session.** -/
theorem sessLate : Spec.sessLate := by
  intro I X lam L Bd aT aL W S cA r₀ h tl bl bf k x D hF hg
  refine SimAt.congr ?_ (lateBatch_draws W cA r₀ h _ _ x)
  show SimAt _ (Step.sample h.M fun j => Step.sample h.kB.n fun c =>
    (proveAtT W cA r₀ h tl k x ⟨j.val, h.kB.e c⟩).bind fun π => Step.pure [π]) D _ _ _
  refine SimAt.sample fun j => SimAt.sample fun c => ?_
  cases e : k.copies[j.val]? with
  | none =>
      have e' : (iskOf tl.preE k D.vals).copies[j.val]? = none := by
        show (k.copies.map _)[j.val]? = none
        rw [List.getElem?_map, e]
        rfl
      rw [proveAtT_none x _ e]
      refine SimAt.pure (a := [(⟨j.val, h.nm j.val, none⟩ : RequestProof lam L)])
        (And.intro hg (List.prefix_refl _)) ?_
      simp only [lateAt_noCopy W cA r₀ h _ x j.val _ _ _ e', PMF.pure_map, PMF.bind_const]
      rfl
  | some t =>
      have e' : (iskOf tl.preE k D.vals).copies[j.val]? =
          some (t.toK (fun u => D.vals.getD u []) tl.preE) := by
        show (k.copies.map _)[j.val]? = _
        rw [List.getElem?_map, e]
        rfl
      have ht : t.tree ∈ k.copies.map fun t => t.tree :=
        List.mem_map.mpr ⟨t, List.mem_of_getElem? e, rfl⟩
      rw [proveAtT_some x _ e, hF.tok.stB]
      have S1 : SimAt (fun D' : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) =>
            Table.via (ghost W) D'.table)
          (proveC Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀)
            (cmsBA cA t.tree.root (L.recOf k.i t.r t.seed).2) (x, L.recOf k.i t.r t.seed)
            (L.encodeIndex k.i t.r) (fun _ => t.tree) tl.preE
            (h.st.B k.i t.r t.seed x (h.nm j.val) (h.kB.e c)) tl.B
            (h.startB (h.rvB (h.kB.e c))) h.capB (h.st.stopB k.i t.r t.seed x (h.nm j.val))) D
          (fun v _ => v)
          (fun _ D' => GoodW W S tl.preE bl bf (some k) D' ∧ D.vals <+: D'.vals) _ :=
        ⟨runStep W Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) _ _ _ (fun _ => t.tree) tl.preE _ tl.B
            _ h.capB _ h.coB h.rtail h.nR h.nK h.nJ h.fill hF.tok.coB hF.tok.rsB hF.tok.fitB
            (runGood_of hg L.onlineBatch (wBC W) (fun _ => t.tree) tl.B (fun _ => ht) hF.ext.B
              hF.lens.frB hF.lens.sB hF.lens.dig)
            (rt_hashT W Tag.onl L.onlineBatch (wBC W) W.embB id _ _ _ _ _ _ _ (fun _ => rfl)
              hF.ghost.backB) hF.tok.okB,
          fun v hv => ⟨⟨holdsRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D _
              hF.lens.frB hF.lens.sB hF.lens.dig hg.1 (fun _ => ht) v hv, hg.2⟩,
            Life2.vals_prefix true _ D v hv⟩⟩
      have S2 := (S1.bind (g := fun c' => Step.pure (⟨j.val, h.nm j.val, c'⟩ : RequestProof lam L))
        (ψ' := fun π _ => π)
        (R' := fun _ D' => GoodW W S tl.preE bl bf (some k) D' ∧ D.vals <+: D'.vals)
        (k' := fun o T => PMF.pure (⟨j.val, h.nm j.val, o⟩, T))
        fun a D' hR => SimAt.pure hR rfl).bind
        (g := fun π => Step.pure [π]) (ψ' := fun πs _ => ownPf [(x, (), true)] πs)
        (R' := fun _ D' => GoodW W S tl.preE bl bf (some k) D' ∧ D.vals <+: D'.vals)
        (k' := fun π T => PMF.pure ([π], T)) fun a D' hR => SimAt.pure hR rfl
      refine S2.congr ?_
      simp only [lateAt_copy W cA r₀ h _ x j.val _ _ _ _ e', PMF.bind_bind, PMF.pure_bind,
        PMF.map_comp]
      rfl

end OnBytes.LateSide

#print axioms OnBytes.LateSide.sessLate
