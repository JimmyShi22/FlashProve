-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Assembly.lean: mode I of the token challenger is the plain challenger that lays
late: the proof of Spec.lateTwin (Johnson/LateSide/Spec.lean) from its hypothesis LateStep.

A general lemma. This file states no goal of the release.

By the map of states stateOf and the lemma on maps of states for admissible adversaries (lump_gAdm,
Compile/DeferRun/Lump.lean). A query: a lazy answer at the exchanged point is a lazy answer of the
exchanged table (lazyAnswer_img, Johnson/GhostSide/ViaDefer.lean). The setup and a shown request:
LateStep. Every other batch: fixed proofs on both sides, and no program (ownPf_fixed).

-/
import Johnson.LateSide.Spec
import Rom.LateAdv
import Johnson.HopSide.Proof
import Johnson.GhostSide.Back
import Compile.DeferRun.Lump
import Compile.Step1_life2_Chall

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.HopSide
open OnBytes.LateWorld
open _root_.Compile.GlueB (GCall GIn GAdm ownPf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- Of fixed proofs, one for each slot, the adversary's own: one for each of its own instances. -/
theorem ownPf_fixed {X Wn Pf : Type} (c : Pf) : ∀ b : ZKCP.Gen.Batch X Wn,
    ownPf b (b.map fun _ => c) = b.ownX.map fun _ => c
  | [] => rfl
  | s :: b => by
    have ih : ((b.zip (b.map fun _ => c)).filter fun t => t.1.2.2).map (fun t => t.2) =
        ((b.filter fun t => t.2.2).map fun t => t.1).map fun _ => c := ownPf_fixed c b
    show ((((s, c) :: b.zip (b.map fun _ => c)).filter fun t => t.1.2.2).map fun t => t.2) =
      (((s :: b).filter fun t => t.2.2).map fun t => t.1).map fun _ => c
    cases hs : s.2.2 with
    | true =>
      rw [List.filter_cons_of_pos (p := fun t : (X × Wn × Bool) × Pf => t.1.2.2) hs,
        List.filter_cons_of_pos (p := fun t : X × Wn × Bool => t.2.2) hs, List.map_cons,
        List.map_cons, List.map_cons, ih]
    | false =>
      rw [List.filter_cons_of_neg (p := fun t : (X × Wn × Bool) × Pf => t.1.2.2) (by simp [hs]),
        List.filter_cons_of_neg (p := fun t : X × Wn × Bool => t.2.2) (by simp [hs]), ih]

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
  {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec} {h : HonestSide lam L Bd aT aL}
  {tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB} {i : I}
  {Good : Option (IskT lam L Bd aT aL) → DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) → Prop}

/-- The invariant with its flag: before the setup no key; after it a key. -/
def InvL (Good : Option (IskT lam L Bd aT aL) → DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) → Prop) :
    Bool → Option (IskT lam L Bd aT aL) × DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) → Prop
  | false, x => x.1 = none ∧ Good none x.2
  | true, x => ∃ k, x.1 = some k ∧ Good (some k) x.2

theorem reply_setup (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (((challT W S cA r₀ h tl i).world true).pre (ghost W)).reply (none, D) .setup =
      ((commitT W S cA h tl i).run true D).map fun y => (.inl y.1.1, (some y.1.2, y.2)) := by
  show ((((commitT W S cA h tl i).bind fun o => Step.pure (Sum.inl o.1, some o.2)).run true D).map
    fun q => (q.1.1, (q.1.2, q.2))) = _
  rw [Life2.run_bind, PMF.map_bind]
  simp only [Step.run, PMF.pure_map]
  rfl

theorem reply_batch (k : IskT lam L Bd aT aL) (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (b : ZKCP.Gen.Batch X Unit) :
    (((challT W S cA r₀ h tl i).world true).pre (ghost W)).reply (some k, D) (.batch b) =
      ((proveWT W cA r₀ h tl k b).run true D).map fun y =>
        (.inr (ownPf b y.1), (some k, y.2)) := by
  show ((((proveWT W cA r₀ h tl k b).bind fun πs =>
    Step.pure (Sum.inr (ownPf b πs), some k)).run true D).map fun q => (q.1.1, (q.1.2, q.2))) = _
  rw [Life2.run_bind, PMF.map_bind]
  simp only [Step.run, PMF.pure_map]
  rfl

/-- a batch that is not one request of the adversary's own -/
theorem batch_fixed (k : IskT lam L Bd aT aL) (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (b : ZKCP.Gen.Batch X Unit)
    (e3 : proveWT W cA r₀ h tl k b = .pure (b.map fun _ => ⟨0, 0, none⟩))
    (e4 : lateBatch W cA r₀ h (iskOf tl.preE k D.vals) (Table.via (ghost W) D.table) b =
      PMF.pure (b.ownX.map fun _ => ⟨0, 0, none⟩, Table.via (ghost W) D.table)) :
    ((((challT W S cA r₀ h tl i).world true).pre (ghost W)).reply (some k, D) (.batch b)).map
        (Prod.map id (stateOf W tl.preE)) =
      (lateW W S cA r₀ h i).reply (stateOf W tl.preE (some k, D)) (.batch b) := by
  rw [reply_batch, e3]
  refine (PMF.map_comp _ _ _).trans ?_
  refine Eq.trans (PMF.pure_map _ ((b.map fun _ => (⟨0, 0, none⟩ : RequestProof lam L)), D)) ?_
  refine Eq.trans ?_ (congrArg (PMF.map fun o : List (RequestProof lam L) × Tb W =>
    ((Sum.inr o.1 : GIn (FullKey lam L aT aL) (RequestProof lam L)),
      (some (iskOf tl.preE k D.vals), o.2))) e4).symm
  rw [PMF.pure_map, ← ownPf_fixed]
  rfl

theorem lateTwin : Spec.lateTwin := by
  intro I X lam L Bd aT aL W S cA r₀ h tl i Good α ok A n hL hA
  refine DeferRun.lump_gAdm_fst ok (((challT W S cA r₀ h tl i).world true).pre (ghost W))
    (lateW W S cA r₀ h i) (stateOf W tl.preE) (InvL Good) ?_ ?_ ?_ ?_ ?_ ?_ A false n
    (none, DSt.init _) hA ⟨rfl, hL.init⟩
  · rintro f ⟨s, D⟩ o q _
    have e := congrArg (PMF.map fun p : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Rng o × Tb W =>
      (p.1, (s.map fun k => iskOf tl.preE k D.vals, p.2)))
      (lazyAnswer_img (ghost_inv W) D.table o q)
    rw [PMF.map_comp] at e
    refine Eq.trans ?_ e
    show (((lazyAnswer D.table (ghost W o q).1 (ghost W o q).2.1).map _).map _).map _ = _
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  · rintro f ⟨s, D⟩ o q hI y hy
    have hy' : y ∈ (((lazyAnswer D.table (ghost W o q).1 (ghost W o q).2.1).map fun p =>
        (p.1, (s, { D with table := p.2 }))).map fun x =>
          ((ghost W o q).2.2 x.1, x.2)).support := hy
    rw [PMF.map_comp] at hy'
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy'
    have hG : ∀ s', Good s' D → Good s' { D with table := z.2 } := by
      intro s' hg
      cases hT : D.table (ghost W o q).1 (ghost W o q).2.1 with
      | some r =>
        rw [lazyAnswer_of_some hT] at hz
        rw [(PMF.mem_support_pure_iff _ _).1 hz]
        exact hg
      | none =>
        rw [lazyAnswer_of_none hT] at hz
        obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
        exact hL.ask s' D _ _ r hg hT
    cases f
    · exact ⟨hI.1, hG none hI.2⟩
    · obtain ⟨k, hk, hg⟩ := hI
      exact ⟨k, hk, hG (some k) hg⟩
  · rintro ⟨s, D⟩ ⟨hs, hg⟩
    obtain rfl : s = none := hs
    rw [reply_setup]
    refine (PMF.map_comp _ _ _).trans ?_
    have e := congrArg (PMF.map fun o : (FullKey lam L aT aL × Isk lam L Bd aT aL) × Tb W =>
      ((Sum.inl o.1.1 : GIn (FullKey lam L aT aL) (RequestProof lam L)), (some o.1.2, o.2)))
      (hL.setup D hg)
    rw [PMF.map_comp] at e
    exact e
  · rintro ⟨s, D⟩ ⟨hs, hg⟩ y hy
    obtain rfl : s = none := hs
    rw [reply_setup] at hy
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
    exact ⟨z.1.2, rfl, hL.setupGood D hg z hz⟩
  · rintro ⟨s, D⟩ b _ ⟨k, hs, hg⟩
    obtain rfl : s = some k := hs
    rcases b with _ | ⟨⟨x, u, own⟩, _ | ⟨v, l⟩⟩
    · exact batch_fixed k D [] rfl rfl
    · cases own
      · exact batch_fixed k D [(x, u, false)] rfl rfl
      · cases u
        rw [reply_batch]
        refine (PMF.map_comp _ _ _).trans ?_
        have e := congrArg (PMF.map fun o : List (RequestProof lam L) × Tb W =>
          ((Sum.inr o.1 : GIn (FullKey lam L aT aL) (RequestProof lam L)),
            (some (iskOf tl.preE k D.vals), o.2))) (hL.sess k D x hg)
        rw [PMF.map_comp] at e
        refine Eq.trans (HopSide.map_congr_support _ fun y hy => ?_) e
        show ((Sum.inr (ownPf [(x, (), true)] y.1) : GIn (FullKey lam L aT aL) (RequestProof lam L)),
            (some (iskOf tl.preE k y.2.vals), Table.via (ghost W) y.2.table)) =
          (Sum.inr (ownPf [(x, (), true)] y.1),
            (some (iskOf tl.preE k D.vals), Table.via (ghost W) y.2.table))
        rw [(hL.sessGood k D x hg y hy).2]
    · exact batch_fixed k D _ (HopSide.proveWT_long k _ v l)
        (by cases own <;> rfl)
  · rintro ⟨s, D⟩ b _ ⟨k, hs, hg⟩ y hy
    obtain rfl : s = some k := hs
    rw [reply_batch] at hy
    obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
    refine ⟨k, rfl, ?_⟩
    rcases b with _ | ⟨⟨x, u, own⟩, _ | ⟨v, l⟩⟩
    · rw [(PMF.mem_support_pure_iff _ _).1 hz]
      exact hg
    · cases own
      · rw [(PMF.mem_support_pure_iff _ _).1 hz]
        exact hg
      · cases u
        exact (hL.sessGood k D x hg z hz).1
    · rw [HopSide.proveWT_long k _ v l] at hz
      rw [(PMF.mem_support_pure_iff _ _).1 hz]
      exact hg

end OnBytes.LateSide

#print axioms OnBytes.LateSide.lateTwin
