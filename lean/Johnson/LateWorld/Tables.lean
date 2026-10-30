-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Tables.lean: THE MAKING OF ONE TABLE WITH ITS LEAVES LAID LATE: the proofs of
Spec.tabBodies and Spec.seedsBad (Johnson/LateWorld/SpecTables.lean). Theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

tabBodies. The honest builder and the one over fillings go side by side (TiedL, Rom/Dry/Tied.lean):
the leaves are deferred, so both get the same digests whatever the leaves hold (tl_treeO,
OnBytes/Dry/Side.lean); so the levels and the root are the same, and the seed's two queries are one
program. TiedL.map_defer (Rom/Dry/TiedDefer.lean) turns that into an equation of laws.

seedsBad. The tree's part never asks a Fiat-Shamir oracle, so that column of the table of answers is
as it was (runDefer_avoids). The seed's first query writes at most at a point of round 1, which is
no second query (round 2). The second query finds an entry, which gives a seed in Gs, by the premise
on the table; or it is answered afresh, and then the seed is S.seed of uniform blocks.

Main names (namespace OnBytes.LateWorld).
  tied_tab     the two builders side by side.
  tabBodies    THE FIRST THEOREM.
  seedsIn_first, seeds_second, seeds_bad   the seed's first query, its second, the two.
  seedsBad     THE SECOND THEOREM.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecTables
import Rom.Dry.TiedDefer
import OnBytes.Dry.Side
import Johnson.Prover.Law.Asks

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The second form's names of oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-- The second form's answers of a Fiat-Shamir oracle. -/
local notation "FsAns₂" => TypedOracleCompiler.Compile.Batch.FsAns

/-! ## The bodies -/

/-- The honest builder and the builder over fillings, side by side. -/
theorem tied_tab (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    TL lateTab (fun (a : TabK lam L Bd aT aL) _
        (b : TreeK lam (typedOracleCarrier L Bd aT aL) × L.OutOfDomainSeed) _ =>
        a = ⟨r, realTree W b₀ (L.encodeIndex i r) b.1, b.2⟩) [] []
      (tabO W S b₀ i r s) (tabF W S b₀ s) := by
  unfold tabO tabF committerTreeKeptByProver
  refine TiedL.bind (tl_treeO lateTab False (fun _ => false) rfl (fun _ _ => rfl) W.depth _ _ [] []
    fun hf => hf.elim) fun T l₁ T' l₁' hTT => ?_
  obtain ⟨⟨hlv, hi, hi'⟩, hl⟩ := hTT
  have hroot : T.root = T'.root := by
    unfold TreeK.root
    rw [hlv]
  rw [hroot]
  refine TiedL.bind (tl_refl lateTab False (fun _ => false) (seedsO W S T'.root) l₁ l₁' hl)
    fun e l₂ e' l₂' he => .done ?_
  obtain ⟨rfl, _⟩ := he
  have hT : T = realTree W b₀ (L.encodeIndex i r) T' := by
    obtain ⟨inp, lv⟩ := T
    obtain ⟨inp', lv'⟩ := T'
    obtain rfl : lv = lv' := hlv
    obtain rfl : inp = _ := hi
    obtain rfl : inp' = _ := hi'
    rfl
  rw [hT]

/-- **The honest table is the reduction's with the bodies put in.** -/
theorem tabBodies : Spec.tabBodies := by
  intro I X lam L Bd aT aL W S b₀ i r s T
  exact TiedL.map_defer Handler.lazy
    (H := fun o => (o.1, o.2.1))
    (H' := fun o => ((⟨r, realTree W b₀ (L.encodeIndex i r) o.1.1, o.1.2⟩ : TabK lam L Bd aT aL), o.2.1))
    (fun a l b l' hab s => by rw [hab]) (tied_tab W S b₀ i r s) T

/-! ## The seeds -/

theorem seedQ1_ne_seedQ0 (v : Bits) (cm : Dig lam) : seedQ1 W S v ≠ seedQ0 W S cm := fun e =>
  absurd (show (2 : ℕ) = 1 from
    congrArg (fun z : FbIn lam (typedOracleCarrier L Bd aT aL) S.t => z.round) e) (by decide)

/-- The seed's first query keeps the property of the table of answers. -/
theorem seedsIn_first (Gs : L.OutOfDomainSeed → Prop) (T : Tb W) (hT : SeedsIn W S Gs T) (cm : Dig lam) :
    ∀ x ∈ (lazyAnswer T (OracleName.fb S.t : ON₂) (seedQ0 W S cm)).support, SeedsIn W S Gs x.2 := by
  intro x hx
  unfold lazyAnswer at hx
  cases h0 : T (OracleName.fb S.t : ON₂) (seedQ0 W S cm) with
  | some r =>
    rw [h0] at hx
    rw [(PMF.mem_support_pure_iff _ _).mp hx]
    exact hT
  | none =>
    rw [h0] at hx
    obtain ⟨r, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    intro v a ha
    refine hT v a ?_
    rw [← ha]
    exact (Derive.set_of_ne_point T (OracleName.fb S.t : ON₂) (seedQ1_ne_seedQ0 W S v cm) r).symm

/-- The seed's second query. -/
theorem seeds_second (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞)
    (hδ : pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ) (T : Tb W)
    (hT : SeedsIn W S Gs T) (v : Bits) :
    pr (lazyAnswer T (OracleName.fb S.t : ON₂) (seedQ1 W S v))
      {x | ¬ Gs (S.seed (show FsAns₂ lam W.K from x.1).1) ∨ ¬ SeedsIn W S Gs x.2} ≤ δ := by
  unfold lazyAnswer
  cases h1 : T (OracleName.fb S.t : ON₂) (seedQ1 W S v) with
  | some a =>
    show pr (PMF.pure (a, T)) _ ≤ δ
    rw [pr_pure, if_neg]
    · exact zero_le _
    · rintro (hn | hn)
      · exact hn (hT v a h1)
      · exact hn hT
  | none =>
    show pr ((unif (FsAns₂ lam W.K)).map fun r =>
      (r, T.set (OracleName.fb S.t : ON₂) (seedQ1 W S v) r)) _ ≤ δ
    rw [pr_map]
    refine le_trans (pr_mono _ (F := {r : FsAns₂ lam W.K | ¬ Gs (S.seed r.1)}) ?_) ?_
    · rintro r (hn | hn)
      · exact hn
      · intro hg
        refine hn fun v' a ha' => ?_
        have ha : T.set (OracleName.fb S.t : ON₂) (seedQ1 W S v) r (OracleName.fb S.t : ON₂) (seedQ1 W S v') =
          some a := ha'
        by_cases hv : seedQ1 W S v' = seedQ1 W S v
        · rw [hv, Derive.set_same] at ha
          obtain rfl := Option.some.inj ha
          exact hg
        · rw [Derive.set_of_ne_point T (OracleName.fb S.t : ON₂) hv r] at ha
          exact hT v' a ha
    · refine le_trans (le_of_eq ?_) hδ
      rw [← Prob.map_fst_unif (C := Fin W.K → Dig lam) (D := Dig lam), pr_map]
      rfl

/-- The seed's two queries, from a table of answers with the property. -/
theorem seeds_bad (Gs : L.OutOfDomainSeed → Prop) (δ : ℝ≥0∞)
    (hδ : pr (unif (Fin W.K → Dig lam)) {u | ¬ Gs (S.seed u)} ≤ δ) (T : Tb W)
    (hT : SeedsIn W S Gs T) (lg : Trace (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (tr : TreeK lam (typedOracleCarrier L Bd aT aL)) :
    pr (((seedsO W S tr.root).bind fun e => OComp.pure (tr, e)).runDefer mkTab T lg)
      {o | ¬ Gs o.1.2 ∨ ¬ SeedsIn W S Gs o.2.1} ≤ δ := by
  show pr ((OComp.query (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t : ON₂)
      (seedQ0 W S tr.root) fun a0 =>
      OComp.query (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t : ON₂)
        (seedQ1 W S (TypedOracleCompiler.Compile.Batch.link (show FsAns₂ lam W.K from a0))) fun a1 =>
        OComp.pure (tr, S.seed (show FsAns₂ lam W.K from a1).1)).interp
      (Handler.defer mkTab Handler.lazy) (T, lg)) _ ≤ δ
  rw [OComp.interp_query, Handler.defer_of_not Handler.lazy (show mkTab (OracleName.fb S.t : ON₂) _ = false
    from rfl), PMF.bind_map]
  refine pr_bind_le_of_forall _ _ _ fun x hx => ?_
  have hT1 := seedsIn_first W S Gs T hT tr.root x hx
  show pr ((OComp.query (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t : ON₂)
      (seedQ1 W S (TypedOracleCompiler.Compile.Batch.link (show FsAns₂ lam W.K from x.1))) fun a1 =>
      OComp.pure (tr, S.seed (show FsAns₂ lam W.K from a1).1)).interp
      (Handler.defer mkTab Handler.lazy) (x.2, lg)) _ ≤ δ
  rw [OComp.interp_query, Handler.defer_of_not Handler.lazy (show mkTab (OracleName.fb S.t : ON₂) _ = false
    from rfl), PMF.bind_map]
  show pr ((lazyAnswer x.2 (OracleName.fb S.t : ON₂) _).map fun y =>
    ((tr, S.seed (show FsAns₂ lam W.K from y.1).1), (y.2, lg))) _ ≤ δ
  rw [pr_map]
  exact seeds_second W S Gs δ hδ x.2 hT1 _

/-- **A seed outside Gs.** -/
theorem seedsBad : Spec.seedsBad := by
  intro I X lam L Bd aT aL W S Gs δ b₀ s T hδ hT
  unfold tabF
  show pr (OComp.interp _ _ (T, [])) _ ≤ δ
  rw [OComp.interp_bind]
  refine pr_bind_le_of_forall _ _ _ fun p hp => ?_
  have hk : p.2.1 (OracleName.fb S.t : ON₂) = T (OracleName.fb S.t : ON₂) :=
    runDefer_avoids mkTab (OracleName.fb S.t : ON₂) _ (avoids_treeO S.t W.depth _) T [] p hp
  have hT1 : SeedsIn W S Gs p.2.1 := fun v a ha => hT v a (by rw [← hk]; exact ha)
  exact seeds_bad W S Gs δ hδ p.2.1 hT1 p.2.2 p.1

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.tabBodies
#print axioms OnBytes.LateWorld.seedsBad
