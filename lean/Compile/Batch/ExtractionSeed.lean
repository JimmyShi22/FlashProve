-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/ExtractionSeed.lean: for the honest committer of the typed scheme in the form that the
programs run (coins from a seed, the Links in the key, a cache in the proving key, pruned Merkle
paths) the extracted index is the committed one, except with probability at most
`deltaSeed W WP p bk`.

`extractsHonestB` (Compile/Batch/Extraction.lean) says it of the committer C of the compiled scheme;
here it is carried on, over the typed oracles. The property is the optional requirement (i* = i for
the honest committer): `HasExtractionError`, ZKCP/GenOptional.lean.

  `outsIn_tossN`, `outsIn_blocks`, `outsIn_derive`
      Take an algorithm, and make its coin tosses from small ones, or derive them from a seed.
      Whatever the new algorithm can return on paths whose queries are entries of a trace, the
      algorithm itself can return on such paths.
  `extEnc_eqG`
      `extEnc_eq` (Compile/Batch/Extraction.lean) for a well-formed wire record whose rounds may
      have proof-of-work bits (`W.OKG`).
  `extraction_of_first`
      For any committer of the form "X0, then Rest": if X0 makes at most t queries, every output of
      X0 contains a node that the program nodeP' W WP p i can return on a path whose queries are in
      X0's trace, and the digest cm that Rest outputs is that node's root, then Pr[ L.decodeIndex (extEnc W
      trace cm) ≠ some i ] ≤ 2 t² / 2^λ. What Rest queries does not enter: the extractor takes the
      first query with a given answer.
  `deltaSeed W WP p bk`
      2 (2 · 2^depth + Seed.cNode W WP p bk.m)² / 2^λ: the queries for the first tree and for its
      coins.
  `ExtrS.X0`, `restP`, `restAll`
      The committer builds that tree first: the committer of `argP` (Compile/Batch/StarS.lean) is,
      as a program, X0 (sample the seed; the node of the root with coins from the seed) followed by
      `restP` (`argP_C_eq`). `queryBound_X0`: X0's number of queries. `first_X0`: X0's node is one
      that `nodeP'` can return within X0's trace. `cm_restP`, `cm_restAll`: the digest in the key is
      its root, also after cache and pruning.
  `extraction_prunedK`
      ZKCP.Gen.HasExtractionError (prunedK W p (Seed.argPL W WP p bk σ ℓ no)) (pullEK (fillIVKK W)
      (fillPrfK W) (extractorBK W)) (deltaSeed W WP p bk) (`prunedK`: Compile/Batch/StarO.lean;
      `Seed.argPL`: Compile/Batch/SeedLazyDefs.lean).

Hypotheses: `L.Wired` (decoding an encoding gives the index back), `W.OKG`. None on the seed oracle:
the coins need not be near uniform for this.

Limits: nothing on a committer that is not the honest one, beyond `extraction_of_first`. Nothing
over one hash function. The bound is loose by a constant, as in Compile/Batch/Extraction.lean.
-/
import Compile.Batch.Extraction
import Compile.Batch.SeedLazyDefs
import Compile.Batch.SeedCache
import Compile.Batch.StarO
import Compile.SeedRootCost
import ZKCP.GenOptional

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob MeasureTheory Compile.Extr Compile.Batch.Cmpl Compile.Batch.Extr Compile.GenLe
open scoped ENNReal

/-! ## Small tosses; coins from a seed -/

section Gen
variable {S : OSpec} {α : Type} {f : Fam S} {tr : Trace S}

theorem outsIn_tossN (w : ℕ) {b : α} :
    ∀ (m : ℕ) (F : (Fin m → Fin (w + 1)) → OComp S α),
      b ∈ OutsIn f tr (OComp.tossN w m F) → ∃ v, b ∈ OutsIn f tr (F v)
  | 0, _, h => ⟨_, h⟩
  | m + 1, F, h => by
    obtain ⟨r, hr⟩ := h
    obtain ⟨v, hv⟩ := outsIn_tossN w m (fun v => F (Fin.cons r v)) hr
    exact ⟨_, hv⟩

theorem outsIn_blocks (bk : CoinPlan) {b : α} :
    ∀ {c : OComp S α}, b ∈ OutsIn f tr (c.blocks bk) → b ∈ OutsIn f tr c
  | .pure _, h => h
  | .query _ _ _, h => ⟨h.1, outsIn_blocks bk h.2⟩
  | .sample n k, h => by
    obtain ⟨v, hv⟩ := outsIn_tossN bk.w (bk.m n) (fun v => (k (bk.φ n v)).blocks bk) h
    exact ⟨_, outsIn_blocks bk hv⟩

theorem outsIn_derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) {b : α} :
    ∀ {c : OComp S α} {j : ℕ}, b ∈ OutsIn f tr (c.derive σ s j) → b ∈ OutsIn f tr c
  | .pure _, _, h => h
  | .query _ _ _, _, h => ⟨h.1, outsIn_derive σ s h.2⟩
  | .sample _ _, _, h => ⟨_, outsIn_derive σ s h.2⟩

theorem exists_outsIn {b : α} : ∀ {c : OComp S α}, b ∈ Outs f c → ∃ tr, b ∈ OutsIn f tr c
  | .pure _, h => ⟨[], mem_outs_pure.1 h⟩
  | .query o q k, h => by
    obtain ⟨tr, ht⟩ := exists_outsIn (mem_outs_query.1 h)
    exact ⟨(⟨o, q, f o q⟩ : QA S) :: tr,
      List.mem_cons_self,
      OutsIn.mono (List.subset_cons_self _ _) ht⟩
  | .sample _ _, h => by
    obtain ⟨r, hr⟩ := mem_outs_sample.1 h
    obtain ⟨tr, ht⟩ := exists_outsIn hr
    exact ⟨tr, r, ht⟩

theorem outs_blocks (bk : CoinPlan) {b : α} {c : OComp S α} (h : b ∈ Outs f (c.blocks bk)) :
    b ∈ Outs f c := by
  obtain ⟨tr, ht⟩ := exists_outsIn h
  exact outs_of_outsIn (outsIn_blocks bk ht)

theorem outs_derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) {b : α} {c : OComp S α}
    {j : ℕ} (h : b ∈ Outs f (c.derive σ s j)) : b ∈ Outs f c := by
  obtain ⟨tr, ht⟩ := exists_outsIn h
  exact outs_of_outsIn (outsIn_derive σ s ht)

theorem queryBound_map {β : Type} (g : α → β) :
    ∀ {c : OComp S α} {t : ℕ}, c.QueryBound t → (c.bind fun a => .pure (g a)).QueryBound t
  | .pure _, _, _ => trivial
  | .query _ _ _, 0, h => h.elim
  | .query _ _ _, _ + 1, h => fun r => queryBound_map g (h r)
  | .sample _ _, _, h => fun r => queryBound_map g (h r)

end Gen

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem extEnc_eqG {W : QueryLayout lam L} {trW : Tc W} (hW : W.OKG) {cm : Dig lam} {y : Fin L.wordLength → L.Symbol}
    (h : ∀ q : Fin L.wordLength, ∃ s, extLeaf trW W.depth cm q.val = some ⟨some (.inl (y q)), s⟩) :
    extEnc W trW cm = y := by
  funext q
  obtain ⟨s, hs⟩ := h q
  exact hW.B.ext.build_rd _ q (y q) (by simp only [hs])

/-- Any committer that first builds the tree under the root in its key.
(not all hypotheses are named here: see the statement below) -/
theorem extraction_of_first (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hwd : L.Wired)
    (hW : W.OKG) (i : I) {β γ : Type} (X0 : TypedOracleComputation lam W.K L β) (nd : β → Node lam L × List Bits)
    (Rest : β → TypedOracleComputation lam W.K L γ) (cmOf : γ → Dig lam) (t : ℕ) (hX : X0.QueryBound t)
    (h1 : ∀ (f : Fam (spec lam W.K L)) (a : β × Tc W),
      a ∈ Outs f X0.withTrace → nd a.1 ∈ OutsIn f a.2 (erase (nodeP' W WP p i) []))
    (h2 : ∀ (f : Fam (spec lam W.K L)) (a : β),
      ∀ b ∈ Outs f (Rest a), cmOf b = (nd a).1.tree.root) :
    Rom.Pr (X0.bind Rest).withTrace (fun _ => {o | L.decodeIndex (extEnc W o.2 (cmOf o.1)) ≠ some i}) ≤
      2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine le_trans ?_ (hashEvents X0 t hX)
  rw [← Pr_eq_law]
  refine lintegral_mono fun f => ?_
  unfold PrCoins
  rw [withTrace_bind, OComp.runEager_bind]
  have key := pr_bind_le_add (X0.withTrace.runEager f)
    (fun a => ((Rest a.1).withTrace.bind fun b => OComp.pure (b.1, a.2 ++ b.2)).runEager f)
    {o : γ × Tc W | L.decodeIndex (extEnc W o.2 (cmOf o.1)) ≠ some i} {o | EM o.2 ∨ EF o.2}
    (ε := 0) fun a ha hn => ?_
  · rw [add_zero] at key
    exact key
  · refine le_of_eq (pr_eq_zero_of_forall_not_mem _ fun o ho hbad => hbad ?_)
    obtain ⟨b, hb, hob⟩ := mem_outs_bind.1 (show o ∈ Outs f _ from ho)
    obtain rfl := mem_outs_pure.1 hob
    have hEM : ¬ EM a.2 := fun h => hn (Or.inl h)
    obtain ⟨hok, hin⟩ := triI_nodeP' WP p i [] (nd a.1) (h1 f a (show a ∈ Outs f _ from ha))
    have hcm : cmOf b.1 = (nd a.1).1.tree.root :=
      h2 f a.1 b.1 (outs_of_outsIn (outsIn_of_withTrace hb))
    show L.decodeIndex (extEnc W (a.2 ++ b.2) (cmOf b.1)) = some i
    rw [hcm, extEnc_eqG (y := L.encodeIndex i (nd a.1).1.r) hW fun q => ?_, hwd.dec_enc]
    have h3 := extLeaf_of_tree hEM hok hin (j := q.val) (lt_of_lt_of_le q.isLt hW.fits)
    rw [Cmpl.encLeaf_val] at h3
    exact ⟨_, (pairM lam W.K L).preimage_mono (List.prefix_append _ _) h3⟩

/-! ## The committer with coins from a seed, Links, cache, pruning -/

variable (W : QueryLayout lam L)
  (WP : WireBP L) (p : Params) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

/-- the extraction error: a bound for a hash event among the queries for the tree under the root in
the key and for its coins -/
def deltaSeed : ℝ≥0∞ := 2 * ((2 * 2 ^ W.depth + Seed.cNode W WP p bk.m : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

namespace ExtrS

/-- the seed, and the first tree with coins from it -/
def X0 (i : I) : TypedOracleComputation lam W.K L (Fin (σ.sd + 1) × (Node lam L × List Bits)) :=
  .sample σ.sd fun s =>
    (((erase (nodeP' W WP p i) []).blocks bk).derive σ s 0).bind fun x => .pure (s, x)

/-- what the committer of argP does after it -/
def restP (i : I) (a : Fin (σ.sd + 1) × (Node lam L × List Bits)) :
    TypedOracleComputation lam W.K L (IVKK lam L × (I × Fin (σ.sd + 1))) :=
  (((((eraseR (restC W WP p i a.2.1) a.2.2).bind fun o => OComp.pure (o.1.1, (o.1.2, o.2))).bind
        fun o => .pure ((o.1, linksOf (keyOf o.2.1)), o.2)).blocks bk).derive
      σ a.1 (0 + Seed.cNode W WP p bk.m)).bind
    fun out => .pure (out.1, (i, a.1))

theorem tosses_first (i : I) :
    Compile.Seed.Tosses (Seed.cNode W WP p bk.m) ((erase (nodeP' W WP p i) []).blocks bk) :=
  ((Seed.sh_nodeP' W WP p bk.m i).wt []).tosses_blocks bk

theorem argP_C_eq (i : I) :
    (argP W WP p bk σ).C i = (X0 W WP p bk σ i).bind (restP W WP p bk σ i) := by
  rw [argP_C, Extr.C_eq, OComp.bind_assoc, OComp.blocks_bind]
  refine congrArg (Rom.OComp.sample σ.sd) (funext fun s => ?_)
  rw [Compile.Seed.derive_bind σ s (tosses_first W WP p bk i), OComp.bind_assoc, OComp.bind_assoc]
  rfl

theorem queryBound_X0 (i : I) :
    (X0 W WP p bk σ i).QueryBound (2 * 2 ^ W.depth + Seed.cNode W WP p bk.m) := fun s =>
  queryBound_map _
    (OComp.QueryBound.derive σ s (tosses_first W WP p bk i) _ 0
      (OComp.QueryBound.blocks bk _ _ ((sq_nodeP' W WP p i).erase [])))

theorem first_X0 (i : I) (f : Fam (spec lam W.K L))
    (a : (Fin (σ.sd + 1) × (Node lam L × List Bits)) × Tc W)
    (ha : a ∈ Outs f (X0 W WP p bk σ i).withTrace) :
    a.1.2 ∈ OutsIn f a.2 (erase (nodeP' W WP p i) []) := by
  obtain ⟨s, hs⟩ := outsIn_of_withTrace ha
  obtain ⟨x, hx, e⟩ := mem_outsIn_bind.1 hs
  have e' : a.1.2 = x := congrArg Prod.snd (show a.1 = (s, x) from e)
  rw [e']
  exact outsIn_blocks bk (outsIn_derive σ s hx)

theorem cm_restP (i : I) (f : Fam (spec lam W.K L)) (a : Fin (σ.sd + 1) × (Node lam L × List Bits))
    (b : IVKK lam L × (I × Fin (σ.sd + 1))) (hb : b ∈ Outs f (restP W WP p bk σ i a)) :
    b.1.1.cm = a.2.1.tree.root := by
  obtain ⟨out, ho, e⟩ := mem_outs_bind.1 hb
  rw [mem_outs_pure.1 e]
  obtain ⟨o, h1, e1⟩ := mem_outs_bind.1 (outs_blocks bk (outs_derive σ a.1 ho))
  rw [mem_outs_pure.1 e1]
  obtain ⟨z, hz, e2⟩ := mem_outs_bind.1 h1
  rw [mem_outs_pure.1 e2]
  exact Extr.tri_restC W WP p (realF f) i a.2.1 a.2.2 z (outs_realQ hz)

/-- all that the committer does after the first tree -/
def restAll (ℓ : ℕ) (i : I) (a : Fin (σ.sd + 1) × (Node lam L × List Bits)) :
    TypedOracleComputation lam W.K L (IVKKO lam L × ((I × Fin (σ.sd + 1)) × Seed.Ca lam)) :=
  ((restP W WP p bk σ i a).bind fun o =>
      (Seed.cacheOf W WP p bk σ ℓ o.2).bind fun c => OComp.pure (o.1, (o.2, c))).bind
    fun o => .pure (pruneIVKK W o.1, o.2)

theorem cm_restAll (ℓ : ℕ) (i : I) (f : Fam (spec lam W.K L))
    (a : Fin (σ.sd + 1) × (Node lam L × List Bits))
    (b : IVKKO lam L × ((I × Fin (σ.sd + 1)) × Seed.Ca lam))
    (hb : b ∈ Outs f (restAll W WP p bk σ ℓ i a)) : b.1.1.cm = a.2.1.tree.root := by
  obtain ⟨o, ho, e1⟩ := mem_outs_bind.1 hb
  rw [mem_outs_pure.1 e1]
  obtain ⟨o', ho', e2⟩ := mem_outs_bind.1 ho
  obtain ⟨c, _, e3⟩ := mem_outs_bind.1 e2
  rw [mem_outs_pure.1 e3]
  exact cm_restP W WP p bk σ i f a o' ho'

end ExtrS

open ExtrS in
/-- Under `L.Wired` and `W.OKG`, for the honest committer the extracted index is the committed one,
except with probability `deltaSeed`: the typed scheme with coins from a seed, the Links in the key,
a cache, pruned Merkle paths. -/
theorem extraction_prunedK (hwd : L.Wired) (hW : W.OKG) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b) :
    ZKCP.Gen.HasExtractionError (prunedK W p (Seed.argPL W WP p bk σ ℓ no))
      (pullEK (fillIVKK W) (fillPrfK W) (extractorBK W)) (deltaSeed W WP p bk) := by
  intro i
  have e : (prunedK W p (Seed.argPL W WP p bk σ ℓ no)).C i =
      (X0 W WP p bk σ i).bind (restAll W WP p bk σ ℓ i) := by
    show (((argP W WP p bk σ).C i).bind fun o =>
          (Seed.cacheOf W WP p bk σ ℓ o.2).bind fun c => OComp.pure (o.1, (o.2, c))).bind
        (fun o => .pure (pruneIVKK W o.1, o.2)) = _
    rw [argP_C_eq, OComp.bind_assoc, OComp.bind_assoc]
    refine congrArg _ (funext fun a => ?_)
    unfold restAll
    rw [OComp.bind_assoc]
  have key := extraction_of_first W WP p hwd hW i (X0 W WP p bk σ i) Prod.snd
    (restAll W WP p bk σ ℓ i)
    (fun o : IVKKO lam L × ((I × Fin (σ.sd + 1)) × Seed.Ca lam) => o.1.1.cm) _
    (queryBound_X0 W WP p bk σ i) (first_X0 W WP p bk σ i) (cm_restAll W WP p bk σ ℓ i)
  rw [← e] at key
  exact key

end Compile.Batch
