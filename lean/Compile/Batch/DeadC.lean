-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadC.lean: if σ.o = other, and given two facts on the compiled prover `proveB`
(`BoxT`, `BoxL` below), the committer of `argP` depends on its oracle answers only up to `agF W`
(Compile/Batch/SpecOneCall.lean: it relates two answers that are both failed proof-of-work attempts,
and not the last) (words of this library: lean/GLOSSARY.md).

The committer is written as a token program (`Step`, Rom/Defer.lean); the scheme's committer is made
from what `erase` (Compile/Star.lean) makes of it (`C_argP_eq` below): a token is then an index into
a list of strings, the store. A piece of the program holds tokens in its arguments and returns
tokens in its value; those that it, or a later piece, will use are the live ones
(Compile/LiveWalk.lean); a dead token is one of the set D of Compile/SpecEraseDead.lean.

What is shown of each piece c of the committer's program (`nodeP'`, `proveT`, `proveLk`, `leavesC`,
`Cp`; Compile/Batch/Star.lean) is `Compile.LiveW ag T TP c` (Compile/LiveWalk.lean). It says: c
never uses the string of a dead token; and, started on a store that holds all tokens taken as live,
after two answers related by ag (two failed attempts that are not the last) c goes on in the same
way (limits on `LiveW`: the header of Compile/LiveWalk.lean).

  `liveNd`, `liveLs`  The live tokens of a node (those of its tree over the encoded index) and of a
                      list of copies.
  `lw_nodeP'`, `lw_proveT`, `lw_proveLk`, `lw_leavesC`, `lw_Cp`  For every relation ag that relates
                                                                 nothing but at the Fiat-Shamir
                                                                 oracles `fb t` and their ghost
                                                                 names `fbw t j` (`OnlyFb`); all but
                                                                 `lw_nodeP'` under `BoxT`, `BoxL`
                                                                 below. (not all hypotheses are
                                                                 named here: see their statements)
  `C_argP_eq`  The committer of `argP` (Compile/Batch/StarS.lean) is the erased program of `Cp`,
               followed by a function that forgets the store; then `realQ`, `blocks`, and `derive`
               from the seed.
  `facF_C_argP`  ∀ i, ((argP W WP p bk σ).C i).FactorsBy (agF W), from σ.o = other, hT and hL.
  `BoxT`, `BoxL`  The hypotheses hT and hL: one execution of `proveB`, for Test on the root's tree
                  and for Link on the root's and a copy's tree, is a `LiveW` with no live token in
                  its value, if the live tokens of these trees are among the live ones.
                  Compile/Batch/DeadCBox.lean proves them for every ag with `OnlyFb` and `FitsSh`.

Why `argP` and not `argB`: the committer C of Compile/Batch/Star.lean returns its whole store in the
proving key, the tails of failed attempts too: after two failed attempts with different tails it
returns different values, so it does not depend on its answers only up to `agF W`. The proving key
of `argP` is (i, seed): the store is dropped.

Limits: nothing on P or V; nothing on numbers of queries.
-/
import Compile.Batch.DeadO
import Compile.Batch.StarS
import Compile.SeedRoot
import Rom.OverOneNDerive

noncomputable section

namespace Compile.Batch.Dead
open Iop Rom Compile

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the live tokens of a node: those of its tree -/
def liveNd (nd : Node lam L) (u : Tok) : Prop := liveTH nd.tree u

/-- the live tokens of a list of copies -/
def liveLs (ls : List (LeafRec lam L)) (u : Tok) : Prop := ∃ lf ∈ ls, liveNd lf.node u

/-- the hypothesis on proveB for Test -/
def BoxT (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop) : Prop :=
  ∀ (T : Tok → Prop) (tree : TreeH lam) (i : I) (r : L.EncodingRandomness), (∀ u, liveTH tree u → T u) →
    LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T (fun _ _ => False)
      (proveB p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T
        (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [tree] (i, r)
        (fun _ => true) [some ()])

/-- the hypothesis on proveB for Link -/
def BoxL (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop) : Prop :=
  ∀ (T : Tok → Prop) (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness), (∀ u, liveTH root u → T u) →
    (∀ u, liveTH tree u → T u) →
    LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T (fun _ _ => False)
      (proveB p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
        (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [root, tree]
        (i, r₀, r) (fun _ => true) [some ()])

/-- a fresh encoding and its salted tree -/
theorem lw_nodeP' (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop} (hag : OnlyFb ag)
    {T : Tok → Prop} (i : I) :
    LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T liveNd (nodeP' W WP p i) :=
  (lw_drawT WP.ri).bind fun _ =>
    (lw_commitE hag p.sMT W.depth _).bind fun _ => .pure fun _ hu => .inr hu

/-- Test's compiled prover on the root -/
theorem lw_proveT (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop} (hT : BoxT W WP p ag)
    {T : Tok → Prop} (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) (h : ∀ u, liveTH tree u → T u) :
    LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T
      (fun _ _ => False) (proveT W WP p tree i r) :=
  (hT T tree i r h).bind fun _ => .pure fun _ hu => hu.elim

/-- Link's compiled prover from the root to a copy -/
theorem lw_proveLk (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop} (hL : BoxL W WP p ag)
    {T : Tok → Prop} (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness)
    (h₀ : ∀ u, liveTH root u → T u) (h : ∀ u, liveTH tree u → T u) :
    LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T
      (fun _ _ => False) (proveLk W WP p root tree i r₀ r) :=
  (hL T root tree i r₀ r h₀ h).bind fun _ => .pure fun _ hu => hu.elim

/-- the copies, each with its Link -/
theorem lw_leavesC (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop} (hag : OnlyFb ag)
    (hL : BoxL W WP p ag) (i : I) (root : Node lam L) :
    ∀ (n : ℕ) (T : Tok → Prop), (∀ u, liveNd root u → T u) →
      LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T liveLs (leavesC W WP p i root n)
  | 0, _, _ => .pure fun _ hu => by obtain ⟨_, h, _⟩ := hu; exact nomatch h
  | n + 1, T, h => (lw_nodeP' W WP p hag i).bind fun nd =>
      (lw_proveLk W WP p hL root.tree nd.tree i root.r nd.r
          (fun u hu => .inl (h u hu)) fun u hu => .inr hu).bind fun π =>
      (lw_leavesC W WP p hag hL i root n _ fun u hu => .inl (.inl (h u hu))).bind
          fun rest => .pure fun u hu => by
        obtain ⟨lf, hm, hu⟩ := hu
        rcases List.mem_cons.1 hm with e | e
        · subst e
          exact .inl (.inl (.inr hu))
        · exact .inr ⟨lf, e, hu⟩

/-- The committer's program with tokens. It starts with no token at all. -/
theorem lw_Cp (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop} (hag : OnlyFb ag)
    (hT : BoxT W WP p ag) (hL : BoxL W WP p ag) {T : Tok → Prop} (i : I) :
    LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T
      (fun o u => liveNd o.2.root u ∨ liveLs o.2.leaves u) (Cp W WP p i) :=
  (lw_nodeP' W WP p hag i).bind fun root =>
  (lw_proveT W WP p hT root.tree i root.r fun _ hu => .inr hu).bind fun _ =>
  (lw_leavesC W WP p hag hL i root (p.M + 1) _ fun _ hu => .inl (.inr hu)).bind fun _ =>
    .pure fun _ hu => hu.elim (fun h => .inl (.inl (.inr h))) .inr

/-- The committer of argP, with its last step moved inside. -/
theorem C_argP_eq (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (i : I) :
    (argP W WP p bk σ).C i =
      .sample σ.sd fun s =>
        ((realQ ((erase (Cp W WP p i) []).bind fun o =>
                .pure ((o.1.1, linksOf (keyOf o.1.2)), (i, s)))).blocks bk).derive
            σ s 0 := by
  rw [argP_C]
  refine congrArg (OComp.sample σ.sd) (funext fun s => ?_)
  rw [← OComp.derive_bind_pure]
  refine congrArg (fun c => OComp.derive σ s c 0) ?_
  have hb : ∀ c : TypedOracleComputation lam W.K L ((IVKK lam L) × ISK lam L),
      (c.blocks bk).bind (fun out => (.pure (out.1, (i, s)) : TypedOracleComputation lam W.K L _)) =
        (c.bind fun out => .pure (out.1, (i, s))).blocks bk := fun c => by
    rw [OComp.blocks_bind]
    rfl
  rw [hb]
  refine congrArg (OComp.blocks bk) ?_
  unfold C Ctok
  rw [OComp.bind_assoc, realQ_bind, realQ_bind, OComp.bind_assoc]
  rfl

/-- If σ.o = other, under `BoxT`, `BoxL`: the committer of argP has `FactorsBy (agF W)`. -/
theorem facF_C_argP (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other) (hT : BoxT W WP p (agF W))
    (hL : BoxL W WP p (agF W)) (i : I) :
    ((argP W WP p bk σ).C i).FactorsBy (agF W) := by
  rw [C_argP_eq]
  exact fun s =>
    ((facF_realQ W _
        ((lw_Cp W WP p (onlyFb_agF W) hT hL (T := fun _ => False) i).erase [] (fun _ h => h.elim)
          (fun a => .pure ((a.1, linksOf (keyOf a.2)), (i, s))) fun _ => trivial)).blocks bk).derive
      σ s (agF_seed W σ hσ) 0

end Compile.Batch.Dead
