-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Good.lean: THE INVARIANT OF THE STEP FROM MODE I OF THE TOKEN CHALLENGER TO THE
PLAIN CHALLENGER THAT LAYS LATE, and the two statements of which that step is made. DEFINITIONS,
SMALL LEMMAS, TWO STATEMENTS.

General statements. This file states no goal of the release.
The definitions of this file are a device of one step of a proof of index privacy. They stand in no
statement on the scheme.

  ExtIn W      a position of an external string stands at a leaf that a table's tree has, for each
               of the three wires.
  FitAll       the premises on the letters, together: the token side's letters fit the honest side's
               (TokFit, Johnson/TokenSide2/Sess.lean); the nonces are read back (GhostOK,
               Johnson/GhostSide/TwinWhole.lean); the rules' letters (LensOK,
               Johnson/TokenRules/Spec.lean); ExtIn.
  HoldsW       the invariant of the rule of release (Holds, Johnson/TokenRel/Holds.lean) of a state
               and a list of trees, each with 2 ^ W.depth leaves.
  GoodW        THE INVARIANT: before the setup HoldsW of no tree; after it, of the key's trees.
  runGood_of   HoldsW gives what a compiled run on trees of the list asks (RunGood,
               Johnson/LateSide/Run.lean).
  HoldsW.sub, HoldsW.lt, keyIn_of_good   fewer trees; the tokens of the trees' salts are in the
               store.
  tabK_stable  a table that is read off the store stays when the store grows.
  Spec.setupLate, Spec.sessLate   the clauses setup | setupGood and sess | sessGood of LateStep
               (Johnson/LateSide/Spec.lean) at GoodW, under FitAll. Their proofs are in
               Johnson/LateSide/Setup.lean and Johnson/LateSide2/Sess.lean.
  lateStep_of  LateStep at GoodW from these two and Spec.lateDraws (Johnson/LateSide/Need.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateSide.Spec
import Johnson.LateSide.Units
import Johnson.TokenRel.Holds
import Johnson.TokenSide2.Sess
import Compile.DeferRun.Sim

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open OnBytes.HopSide OnBytes.LateWorld OnBytes.TokenRel
open _root_.Compile.GlueB (GCall GIn GAdm ownPf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- A position of an external string stands at a leaf that a table's tree has. -/
structure ExtIn (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) : Prop where
  T : ∀ p, (wTC W).ext.leaf p < 2 ^ W.depth
  Lk : ∀ p, (wLC W).ext.leaf p < 2 ^ W.depth
  B : ∀ p, (wBC W).ext.leaf p < 2 ^ W.depth

/-- The premises on the letters. -/
structure FitAll (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
    (bl bf : ℕ) : Prop where
  tok : TokFit W h tl
  ghost : GhostOK W S h.capT h.capL h.capB
  lens : LensOK bl bf tl
  ext : ExtIn W

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The invariant of the rule of release, of a state and trees with 2 ^ W.depth leaves each. -/
def HoldsW (preE : Bits) (bl bf : ℕ) (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))) : Prop :=
  Holds (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) preE D Ts ∧
    ∀ T ∈ Ts, T.tok.length = 2 ^ W.depth

/-- **The invariant.** -/
def GoodW (preE : Bits) (bl bf : ℕ) :
    Option (IskT lam L Bd aT aL) → DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) → Prop
  | none, D => HoldsW W S preE bl bf D []
  | some k, D => HoldsW W S preE bl bf D (k.copies.map fun t => t.tree)

variable {W S}

theorem HoldsW.sub {preE : Bits} {bl bf : ℕ} {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    {Ts Ts' : List (TreeT lam (typedOracleCarrier L Bd aT aL))} (h : HoldsW W S preE bl bf D Ts)
    (hs : ∀ T ∈ Ts', T ∈ Ts) : HoldsW W S preE bl bf D Ts' :=
  ⟨⟨h.1.1, h.1.2.1, fun T hT => h.1.2.2 T (hs T hT)⟩, fun T hT => h.2 T (hs T hT)⟩

/-- the tokens of the salts of a tree of the list are in the store -/
theorem HoldsW.lt {preE : Bits} {bl bf : ℕ} {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    {Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))} (h : HoldsW W S preE bl bf D Ts)
    {T : TreeT lam (typedOracleCarrier L Bd aT aL)} (hT : T ∈ Ts) : ∀ a ∈ T.tok, a.1 < D.vals.length :=
  fun a ha => ((h.1.2.2 T hT).1 a ha).1

/-- What a compiled run on trees of the list asks of the state. -/
theorem runGood_of {preE : Bits} {bl bf : ℕ} {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    {Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))} (h : HoldsW W S preE bl bf D Ts) {Y : Type}
    {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
    (xt : ℕ → TreeT lam (typedOracleCarrier L Bd aT aL)) (ln : RunLen lam (typedOracleCarrier L Bd aT aL))
    (hx : ∀ k, xt k ∈ Ts) (he : ∀ p, wq.ext.leaf p < 2 ^ W.depth) (h1 : bl ≤ ln.fr)
    (h2 : bf ≤ ln.sFS) (h3 : bf ≤ lam) : RunGood W Q wq xt preE ln bl bf (seedPts W S) D :=
  ⟨h1, h2, h3, fun p => by rw [h.2 _ (hx _)]; exact he p, h.1.1, h.1.2.1,
    fun k => (h.1.2.2 _ (hx k)).1, fun k => (h.1.2.2 _ (hx k)).2⟩

/-- A table that is read off the store stays when the store grows. -/
theorem tabK_stable {vs vs' : List Bits} (hp : vs <+: vs') (pre : Bits) (t : TabT lam L Bd aT aL)
    (ht : ∀ a ∈ t.tree.tok, a.1 < vs.length) :
    t.toK (fun u => vs'.getD u []) pre = t.toK (fun u => vs.getD u []) pre := by
  show (⟨t.r, t.tree.toK (fun u => vs'.getD u []) pre, t.seed⟩ : TabK lam L Bd aT aL) =
    ⟨t.r, t.tree.toK (fun u => vs.getD u []) pre, t.seed⟩
  rw [toK_prefix hp pre t.tree ht]

theorem keyIn_of_good {preE : Bits} {bl bf : ℕ} {k : IskT lam L Bd aT aL}
    {D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (h : GoodW W S preE bl bf (some k) D) :
    KeyIn k D.vals :=
  fun t ht => HoldsW.lt h (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-! ## What is left -/

/-- The clauses setup and setupGood of LateStep, at GoodW. -/
def Spec.setupLate : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (h : HonestSide lam L Bd aT aL)
      (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) (bl bf : ℕ) (i : I)
      (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))),
    FitAll W S h tl bl bf → GoodW W S tl.preE bl bf none D →
    DeferRun.SimAt (fun D' => Table.via (ghost W) D'.table) (commitT W S cA h tl i) D
      (fun o D' => (o.1, iskOf tl.preE o.2 D'.vals))
      (fun o D' => GoodW W S tl.preE bl bf (some o.2) D')
      (commitInward W S cA h i (Table.via (ghost W) D.table))

/-- The clauses sess and sessGood of LateStep, at GoodW. -/
def Spec.sessLate : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
      (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) (bl bf : ℕ)
      (k : IskT lam L Bd aT aL) (x : X) (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))),
    FitAll W S h tl bl bf → GoodW W S tl.preE bl bf (some k) D →
    DeferRun.SimAt (fun D' => Table.via (ghost W) D'.table)
      (proveWT W cA r₀ h tl k [(x, (), true)]) D
      (fun πs _ => ownPf [(x, (), true)] πs)
      (fun _ D' => GoodW W S tl.preE bl bf (some k) D' ∧ D.vals <+: D'.vals)
      (lateBatch W cA r₀ h (iskOf tl.preE k D.vals) (Table.via (ghost W) D.table) [(x, (), true)])

/-- **LateStep at GoodW** from the two statements and "lateCommit is commitInward". -/
theorem lateStep_of (hS : Spec.setupLate) (hP : Spec.sessLate) (hN : Spec.lateDraws)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) (bl bf : ℕ) (i : I)
    (hF : FitAll W S h tl bl bf) : LateStep W S cA r₀ h tl i (GoodW W S tl.preE bl bf) where
  init := ⟨holdsStart _ _ _ _ _ _ _, fun _ hT => absurd hT List.not_mem_nil⟩
  ask := fun s D o q r hg hn => by
    cases s with
    | none => exact ⟨holdsAsk _ _ _ _ _ _ _ D _ o q r hg.1 hn, hg.2⟩
    | some k => exact ⟨holdsAsk _ _ _ _ _ _ _ D _ o q r hg.1 hn, hg.2⟩
  setup := fun D hg => by
    rw [hN W S cA h i]
    exact (hS I X lam L Bd aT aL W S cA h tl bl bf i D hF hg).law
  setupGood := fun D hg => (hS I X lam L Bd aT aL W S cA h tl bl bf i D hF hg).post
  sess := fun k D x hg => (hP I X lam L Bd aT aL W S cA r₀ h tl bl bf k x D hF hg).law
  sessGood := fun k D x hg y hy =>
    have hy' := (hP I X lam L Bd aT aL W S cA r₀ h tl bl bf k x D hF hg).post y hy
    ⟨hy'.1, iskOf_prefix (keyIn_of_good hg) hy'.2 tl.preE⟩

end OnBytes.LateSide

#print axioms OnBytes.LateSide.lateStep_of
