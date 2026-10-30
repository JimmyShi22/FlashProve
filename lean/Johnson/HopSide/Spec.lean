-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HopSide/Spec.lean: FROM THE REAL EXPERIMENT OF THE SCHEME WITH THE WHOLE KEY PUBLISHED
(argW, Johnson/WholeKey/Defs.lean) TO MODE I OF THE TOKEN CHALLENGER (challT,
Johnson/TokenSide/Whole.lean). DEFINITIONS AND TWO STATEMENTS; the proofs are in
Johnson/HopSide/Proof.lean.

General statements. This file states no goal of the release.
The definitions of this file are a device of one step of a proof of index privacy. They stand in no
statement on the scheme.

The first hop of a proof of index privacy. In mode I (Rom/Defer.lean) the honest side's marked
evaluations get fresh answers that do not look at the oracle's table. The token programs write the
later tries of a search under further names; the adversary's queries are exchanged accordingly
(ghost W, Johnson/GhostSide/Defs.lean; World.pre, Rom/SpecVia.lean).

  iskOf pre k vs   the prover's key as the scheme keeps it, read off the key with tokens k and the
                   store vs of all strings.
  KeyIn k vs       the tokens of the salts in k's trees are numbers of strings of vs.
  SameStep … cut   WHAT IS ASKED OF THE TOKEN PROGRAMS: as ordinary oracle algorithms (plainOf,
                   Johnson/TokenSide/Erased.lean) the committer and the prover of one shown request
                   have the runs of the scheme's committer and prover, under every rule for
                   answering queries (Rom/Handle/Defs.lean).
                     setup    the committer: the key, and the prover's key read off by iskOf.
                     keyIn    the tokens of the key that it keeps are in its store.
                     sess     the prover of one request that is shown.
                     cutFree  see cut.
                   cut: a map on the scheme's prover's keys that the scheme's prover does not
                   notice. A kept tree holds a salt for every natural number, and no law speaks of
                   those beyond the tree; cut is there to set them to what iskOf gives. Where the
                   scheme keeps none, cut is the identity.
  Spec.realTwin    an admissible adversary has the same output in the real experiment and against
                   mode R of the challenger, its queries exchanged.
  Spec.hopTwin     the real experiment is within Rom.costTotal, at the written counts of one setup
                   and n sessions, of mode I of the challenger, the adversary's queries exchanged.

A batch of one request that is NOT the adversary's own: the real prover runs a session there and
shows nothing; the token challenger runs none. SameStep speaks of the shown request alone; the
unseen session is dropped on the real side, exactly, before mode R (cut_drop,
Johnson/HopSide/Proof.lean).
The counts of Spec.hopTwin are the token side's own. The statement of index privacy is reached at
the counts of its written error, by the general lemma under hopTwin (hop_prem,
Johnson/LateSide/Whole.lean); Spec.realTwin and Spec.hopTwin themselves are called by nothing there.
The price in Spec.hopTwin is a formula (Rom.costTotal, Rom/SpecHopCost.lean); no number is
evaluated.

SameStep CAN BE MET: it is the statement that the token programs are laid on the scheme's terms, and
it is proved at all letters that fit, with cut the identity (sameStepT,
Johnson/TokenSide2/Closed.lean). Beside the proofs of this folder there is one small member of its
clause sess: at a key without copies (sess_noCopies, Johnson/HopSide/Proof.lean).
Sources. The form of Spec.realTwin follows real_eq_modeRPG (Compile/Batch/PubProgReal.lean): the
real experiment and mode R of a token challenger give an admissible adversary the same output.
Spec.hopTwin states its bound in the form of Rom.hopCost_total (Rom/HopCost.lean), which its proof
reaches through real_to_modeI (Compile/DeferRun/Hop.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Erased
import Johnson.TokenRules.Spec
import Johnson.GhostSide.TwinWhole
import Rom.SpecHopCost

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.HopSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.TokenRules
open _root_.Compile.GlueB (GCall GIn GAdm realW)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The prover's key as the scheme keeps it, read off the key with tokens and the store. -/
def iskOf (pre : Bits) (k : IskT lam L Bd aT aL) (vs : List Bits) : Isk lam L Bd aT aL :=
  ⟨k.i, k.copies.map (TabT.toK (fun t => vs.getD t []) pre)⟩

/-- The tokens of the salts in the key's trees are numbers of strings of the store. -/
def KeyIn (k : IskT lam L Bd aT aL) (vs : List Bits) : Prop :=
  ∀ t ∈ k.copies, ∀ a ∈ t.tree.tok, a.1 < vs.length

/-- **What is asked of the token programs**: see the head. -/
structure SameStep (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
    (cut : Isk lam L Bd aT aL → Isk lam L Bd aT aL) : Prop where
  setup : ∀ (i : I) (σ : Type) (hd : Handler (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) σ) (s : σ),
    ((plainOf (commitT W S cA h tl i) []).interp hd s).map
        (fun y => ((y.1.1.1, iskOf tl.preE y.1.1.2 y.1.2), y.2)) =
      ((commitW W S cA h i).interp hd s).map fun y => ((y.1.1, cut y.1.2), y.2)
  keyIn : ∀ i : I, Post (fun y : (FullKey lam L aT aL × IskT lam L Bd aT aL) × List Bits =>
    KeyIn y.1.2 y.2) (plainOf (commitT W S cA h tl i) [])
  sess : ∀ (k : IskT lam L Bd aT aL) (vs : List Bits), KeyIn k vs → ∀ (x : X) (σ : Type)
      (hd : Handler (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) σ) (s : σ),
    ((plainOf (proveWT W cA r₀ h tl k [(x, (), true)]) vs).interp hd s).map
        (fun y => (y.1.1, y.2)) =
      ((proveW W cA r₀ h (iskOf tl.preE k vs) [(x, ())]).interp hd s).map fun y => (y.1.val, y.2)
  cutFree : ∀ (k : Isk lam L Bd aT aL) (b : List (X × Unit)),
    proveW W cA r₀ h (cut k) b = proveW W cA r₀ h k b

/-- **The real experiment is mode R of the token challenger**, the adversary's queries exchanged. -/
def Spec.realTwin : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)
      (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (cut : Isk lam L Bd aT aL → Isk lam L Bd aT aL) (i : I) (α : Type)
      (ok : ZKCP.Gen.Batch X Unit → Prop)
      (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
        (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ),
    SameStep W S cA r₀ h tl cut → GhostOK W S h.capT h.capL h.capB → GAdm ok A false n →
    (interact (realW (argW W S cA r₀ p h) i) A (none, Table.empty _)).map Prod.fst =
      (interact (((challT W S cA r₀ h tl i).world false).pre (ghost W)) A
        (none, DSt.init _)).map Prod.fst

/-- **The hop**: the real experiment against mode I of the token challenger. -/
def Spec.hopTwin : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)
      (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (cut : Isk lam L Bd aT aL → Isk lam L Bd aT aL) (bl bf : ℕ) (i : I) (α : Type)
      (ok : ZKCP.Gen.Batch X Unit → Prop)
      (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
        (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (t n : ℕ),
    SameStep W S cA r₀ h tl cut → GhostOK W S h.capT h.capL h.capB → LensOK bl bf tl →
    A.TotalBound t (n + 1) → GAdm ok A false n →
    tv ((interact (realW (argW W S cA r₀ p h) i) A (none, Table.empty _)).map Prod.fst)
        ((interact (((challT W S cA r₀ h tl i).world true).pre (ghost W)) A
          (none, DSt.init _)).map Prod.fst) ≤
      costTotal (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (eAllT W S h n) (mAllT W h tl n)
        (bitsOfT lam bl bf) (osAllT h) t

end OnBytes.HopSide
