-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateSide/Spec.lean: MODE I OF THE TOKEN CHALLENGER (challT, Johnson/TokenSide/Whole.lean) IS
THE PLAIN CHALLENGER THAT LAYS LATE (lateW, Johnson/LateWorld/Defs.lean). A DEFINITION AND A
STATEMENT; the proof is in Johnson/LateSide/Assembly.lean.

General statements. This file states no goal of the release.
The definitions of this file are a device of one step of a proof of index privacy. They stand in no
statement on the scheme.

In mode I (Rom/Defer.lean) the token challenger's marked evaluations get fresh answers, and a reveal
writes the released ones into the table where it has no entry. lateW says the same without tokens,
on the scheme's own terms. The token programs write the later tries of a search under further names,
so the adversary's queries, and the table, are exchanged (ghost W, Johnson/GhostSide/Defs.lean).

  stateOf pre x    the plain challenger's state, read off the token challenger's: the scheme's key
                   off the key with tokens and the store (iskOf, Johnson/HopSide/Spec.lean); the
                   table, exchanged.
  LateStep … Good  WHAT IS ASKED, STEP BY STEP. Good s D: an invariant of (the challenger's own
                   state, the state of the experiment), a letter.
                     init       it holds at the start;
                     ask        a new entry of the table keeps it;
                     setup      the committer in mode I, its key read off and its table exchanged,
                                has the law of lateCommit;  setupGood: and ends in Good;
                     sess       the prover of one shown request in mode I, of its proofs the
                                adversary's own, has the law of lateBatch;
                     sessGood   and ends in Good, and the key that is read off stays.
  Spec.lateTwin    under LateStep, an admissible adversary has the same output against mode I of the
                   token challenger, its queries exchanged, and against lateW.

LateStep CAN BE MET: its clauses setup and sess are the content of this step of the proof, and they
are proved at an invariant that is written out, under premises on the letters (lateStep_of,
Johnson/LateSide/Good.lean, with Johnson/LateSide/Setup.lean, Johnson/LateSide2/Sess.lean and
Johnson/TokenSide2/LateDraws.lean).
The two challengers part at a second setup: lateW runs its committer again, the token challenger
replies with an empty list. An admissible adversary asks for one setup, so the statement does not
meet that case.
Sources. Spec.lateTwin has the form of hopLateBP (Compile/Batch/PubLate.lean): mode I of a token
challenger and a challenger that lays late give an adversary the same output.
Terms: lean/GLOSSARY.md.

-/
import Johnson.HopSide.Spec
import Johnson.LateWorld.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.GhostSide OnBytes.HopSide
open OnBytes.LateWorld
open _root_.Compile.GlueB (GCall GIn GAdm ownPf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The plain challenger's state, read off the token challenger's. -/
def stateOf (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (pre : Bits)
    (x : Option (IskT lam L Bd aT aL) × DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    Option (Isk lam L Bd aT aL) × Tb W :=
  (x.1.map fun k => iskOf pre k x.2.vals, Table.via (ghost W) x.2.table)

/-- **What is asked, step by step**: see the head. -/
structure LateStep (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
    (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) (i : I)
    (Good : Option (IskT lam L Bd aT aL) → DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) → Prop) :
    Prop where
  init : Good none (DSt.init _)
  ask : ∀ s D o q r, Good s D → D.table o q = none →
    Good s { D with table := D.table.set o q r }
  setup : ∀ D, Good none D →
    ((commitT W S cA h tl i).run true D).map
        (fun y => ((y.1.1, iskOf tl.preE y.1.2 y.2.vals), Table.via (ghost W) y.2.table)) =
      lateCommit W S cA h i (Table.via (ghost W) D.table)
  setupGood : ∀ D, Good none D →
    ∀ y ∈ ((commitT W S cA h tl i).run true D).support, Good (some y.1.2) y.2
  sess : ∀ k D (x : X), Good (some k) D →
    ((proveWT W cA r₀ h tl k [(x, (), true)]).run true D).map
        (fun y => (ownPf [(x, (), true)] y.1, Table.via (ghost W) y.2.table)) =
      lateBatch W cA r₀ h (iskOf tl.preE k D.vals) (Table.via (ghost W) D.table) [(x, (), true)]
  sessGood : ∀ k D (x : X), Good (some k) D →
    ∀ y ∈ ((proveWT W cA r₀ h tl k [(x, (), true)]).run true D).support,
      Good (some k) y.2 ∧ iskOf tl.preE k y.2.vals = iskOf tl.preE k D.vals

/-- **Mode I of the token challenger is the plain challenger that lays late.** -/
def Spec.lateTwin : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
      (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) (i : I)
      (Good : Option (IskT lam L Bd aT aL) → DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) → Prop)
      (α : Type) (ok : ZKCP.Gen.Batch X Unit → Prop)
      (A : Adv (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (GCall X Unit)
        (GIn (FullKey lam L aT aL) (RequestProof lam L)) α) (n : ℕ),
    LateStep W S cA r₀ h tl i Good → GAdm ok A false n →
    (interact (((challT W S cA r₀ h tl i).world true).pre (ghost W)) A
        (none, DSt.init _)).map Prod.fst =
      (interact (lateW W S cA r₀ h i) A (none, Table.empty _)).map Prod.fst

end OnBytes.LateSide
