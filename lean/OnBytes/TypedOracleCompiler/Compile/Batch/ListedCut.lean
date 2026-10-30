-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedCut.lean: the verifier along lists
(OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean, verifyBSL) run on the argument string CUT TO THE
LISTS: every opening of the string that stands at no listed leaf and at no listed position is struck
before anything reads the string. Definitions; all have code.

No soundness: a test. This module states nothing on soundness.

Why. verifyBSL takes, beside the argument string π, two lists own and listed that say where
openings of π can stand. Its strict format looks at the listed places alone; its forests, the
transcript that it builds (mkTr) and the external strings that it builds (build) read π wherever the
protocol reads. So at lists that leave out a place with an opening it is another function of π than
the compiled verifier verifyOneProtocol (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean), and its equation with
verifyOneProtocol has two premises on whoever made the lists. Here the lists are taken as part of the
string: what they do not name is not there.

Main names.
  keptR w own p: is the leaf of the position p, by the round's annotation and wiring (its component
    a.own p, its tree w.tree p, its leaf w.place p), in that tree's list?
  cutS s A W own f: the openings f of the prover's oracles, none where keptR says no.
  OneProtocolProof.cutTo π sh wl own listed: π with its field opens cut so, and its field ext none outside
    listed. The seven other fields are π's.
  verifyBSC: verifyBSL at π.cutTo sh wl own listed and the same two lists.

Limits. Definitions alone: that verifyBSC is verifyOneProtocol at the cut string is
OnBytes/TypedOracleCompiler/Compile/Batch/ListedCutLaws.lean's. The cut goes by the wiring's maps from a position to
its tree and leaf (tree, place); the lists' walks go by the maps from a leaf to its position
(posAt0, posAtJ): that the two agree is a law of the wiring, which is a premise there. A listed leaf
is searched in its tree's list from the front, and a listed position in listed. mkRd and mkRdE stay
the caller's: what OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean says of them holds of verifyBSC
too. Nothing on time or
memory is a theorem. Nothing on soundness. The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedVerifier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- Is the leaf of the position p listed? own: the lists of leaves of the trees of the round's
shared component, and of the slot's. -/
def keptR {r : Round} {a : RAnn r} (w : WireRB lam K r a) (own : List (List ℕ) × List (List ℕ))
    (p : r.Pos) : Bool :=
  cond (a.own p) ((own.2.getD (w.tree p) []).contains (w.place p))
    ((own.1.getD (w.tree p) []).contains (w.place p))

/-- The openings f, none where the position's leaf is not listed. -/
def cutS : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Leaves →
    ((p : OPos s) → Option (Opening lam (OSym s p))) →
    (p : OPos s) → Option (Opening lam (OSym s p))
  | [], _, _, _, f, p => f p
  | _ :: _, (_, _), (w, _), own, f, .inl p =>
      if keptR w (own.headD ([], [])) p then f (.inl p) else none
  | _ :: s, (_, A), (_, W), own, f, .inr p => cutS s A W own.tail (fun q => f (.inr q)) p

/-- **The argument string cut to the lists.** -/
def OneProtocolProof.cutTo {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (π : OneProtocolProof lam Q)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (own : Leaves)
    (listed : List E.Pos) : OneProtocolProof lam Q :=
  haveI := wl.dec
  ⟨π.salt, π.roots, π.plains, cutS Q.loc.shape Q.ann sh own π.opens,
    fun p => if listed.contains p then π.ext p else none, π.rtreq, π.slot, π.path, π.rsalt⟩

/-- **The verifier along the lists, on the string cut to the lists.** -/
def verifyBSC (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (own : Leaves) (listed : List E.Pos)
    (mkRd : Y → Rho Q.loc.shape → Plains Q.loc.shape → Leaves)
    (mkRdE : Y → Rho Q.loc.shape → List E.Pos) : TypedOracleComputation lam K L Bool :=
  verifyBSL sMT sFS t Q sh wl nOpen maxDepth embS embP xin embE depthReq cms x
    (π.cutTo sh wl own listed) own listed mkRd mkRdE

end TypedOracleCompiler.Compile.Batch
