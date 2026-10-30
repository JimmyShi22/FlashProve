-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Chunks.lean: THE END OF A COMPILED RUN AS A TOKEN PROGRAM, WITH THE TOKENS SHOWN
IN SEVERAL REVEALS, IN A CHOSEN ORDER. DEFINITIONS ALONE.

General definitions. This file states no goal of the release. The programs are a device of one step
of a proof of index privacy (the head of Johnson/TokenSide/Split.lean) and stand in no statement.

Why. In the mode in which marked evaluations are deferred (mode I of Rom/Defer.lean) a reveal writes
the answers of the evaluations that it releases into the table, where the table has no entry, IN THE
ORDER IN WHICH THEY WERE MADE. Two evaluations at one point have two fresh answers, so the order in
which they are written decides what the table holds. The plain rule that this is to be compared with
(handOut, Johnson/WholeKey/Sim.lean) writes in an order of its own: all entries of the run's log
that are no leaves; the opened leaves of the run's own trees, by place; the opened leaves of the
external strings' trees, position by position. Within one reveal the order is fixed; from reveal to
reveal it is the program's to choose. So the program here shows its tokens in that order, chunk by
chunk:
  1. the first salt and the chain's tokens (all evaluations of the run but its leaves are charged to
     these);
  2. for each leaf of the run's own trees that stands at a position which is read, the leaf's two
     tokens: round by round, the slot's trees, then the shared ones, tree by tree, by rising number
     of the leaf (shownK, laid term by term on laidK);
  3. for each position that is read in the external strings, the two tokens of its leaf (shownExt,
     laid on extLaid).
The values that these reveals return are dropped. Then ONE reveal of all these tokens together reads
the values for the proof string; it releases nothing, since all is shown by then.

In mode R, and in the erasure of the program, a reveal is a read: there the chunks change nothing.

Main names (namespace OnBytes.TokenSide).
  shownTree, shownTrees, shownK, shownExt   the chunks of the leaves.
  chunksT, revealsT   all chunks; the reveals in turn.
  showC, finishC, endC, proveC   all tokens that are shown; the reveals with the string; the end of
    a run; the compiled prover of one slot.

The scheme's token programs (linkT, commitAtT, proveAtT, Johnson/TokenSide/Whole.lean) call proveC.

Limits. Definitions alone. That these programs keep the rules of deferred programming is shown in
Johnson/TokenRules/EndC.lean; what they write into the table in mode I, in
Johnson/TokenRel/Release.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Finish

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- For each leaf of one kept tree that stands at a position which is read, in the tree's order: the
leaf's tokens. -/
def shownTree {r : Round} (posAt : ℕ → Option r.Pos) (rd : r.Pos → Bool) (T : TreeT lam L) :
    List (List Tok) :=
  ((List.range (T.lv.headD []).length).filter fun j =>
      match posAt j with
      | some p => rd p
      | none => false).map T.toksAt

/-- The same for the trees of one component of one round, from tree number k on. -/
def shownTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (rd : r.Pos → Bool) :
    ℕ → List (TreeT lam L) → List (List Tok)
  | _, [] => []
  | k, T :: Ts => shownTree (posAt k) rd T ++ shownTrees posAt rd (k + 1) Ts

/-- The same for all rounds: in each round the slot's component, then the shared one. rd: is the
position read? -/
def shownK : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → KeptT lam L s → (OPos s → Bool) →
    List (List Tok)
  | [], _, _, _, _ => []
  | _ :: s, (_, A), (w, W), (kp, ks), rd =>
      shownTrees w.posAtJ (fun p => rd (.inl p)) 0 kp.2.2 ++
        (shownTrees w.posAt0 (fun p => rd (.inl p)) 0 kp.2.1 ++
          shownK s A W ks fun p => rd (.inr p))

/-- The reveals in turn; what they return is dropped. -/
def revealsT : List (List Tok) → StT lam K L Unit
  | [] => .pure ()
  | ts :: l => Step.reveal ts fun _ => revealsT l

section Prove
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preX : Bits)
  (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ)
  (stop : Rho Q.loc.shape → Bool)

/-- For each position that is read in the external strings at the verifier messages ρ: the tokens of
its leaf. -/
def shownExt (ρ : Rho Q.loc.shape) : List (List Tok) :=
  (wq.ext.all.filter fun p => haveI := wq.ext.dec; decide (p ∈ Q.loc.extReads x ρ)).map fun p =>
    (xt (wq.ext.which p)).toksAt (wq.ext.leaf p)

/-- **All chunks**, in the order in which they are shown. -/
def chunksT (salt : Tok) (z : OutT lam L Q.loc.shape) : List (List Tok) :=
  (salt :: z.toks) ::
    (shownK Q.loc.shape Q.ann wq.sh z.kept (fun p =>
        haveI := wq.decO
        decide (p ∈ Q.loc.reads x z.rho (trT Q.loc.shape z.kept z.rho).plains)) ++
      shownExt Q wq x xt z.rho)

/-- all tokens that are shown -/
def showC (salt : Tok) (z : OutT lam L Q.loc.shape) : List Tok := (chunksT Q wq x xt salt z).flatten

/-- The reveals, chunk by chunk; then one reveal of all for the values, and the proof string: the
compiled prover's finish at the revealed values. -/
def finishC (salt : Tok) (cd : CoinsD lam L) (z : OutT lam L Q.loc.shape) :
    StT lam K L (OneProtocolProof lam Q) :=
  (revealsT (K := K) (L := L) (chunksT Q wq x xt salt z)).bind fun _ =>
  Step.reveal (showC Q wq x xt salt z) fun vs =>
    .pure (finish Q wq x y (fun k => (xt k).toK (valOf (showC Q wq x xt salt z) vs) preX)
      (coinsK (valOf (showC Q wq x xt salt z) vs salt) cd)
      (outK (valOf (showC Q wq x xt salt z) vs)
        (fun i b => pre i b (valOf (showC Q wq x xt salt z) vs salt)) z))

/-- **The end of a run**: no value, or the test says stop: "none", and nothing is shown. Else the
reveals and the string. No oracle is asked. -/
def endC (a : Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)) :
    StT lam K L (Option (OneProtocolProof lam Q)) :=
  match a.2.2 with
  | .ok z =>
      if stop z.rho then .pure none
      else (finishC Q wq x y xt preX pre a.1 a.2.1 z).bind fun π => .pure (some π)
  | .noFormat => .pure none
  | .ranOut _ => .pure none

/-- **The compiled prover of one slot as a token program**: all hashing, then the end. -/
def proveC : StT lam K L (Option (OneProtocolProof lam Q)) :=
  (hashT t Q wq embS embP xin cms x σ ln pre cap).bind (endC Q wq x y xt preX pre stop)

end Prove

end OnBytes.TokenSide
