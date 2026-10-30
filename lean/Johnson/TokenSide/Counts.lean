-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Counts.lean: HOW MANY ORDINARY AND MARKED EVALUATIONS THE TOKEN PROGRAMS OF THIS
FOLDER MAY MAKE, oracle by oracle, as written functions. DEFINITIONS ALONE.

These are the letters e and M of deferred programming (DSt.Within, Rom/Defer.lean; costTotal,
Rom/SpecHopCost.lean) for the challenger challT (Johnson/TokenSide/Whole.lean). They are meant as
upper bounds at the worst case: EVERY SEARCH IS COUNTED AT ITS CAP, and every round is counted with
the trees of both its components. It follows the pattern of the first form's counts (mProveB, eCB,
mCB, mAllB, Compile/Batch/SpecDiscipline.lean).

One compiled run at the tag t (mRun, eRun):
  marked   leaf: one for each leaf of each tree · fb t: one a round (try number 0) · fbw t k: one
           for each round with a test whose cap is above k (try number k + 1) · g t, rleaf: one if
           there is a shared round · rnode: the depth of the request tree, if there is a shared
           round
  ordinary node: at most one for each leaf of each tree
One table (mTab, eTab): 2 ^ depth marked leaves; at most 2 ^ depth ordinary nodes; the seed's two
ordinary queries at its Fiat-Shamir oracle.
The setup (mSetup, eSetup): h.M + 2 tables, the run on the first table, h.M + 1 links.
A session (mSess, eSess): one run.

Main names (namespace OnBytes.TokenSide).
  cLeaves, hasTest, cTry, joinsT   counts over the rounds of a shape.
  mRun, eRun, mTab, eTab, mSetup, eSetup, mSess, eSess, mAllT, eAllT   the counts.
  capSup, capTop, osAllT   the largest cap; the oracles with marked evaluations.

Limits. Definitions alone: that the programs stay within these counts is not shown here. No closed
form of any sum.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Whole

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ}

/-! ## Over the rounds of a shape -/

/-- the leaves of all trees of all rounds, both components -/
def cLeaves : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) =>
      ((w.depthJ.map fun d => 2 ^ d).sum + (w.depth0.map fun d => 2 ^ d).sum) + cLeaves s A W

/-- has the Fiat-Shamir query of this round a test? The kind says which of the wire's two tests is
read. -/
def hasTest {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Bool :=
  match a.kind with
  | .lo => w.grJ.isSome
  | .sh => w.gr0.isSome

/-- the rounds with a test whose search may reach try number k + 1. i: the number of the first of
the rounds s. -/
def cTry (k : ℕ) (cap : ℕ → ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → ℕ
  | [], _, _, _ => 0
  | _ :: s, (_, A), (w, W), i =>
      (if hasTest w = true ∧ k < cap i then 1 else 0) + cTry k cap s A W (i + 1)

/-- 1 if there is a shared round, else 0 -/
def joinsT : (s : Shape) → RoundSplits s → ℕ
  | [], _ => 0
  | _ :: s, (a, A) => match a.kind with
    | .sh => 1
    | .lo => joinsT s A

/-- the largest cap among the rounds 0, .., n - 1 -/
def capSup (cap : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range n).sup cap

/-! ## One compiled run, one table -/

/-- marked evaluations of one compiled run at the tag t; dq: the depth of its request tree -/
def mRun (t : Tag) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (cap : ℕ → ℕ) (dq : ℕ) : OracleName → ℕ
  | .leaf => cLeaves s A W
  | .rleaf => joinsT s A
  | .rnode => joinsT s A * dq
  | .fb t' => if t' = t then s.length else 0
  | .fbw t' k => if t' = t then cTry k cap s A W 0 else 0
  | .g t' => if t' = t then joinsT s A else 0
  | _ => 0

/-- ordinary queries of one compiled run -/
def eRun (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) : OracleName → ℕ
  | .node => cLeaves s A W
  | _ => 0

/-- marked evaluations of one table -/
def mTab (depth : ℕ) : OracleName → ℕ
  | .leaf => 2 ^ depth
  | _ => 0

/-- ordinary queries of one table; t: the tag of the seeds' queries -/
def eTab (depth : ℕ) (t : Tag) : OracleName → ℕ
  | .node => 2 ^ depth
  | .fb t' => if t' = t then 2 else 0
  | _ => 0

/-! ## The scheme -/

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)

/-- The counts of the setup: h.M + 2 tables, the run on the first table, h.M + 1 links. -/
def mSetup : OracleName → ℕ := fun o =>
  (h.M + 2) * mTab W.depth o + mRun Tag.test L.offline.shape aT (wTC W).sh h.capT tl.T.dq o +
    (h.M + 1) * mRun Tag.link L.link.shape aL (wLC W).sh h.capL tl.Lk.dq o

def eSetup : OracleName → ℕ := fun o =>
  (h.M + 2) * eTab W.depth S.t o + eRun L.offline.shape aT (wTC W).sh o +
    (h.M + 1) * eRun L.link.shape aL (wLC W).sh o

/-- The counts of one session. -/
def mSess : OracleName → ℕ := mRun Tag.onl L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh h.capB tl.B.dq
def eSess : OracleName → ℕ := eRun L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh

/-- **The counts of the setup and n sessions.** -/
def mAllT (n : ℕ) : OracleName → ℕ := fun o => mSetup W h tl o + n * mSess W h tl o
def eAllT (n : ℕ) : OracleName → ℕ := fun o => eSetup W S h o + n * eSess W o

/-- the largest cap of the three protocols' searches -/
def capTop : ℕ :=
  max (capSup h.capT L.offline.shape.length)
    (max (capSup h.capL L.link.shape.length) (capSup h.capB L.onlineBatch.loc.shape.length))

/-- the oracles with marked evaluations -/
def osAllT : Finset OracleName := osT (capTop h)

end OnBytes.TokenSide
