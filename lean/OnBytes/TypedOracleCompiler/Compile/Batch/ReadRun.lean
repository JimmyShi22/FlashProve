-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ReadRun.lean: what a chain yields, read off a list of entries: a reading
`extSOf` for a value that a chain apart draws. Over any interface and wire.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Why. `mem_off_ours` (SoundOurs.lean) takes as a parameter a reading `extS`, a function from a list
of entries and the external roots to Sd. Here is one. In the use that is meant, a record's seeds,
the value is the verifier's messages of a chain of its own at one fixed proof string (no salt, no
root, fixed plain parts); `chainAt` and `extSOf` take all of these as arguments.

  `runsIn_unique`
      In a list in which each query has one answer (`OneAns`, TwoLanes.lean: it holds outside
      `Bad3`) an algorithm without coins has at most one run: `RunsIn tr c a → RunsIn tr c b → a =
      b`. Without `OneAns` this is false: one query, two answers, two runs.
  `OneAns.mono`
      A part of such a list is such a list.
  `readRun tr c`
      The result of c's run in tr, if there is one (by choice; under `OneAns` it is the one run;
      none: some query of it is not in tr).
  `readRun_eq`
      `OneAns tr → RunsIn tr c a → readRun tr c = some a`.
  `readRun_stable`
      `OneAns tr → pre ⊆ tr → RunsIn pre c a → readRun pre c = readRun tr c`: once the run's entries
      stand, the reading does not move.
  `chainAt`
      A protocol's chain at a fixed string (salt, request root, roots, plain parts) and a fixed
      field x, under the external roots cms.
  `extSOf`
      The reading: `seedOf` of the verifier messages that the chain yields in tr under cms; the
      default d where the chain has not run in tr, or refuses.
  `extSOf_run`
      `OneAns tr` → the chain runs in tr and yields ρ → `extSOf … tr cms = seedOf ρ`.
  `extSOf_stable`
      `OneAns tr → pre ⊆ tr` → the chain runs in pre → `extSOf … pre cms = extSOf … tr cms`.

Limits. Not said: any protocol. Not said: that a maker's log has the chain's run before its first
query. From membership of a log's entries to the hypothesis of `extSOf_stable`, that the chain runs
in pre, there are three steps: `ours_first` (OursFirst.lean), that an algorithm runs in its own log,
and the step through bind; the last two and the assembly are not in this folder. Nothing on
probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.TwoLanes

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol

theorem OneAns.mono {S : OSpec} {pre tr : Trace S} (h : OneAns tr) (hs : pre ⊆ tr) : OneAns pre :=
  fun o q r r' ha hb => h o q r r' (hs ha) (hs hb)

/-- in a list in which each query has one answer an algorithm has at most one run -/
theorem runsIn_unique {S : OSpec} {α : Type} {tr : Trace S} (h1 : OneAns tr)
    {c : OComp S α} {a b : α}
    (ha : RunsIn tr c a) (hb : RunsIn tr c b) : a = b := by
  induction ha with
  | pure a => exact runsIn_pure_iff.1 hb
  | query o q k r a hm _ ih =>
    obtain ⟨r', hm', hr'⟩ := runsIn_query_iff.1 hb
    obtain rfl := h1 o q r r' hm hm'
    exact ih hr'

open Classical in
/-- the result of c's run in tr, if there is one -/
def readRun {S : OSpec} {α : Type} (tr : Trace S) (c : OComp S α) : Option α :=
  if h : ∃ a, RunsIn tr c a then some h.choose else none

theorem readRun_eq {S : OSpec} {α : Type} {tr : Trace S} (h1 : OneAns tr) {c : OComp S α} {a : α}
    (ha : RunsIn tr c a) : readRun tr c = some a := by
  unfold readRun
  rw [dif_pos ⟨a, ha⟩]
  exact congrArg some (runsIn_unique h1 (Exists.choose_spec (⟨a, ha⟩ : ∃ a, RunsIn tr c a)) ha)

/-- Once the run's entries stand, the reading does not move. -/
theorem readRun_stable {S : OSpec} {α : Type} {pre tr : Trace S} (h1 : OneAns tr) (hs : pre ⊆ tr)
    {c : OComp S α} {a : α}
    (ha : RunsIn pre c a) : readRun pre c = readRun tr c := by
  rw [readRun_eq (h1.mono hs) ha, readRun_eq h1 (ha.mono hs)]

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- a protocol's chain at a fixed string and a fixed field x, under the external roots cms -/
def chainAt (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xo : Option X) (salt : Bits)
        (rtreq : Dig lam)
    (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (cms : List (Dig lam)) :
    TypedOracleComputation lam W.K L (Option (Rho Q.loc.shape × RootsOfChain lam Q.loc.shape × Phase lam)) :=
  recomputeChain (K := W.K) t cms xo salt rtreq Q.loc.shape Q.ann wq.sh embP 0 .first roots plains

/-- The reading. -/
def extSOf (t : Tag) {Y Sd : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xo : Option X) (salt : Bits)
        (rtreq : Dig lam)
    (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (seedOf : Rho Q.loc.shape → Sd) (d : Sd)
    (tr : Tc W) (cms : List (Dig lam)) : Sd :=
  match readRun tr (chainAt t Q wq embP xo salt rtreq roots plains cms) with
  | some (some z) => seedOf z.1
  | _ => d

/-- A run that has recomputed the value has it as the reading. -/
theorem extSOf_run (t : Tag) {Y Sd : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xo : Option X) (salt : Bits)
        (rtreq : Dig lam)
    (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (seedOf : Rho Q.loc.shape → Sd) (d : Sd)
    {tr : Tc W} (h1 : OneAns tr) (cms : List (Dig lam)) {ρ : Rho Q.loc.shape}
        {rts : RootsOfChain lam Q.loc.shape} {ph : Phase lam}
    (hr : RunsIn tr (chainAt t Q wq embP xo salt rtreq roots plains cms) (some (ρ, rts, ph))) :
    extSOf t Q wq embP xo salt rtreq roots plains seedOf d tr cms = seedOf ρ := by
  unfold extSOf
  rw [readRun_eq h1 hr]

/-- Seed first: once the chain has run in a part of the list, the reading is the final one. -/
theorem extSOf_stable (t : Tag) {Y Sd : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xo : Option X) (salt : Bits)
        (rtreq : Dig lam)
    (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (seedOf : Rho Q.loc.shape → Sd) (d : Sd)
    {pre tr : Tc W} (h1 : OneAns tr) (hs : pre ⊆ tr) (cms : List (Dig lam))
    {z : Option (Rho Q.loc.shape × RootsOfChain lam Q.loc.shape × Phase lam)}
    (hr : RunsIn pre (chainAt t Q wq embP xo salt rtreq roots plains cms) z) :
    extSOf t Q wq embP xo salt rtreq roots plains seedOf d pre cms =
      extSOf t Q wq embP xo salt rtreq roots plains seedOf d tr cms := by
  unfold extSOf
  rw [readRun_stable h1 hs hr]

end TypedOracleCompiler.Compile.Batch
