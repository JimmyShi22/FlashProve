-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ReplyClause.lean: over the second compiler (OnBytes/TypedOracleCompiler/), the compiler's
conclusion for a written batch protocol whose chain takes in the early part of the instance alone,
from one hypothesis on the protocol in the place of a given state function.

The text. Six theorems are those of OnBytes/Slice/ReplyState.lean (`mem_of_accepted_reply`,
`laneOf_reply_ok`), OnBytes/Slice/ReplyClause.lean (`stLaws_reply`, `joint_reply`, `batchAt_reply`)
and OnBytes/Slice/TimesSharedBelow.lean (`batchAt_reply_two`), which are over the library's
compiler, said again. What turned: the imports and opened namespaces; a reading is `Reading L
W.embE`. No proof turned. THEIR DOCSTRINGS ARE THE SOURCES' TOO: where one says "the library's" or
names a file under Compile/Batch/, read the second compiler's namesake under
OnBytes/TypedOracleCompiler/Compile/Batch/. All else that they name has no interface and is used as it lies: the
hypothesis `ReplyLost` and the state function `replySt` with its laws
(OnBytes/Slice/ReplyState.lean), `BelowBy` and `below_timesShared`
(OnBytes/Slice/TimesSharedBelow.lean). One theorem is new: `judgeAt_reply`.

Main theorems.
 `batchAt_reply`, `batchAt_reply_two` from `ReplyLost` to `BatchAt`
     (OnBytes/TypedOracleCompiler/Slice/BatchClause.lean): with one bound on the errors, the shared rounds'
     multiplied by the number of slots; with two numbers, one for the local and one for the shared
     rounds.
 `judgeAt_reply` and so to `JudgeAt` (OnBytes/TypedOracleCompiler/Slice/OneWorldJ.lean) of the compiled verifier
     with the strict format (`judgeBS`, OnBytes/TypedOracleCompiler/Slice/BatchJudge.lean): the first clause of
     `Part.OK`.
`batchAt_reply` has the form with "there is" (`BatchAt`), which is for use in one world. Where the
set must be named, it is `batBad` at the multiplied errors and at `replySt`; `stLaws_reply` and
`joint_reply` are what `batBad_lang`, `batBad_rare` and, for the strict format, `batBad_langS` ask
of it.

What is not claimed. `ReplyLost` is a hypothesis, shown of no written protocol. No interface, no
wiring and no written batch protocol is given here. The five hypotheses of `judgeAt_reply` are met
together by nothing here. All limits in the heads of the three files over the library, and of
OnBytes/TypedOracleCompiler/Slice/StrictClause.lean, Reading.lean and BatchJudge.lean, hold here too. The compiler
under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.TimesSharedBelow
import OnBytes.TypedOracleCompiler.Slice.BatchJudge

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (ReplyLost replySt replySt_laws replySt_joint replySt_joint_times replySt_start
  replySt_prover replySt_full BelowBy below_timesShared)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

section
variable {W : QueryLayout lam L}

/-- `Compile.Batch.mem_of_accepted` at the state function `replySt` and the constant sequence of
instances `fun _ => early x`. Its three hypotheses on the state function are replaced by one,
`ReplyLost`. hS and hx are the library's at this state function and this sequence. The library's ε,
the lane's errors, is called εl here, and is free as there (the event does not read it); ε here is
the state function's. Every other argument is carried over to the letter.
hx ties early to the interface: where no later query holds the instance (L.late = none) the chain
has taken in (xin x).map L.early in every round (Compile/Batch/LateX.lean: `instX`), so with Y = X,
xin = some and xout = id, hx says that early x is L.early x. The theorem does not assume L.late =
none; where L.late = some n, hx says from round n on that xout (xin x) is some (early x): with xin =
some and xout = id, that x is its own early part. -/
theorem mem_of_accepted_reply (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (hOK : wq.OKG) (hloc : Q.loc.IsLocal) (hco : Q.ann.Coherent)
    {Lg : Y → E.Str → Prop} (early : Y → Y)
    (prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p))
    (hprjS : ∀ p a, prjS p (embS p a) = some a)
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann))
    (hprjP : ∀ z, prjP (embP z) = some z) (xout : Option X → Option Y)
    (extY : Tc W → List (Dig lam) → E.Str) (ε εl : Err Q.loc.shape)
    (hlost : ReplyLost Q.loc ε early Lg) {tr : Tc W} (hM : ¬ EM tr)
    (hF : ¬ EF tr)
    (hS : ¬ StepEvent
      (laneOf W t Q wq.sh prjS prjP εl (replySt Q.loc ε early Lg) xout extY).step tr)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (hx : ∀ i, xout (instX L (xin x) i) = some (early x))
    (hlate : ∀ n, L.late = some n → xin x ≠ none → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE (W.dReq t) cms x π) true)
    (hstab : ∀ pre (q : FbIn lam L t) (a : FsAns lam W.K) post, tr = pre ++ fbE t q a :: post →
      (∀ c ∈ cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) c) →
      extY pre cms = extY tr cms)
    (hagree : ∀ p a sl,
      extLeaf tr wq.ext.depth (cms.getD (wq.ext.which p) default) (wq.ext.leaf p) =
        some ⟨embE a, sl⟩ →
      E.rd (extY tr cms) p = a) : Lg x (extY tr cms) :=
  mem_of_accepted t Q wq embS embP xin embE hOK hloc hco (replySt Q.loc ε early Lg) prjS hprjS prjP
    hprjP xout extY εl hM hF hS cms x π (fun _ => early x) hx hlate
    (replySt_laws hlost x).1 (replySt_laws hlost x).2.1 (replySt_laws hlost x).2.2
    hrun hstab hagree

/-- The library's `laneOf_ok` at the state function `replySt`, for a protocol with local rounds
only. Given the wire's law, the lane of the event in `mem_of_accepted_reply`, at εl = ε, has
`Lane.OK` (Compile/Batch/Facts.lean). The library's bound on that event (`Lane.pr_step_le`) asks
three things: `Lane.OK`, N = 2 ^ W.dReq t, and a bound on the errors. -/
theorem laneOf_reply_ok {t : Tag} {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E}
    {ws : RoundsQueryLayout lam W.K Q.shape (RoundSplits.allLocal Q.shape)}
    {prjS : (p : OPos Q.shape) → Body L → Option (OSym Q.shape p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.shape (RoundSplits.allLocal Q.shape))}
    {ε : Err Q.shape} {early : Y → Y} {Lg : Y → E.Str → Prop} {xout : Option X → Option Y}
    {extY : Tc W → List (Dig lam) → E.Str} {N : ℕ}
    (hws : RoundsQueryLayout.OKG Q.shape (RoundSplits.allLocal Q.shape) ws) :
    (laneOf W t (BatchInteractiveOracleProof.ofProto Q) ws prjS prjP ε (replySt Q ε early Lg) xout extY).OK N :=
  laneOf_ok hws (replySt_joint N)

end

/-- The laws of a state function for the language Lg hold of `replySt` at early := L.early, if no
later query holds the instance and the protocol has `ReplyLost`. -/
theorem stLaws_reply {W : QueryLayout lam L} (Z : WrittenB W) (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop)
    (ε : Err Z.Q.loc.shape) (hlate : L.late = none) (h : ReplyLost Z.Q.loc ε L.early Lg) :
    StLaws Z (replySt Z.Q.loc ε L.early Lg) Lg where
  start := fun y _ _ => replySt_start h y _
  prover := fun y x τ m h0 => replySt_prover y x τ m h0
  switch := fun _ _ _ _ hn => by
    rw [hlate] at hn
    cases hn
  full := fun y x τ hL h0 => by
    rw [hlate] at h0
    exact replySt_full y x τ hL h0

/-- The law on verifier messages holds of `replySt`, at the errors ε with those of the shared rounds
multiplied by the number of slots. -/
theorem joint_reply {W : QueryLayout lam L} (Z : WrittenB W) (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop)
    (ε : Err Z.Q.loc.shape) :
    Joint Z (Err.timesShared L.maxBatchSize Z.Q.ann ε) (replySt Z.Q.loc ε L.early Lg) :=
  fun y x => replySt_joint_times L.maxBatchSize Z.Q.ann y x

/-- From `ReplyLost` to the compiler's conclusion, for the language Lg and the reading R: if no
later query holds the instance, the protocol has `ReplyLost` with the errors ε, every one of these,
the shared rounds' multiplied by the number of slots, is at most the share e of its round's verifier
messages, `Z.OK` holds, and there are as many slots as the request tree at Z's tag has leaves. The
set is `batBad` at these multiplied errors and at `replySt` with the errors ε. -/
theorem batchAt_reply {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (ε : Err Z.Q.loc.shape)
    (hlate : L.late = none) (h : ReplyLost Z.Q.loc ε L.early Lg)
    (hb : Err.Below (Err.timesShared L.maxBatchSize Z.Q.ann ε) εs) (hZ : Z.OK) (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) :
    BatchAt Z R Lg εs :=
  batchAt Z R Lg εs (Err.timesShared L.maxBatchSize Z.Q.ann ε) (replySt Z.Q.loc ε L.early Lg) hb
    (joint_reply Z Lg ε) (stLaws_reply Z Lg ε hlate h) hZ hN

/-- `batchAt_reply` with the two numbers: the compiler's conclusion at the larger of c and maxBatchSize c',
if every local round's count is at most c and every shared round's at most c'. -/
theorem batchAt_reply_two {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (c c' : ℝ≥0∞) (ε : Err Z.Q.loc.shape)
    (hlate : L.late = none) (h : ReplyLost Z.Q.loc ε L.early Lg)
    (hb : BelowBy Z.Q.ann ε c c') (hZ : Z.OK) (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) :
    BatchAt Z R Lg (max c ((L.maxBatchSize : ℝ≥0∞) * c')) :=
  batchAt_reply Z R Lg _ ε hlate h (below_timesShared L.maxBatchSize Z.Q.ann ε c c' hb) hZ hN

/-- From `ReplyLost` to what a part of the join asks of its judge, for the compiled verifier
with the strict format: `batchAt_reply_two` and then `judgeAt_BS`. The error is the larger of c and
maxBatchSize c'. It is the first clause of `Part.OK` (OnBytes/TypedOracleCompiler/Slice/Part.lean) and the hypothesis `hj` of
`Part.on_ok_of` (PartOn.lean). The other clauses are shown of no checker; `fit` as it stands is not
met by a checker whose reader opens one tree twice (for that: OnBytes/TypedOracleCompiler/Slice/PartGuard.lean). sMT
and sFS are free: nothing here ties them to a format's salts. -/
theorem judgeAt_reply {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (sMT sFS : ℕ) (c c' : ℝ≥0∞) (ε : Err Z.Q.loc.shape)
    (hlate : L.late = none) (h : ReplyLost Z.Q.loc ε L.early Lg)
    (hb : BelowBy Z.Q.ann ε c c') (hZ : Z.OK) (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) :
    JudgeAt W (judgeBS Z R Lg sMT sFS) (max c ((L.maxBatchSize : ℝ≥0∞) * c')) :=
  judgeAt_BS Z R Lg sMT sFS hZ _ (batchAt_reply_two Z R Lg c c' ε hlate h hb hZ hN)

end TypedOracleCompiler.Slice
