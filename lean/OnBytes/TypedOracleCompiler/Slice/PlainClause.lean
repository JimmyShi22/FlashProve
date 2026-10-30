-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/PlainClause.lean: what the sibling's compiler gives for an accepted string of any
protocol with local rounds only that is written into an interface's oracles, for any language of
strings. A file of this project that is not in this library said again over the sibling's types
(OnBytes/TypedOracleCompiler/): a query
holds a list of roots, a round's component a list of trees, and a leaf's body has a type of the
interface's choosing. What turns: a stored symbol is written by the wire's `embE`, and a reading is
one for that `embE`.

The sibling's lemma on one protocol (`mem_of_accepted`) is general: the protocol P need not be one
of L's three. How a symbol of P's oracles is written into a leaf's body (`embS`) and how a plain
part of P is written into a query (`embP`) are free, and all that is asked of each is that it can be
read back (`prjS`, `prjP`). Nothing asks that two positions have different bodies. How the external
string is read off a trace is free too, within two conditions (see the paragraph on a reading
below). For this last freedom the sibling's lemma does not do, since it ties the reading to every
leaf: the proof goes through `accepted_at` (OnBytes/TypedOracleCompiler/Slice/AcceptedAt.lean), a copy of the
sibling's proof with that hypothesis weakened.

What is given (`Written`): a tag t of L; a protocol P on one external string of L's kind, without an
instance; its wiring; the two ways of writing with their ways back.
What is asked (`Written.OK`): the two laws of reading back; the sibling's laws of P's wiring; that
P's wiring places the external string as L's own is meant to (one root, position p at leaf p, L's
depth).
A reading (`Reading`, OnBytes/TypedOracleCompiler/Slice/Reading.lean): a function of what the trace determines at
the leaves under the root, with a test `keeps` on position, symbol and salt, and the law that at a
leaf whose body is `embE` of a kept symbol the string read has that symbol. The third clause then
speaks of accepted strings whose external openings pass the test.
Asked besides: round-by-round soundness of P for Lg with every error at most e; that P's verifier is
local. Of L's own wiring the theorems ask nothing: a protocol with local rounds alone obeys the law
on verifier's messages at every number of slots. They use its `embE`, of which nothing is asked.

Main definitions: `Written`, `Written.OK`, `Written.verifier`, `Written.lane`, `plainBad`,
`PlainAt`.
Main theorems: `plainBad_rare`, `plainBad_mono`, `plainBad_lang`, `plainBad_stable`, `plainAt`.
The form with "there is" (`PlainAt`) is for use in one world, where the bound on Bad and the run
stand under the same random oracles. For a run under one fixed family of oracle functions it would
be true for free; there the named set must be used (`plainBad_lang` with `plainBad_rare`).

Not claimed. No interface, no protocol and no way of writing is given here
(OnBytes/TypedOracleCompiler/Slice/Plain3Strings.lean has one): nothing in this file speaks of a key file, of any
file, or of the program. No reading is given here. A clause at a reading is worth what the reading
is worth (see `Reading`). That some protocol is round-by-round sound for some language is a
hypothesis. That any string is accepted is not shown. Nothing is asked that ties the greatest depth
of P's wiring to L's depth, nor that L's string fits under L's depth: where P's greatest depth is
smaller the verifier refuses every external opening, and the third clause is empty for a P that
reads the string. The sibling's verifier refuses a component with more than `maxRt` trees: for a P
with such a round the third clause is empty. Nothing on two written protocols in one family of
oracles: under one tag both can step at one query, and their bounds add. The verifier is the
sibling's `verifyB`, without the test of the strict format (OnBytes/TypedOracleCompiler/Slice/StrictClause.lean has
the third clause for the strict one). The bound says nothing once it reaches 1. The oracles are the
typed random oracles of the sibling's compiler, not a hash function on strings. The sibling:
what its own heads and its page say is not shown of it is not shown here. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.AcceptedAt
import OnBytes.TypedOracleCompiler.Slice.Reading

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A protocol with local rounds only, on one external string of L's kind and without an instance,
as it is written into the oracles of the interface L under the wiring W. -/
structure Written (W : QueryLayout lam L) where
  /-- the tag under which its challenge queries are asked -/
  t : Tag
  /-- the protocol; it need not be one of L's -/
  P : InteractiveOracleProof Unit (oneExternalString L.wordLength L.Symbol)
  /-- its wiring -/
  wq : ProtocolQueryLayout lam W.K (BatchInteractiveOracleProof.ofProto P)
  /-- how a symbol of its oracles is written into a leaf's body -/
  embS : (p : OPos P.shape) → OSym P.shape p → Body L
  /-- how such a body is read back at a position -/
  prjS : (p : OPos P.shape) → Body L → Option (OSym P.shape p)
  /-- how a plain part is written into a query -/
  embP : PlainPart P.shape (RoundSplits.allLocal P.shape) → PlainPart (shapeOf L t) (annOf L t)
  /-- how it is read back -/
  prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart P.shape (RoundSplits.allLocal P.shape))

/-- What is asked of a written protocol. The first two clauses are all that is asked of the two ways
of writing. -/
structure Written.OK {W : QueryLayout lam L} (Z : Written W) : Prop where
  backS : ∀ p a, Z.prjS p (Z.embS p a) = some a
  backP : ∀ z, Z.prjP (Z.embP z) = some z
  wire : Z.wq.OKG
  extDepth : Z.wq.ext.depth = W.depth
  ext : ∀ p, Z.wq.ext.which p = 0 ∧ Z.wq.ext.leaf p = p.val

/-- The compiled verifier of a written protocol, with the external root cm: the sibling's `verifyB`,
without the test of the strict format. -/
noncomputable def Written.verifier {W : QueryLayout lam L} (Z : Written W) (cm : Dig lam)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto Z.P)) : TypedOracleComputation lam W.K L Bool :=
  verifyB Z.t (BatchInteractiveOracleProof.ofProto Z.P) Z.wq Z.embS Z.embP (fun _ => none)
    W.embE (W.dReq Z.t) [cm] () π

/-- The written protocol as a lane of the sibling's analysis, with the canonical state function of
round-by-round soundness at the error counts ε, judged at the string as R reads it. -/
noncomputable def Written.lane {W : QueryLayout lam L} (Z : Written W) (R : Reading L W.embE)
    (ε : Err Z.P.shape) : Lane W :=
  laneOf W Z.t (BatchInteractiveOracleProof.ofProto Z.P) Z.wq.sh Z.prjS Z.prjP ε (stOf Z.P ε) (fun _ => some ())
    fun tr cms => R.at W tr (cms.getD 0 default)

/-- The named set of bad traces of a written protocol: the two clashes of `linkBad`
(OnBytes/Slice/LinkClause.lean, over the library), and a lucky step of the written protocol. In
judging a step, the transcript is read off the trace through `prjS` and `prjP`: each round's symbols
are those of the leaves that the trace before the query determines under the roots in that round's
own query, each position under the root of ITS OWN tree, at the places of P's wiring (the fixed
symbol 0 where the query holds no root of that number); a body that `prjS` does not read at its
position counts as the fixed symbol 0; a query whose plain field `prjP` does not read as that
round's has no transcript and causes no step. `prjS` may read at one position a body that was
written at another. The external string is read through R, at L's depth. -/
def plainBad {W : QueryLayout lam L} (Z : Written W) (R : Reading L W.embE) (ε : Err Z.P.shape) :
    Tc W → Prop :=
  fun tr => (EM tr ∨ EF tr) ∨ StepEvent (Z.lane R ε).step tr

/-- The compiler's conclusion on an accepted string of a written protocol, for the reading R and the
language Lg: the four clauses of `TestAt` (a file of this project that is not in this library, over
the library), the
third for strings whose external openings R keeps. That is asked of all external openings that the
string holds, also at positions that P does not read. -/
def PlainAt {W : QueryLayout lam L} (Z : Written W) (R : Reading L W.embE)
    (Lg : Unit → (oneExternalString L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤
        (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cm π, ¬ Bad tr → (∀ p op, π.ext p = some op → R.keeps p op.sym op.salt) →
      RunsIn tr (Z.verifier cm π) true → Lg () (R.at W tr cm)) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm →
      R.at W tr cm = R.at W (tr ++ tr') cm)

section
variable {W : QueryLayout lam L} (Z : Written W) (R : Reading L W.embE) (ε : Err Z.P.shape)

/-- Under the typed random oracles the named set is reached with small probability: at most t e
+ 2 t^2 / 2^lam by an algorithm with at most t queries, if every error count is at most the share e
of its round's verifier messages and `Z.OK` holds (of it the laws of the rounds' wiring are used).
-/
theorem plainBad_rare (εs : ℝ≥0∞) (hb : Err.Below ε εs) (hZ : Z.OK)
    (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | plainBad Z R ε o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have oZ : (Z.lane R ε).OK (2 ^ (W.dReq Z.t)) := laneOf_ok hZ.wire.sh (stOf_joint Z.P ε _)
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K L) (Z.lane R ε).step (fun _ => εs)
    (fun pre e he hs => hs.1 he)
    (fun pre o q _ => by
      by_cases ho : o = OracleName.fb Z.t
      · subst ho
        exact Lane.pr_step_le (Z.lane R ε) rfl oZ hb pre q
      · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
        rintro r - hr
        exact ho (Lane.step_oracle hr)) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc pr A.withTrace.law {o | (EM o.2 ∨ EF o.2) ∨ StepEvent (Z.lane R ε).step o.2}
      ≤ pr A.withTrace.law {o | EM o.2 ∨ EF o.2}
        + pr A.withTrace.law {o | StepEvent (Z.lane R ε).step o.2} := pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ = (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := add_comm _ _

/-- The named set is closed under appending queries. -/
theorem plainBad_mono (tr tr' : Tc W) (h : plainBad Z R ε tr) : plainBad Z R ε (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- Outside the named set an accepted string whose external openings R keeps means that the language
holds of the string that R reads off the trace under the root, if the written protocol is
round-by-round sound for the language with the error counts ε that the set is made from. This is
said under the hypotheses that stand in the statement itself, which this comment does not list; it
is no claim that they hold. At large counts ε the premise hs asks less and the named set costs more:
its price is bounded only where every count is at most the share εs of its round's verifier messages
(`plainBad_rare`), and at t εs of 1 or more that bound says nothing. -/
theorem plainBad_lang (Lg : Unit → (oneExternalString L.wordLength L.Symbol).Str → Prop) (hs : Z.P.Sound Lg ε)
    (hl : Z.P.IsLocal) (hZ : Z.OK) (tr : Tc W) (cm : Dig lam)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto Z.P)) (hB : ¬ plainBad Z R ε tr)
    (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt)
    (hrun : RunsIn tr (Z.verifier cm π) true) : Lg () (R.at W tr cm) := by
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  exact accepted_at Z.t (BatchInteractiveOracleProof.ofProto Z.P) Z.wq Z.embS Z.embP (fun _ => none)
    W.embE hZ.wire hl (_root_.Iop.BatchOne.BAnn.allLocal_coherent _) (Lg := Lg)
    (stOf Z.P ε) Z.prjS hZ.backS Z.prjP hZ.backP
    (fun _ => some ()) (fun tr cms => R.at W tr (cms.getD 0 default)) ε hM
    (fun h => hB (Or.inl (Or.inr h))) (fun h => hB (Or.inr h)) [cm] () π
    (fun _ => ()) (fun _ => rfl) (fun _ _ h => absurd rfl h)
    (fun y hL => stOf_start hs y () hL) (fun y τ m _ h => stOf_prover y () τ m h)
    (fun y τ _ h => stOf_full y () τ h) hrun
    (fun pre q a post htr hocc => R.at_before htr hM (hocc _ (by simp)))
    (fun p op hop h => by
      rw [hZ.extDepth, (hZ.ext p).1, (hZ.ext p).2] at h
      exact R.law _ p op.sym op.salt h (hk p op hop))

/-- If the longer trace is outside the named set, what is read off under a root that was announced
in the shorter one does not change. -/
theorem plainBad_stable (tr tr' : Tc W) (cm : Dig lam) (hB : ¬ plainBad Z R ε (tr ++ tr'))
    (hann : Announced W tr cm) : R.at W tr cm = R.at W (tr ++ tr') cm :=
  R.at_stable (fun h => hB (Or.inl (Or.inl h))) (List.prefix_append _ _)
    (occursIn_of_announced hann)

end

/-- Round-by-round soundness of a written protocol for a language gives the compiler's conclusion
for that language and that reading: from soundness of P for the language, every error at most e, a
local verifier, and `Z.OK`. The set is `plainBad`. -/
theorem plainAt {W : QueryLayout lam L} (Z : Written W) (R : Reading L W.embE)
    (Lg : Unit → (oneExternalString L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (ε : Err Z.P.shape)
    (hb : Err.Below ε εs) (hs : Z.P.Sound Lg ε) (hl : Z.P.IsLocal) (hZ : Z.OK) :
    PlainAt Z R Lg εs := by
  refine ⟨plainBad Z R ε, fun β A t hA => ?_, plainBad_mono Z R ε,
    fun tr cm π hB hk => plainBad_lang Z R ε Lg hs hl hZ tr cm π hB hk, plainBad_stable Z R ε⟩
  refine (plainBad_rare Z R ε εs hb hZ β A t hA).trans ?_
  gcongr
  exact Nat.le_succ t

end TypedOracleCompiler.Slice
