-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/BatchClause.lean: what the compiler over the sibling's types gives for an accepted
string of any batch protocol that is written into an interface's oracles, for any language and any
reading.

CUT BY PROGRAM from OnBytes/Slice/BatchClause.lean (over the library), with the strict third clause
of a file of this project that is not in this library. What turned: the imports and opened
namespaces; a reading is
`Reading L W.embE`; where the library writes a stored symbol into a leaf's body in its one way, the
sibling's wiring names the way (`W.embE`). No proof turned. The batch protocol, its annotation,
partial transcripts, error counts and the library's late form of soundness of a batch
(`Iop.BatchInteractiveOracleProof.SndBL`) are the library's own types here too: the sibling says again the interface
and the wirings alone.

OnBytes/TypedOracleCompiler/Slice/PlainClause.lean states four clauses for a protocol with local rounds only and
without an instance. This file states the same four for a batch protocol: rounds may be shared
between slots, and a slot has an instance. The protocol Q need not be the interface's own Batch, the
two ways of writing are free but for the law that what is written can be read back, and the external
string is read through any reading (OnBytes/TypedOracleCompiler/Slice/Reading.lean).

What is given (`WrittenB`): a tag t of L; a batch protocol Q on one external string of L's kind,
with instances of L's type; its wiring; the two ways of writing with their ways back. What is asked
(`WrittenB.OK`): the two laws of reading back; the sibling's laws of Q's wiring; that Q's verifier
is local; that Q's annotation is coherent; that a late round of the interface, if there is one, is a
round of Q and not its first, and that it and all rounds before it are local in Q (the interface's
`late` counts Q's rounds here); that Q's wiring places the external string as L's own is meant to
(one root, position p at leaf p, L's depth). A state function is GIVEN, not made: the library's
soundness of a batch says that there is one and names none. Asked of it: `StLaws`, the clauses of
the library's late form of soundness of a batch (`Iop.BatchInteractiveOracleProof.SndBL`) without its "there is", and
`Joint`, the law on verifier messages for all slots together; `sndBL_iff`: that there is a state
function with these two, with the clause on the late round, is that form. Of L's own wiring the
theorems ask one thing alone: L.maxBatchSize, the number of slots, is the number of leaves of the request tree
at Z's tag (so at a tag other than that of Batch they ask that this tree has L.maxBatchSize leaves). The
interface's `early` and
`late` are read: they say how an instance enters a slot's chain. As with `PlainAt`, the form with
"there is" (`BatchAt`) is for use in one world, where the bound on Bad and the run stand under the
same random oracles. For a run under one fixed family of oracle functions it would be true for free;
there the named set must be used (`batBad_lang` with `batBad_rare`).

Main definitions: `WrittenB`, `WrittenB.OK`, `WrittenB.verifier`, `WrittenB.lane`, `StLaws`,
`Joint`, `batBad`, `BatchAt`, `WrittenB.verifierS`.
Main theorems: `sndBL_iff`, `batBad_rare`, `batBad_mono`, `batBad_lang`, `batBad_stable`, `batchAt`,
`batBad_langS`.

Not claimed. No interface, no protocol, no way of writing and no state function is given here:
nothing speaks of a proof file, of any file, or of the program. That some batch protocol has a state
function with these laws for some language is a hypothesis. The interface's own Batch as an instance
(over the library: in a file of this project that is not in this library) is not said again. A
clause at a reading is
worth what the reading is worth (see `Reading`). That any string is accepted is not shown. Nothing
is asked that ties the greatest depth of Q's wiring to L's depth, nor that L's string fits under L's
depth: where Q's greatest depth is smaller the verifier refuses every external opening, and the
third clause is empty for a Q that reads the string. The sibling's verifier refuses a component with
more than `maxRt` trees: for a Q with such a round the third clause is empty. Nothing is asked of
the order of shared and local rounds: where the verifier has no format for a round it refuses every
string. Nothing on two written protocols in one family of oracles: under one tag both can step at
one query, and their bounds add. For the verifier with the strict format the third clause alone is
stated, for the named set alone (`batBad_langS`); the strict format's tests are used for nothing,
and by the sibling's own page its definitions of that format tree by tree are pinned by no theorem.
The bound says nothing once it reaches 1. The oracles are the typed random oracles of the sibling's
compiler, not a hash function on strings. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.StrictClause

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A batch protocol on one external string of L's kind, with instances of L's type, as it is
written into the oracles of the interface L under the wiring W. -/
structure WrittenB (W : QueryLayout lam L) where
  /-- the tag under which its challenge queries are asked -/
  t : Tag
  /-- the protocol; it need not be L's Batch -/
  Q : BatchInteractiveOracleProof X (oneExternalString L.wordLength L.Symbol)
  /-- its wiring -/
  wq : ProtocolQueryLayout lam W.K Q
  /-- how a symbol of its oracles is written into a leaf's body -/
  embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L
  /-- how such a body is read back at a position -/
  prjS : (p : OPos Q.loc.shape) → Body L → Option (OSym Q.loc.shape p)
  /-- how a plain part is written into a query -/
  embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)
  /-- how it is read back -/
  prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart Q.loc.shape Q.ann)

/-- What is asked of a written batch protocol. The first two clauses are all that is asked of the
two ways of writing. -/
structure WrittenB.OK {W : QueryLayout lam L} (Z : WrittenB W) : Prop where
  backS : ∀ p a, Z.prjS p (Z.embS p a) = some a
  backP : ∀ z, Z.prjP (Z.embP z) = some z
  wire : Z.wq.OKG
  loc : Z.Q.loc.IsLocal
  coh : Z.Q.ann.Coherent
  late : ∀ n, L.late = some n → 0 < n ∧ RoundSplits.LocalTo n Z.Q.loc.shape Z.Q.ann
  extDepth : Z.wq.ext.depth = W.depth
  ext : ∀ p, Z.wq.ext.which p = 0 ∧ Z.wq.ext.leaf p = p.val

/-- The compiled verifier of one slot of a written batch protocol, with the external root cm and the
instance x: the sibling's `verifyB`, without the test of the strict format. -/
noncomputable def WrittenB.verifier {W : QueryLayout lam L} (Z : WrittenB W) (cm : Dig lam) (x : X)
    (π : OneProtocolProof lam Z.Q) : TypedOracleComputation lam W.K L Bool :=
  verifyB Z.t Z.Q Z.wq Z.embS Z.embP some W.embE (W.dReq Z.t) [cm] x π

/-- The written batch protocol as a lane of the sibling's analysis, with a given state function,
judged at the string as R reads it. -/
noncomputable def WrittenB.lane {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (ε : Err Z.Q.loc.shape) (State : (Fin L.wordLength → L.Symbol) → X → PTr Z.Q.loc.shape → Bool) : Lane W :=
  laneOf W Z.t Z.Q Z.wq.sh Z.prjS Z.prjP ε State id fun tr cms => R.at W tr (cms.getD 0 default)

/-- The laws of a state function for the language Lg: the clauses of `Iop.BatchInteractiveOracleProof.SndBL` without
its "there is", without its first clause (it is `WrittenB.OK.late`) and without the law on verifier
messages (it is `Joint`). A false statement starts in state 0 of its early part; a prover's message
never changes 0 to 1; at the late round state 0 of the early part gives state 0 of a false instance;
at the end state 0 means that a false instance is rejected. -/
structure StLaws {W : QueryLayout lam L} (Z : WrittenB W)
    (State : (Fin L.wordLength → L.Symbol) → X → PTr Z.Q.loc.shape → Bool)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) : Prop where
  start : ∀ y x, ¬ Lg x y → State y (L.early x) (PTr.empty Z.Q.loc.shape) = false
  prover : ∀ y x (τ : AtP Z.Q.loc.shape) (m : τ.round.Msg),
    State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false
  switch : ∀ y x (τ : AtP Z.Q.loc.shape), ¬ Lg x y → L.late = some τ.idx →
    State y (L.early x) (.atP τ) = false → State y x (.atP τ) = false
  full : ∀ y x (τ : Tr Z.Q.loc.shape), ¬ Lg x y →
    State y (if L.late.isSome then x else L.early x) (.full τ) = false →
    Z.Q.loc.accept x y τ = false

/-- The law on verifier messages, for every external string and every vector of instances, at the
error counts ε: the library's `JointLaw`. In a shared round the count is of the verifier messages
that turn the state of some slot. -/
def Joint {W : QueryLayout lam L} (Z : WrittenB W) (ε : Err Z.Q.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → X → PTr Z.Q.loc.shape → Bool) : Prop :=
  ∀ y (x : Fin L.maxBatchSize → Option X),
    JointLaw L.maxBatchSize Z.Q.loc.shape Z.Q.ann ε fun j => (x j).map (State y)

/-- That there is a state function with `StLaws` for Lg and `Joint` at ε, with the clause on the
late round, is the library's late form of soundness of Q at L's number of slots, `early` and `late`:
for every written batch protocol. -/
theorem sndBL_iff {W : QueryLayout lam L} (Z : WrittenB W) (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop)
    (ε : Err Z.Q.loc.shape) :
    Z.Q.SndBL L.maxBatchSize L.early L.late Lg ε ↔
      (∀ n, L.late = some n → 0 < n ∧ RoundSplits.LocalTo n Z.Q.loc.shape Z.Q.ann) ∧
        ∃ State, StLaws Z State Lg ∧ Joint Z ε State :=
  ⟨fun ⟨h0, State, h1, h2, h3, h4, h5⟩ => ⟨h0, State, ⟨h1, h2, h3, h4⟩, h5⟩,
   fun ⟨h0, State, ⟨h1, h2, h3, h4⟩, h5⟩ => ⟨h0, State, h1, h2, h3, h4, h5⟩⟩

/-- The named set of bad traces of a written batch protocol: the two clashes of `linkBad`
(OnBytes/Slice/LinkClause.lean, over the library), and a lucky step of the written protocol under
the given state function. What the docstring of `plainBad` (OnBytes/TypedOracleCompiler/Slice/PlainClause.lean) says
of how symbols, plain parts and the external string are read holds here for each of a round's two
components; in the joining round the slot's component stands in the query to g. A step is judged by
the state function of the instance that the query's own chain has taken in (the sibling's `lastX`);
at a shared query it is a step if the answer turns the state of SOME slot whose value the trace
determines under the request root. So the set also hangs on entries at the oracles g, rleaf and
rnode. -/
def batBad {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE) (ε : Err Z.Q.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → X → PTr Z.Q.loc.shape → Bool) : Tc W → Prop :=
  fun tr => (EM tr ∨ EF tr) ∨ StepEvent (Z.lane R ε State).step tr

/-- The compiler's conclusion on an accepted string of one slot of a written batch protocol, for the
reading R and the language Lg: the four clauses of `PlainAt`, with an instance. The third is for
strings whose external openings R keeps; that is asked of all external openings that the string
holds, also at positions that Q does not read. -/
def BatchAt {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤
        (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cm x π, ¬ Bad tr → (∀ p op, π.ext p = some op → R.keeps p op.sym op.salt) →
      RunsIn tr (Z.verifier cm x π) true → Lg x (R.at W tr cm)) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm →
      R.at W tr cm = R.at W (tr ++ tr') cm)

section
variable {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE) (ε : Err Z.Q.loc.shape)
  (State : (Fin L.wordLength → L.Symbol) → X → PTr Z.Q.loc.shape → Bool)

/-- Under the typed random oracles the named set is reached with small probability: at most t e
+ 2 t^2 / 2^lam by an algorithm with at most t queries, if every error count is at most the share e
of its round's verifier messages, the state function obeys the law on verifier messages at these
counts, `Z.OK` holds (of it the laws of the rounds' wiring are used), and there are as many slots
as the request tree at Z's tag has leaves. -/
theorem batBad_rare (εs : ℝ≥0∞) (hb : Err.Below ε εs) (hJ : Joint Z ε State) (hZ : Z.OK)
    (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | batBad Z R ε State o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have oZ : (Z.lane R ε State).OK L.maxBatchSize := laneOf_ok hZ.wire.sh hJ
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K L) (Z.lane R ε State).step (fun _ => εs)
    (fun pre e he hs => hs.1 he)
    (fun pre o q _ => by
      by_cases ho : o = OracleName.fb Z.t
      · subst ho
        exact Lane.pr_step_le (Z.lane R ε State) hN oZ hb pre q
      · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
        rintro r - hr
        exact ho (Lane.step_oracle hr)) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc pr A.withTrace.law {o | (EM o.2 ∨ EF o.2) ∨ StepEvent (Z.lane R ε State).step o.2}
      ≤ pr A.withTrace.law {o | EM o.2 ∨ EF o.2}
        + pr A.withTrace.law {o | StepEvent (Z.lane R ε State).step o.2} := pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ = (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := add_comm _ _

/-- The named set is closed under appending queries. -/
theorem batBad_mono (tr tr' : Tc W) (h : batBad Z R ε State tr) :
    batBad Z R ε State (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- Outside the named set an accepted string whose external openings R keeps means that the
language holds of the instance and the string that R reads off the trace under the root, if the
state function that the set is made from has the laws `StLaws` for the language and `Z.OK` holds. It
says something only together with `batBad_rare` at the same state function and counts and a small e.
-/
theorem batBad_lang (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (hS : StLaws Z State Lg) (hZ : Z.OK)
    (tr : Tc W) (cm : Dig lam) (x : X) (π : OneProtocolProof lam Z.Q) (hB : ¬ batBad Z R ε State tr)
    (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt)
    (hrun : RunsIn tr (Z.verifier cm x π) true) : Lg x (R.at W tr cm) := by
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  exact accepted_at Z.t Z.Q Z.wq Z.embS Z.embP some W.embE hZ.wire hZ.loc hZ.coh
    (Lg := Lg) State Z.prjS hZ.backS Z.prjP hZ.backP id
    (fun tr cms => R.at W tr (cms.getD 0 default)) ε hM (fun h => hB (Or.inl (Or.inr h)))
    (fun h => hB (Or.inr h)) [cm] x π (instB L x) (instX_some L x) (fun n hn _ => hZ.late n hn)
    (fun y hL => by rw [instB_zero hZ.late]; exact hS.start y x hL)
    (fun y τ m hL h => by
      rcases instB_step hZ.late x τ.idx with h1 | ⟨h1, h2, h3⟩
      · rw [h1] at h; exact hS.prover y _ τ m h
      · rw [h2] at h; rw [h3]; exact hS.prover y x τ m (hS.switch y x τ hL h1 h))
    (fun y τ hL h => hS.full y x τ hL (by rw [← instB_last hZ.late]; exact h)) hrun
    (fun pre q a post htr hocc => R.at_before htr hM (hocc _ (by simp)))
    (fun p op hop h => by
      rw [hZ.extDepth, (hZ.ext p).1, (hZ.ext p).2] at h
      exact R.law _ p op.sym op.salt h (hk p op hop))

/-- If the longer trace is outside the named set, what is read off under a root that was announced
in the shorter one does not change. -/
theorem batBad_stable (tr tr' : Tc W) (cm : Dig lam) (hB : ¬ batBad Z R ε State (tr ++ tr'))
    (hann : Announced W tr cm) : R.at W tr cm = R.at W (tr ++ tr') cm :=
  R.at_stable (fun h => hB (Or.inl (Or.inl h))) (List.prefix_append _ _)
    (occursIn_of_announced hann)

end

/-- A state function with the laws for a language gives the compiler's conclusion for that
language and that reading: from `StLaws`, `Joint`, every error at most e, `Z.OK`, and as many
slots as the request tree at Z's tag has leaves. The set is `batBad`. -/
theorem batchAt {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (ε : Err Z.Q.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → X → PTr Z.Q.loc.shape → Bool) (hb : Err.Below ε εs)
    (hJ : Joint Z ε State) (hS : StLaws Z State Lg) (hZ : Z.OK) (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) :
    BatchAt Z R Lg εs := by
  refine ⟨batBad Z R ε State, fun β A t hA => ?_, batBad_mono Z R ε State,
    fun tr cm x π hB hk => batBad_lang Z R ε State Lg hS hZ tr cm x π hB hk,
    batBad_stable Z R ε State⟩
  refine (batBad_rare Z R ε State εs hb hJ hZ hN β A t hA).trans ?_
  gcongr
  exact Nat.le_succ t

/-! ## The strict format -/

/-- The compiled verifier of one slot of a written batch protocol with the strict format: the
sibling's `verifyOneProtocol`. -/
noncomputable def WrittenB.verifierS {W : QueryLayout lam L} (Z : WrittenB W) (sMT sFS : ℕ)
    (cm : Dig lam) (x : X) (π : OneProtocolProof lam Z.Q) : TypedOracleComputation lam W.K L Bool :=
  verifyOneProtocol sMT sFS Z.t Z.Q Z.wq Z.embS Z.embP some W.embE (W.dReq Z.t) [cm] x π

/-- `batBad_lang` for the verifier with the strict format. -/
theorem batBad_langS {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (ε : Err Z.Q.loc.shape) (State : (Fin L.wordLength → L.Symbol) → X → PTr Z.Q.loc.shape → Bool)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (hS : StLaws Z State Lg) (hZ : Z.OK) (sMT sFS : ℕ)
    (tr : Tc W) (cm : Dig lam) (x : X) (π : OneProtocolProof lam Z.Q) (hB : ¬ batBad Z R ε State tr)
    (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt)
    (hrun : RunsIn tr (Z.verifierS sMT sFS cm x π) true) : Lg x (R.at W tr cm) := by
  obtain ⟨P1, P2, h⟩ := runsIn_verifyB_of_strict hZ.wire hrun
  exact batBad_lang Z R ε State Lg hS hZ tr cm x (π.withPaths P1 P2) hB
    (keeps_withPaths R π P1 P2 hk) h

end TypedOracleCompiler.Slice
