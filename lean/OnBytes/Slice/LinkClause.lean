-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkClause.lean: what the compiler gives for an accepted Link string, for any language
of pairs of strings.

The library's theorem on the compiled argument (`Compile.Batch.bcsSoundBatchK`) asks soundness of
all three protocols of an interface, each for a language that is written with the interface's own
decoder. At an entry file only the Link protocol is run. This file states and proves the part of
that theorem that speaks of Link, and for every language Lg of pairs of strings for which Link is
round-by-round sound. The interface's decoder plays no part in it.

What is asked. Of Link: round-by-round soundness for Lg with every error at most e, and that its
verifier is local (it depends on the oracles only at the positions that it reads). Of the wiring:
the library's laws of a wiring. Of the two other protocols: error lists with every error at most e,
and for Batch a state function that obeys the law on verifier messages. The last are needed because
all three protocols share the random oracles, so the set of bad traces has a part for each. Nothing
is asked on what the two other protocols prove.

Main definition: `linkBad`, the named set of bad traces: a clash in a hash tree, a clash in a chain,
or a lucky step (its docstring says what each is). On that set: `linkBad_rare`, `linkBad_mono`,
`linkBad_lang`, `linkBad_stable`: the four clauses below, of that set, the first with the bound
t * e + 2 t^2 / 2^lam.

Second definition: `LinkAt W Lg e`, the same with the set hidden, for use in one world, where the
bound on Bad and the run stand under the same random oracles (OnBytes/Slice/Experiment.lean:
`link_experiment`). For a run under one fixed family of oracle functions, such as BLAKE2b's, the
form with "there is" would be true for free: nothing would forbid a Bad that holds every trace with
that family's answers. There the named set must be used (`linkBad_run`,
OnBytes/Slice/Experiment.lean).
`LinkAt W Lg e`: there is an event Bad on traces such that
 1. every algorithm with at most t queries reaches Bad with probability at most
    t * e + 2 (t + 1)^2 / 2^lam;
 2. Bad is closed under appending queries;
 3. outside Bad, if the compiled Link verifier accepts a string under the roots cm and cm' and all
    its queries are in the trace, then the pair of strings that is read off the trace under the two
    roots is in Lg;
 4. outside Bad, what is read off the trace under an announced root never changes.
Main theorem: `linkAt`.

Not claimed. Nothing on Test or Batch. The bound says nothing once it reaches 1. The oracles are the
typed random oracles of the library's compiler.
The proof follows the library's own proof of `bcsSoundBatchK`, with the language set free.
-/
import CompileK.KnowSound

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The compiler's conclusion on an accepted Link string, for the language Lg. -/
def LinkAt (W : QueryLayout lam L) (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤
        (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cm cm' π, ¬ Bad tr → RunsIn tr (vL W cm cm' π) true →
      Lg () (extEnc W tr cm, extEnc W tr cm')) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm →
      extEnc W tr cm = extEnc W (tr ++ tr') cm)

/-- **The named set of bad traces.** A trace is a list of queries to the typed oracles with their
answers, in the order in which they were asked. It is bad if it shows one of three events.
 1. A clash in a hash tree (the library's `EM`): the answer of a new query to a leaf or node oracle
    occurs at an earlier entry of the trace.
 2. A clash in a chain (the library's `EF`): the link value in the answer of a new query to a
    round's challenge oracle, or to the oracle g, is the link value or a chain field of an earlier
    such query, or the input of an earlier query to the leaf oracle of request trees.
 3. A lucky step (the library's `StepEvent` of `stepS`): a new query to a round's challenge oracle
    that is rooted in the trace, whose answer turns the round-by-round state of its transcript from
    "the prover has lost" to "the prover has not lost". The state is the library's `stOf`: lost in
    the sense of round-by-round soundness with the error counts εT, εL (for Test and Link), and
    the given state function for Batch. All three protocols share the oracles, so each has a part.
An entry is "new" if the same query with the same answer does not stand earlier in the list. For the
first event there occur: at a query to a leaf oracle its answer; at a query to a node oracle its
answer and the two halves of its input; at a challenge query its root fields (its own root, and the
outer or request roots that stand in its head); at a query to g its root field; at an entry of the
marker oracle `ann` its digest. A challenge query is "rooted" if the list before it holds the chain
of challenge queries that leads to it from a first query, which names the roots. Its transcript:
each round's prover message is the plain part that stands in that round's query and, under the
query's root field, the symbols that the list before the new query determines, zeros elsewhere; each
earlier verifier message is made from that round's answer. The state is judged for the strings that
are read off the list before the query, under these roots.
Each event is a property of the list alone. The two clashes can be read off it. The lucky step is
fixed by the list too, but through "lost", which speaks of all continuations of a transcript. -/
def linkBad (W : QueryLayout lam L) (εT : Err L.offline.shape) (εL : Err L.link.shape)
    (εB : Err L.onlineBatch.loc.shape) (State : (Fin L.wordLength → L.Symbol) → X → PTr L.onlineBatch.loc.shape → Bool) :
    Tc W → Prop :=
  fun tr => (EM tr ∨ EF tr) ∨
    StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) tr

section
variable (W : QueryLayout lam L) (εT : Err L.offline.shape) (εL : Err L.link.shape)
  (εB : Err L.onlineBatch.loc.shape) (State : (Fin L.wordLength → L.Symbol) → X → PTr L.onlineBatch.loc.shape → Bool)

/-- **Under the typed random oracles the named set is reached with small probability**: at most
t e + 2 t^2 / 2^lam by an algorithm with at most t queries, if every error count is at most the
share e of its round's verifier messages. -/
theorem linkBad_rare (εs : ℝ≥0∞) (hbT : Err.Below εT εs) (hbL : Err.Below εL εs)
    (hbB : Err.Below εB εs)
    (hB4 : ∀ y (x : Fin L.maxBatchSize → Option X),
      JointLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB fun j => (x j).map (State y))
    (hW : W.OKG) (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | linkBad W εT εL εB State o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have oT : (laneT W εT).OK L.maxBatchSize := laneOf_ok hW.T.sh (stOf_joint L.offline εT L.maxBatchSize)
  have oL : (laneL W εL).OK L.maxBatchSize := laneOf_ok hW.Lk.sh (stOf_joint L.link εL L.maxBatchSize)
  have oB : (laneB W εB State).OK L.maxBatchSize := laneOf_ok hW.B.sh hB4
  have h := pr_stepEvent_le (S := spec lam W.K L)
    (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) (fun _ => εs)
    (fun pre e he hs => hs.elim (fun h1 => h1.1 he) fun h1 =>
      h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
    (fun pre o q _ => pr_stepS_le rfl rfl rfl hW.slots oT oL oB hbT hbL hbB pre o q) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc pr A.withTrace.law {o | (EM o.2 ∨ EF o.2) ∨
          StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) o.2}
      ≤ pr A.withTrace.law {o | EM o.2 ∨ EF o.2}
        + pr A.withTrace.law
            {o | StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) o.2} :=
        pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ = (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := add_comm _ _

/-- **The named set is closed under appending queries.** -/
theorem linkBad_mono (tr tr' : Tc W) (h : linkBad W εT εL εB State tr) :
    linkBad W εT εL εB State (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- **Outside the named set an accepted Link string means that the language holds** of the two
strings that are read off the trace under the two roots, if Link is round-by-round sound for the
language with the error counts εL that the set is made from. It says something only together with
`linkBad_rare` at the same counts and a small e: with counts as large as the rounds' numbers of
verifier messages, soundness holds for every language, every position before the end is lost, and
every trace with an accepted run's queries is bad. -/
theorem linkBad_lang (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (hsL : L.link.Sound Lg εL)
    (hlL : L.link.IsLocal) (hW : W.OKG) (tr : Tc W) (cm cm' : Dig lam)
    (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) (hB : ¬ linkBad W εT εL εB State tr)
    (hrun : RunsIn tr (vL W cm cm' π) true) : Lg () (extEnc W tr cm, extEnc W tr cm') := by
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  exact mem_of_accepted Tag.link (BatchInteractiveOracleProof.ofProto L.link) W.Lk _ id (fun _ => none)
    (fun s => some (.inl s)) hW.Lk hlL (Iop.BatchOne.BAnn.allLocal_coherent _) (Lg := Lg)
    (stOf L.link εL) (prjSym Tag.link) (fun p a => prjSym_emb Tag.link p a) some (fun _ => rfl)
    (fun _ => some ())
    (fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default))) εL hM
    (fun h => hB (Or.inl (Or.inr h)))
    (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inr (Or.inl h2)⟩))
    [cm, cm'] () π (fun _ => ()) (fun _ => rfl) (fun _ _ h => absurd rfl h)
    (fun y hL => stOf_start hsL y () hL) (fun y τ m _ h => stOf_prover y () τ m h)
    (fun y τ _ h => stOf_full y () τ h) hrun
    (fun pre q a post htr hocc =>
      Prod.ext (extEnc_before htr hM (hocc _ (by simp)))
        (extEnc_before htr hM (hocc _ (by simp))))
    (fun p a sl h => by
      rw [hW.extDepth.2.1] at h
      cases p with
      | inl p =>
        rw [(hW.extL.1 p).1, (hW.extL.1 p).2] at h
        exact extEnc_apply hW h
      | inr p =>
        rw [(hW.extL.2 p).1, (hW.extL.2 p).2] at h
        exact extEnc_apply hW h)

/-- If the longer trace is outside the named set, what is read off under a root that was announced
in the shorter one does not change. A root is announced in a trace that holds an entry of the marker
oracle `ann` for it, which the verifier never asks and which stands for no hash call. -/
theorem linkBad_stable (tr tr' : Tc W) (cm : Dig lam)
    (hB : ¬ linkBad W εT εL εB State (tr ++ tr')) (hann : Announced W tr cm) :
    extEnc W tr cm = extEnc W (tr ++ tr') cm :=
  extEnc_stable (fun h => hB (Or.inl (Or.inl h))) (List.prefix_append _ _)
    (occursIn_of_announced hann)

end

/-- **Round-by-round soundness of Link for a language gives the compiler's conclusion for that
language.** The set is `linkBad`. -/
theorem linkAt (W : QueryLayout lam L) (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → X → PTr L.onlineBatch.loc.shape → Bool)
    (hbT : Err.Below εT εs) (hbL : Err.Below εL εs) (hbB : Err.Below εB εs)
    (hB4 : ∀ y (x : Fin L.maxBatchSize → Option X),
      JointLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB fun j => (x j).map (State y))
    (hsL : L.link.Sound Lg εL) (hlL : L.link.IsLocal) (hW : W.OKG) : LinkAt W Lg εs := by
  refine ⟨linkBad W εT εL εB State, fun β A t hA => ?_, linkBad_mono W εT εL εB State,
    fun tr cm cm' π => linkBad_lang W εT εL εB State Lg hsL hlL hW tr cm cm' π,
    linkBad_stable W εT εL εB State⟩
  refine (linkBad_rare W εT εL εB State εs hbT hbL hbB hB4 hW β A t hA).trans ?_
  gcongr
  exact Nat.le_succ t

end OnBytes.Slice

#print axioms OnBytes.Slice.linkBad_rare
#print axioms OnBytes.Slice.linkBad_mono
#print axioms OnBytes.Slice.linkBad_lang
#print axioms OnBytes.Slice.linkBad_stable
#print axioms OnBytes.Slice.linkAt
