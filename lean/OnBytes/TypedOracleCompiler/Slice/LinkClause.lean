-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/LinkClause.lean: what the sibling's compiler gives for an accepted Link string,
for any language of pairs of strings; and the sibling's compiled Link verifier as a judge. General
in the wiring. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with;
it builds on definitions of Compile/.

After OnBytes/Slice/LinkClause.lean (its seven declarations), `vL_of_vLS` and `LinkOut` of
OnBytes/Slice/Experiment.lean, `judgeL` and `judgeAt_L` of OnBytes/Slice/JudgeLink.lean. `BatchProtocolWithLeafBody`,
`QueryLayout`, `TypedOracleComputation`, `Tc`, `vL`, `vLS`, `extEnc`, `EM`, `EF`, `stepS`, `stOf`, `tVQB` are the sibling's
here: a list of roots a query; the type of leaves' bodies is a field of the interface, and the
wiring says how symbols are written into bodies and read back. `Judge`, `JudgeAt` and `Reading` are
those of OnBytes/TypedOracleCompiler/Slice/OneWorldJ.lean and Reading.lean.

AS TEXT (9). `LinkAt`, `linkBad`, `linkBad_rare`, `linkBad_mono`, `linkBad_stable`, `linkAt`,
`vL_of_vLS`, `LinkOut`, `judgeAt_L`. Of the docstrings two are turned: in `linkBad`'s and `judgeL`'s
"the library's" became "the sibling's", and `linkBad`'s says of a query's roots what holds over the
sibling: a list, of which the first two count.
TURNED (2).
 `linkBad_lang`     two arguments of `mem_of_accepted`: the embedding of external symbols is
                    `W.embE`, where the original writes the library's tagged body; the reading back
                    of Link's symbols is `W.prjL` with `hW.prjL_emb`, where the original has `prjSym
                    Tag.link`. As in the sibling's own Compile/Batch/Sound.lean.
 `judgeL`           the reading `Reading.wide` takes one law more: `hW.prjE_emb`.
NEW: none. NO COUNTERPART: none.

What is asked, and the four clauses of `LinkAt`, are the original's: see its head. `LinkAt` has its
set of traces under "there is": it is for use in one world, where the bound on the set and the run
stand under the same random oracles; for a run under one fixed family the named set `linkBad` must
be used.

WHAT IS NOT SAID. That any interface's Link is round-by-round sound: a hypothesis. That any wiring
has the laws `OKG`. Nothing on Test or Batch. The bound says nothing once it reaches 1. The oracles
are the typed random oracles of the sibling's compiler. No part, no implementation by one oracle, no
checker.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Sound
import OnBytes.TypedOracleCompiler.Compile.Batch.ForestSound
import OnBytes.TypedOracleCompiler.Compile.Batch.GlueTools
import OnBytes.TypedOracleCompiler.Compile.Batch.TVQB
import OnBytes.TypedOracleCompiler.Slice.OneWorldJ

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

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

/-- The named set of bad traces. A trace is a list of queries to the typed oracles with their
answers, in the order in which they were asked. It is bad if it shows one of three events.
 1. A clash in a hash tree (the sibling's `EM`): the answer of a new query to a leaf or node oracle
    occurs at an earlier entry of the trace.
 2. A clash in a chain (the sibling's `EF`): the link value in the answer of a new query to a
    round's challenge oracle, or to the oracle g, is the link value or a chain field of an earlier
    such query, or the input of an earlier query to the leaf oracle of request trees.
 3. A lucky step (the library's `StepEvent` of `stepS`): a new query to a round's challenge oracle
    that is rooted in the trace, whose answer turns the round-by-round state of its transcript from
    "the prover has lost" to "the prover has not lost". The state is the sibling's `stOf`: lost in
    the sense of round-by-round soundness with the error counts εT, εL (for Test and Link), and
    the given state function for Batch. All three protocols share the oracles, so each has a part.
An entry is "new" if the same query with the same answer does not stand earlier in the list. For the
first event there occur: at a query to a leaf oracle its answer; at a query to a node oracle its
answer and the two halves of its input; at a challenge query its root fields (the first two of its
own list of roots, and the outer or request roots that stand in its head); at a query to g the first
two of its roots; at an entry of the marker oracle `ann` its digest. A challenge query is "rooted"
if the list before it holds the chain of challenge queries that leads to it from a first query,
which names the roots. Its transcript: each round's prover message is the plain part that stands in
that round's query and, under the query's roots, the symbols that the list before the new query
determines, zeros elsewhere; each earlier verifier message is made from that round's answer. The
state is judged for the strings that are read off the list before the query, under these roots.
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

/-- Under the typed random oracles the named set is reached with small probability: at most
t e + 2 t^2 / 2^lam by an algorithm with at most t queries, if every error count is at most the
share e of its round's verifier messages. -/
theorem linkBad_rare (εs : ℝ≥0∞) (hbT : Err.Below εT εs) (hbL : Err.Below εL εs)
    (hbB : Err.Below εB εs)
    (hB4 : ∀ y (x : Fin L.maxBatchSize → Option X),
      JointLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB fun j => (x j).map (State y))
    (hW : W.OKG) (haT : L.annT = RoundSplits.allLocal L.offline.shape)
    (haL : L.annL = RoundSplits.allLocal L.link.shape) (β : Type) (A : TypedOracleComputation lam W.K L β) (t : ℕ)
    (hA : A.QueryBound t) :
    pr A.withTrace.law {o | linkBad W εT εL εB State o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have jT : ∀ y (x : Fin (2 ^ W.depthReqT) → Option Unit),
      JointLaw (2 ^ W.depthReqT) L.offline.shape L.annT εT fun j => (x j).map (stOf L.offline εT y) := by
    rw [haT]; exact stOf_joint L.offline εT _
  have jL : ∀ y (x : Fin (2 ^ W.depthReqL) → Option Unit),
      JointLaw (2 ^ W.depthReqL) L.link.shape L.annL εL fun j => (x j).map (stOf L.link εL y) := by
    rw [haL]; exact stOf_joint L.link εL _
  have oT : (laneT W εT).OK (2 ^ W.depthReqT) := laneOf_ok hW.T.sh jT
  have oL : (laneL W εL).OK (2 ^ W.depthReqL) := laneOf_ok hW.Lk.sh jL
  have oB : (laneB W εB State).OK L.maxBatchSize := laneOf_ok hW.B.sh hB4
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K L)
    (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) (fun _ => εs)
    (fun pre e he hs => hs.elim (fun h1 => h1.1 he) fun h1 =>
      h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
    (fun pre o q _ => pr_stepS_le rfl rfl rfl rfl rfl hW.slots oT oL oB hbT hbL hbB pre o q) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc pr A.withTrace.law {o | (EM o.2 ∨ EF o.2) ∨
          StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) o.2}
      ≤ pr A.withTrace.law {o | EM o.2 ∨ EF o.2}
        + pr A.withTrace.law
            {o | StepEvent (stepS W (laneT W εT) (laneL W εL) (laneB W εB State)) o.2} :=
        pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ = (t : ℝ≥0∞) * εs + 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := add_comm _ _

/-- The named set is closed under appending queries. -/
theorem linkBad_mono (tr tr' : Tc W) (h : linkBad W εT εL εB State tr) :
    linkBad W εT εL εB State (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- Outside the named set an accepted Link string means that the language holds of the two
strings that are read off the trace under the two roots, if Link is round-by-round sound for the
language with the error counts εL that the set is made from. It says something only together with
`linkBad_rare` at the same counts and a small e: with counts as large as the rounds' numbers of
verifier messages, soundness holds for every language, every position before the end is lost, and
every trace with an accepted run's queries is bad. -/
theorem linkBad_lang (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (hsL : L.link.Sound Lg εL)
    (hlL : L.link.IsLocal) (hW : W.OKG) (haL : L.annL = RoundSplits.allLocal L.link.shape) (tr : Tc W)
    (cm cm' : Dig lam) (π : OneProtocolProof lam L.batL) (hB : ¬ linkBad W εT εL εB State tr)
    (hrun : RunsIn tr (vL W cm cm' π) true) : Lg () (extEnc W tr cm, extEnc W tr cm') := by
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  have cL : L.annL.Coherent := by rw [haL]; exact Iop.BatchOne.BAnn.allLocal_coherent _
  exact mem_of_accepted Tag.link L.batL W.Lk _ id (fun _ => none)
    W.embE hW.Lk hlL cL (Lg := Lg)
    (stOf L.link εL) W.prjL hW.prjL_emb some (fun _ => rfl)
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

/-- Round-by-round soundness of Link for a language gives the compiler's conclusion for that
language. The set is `linkBad`. -/
theorem linkAt (W : QueryLayout lam L) (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → X → PTr L.onlineBatch.loc.shape → Bool)
    (hbT : Err.Below εT εs) (hbL : Err.Below εL εs) (hbB : Err.Below εB εs)
    (hB4 : ∀ y (x : Fin L.maxBatchSize → Option X),
      JointLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB fun j => (x j).map (State y))
    (hsL : L.link.Sound Lg εL) (hlL : L.link.IsLocal) (hW : W.OKG)
    (haT : L.annT = RoundSplits.allLocal L.offline.shape) (haL : L.annL = RoundSplits.allLocal L.link.shape) :
    LinkAt W Lg εs := by
  refine ⟨linkBad W εT εL εB State, fun β A t hA => ?_, linkBad_mono W εT εL εB State,
    fun tr cm cm' π => linkBad_lang W εT εL εB State Lg hsL hlL hW haL tr cm cm' π,
    linkBad_stable W εT εL εB State⟩
  refine (linkBad_rare W εT εL εB State εs hbT hbL hbB hB4 hW haT haL β A t hA).trans ?_
  gcongr
  exact Nat.le_succ t

/-! ## The strict format, and what a maker puts out -/

/-- What the Link verifier with the strict format accepts, the plain Link verifier accepts on a
string with other paths, within the same trace. -/
theorem vL_of_vLS (W : QueryLayout lam L) (hW : W.OKG) {sMT sFS : ℕ} {cm cm' : Dig lam}
    {π : OneProtocolProof lam L.batL} {tr : Tc W}
    (h : RunsIn tr (vLS W sMT sFS cm cm' π) true) : ∃ π', RunsIn tr (vL W cm cm' π') true :=
  let ⟨P1, P2, h'⟩ := runsIn_verifyB_of_strict hW.Lk h
  ⟨π.withPaths P1 P2, h'⟩

/-- What a cheating maker of a Link string puts out: two roots and the string. -/
abbrev LinkOut (lam : ℕ) (L : BatchProtocolWithLeafBody I X) : Type :=
  Dig lam × Dig lam × OneProtocolProof lam L.batL

/-! ## The compiled Link verifier as a judge -/

/-- The sibling's compiled Link verifier as a judge, at the sibling's own reading. Its language
holds for free of a list of other than two strings; the list of roots always has two. -/
def judgeL (W : QueryLayout lam L) (hW : W.OKG) (sMT sFS : ℕ)
    (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) : Judge W (LinkOut lam L) where
  run := fun o => vLS W sMT sFS o.1 o.2.1 o.2.2
  tV := tVQB W.Lk W.depthReqL
  bound := fun o => detBound_vLS W sMT sFS o.1 o.2.1 o.2.2
  roots := fun o => [o.1, o.2.1]
  R := Reading.wide hW.B.ext hW.prjE_emb
  Lang := fun _ ys => ∀ y₀ y₁, ys = [y₀, y₁] → Lg () (y₀, y₁)
  ok := fun _ => True

/-- The compiler's conclusion on an accepted Link string is the judge's. -/
theorem judgeAt_L (W : QueryLayout lam L) (hW : W.OKG) (sMT sFS : ℕ)
    (Lg : Unit → (twoExternalStrings L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (h : LinkAt W Lg εs) :
    JudgeAt W (judgeL W hW sMT sFS Lg) εs := by
  obtain ⟨Bad, hrare, hmono, hL, hst⟩ := h
  refine ⟨Bad, hrare, hmono, fun tr o hnb _ hrun y₀ y₁ hy => ?_, fun tr tr' cm hnb ha => ?_⟩
  · obtain ⟨π', hπ'⟩ := vL_of_vLS W hW hrun
    have h2 := hL tr o.1 o.2.1 π' hnb hπ'
    have e : [extEnc W tr o.1, extEnc W tr o.2.1] = [y₀, y₁] := hy
    obtain ⟨e0, e1⟩ := List.cons.inj e
    obtain ⟨e1', -⟩ := List.cons.inj e1
    rw [← e0, ← e1']
    exact h2
  · exact hst tr tr' cm hnb ha

end TypedOracleCompiler.Slice
