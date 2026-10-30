-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/PublicRead/Spec.lean: A SCHEME WHOSE LETTERS ARE READ OFF THE HASH FUNCTION: index privacy and
completeness of the scheme "read d, then run the scheme at d", from the same properties of each
scheme at a fixed d. DEFINITIONS, SIX STATEMENTS, each a Prop under a name, with NO PROOF HERE, and
five small lemmas with their proofs. The six are proved in ZKCP/PublicRead/Complete.lean (the law of
the reading, the measure's side, completeness) and ZKCP/PublicRead/Privacy.lean (index privacy).

General definitions and statements, over one hash function, for schemes that serve batches
(ZKCP/Gen.lean). This file states no goal of the release.

Why. A theorem on a scheme speaks of letters that are fixed before the hash function is drawn. A
verifier may first ask the hash function at public strings (a public reading, which gives a value d)
and then run at letters made of d. For soundness the library crosses that step by pub_lift
(Johnson/TypedOracleCompiler/RecCompile/PublicLift.lean). Here the like is stated for index privacy and for
completeness.

  glueArg Pub A   the scheme: the committer reads d and commits at d; the prover's key keeps d; the
                  verifier reads d for itself.
  runPub          the public reading with a fresh uniform answer at each query; it keeps the list of
                  (string, answer).
  glueSim Pub Sm  the simulator: it makes the public reading's answers itself (runPub) and keeps the
                  list; it answers a string of that list from the list, and hands every other query,
                  and every batch, to the simulator at d.
  ConsistentOn    the second clause of index privacy on a range, alone.
  Spec.reading_law    the simulator's own draw of d has the law of the real d.
  Spec.measure_pub    a quantity that hangs on d and on the hash function, but not on the function's
                  values at public strings, and whose average is at most B at each fixed d, has an
                  average of at most B at the d that is read off the function.
  Spec.complete_pub   completeness passes to glueArg, at the same error.
  Spec.privacy_pub    index privacy on a range passes to glueArg with glueSim, at the same bound.
  Spec.complete_pub_on, Spec.privacy_pub_on   the same where the property is known at the d of a set
                  Dok alone: the probability β that the real reading gives a d outside Dok is added.
                  The forms without _on are these at Dok := all, β := 0 (privacy_pub_of_on,
                  ZKCP/PublicRead/Privacy.lean; complete_pub, ZKCP/PublicRead/Complete.lean).
  commit_at, verify_at   under each fixed hash function g the committer of glueArg commits, and its
                  verifier verifies, at the one value Pub.det g.
  glueArg_pure_C, glueArg_pure_V, glueArg_P   glueArg at a reading that asks nothing; its prover.

FIVE THINGS THAT THE FORM OF THE STATEMENTS HOLDS.
  (1) One simulator, before the index: Sm is a function of d that is an argument, glueSim Pub Sm is
      one term, and in PrivacyOn the simulator stands outside "for every index".
  (2) The environment is a function of the adversary's view (Gen.ViewEnv): it asks no oracle. What
      it sees of the public strings is what the adversary was answered, from the list. An
      environment with access of its own to the hash function is modelled nowhere in the library,
      and nothing here covers one.
  (3) The reading may be adaptive: a later string may hang on an earlier answer. NoRepeat says that
      the strings of one run are pairwise different; Pt holds at least the strings of all runs; the
      honest side at d is asked to keep off ALL of Pt, at every d.
  (4) One bound for all d. Where a premise fails at some d, the forms _on set these d aside, and
      their probability is a number in the bound.
  (5) In glueArg d hangs on the hash function alone, not on the index or on a coin: Pub is a letter
      outside the index, it has no coins, and commit_at says what the committer does with it. That
      holds by construction of glueArg. It says nothing on public files (this file has none) or on
      any other committer. What lets the simulator draw d without the index is Spec.reading_law.

WHAT IS ASKED. Of the reading: no coins; strings of a set Pt alone; none twice. Of the schemes, at
EVERY d of the type D, reached by the reading or not (in the forms _on: at every d of Dok): the
property itself, with one bound for all d; and that the committer and the prover (for completeness:
the verifier too) ask no string of Pt.
OF THE SIMULATORS NOTHING IS ASKED BEYOND THE PROPERTY (in Spec.privacy_pub_on: beyond the property
at the d of Dok and its second clause at the other d): the simulator at d is never asked at a string
of the list. Why that is enough: THE PREMISE AT d IS USED AT ADVERSARIES THAT ARE WIRED AT ARBITRARY
CONSTANTS. The wired adversary carries the list's answers as numbers of its own, whatever the
simulator's own table would say at these strings. So a simulator whose key or proofs are right only
at its own answer at a public string is shut out by the premise at d already. And glueSim's answer
at a listed string returns the state untouched: against glueSim the adversary IS the wired adversary
against the simulator at d, step for step.

THE PREMISE ON THE COMMITTER IS NEEDED, in two senses.
  The statement is false without it (argued, not typed): a committer at d that publishes the
  function's answer at a public string has a simulator at each fixed d, and glueSim fails for the
  glued scheme. There only THIS simulator fails: the glued scheme is still private.
  Privacy itself can be lost wholly (ZKCP/PublicRead/Toy.lean [not in this library]; said here
  without a theorem): a committer at d that asks the public string and publishes the index if the
  answer is d.
NoRepeat is needed too (argued, not typed): a reading that asks one string twice gets one answer
twice from a hash function, and two answers from runPub.

Limits. Statements: their proofs are in the two files named above. One small member of the premises
of Spec.privacy_pub is claimed in ZKCP/PublicRead/Member.lean [not in this library; so here read:
not proved in this library]: there the reading reads, the scheme
hangs on d and the committer hashes, but the key does not hang on the index, so nothing is hidden.
No member is shown in which an index is hidden. What is meant to pay the premises at the release's
verifier: for the reading layoutsByPublicReading_noCoin, layoutsByPublicReading_asks, layoutsByPublicReading_once, and for "asks no public string"
layoutsByPublicReading_spare (Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean) with asksIn_overOne
(Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublicArm.lean) and no_commitW, no_proveW
(Johnson/WholeKey/Work.lean). Johnson/PublicAt/Whole.lean lays the last three together, with the
laws of the reading and the properties at each d as premises. That the release's committer and
prover have glueArg's form is not shown. The public strings are fixed before the hash function is
drawn: a committer that picks its public files with the hash function in hand is not covered. One
run of the committer. The statements are idle at an empty range or a range with one index, at a
bound of 1 or more, and at β ≥ 1; at a reading that asks nothing they say nothing new.
Terms: lean/GLOSSARY.md.

-/
import ZKCP.OnRange
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublic

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace ZKCP.PublicRead
open Rom Prob
open TypedOracleCompiler.Compile.Batch.Cms (NoRepeat)

variable {lam : ℕ} {I X W PP IVK ISK Pf D : Type}

/-- **The scheme "read d, then run the scheme at d".** -/
def glueArg (Pub : Rom.OComp (rom lam) D) (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) :
    Gen.Arg (rom lam) I X W IVK (D × ISK) Pf where
  C := fun i => Pub.bind fun d => ((A d).C i).bind fun k => .pure (k.1, (d, k.2))
  P := fun isk b => (A isk.1).P isk.2 b
  V := fun k x π => Pub.bind fun d => (A d).V k x π

/-- At a reading that asks nothing the verifier is the verifier at d. -/
theorem glueArg_pure_V (d : D) (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) :
    (glueArg (.pure d) A).V = (A d).V := rfl

/-- At a reading that asks nothing the committer is the committer at d, with d laid into the
prover's key. -/
theorem glueArg_pure_C (d : D) (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (i : I) :
    (glueArg (.pure d) A).C i = ((A d).C i).bind fun k => .pure (k.1, (d, k.2)) := rfl

/-- At every reading the prover is the prover at the d that its key keeps. -/
theorem glueArg_P (Pub : Rom.OComp (rom lam) D) (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf)
    (d : D) (isk : ISK) : (glueArg Pub A).P (d, isk) = (A d).P isk := rfl

/-- The strings that a run of the public reading has asked, each with its answer. -/
abbrev Path (lam : ℕ) : Type := List (List Bool × (Fin lam → Bool))

/-- The public reading with a fresh uniform answer at each query; l: what was asked so far. -/
def runPub : Rom.OComp (rom lam) D → Path lam → PMF (D × Path lam)
  | .pure d, l => PMF.pure (d, l)
  | .sample n k, l => (unif (Fin (n + 1))).bind fun x => runPub (k x) l
  | .query _ s k, l => (unif (Fin lam → Bool)).bind fun r =>
      runPub (k r) (l ++ [((show List Bool from s), r)])

/-- **The simulator.** Its state: d, the list, the state of the simulator at d. -/
def glueSim (Pub : Rom.OComp (rom lam) D) (Sm : D → Gen.Simulator (rom lam) PP IVK X Pf) :
    Gen.Simulator (rom lam) PP IVK X Pf where
  St := (d : D) × (Path lam × (Sm d).St)
  init := fun pp N => (runPub Pub []).bind fun p =>
    ((Sm p.1).init pp N).map fun o => (o.1, ⟨p.1, p.2, o.2⟩)
  answer := fun st o s =>
    match st.2.1.lookup s with
    | some r => PMF.pure (r, st)
    | none => ((Sm st.1).answer st.2.2 o s).map fun a => (a.1, ⟨st.1, st.2.1, a.2⟩)
  prove := fun st xs => ((Sm st.1).prove st.2.2 xs).map fun a => (a.1, ⟨st.1, st.2.1, a.2⟩)

/-- **Under a fixed hash function the committer commits at the one value that the reading has
there**, whatever the index is. -/
theorem commit_at {Pub : Rom.OComp (rom lam) D} (hc : Pub.NoCoin)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (i : I) (g : Fam (rom lam)) :
    ((glueArg Pub A).C i).runEager g =
      (((A (Pub.det g)).C i).runEager g).map fun k => (k.1, (Pub.det g, k.2)) := by
  show (Pub.bind fun d => ((A d).C i).bind fun k => Rom.OComp.pure (k.1, (d, k.2))).runEager g = _
  rw [hc.runEager_bind, Rom.OComp.runEager_bind]
  rfl

/-- The verifier verifies at the same value. -/
theorem verify_at {Pub : Rom.OComp (rom lam) D} (hc : Pub.NoCoin)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (k : IVK) (x : X) (π : Pf) (g : Fam (rom lam)) :
    ((glueArg Pub A).V k x π).runEager g = ((A (Pub.det g)).V k x π).runEager g :=
  hc.runEager_bind _ g

/-- The second clause of Gen.PrivacyFor, alone, where Gen.PrivacyOn asks it: at the indices of the
range, valid environments and adversaries with a bound on their queries. -/
def ConsistentOn (R : Gen.RelPair I X W PP) (B : ℕ) (Sim : Gen.Simulator (rom lam) PP IVK X Pf)
    (ok : I → Prop) : Prop :=
  ∀ i, ok i → ∀ Z : Gen.ViewEnv (rom lam) IVK X W Pf, Z.IsValid R B i →
    ∀ (tV : ℕ) (Vt : IVK → Gen.AdvVerifier (rom lam) X Pf) (N : ℕ),
      (∀ ivk, (Vt ivk).QueryBound tV) →
      pr (Gen.idealExp R Sim Vt Z i N) {v | ¬ Gen.TraceConsistent v.trace} = 0

namespace Spec

/-- **The simulator's own draw of d has the law of the real d**: the value that the reading gets
from a uniformly drawn hash function. -/
def reading_law : Prop :=
  ∀ (lam : ℕ) (D : Type) (Pub : Rom.OComp (rom lam) D), Pub.NoCoin → NoRepeat Pub →
    ∀ E : Set D, Rom.Pr Pub (fun _ => E) = pr (runPub Pub []) {p | p.1 ∈ E}

/-- **The measure's side.** -/
def measure_pub : Prop :=
  ∀ (lam : ℕ) (D : Type) (Pt : List Bool → Prop) (F : D → Fam (rom lam) → ℝ≥0∞) (B : ℝ≥0∞),
    (∀ d, Measurable (F d)) →
    (∀ d g s r, Pt s → F d (g.set () s r) = F d g) →
    (∀ d, ∫⁻ g, F d g ∂(Rom.U (rom lam)) ≤ B) →
    ∀ Pub : Rom.OComp (rom lam) D, Pub.NoCoin → (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
      ∫⁻ g, F (Pub.det g) g ∂(Rom.U (rom lam)) ≤ B

/-- **Completeness passes to the glued scheme, at the same error.** -/
def complete_pub : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf D : Type) (R : Gen.RelPair I X W PP)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (B : ℕ) (α : ℝ≥0∞) (Pt : List Bool → Prop)
    (Pub : Rom.OComp (rom lam) D),
    Pub.NoCoin → (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
    (∀ d i, ((A d).C i).AsksIn fun _ s => ¬ Pt s) →
    (∀ d isk b, ((A d).P isk b).AsksIn fun _ s => ¬ Pt s) →
    (∀ d k x π, ((A d).V k x π).AsksIn fun _ s => ¬ Pt s) →
    (∀ d, Gen.HasCompletenessError R (A d) B α) →
    Gen.HasCompletenessError R (glueArg Pub A) B α

/-- **Index privacy on a range passes to the glued scheme, with the glued simulator, at the same
bound.** -/
def privacy_pub : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf D : Type) (R : Gen.RelPair I X W PP)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (Sm : D → Gen.Simulator (rom lam) PP IVK X Pf)
    (B : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) (Pt : List Bool → Prop)
    (Pub : Rom.OComp (rom lam) D),
    Pub.NoCoin → (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
    (∀ d i, ((A d).C i).AsksIn fun _ s => ¬ Pt s) →
    (∀ d isk b, ((A d).P isk b).AsksIn fun _ s => ¬ Pt s) →
    (∀ d, Gen.PrivacyOn R (A d) B (Sm d) ζ ok) →
    Gen.PrivacyOn R (glueArg Pub A) B (glueSim Pub Sm) ζ ok

/-- **Completeness, where it is known at the d of Dok alone.** β is measured at the real reading. -/
def complete_pub_on : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf D : Type) (R : Gen.RelPair I X W PP)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (B : ℕ) (α β : ℝ≥0∞) (Pt : List Bool → Prop)
    (Dok : D → Prop) (Pub : Rom.OComp (rom lam) D),
    Pub.NoCoin → (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
    (∀ d, Dok d → ∀ i, ((A d).C i).AsksIn fun _ s => ¬ Pt s) →
    (∀ d, Dok d → ∀ isk b, ((A d).P isk b).AsksIn fun _ s => ¬ Pt s) →
    (∀ d, Dok d → ∀ k x π, ((A d).V k x π).AsksIn fun _ s => ¬ Pt s) →
    (∀ d, Dok d → Gen.HasCompletenessError R (A d) B α) →
    Rom.Pr Pub (fun _ => {d | ¬ Dok d}) ≤ β →
    Gen.HasCompletenessError R (glueArg Pub A) B (α + β)

/-- **Index privacy, where it is known at the d of Dok alone.** At the other d, and at these alone,
the simulator is still asked for the second clause of the property (ConsistentOn): that clause says
"with probability 0", so no β can pay for it. β is measured at the real reading. -/
def privacy_pub_on : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf D : Type) (R : Gen.RelPair I X W PP)
    (A : D → Gen.Arg (rom lam) I X W IVK ISK Pf) (Sm : D → Gen.Simulator (rom lam) PP IVK X Pf)
    (B : ℕ) (ζ : ℕ → ℕ → ℝ≥0∞) (β : ℝ≥0∞) (ok : I → Prop) (Pt : List Bool → Prop) (Dok : D → Prop)
    (Pub : Rom.OComp (rom lam) D),
    Pub.NoCoin → (Pub.AsksIn fun _ s => Pt s) → NoRepeat Pub →
    (∀ d, Dok d → ∀ i, ((A d).C i).AsksIn fun _ s => ¬ Pt s) →
    (∀ d, Dok d → ∀ isk b, ((A d).P isk b).AsksIn fun _ s => ¬ Pt s) →
    (∀ d, Dok d → Gen.PrivacyOn R (A d) B (Sm d) ζ ok) →
    (∀ d, ¬ Dok d → ConsistentOn R B (Sm d) ok) →
    Rom.Pr Pub (fun _ => {d | ¬ Dok d}) ≤ β →
    Gen.PrivacyOn R (glueArg Pub A) B (glueSim Pub Sm) (fun t N => ζ t N + β) ok

end Spec

end ZKCP.PublicRead

#print axioms ZKCP.PublicRead.commit_at
#print axioms ZKCP.PublicRead.verify_at
#print axioms ZKCP.PublicRead.glueArg_pure_C
#print axioms ZKCP.PublicRead.glueArg_pure_V
#print axioms ZKCP.PublicRead.glueArg_P
