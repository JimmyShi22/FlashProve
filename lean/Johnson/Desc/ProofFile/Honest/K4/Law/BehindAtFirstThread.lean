-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/BehindAtFirstThread.lean: CONDITIONAL.

Can the hypotheses be met together? The statements ask h : `HeadAtReturn files A`
(Honest/Thread/TheFirstThread.lean) and g < 12, and nothing else. h holds that the maker returned A
at some filling (its field returned), three data, and the library's hypothesis `AtMgA` at A's public
part: facts on the public files and the return alone. That any files have such an h is not shown
here; the statement meant to give one at the base filling is `headAtReturn_base`
(AtFullSide/K1/HeadAtReturn.lean, its writers' file, not called here). AND `BehindS` IS AN
IMPLICATION: IT SPEAKS ONLY WHERE THE THREAD STANDS IN FRONT OF THE MEMBER AND THE MEMBER's STEP
ACCEPTS. NO STAND OF THIS THREAD BEYOND BORDER 0 IS KNOWN TO ANYBODY, SO THE STATEMENT IS NOT KNOWN
TO SPEAK AT ANY RUN.

What is here. AT THE THREADS' WRITERS' ONE TERM FOR THE FIRST CHAIN's THREAD, `firstThread h parts
w` (Honest/Thread/TheFirstThread.lean), AT THE TWELVE MEMBERS OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(kind K4), the members number 28 g + 4, g < 12: what that term's family of clauses of keeps
(`firstClauses h`) says at K4, and `BehindS`. Law/BehindColumns.lean has `BehindS` at letters under
a hypothesis keepsGivesClause on the family; HERE THAT HYPOTHESIS IS PROVED. No definition; three
statements with their proofs: unfoldings and calls.

  `k4_first_clause_iff`   **at the kind K4, at any place p, `firstClauses h` is: `K4KeepsM s s'`
      (Law/KeepsStep.lean) and `formsBehind` of the head's public data at p and s'**
      (Honest/Thread/FHeadF.lean). Each further layer of the family is "True" at K4.
  `k4_first_clause_of_keeps_and_form`   **keepsGivesClause**: `K4KeepsM s s'` and the thread's form
      at the border 28 g + 5 give the clause at K4's place of group g.
  `k4_behindS_at_first_thread`   **`BehindS` (Honest/Thread/PaysS.lean) AT b = 28 g + 4, FROM h AND
      g < 12 ALONE**, at every Said: where the thread stands in front of the member and the member's
      step accepts, the form and what rides hold at the border behind, and the step kept what keeps
      names.

Letters. The public files, the return A, the types of the index, of the tables' randomness and of
the trace, the parts (the script and the falls' stated numbers), the run's input w and what has been
said (Said) are arguments: nothing is asked of them beyond h. Nothing is read of Said.

Limits. CONDITIONAL, as said at the top. Of the threads' five statements at a border this file has
one. At an input w that the thread's own condition on the input refuses (`ReadyInput`,
Honest/Thread/ReadyInput.lean: the instance's start is unfit, the index out of range, or the trace
not the prover's own) the thread stands nowhere and the statement holds for nothing. No proof here
opens the prover's moves: that the member's step accepts (`Thread.Stepped`) is a hypothesis inside
`BehindS`. `firstThread` is a definition of the threads' writers; if its letters turn, these
statements turn with them. The proofs spell of its letters only the head, the border 339, the run's
input and the family `firstClauses h`, and need besides that this family is a pair (K4's clause,
`formsBehind`) under layers that are "True" at K4, however many, and that what rides is `ridersOf`
of `csHead` at some ν, st, R: the other letters are left to Lean to fill, so that a turn of theirs
does not redden this file. Its imports reach files that are no part of the library yet: of ours
Law/BehindColumns.lean, Law/FormBehindHead.lean, Law/LaidAtGroup.lean and Law/LaysOwn.lean; of the
threads' writers Honest/Thread/TheFirstThread.lean and what that file imports of theirs (the
family's layers, FHead.lean and those over it, among them). THE FULL SIZE ALONE, AND THE FORMAT's
EARLIER HASH ALONE. A LAW, NOT A PART: it rests, through Law/ElevenHead.lean, on modules under
Johnson/Goal/: no file that defines a part may build on it; it states no goal. Nothing on soundness,
on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.BehindColumns
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (Place KindName)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstClauses firstLetters firstThread
  formsBehind formsBehind_of_form)

variable {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
  (h : HeadAtReturn files A)

/-! ## 1 The family's clause at K4 -/

/-- **THE CLAUSE OF `firstClauses h` AT THE KIND K4**: K4's clause of keeps, and the public tests of
the claims on linear forms behind the place. -/
theorem k4_first_clause_iff (p : Place) (s s' : TS) :
    firstClauses h KindName.K4 p s s' ↔ K4KeepsM s s' ∧ formsBehind h.head.𝔇.pubD p s' := by
  constructor
  · intro a
    -- The family is a pair with layers laid over it, each layer a conjunct on the right. How many
    -- layers there are has turned more than once: so go left until the pair is met.
    repeat (first | exact a | replace a := a.1)
  · intro a
    repeat' (first | exact a.1 | exact a.2 | exact trivial | apply And.intro)

variable (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h and hg. **keepsGivesClause AT THE TERM's OWN FAMILY**: K4's clause of keeps
and the thread's form at the border behind give the family's clause at K4's place of group g. -/
theorem k4_first_clause_of_keeps_and_form {g : ℕ} (hg : g < 12) :
    ∀ k s s' m', K4KeepsM s s' → (firstLetters h parts w).thread.Form (28 * g + 4 + 1) k s' m' →
      firstClauses h KindName.K4 (IM.k4Place g) s s' :=
  fun _ s s' _ hK hF => (k4_first_clause_iff h (IM.k4Place g) s s').2
    ⟨hK, formsBehind_of_form h.head _ _ _ _ _ _ _ _ _ _ _ _ (k4_written_place_at_border hg) hF⟩

/-! ## 2 `BehindS` -/

/-- CONDITIONAL: on h and hg. **`BehindS` AT K4's BORDER 28 g + 4, AT THE FIRST THREAD**, at every
Said: an implication from the thread's stand in front of the member and the member's accepting
step; no such stand is known. -/
theorem k4_behindS_at_first_thread
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {g : ℕ} (hg : g < 12) :
    BehindS (firstThread h parts w) Said (28 * g + 4) :=
  k4_behindS_at_border h.head _ _ _ _ _ _ _ 339 _ w Said (firstClauses h) _ _ _ hg (by omega)
    (k4_first_clause_of_keeps_and_form h parts w hg)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_first_clause_iff
#print axioms ProofFile.Honest.K4.k4_first_clause_of_keeps_and_form
#print axioms ProofFile.Honest.K4.k4_behindS_at_first_thread
