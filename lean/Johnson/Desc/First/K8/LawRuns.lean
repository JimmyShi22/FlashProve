-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawRuns.lean: THE SMALLNESS TEST AS ONE BLOCK: ITS THREE RUNS ("K8.equations";
"K8.lsTail", "K8.tests") WRITE THE OPEN LINK'S PART OF THE CARRIED RECORD ALONE: THE COUNT OF ROOTS,
THE BOOK, THE STATEMENT AND THE REST STAY.

Each run of `K8.whole p` (Johnson/Desc/First/K8/Whole.lean) is a run at a part of the record, lifted
by `atRecord`: what it hands on is the record with that part laid back (`k8PartP.set`).
  `set_rest`: laying the part back leaves the statement, the book, the count of roots, the rows
    owed, the mark, the state of the calls and what was put out.
  `atRecord_rest`: so does a yes of any run lifted by `atRecord`.
  `whole_claims_rest`, `whole_after_rest`: **so does every run of `K8.whole p`.**
  `hear_leaves_lookHeard`, `whole_leaves_fork_look`: the block's DECISION turns neither the
    sub-proof's ledger (`S.fork?`) nor what the lookup on the calls was heard to return
    (`S.lookHeard?`).
  `whole_steps_carriesFo`: SO ITS DECISION STEPS (`Block.Steps`, Johnson/Desc/Sound/FoldSteps.lean)
    at `CarriesFo S.fork? S.lookHeard?` (Johnson/Desc/First/LedgerAtFo.lean): by that file's
    `carriesSame`.
  `whole_roots`: **THE BLOCK's LINE FOR A WALK THAT COUNTS ROOTS**: a yes of its decision adds to
    the count of roots what its declared rounds send (nothing), and its runs leave the count.
Statements and proofs.
Limits. Nothing on what the runs write inside the link's part. Nothing on soundness.

-/
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.First.K8.LawPlanNames
import Johnson.Desc.First.LedgerAtFo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-- All of the record but the open link's part. -/
def restOf (s : S) := (s.st, s.book, s.roots, s.rowsOwed, s.failed, s.check, s.out)

theorem putTl_restOf (s : S) (tl : OnBytes.Model.HTailF2) : restOf (s.putTl tl) = restOf s := by
  unfold S.putTl restOf
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [ho]
  | _ => simp

theorem putFork_restOf (s : S) (F : OnBytes.Model.Fork) : restOf (s.putFork F) = restOf s := by
  unfold S.putFork restOf
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [ho]
  | _ => simp

/-- Laying the part back leaves the rest. -/
theorem set_rest (s : S) (q : K8Part) : restOf (k8PartP.set s q) = restOf s := by
  show restOf ((s.putTl q.tl).putFork q.F) = restOf s
  rw [putFork_restOf, putTl_restOf]

/-- A yes of a run lifted to the record leaves the rest. -/
theorem atRecord_rest {α : Type} (f : K8Part → Except String (α × K8Part)) (s : S) (x : α × S)
    (h : atRecord f s = .ok x) : restOf x.2 = restOf s := by
  unfold atRecord at h
  cases hq : k8PartP.get? s with
  | none => simp [hq] at h
  | some q =>
    simp only [hq] at h
    cases hf : f q with
    | error e => simp [hf, Except.map] at h
    | ok y =>
      simp only [hf, Except.map, Except.ok.injEq] at h
      subst h
      exact set_rest s y.2

/-- **Every run of claims of the block leaves the rest.** -/
theorem whole_claims_rest (p : ParW) (r : String × (Nat → S → Except String (List Claim × S)))
    (hr : r ∈ (whole p).claims) (n : Nat) (s : S) (y : List Claim × S) (h : r.2 n s = .ok y) :
    restOf y.2 = restOf s := by
  obtain ⟨r0, _, rfl⟩ := List.mem_map.1 hr
  exact atRecord_rest _ s y h

/-- **Every run behind the batching leaves the rest.** -/
theorem whole_after_rest (p : ParW) (r : String × (S → Except String S))
    (hr : r ∈ (whole p).after) (s s' : S) (h : r.2 s = .ok s') : restOf s' = restOf s := by
  obtain ⟨r0, _, rfl⟩ := List.mem_map.1 hr
  have h' : Except.map (·.2) (atRecord (fun q => (r0.2 q).map fun q' => ((), q')) s) = .ok s' := h
  cases hx : atRecord (fun q => (r0.2 q).map fun q' => ((), q')) s with
  | error e =>
    rw [hx] at h'
    exact nomatch h'
  | ok x =>
    rw [hx] at h'
    obtain rfl : x.2 = s' := Except.ok.inj h'
    exact atRecord_rest _ s x hx

/-- Laying the smallness test's record leaves what the lookup on the calls was heard to return. -/
theorem putTl_lookHeard (s : S) (tl : OnBytes.Model.HTailF2) :
    (s.putTl tl).lookHeard? = s.lookHeard? := by
  unfold S.putTl S.lookHeard?
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho]
  | _ => simp [h]

/-- The block of the draw leaves it. -/
theorem hear_leaves_lookHeard {Cl : Type} (p : Par) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).Leaves S.lookHeard? := hear_leaves _ putTl_lookHeard p

/-- **The hearing of `K8.whole p` turns neither the sub-proof's ledger nor what the lookup on the
calls returned.** -/
theorem whole_leaves_fork_look (p : ParW) :
    (whole p).Leaves S.fork? ∧ (whole p).Leaves S.lookHeard? :=
  ⟨hear_leaves_fork (Cl := Claim) p.toPar, hear_leaves_lookHeard (Cl := Claim) p.toPar⟩

/-- **The hearing block's decision steps**: what was heard of the lookup on the calls stands, and
the ledger is later, with its sizes: here it is the same ledger. No premise, not even the test on
the plan. -/
theorem whole_steps_carriesFo (p : ParW) :
    (whole p).Steps (CarriesFo S.fork? S.lookHeard?) :=
  fun s rs gs s' h => carriesSame s s' (hear_leaves_fork (Cl := Claim) p.toPar s rs gs s' h)
    (hear_leaves_lookHeard (Cl := Claim) p.toPar s rs gs s' h)

/-- **The block's line for a walk that counts roots.** -/
theorem whole_roots (p : ParW) :
    (∀ s rs gs s', (whole p).decide s rs gs = .ok s' →
      s'.roots = s.roots + rootsOfRounds (whole p).rounds) ∧
    (∀ r ∈ (whole p).claims, ∀ n s y, r.2 n s = .ok y → y.2.roots = s.roots) ∧
    ∀ r ∈ (whole p).after, ∀ s s', r.2 s = .ok s' → s'.roots = s.roots :=
  ⟨fun s rs gs s' h => hear_roots_step (Cl := Claim) p.toPar s s' rs gs h,
    fun r hr n s y h => congrArg (fun x => x.2.2.1) (whole_claims_rest p r hr n s y h),
    fun r hr s s' h => congrArg (fun x => x.2.2.1) (whole_after_rest p r hr s s' h)⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.set_rest
#print axioms VerifiableInference.Desc.First.K8.whole_claims_rest
#print axioms VerifiableInference.Desc.First.K8.whole_after_rest
#print axioms VerifiableInference.Desc.First.K8.whole_leaves_fork_look
#print axioms VerifiableInference.Desc.First.K8.whole_steps_carriesFo
#print axioms VerifiableInference.Desc.First.K8.whole_roots
