-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/StatedBy.lean: NOT a law on a part: A BRIDGE (the first
statement has no premise; the other three have one each, h): the sentence `SumLaw.StatedBy ns rs`
(Honest/SumLaw/Fits.lean: the declared rounds state, round by round, so many scalars, no other item
but roots, and no oracle message) IS this folder's equation on `statedOf rs`
(Honest/Small/Field.lean). So a caller that holds `StatedBy` pays the premise hrs of
`scalarsPart_exact` (Honest/Small/Scalars.lean) and of `quietPart_exact` (Honest/Small/Quiet.lean).

  `statedBy_iff`          `StatedBy ns rs` is `statedOf rs = ns.map fun n => (.replicate n .e, [])`
  `stated_quiet_of`       from `StatedBy (List.replicate n 0) rs`: hrs of the quiet part's law
  `stated_quiet_one_of`   its case n = 1: from `StatedBy [0] rs`
  `stated_scalars_of`     from `StatedBy [n] rs`: hrs of the scalars' part's law

A THIN FILE APART, because it imports Honest/SumLaw/Fits.lean (the masked sumcheck's law, by other
authors), which is neither the frame's nor this folder's.

The frame's terms that are used here (part, round, item, oracle message and the like): the head of
Honest/Small/Field.lean. All names stand in the namespace ProofFile.Honest.Small: a caller opens it.

Limits. What `statedOf` lets through and does not read (Honest/Small/Field.lean, Limits), `StatedBy`
lets through and does not read. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Oracle)

/-- `StatedBy ns rs` is this folder's equation on `statedOf rs`. No premise. -/
theorem statedBy_iff : ∀ (ns : List Nat) (rs : List (Fmt.DeclaredRound × List Oracle)),
    SumLaw.StatedBy ns rs ↔ statedOf rs = ns.map fun n => (List.replicate n Fmt.Item.e, [])
  | [], [] => ⟨fun _ => rfl, fun _ => trivial⟩
  | n :: ns, r :: rs => by
    show (r.1.items.filter (· != .root) = List.replicate n .e ∧ r.2 = [] ∧
        SumLaw.StatedBy ns rs) ↔
      (r.1.items.filter (· != .root), r.2) :: statedOf rs =
        (List.replicate n Fmt.Item.e, []) :: ns.map fun n => (List.replicate n Fmt.Item.e, [])
    rw [statedBy_iff ns rs, List.cons.injEq, Prod.mk.injEq, and_assoc]
  | [], _ :: _ => ⟨fun h => h.elim, fun h => by simp [statedOf] at h⟩
  | _ :: _, [] => ⟨fun h => h.elim, fun h => by simp [statedOf] at h⟩

/-- CONDITIONAL on h. From `StatedBy` at n zeros: hrs of the quiet part's law. -/
theorem stated_quiet_of {n : Nat} {rs : List (Fmt.DeclaredRound × List Oracle)}
    (h : SumLaw.StatedBy (List.replicate n 0) rs) : statedOf rs = List.replicate n ([], []) := by
  rw [(statedBy_iff _ _).1 h, List.map_replicate]
  rfl

/-- CONDITIONAL on h. The case n = 1. -/
theorem stated_quiet_one_of {rs : List (Fmt.DeclaredRound × List Oracle)}
    (h : SumLaw.StatedBy [0] rs) : statedOf rs = List.replicate 1 ([], []) :=
  stated_quiet_of (n := 1) h

/-- CONDITIONAL on h. From `StatedBy [n] rs`: hrs of the scalars' part's law. -/
theorem stated_scalars_of {n : Nat} {rs : List (Fmt.DeclaredRound × List Oracle)}
    (h : SumLaw.StatedBy [n] rs) : statedOf rs = [(List.replicate n .e, [])] :=
  (statedBy_iff _ _).1 h

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.statedBy_iff
#print axioms ProofFile.Honest.Small.stated_quiet_of
#print axioms ProofFile.Honest.Small.stated_quiet_one_of
#print axioms ProofFile.Honest.Small.stated_scalars_of
