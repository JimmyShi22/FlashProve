-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/SendAgree.lean: the three makers of an out-of-domain sample that are a named part
of the description (Johnson/Desc/Own/Send.lean) are the program's, at all arguments.

Statements and proofs. No block imports this file.
Main names:
  `padMade_eq`: padMade codes s = Send.pad codes s.
  `padMade_isSome_iff`: what the one refusal of padMade checks: it returns places just where the row
    that takes the pad has as many places as the pad needs.
  `formMade_eq`: formMade codes s o seed answer = Send.form codes s o seed answer.
  `seedsMade_eq`: seedsMade bits n l = Send.seedsOf bits n l.
  `seedsMade_length`: what the two refusals of seedsMade check: it returns seeds just where l has n
    * (bits + 1) elements.
Limits: No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.Own.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

theorem padMade_eq (codes : Codes) (s : OracleShape) : padMade codes s = Send.pad codes s := rfl

/-- What the one refusal of padMade checks. -/
theorem padMade_isSome_iff (codes : Codes) (s : OracleShape) :
    (padMade codes s).isSome = true ↔
      (if 0 < s.maskRows ∨ s.mainDeg = 3 then 1 else 3) * s.answers ≤
        if 0 < s.maskRows then (codes.mask.getD s.maskCode default).ell
        else (codes.base.getD s.code default).ell := by
  have key : ∀ (len need : Nat) (x : List PadPlace),
      (if len < need then none else some x : Option (List PadPlace)).isSome = true ↔
        need ≤ len := by
    intro len need x
    by_cases h : len < need
    · rw [if_pos h]
      constructor
      · intro k
        cases k
      · intro k
        omega
    · rw [if_neg h]
      exact ⟨fun _ => Nat.le_of_not_lt h, fun _ => rfl⟩
  have h1 : (if 0 < s.maskRows ∨ s.mainDeg = 3 then 1 else 3) =
      if (Send.cube codes s).hasMask || s.mainDeg == 3 then 1 else 3 := by
    show _ = if decide (0 < s.maskRows) || s.mainDeg == 3 then 1 else 3
    by_cases a : 0 < s.maskRows <;> by_cases b : s.mainDeg = 3 <;> simp [a, b]
  have h2 : (if 0 < s.maskRows then (codes.mask.getD s.maskCode default).ell
      else (codes.base.getD s.code default).ell) =
      if (Send.cube codes s).hasMask then (codes.mask.getD s.maskCode default).ell
      else (codes.base.getD s.code default).ell := by
    show _ = if decide (0 < s.maskRows) then _ else _
    by_cases a : 0 < s.maskRows <;> simp [a]
  rw [h1, h2]
  exact key _ _ _

theorem formMade_eq (codes : Codes) (s : OracleShape) (o : Nat) (seed : SampleSeed)
    (answer : Nat) : formMade codes s o seed answer = Send.form codes s o seed answer := rfl

theorem seedsMade_eq (bits : Nat) : ∀ (n : Nat) (l : List E),
    seedsMade bits n l = Send.seedsOf bits n l
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | n + 1, l => by
    unfold seedsMade Send.seedsOf
    cases l.drop bits with
    | nil => rfl
    | cons beta rest =>
      show (seedsMade bits n rest).map _ = (Send.seedsOf bits n rest).map _
      rw [seedsMade_eq bits n rest]

theorem seedsMade_length (bits : Nat) : ∀ (n : Nat) (l : List E),
    (seedsMade bits n l).isSome = true ↔ l.length = n * (bits + 1)
  | 0, [] => by simp [seedsMade]
  | 0, _ :: _ => by simp [seedsMade]
  | n + 1, l => by
    unfold seedsMade
    cases h : l.drop bits with
    | nil =>
      have hl : l.length ≤ bits := List.drop_eq_nil_iff.1 h
      constructor
      · intro k
        cases k
      · intro k
        rw [Nat.succ_mul] at k
        omega
    | cons beta rest =>
      have hlen : (l.drop bits).length = rest.length + 1 := by rw [h]; rfl
      rw [List.length_drop] at hlen
      show ((seedsMade bits n rest).map _).isSome = true ↔ _
      rw [Option.isSome_map, seedsMade_length bits n rest, Nat.succ_mul]
      omega

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.padMade_eq
#print axioms VerifiableInference.Desc.Own.padMade_isSome_iff
#print axioms VerifiableInference.Desc.Own.formMade_eq
#print axioms VerifiableInference.Desc.Own.seedsMade_eq
#print axioms VerifiableInference.Desc.Own.seedsMade_length
