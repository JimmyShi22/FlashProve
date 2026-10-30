-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/PlacesOffRad.lean: THE NAMED TEST `placesOffC` (PlacesOffPadC.lean) READS OF THE MEMBERS
    THEIR SHAPES AND SEATS ALONE: so it says the same at two lists of members with the same pairs
    (shape, seat); so at the
composed meaning's own members (radii off the rows of the sendings, sendRowsOf: slow to evaluate)
    it says what it says at the same make with the radius 0 everywhere (quick).
  `copiesMiss_same` · **`placesOffC_same`**: the same pairs ⟹ the same answer.
  **`placesOffC_rad`**: placesOffC … (P5T.msAtR Z rad) … = placesOffC … (P5T.msAtR Z rad') …: by
      `memsSame_atR` (Johnson/P5T/MembersByMake.lean): at every radius the pairs are
      the
    list of rounds' own.
Use. A run at rad' := fun _ _ => 0 answers for At.ms Zp lay := P5T.msAtR Zp (At.rad Zp lay).
Limits. An equation of two Bools: it says nothing on which Bool.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.PlacesOffPadC
import Johnson.P5T.MembersByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open Meaning
open OnBytes OnBytes.Road
open OnBytes.Params (ReqArray ReqLayout)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem seatOf numOf)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (copiesMiss missB)

section
variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (N : Numbers) {ms ms' : List Mem}

/-- The test at one array reads the pairs (shape, seat) alone. -/
theorem copiesMiss_same
    (h : ∀ p : OnBytes.OracleShape × (ℕ × ℕ), p ∈ ms.map (fun x => ((x.1.l.get x.2).1, seatOf x)) ↔
      p ∈ ms'.map (fun x => ((x.1.l.get x.2).1, seatOf x))) (k n : ℕ) (A : ReqArray) :
    copiesMiss cs arr ms N k n A = copiesMiss cs arr ms' N k n A := by
  have key : ∀ l : List Mem, copiesMiss cs arr l N k n A =
      (l.map fun x => ((x.1.l.get x.2).1, seatOf x)).all fun p =>
        !(decide (p.2 ∈ N.group k) && decide (arr p.2.1 p.2.2 = n)) || missB cs p.1 A := by
    intro l
    unfold copiesMiss
    rw [List.all_map]
    rfl
  rw [key ms, key ms', Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H p hp => H p ((h p).2 hp), fun H p hp => H p ((h p).1 hp)⟩

/-- **The same pairs: the same answer.** -/
theorem placesOffC_same
    (h : ∀ p : OnBytes.OracleShape × (ℕ × ℕ), p ∈ ms.map (fun x => ((x.1.l.get x.2).1, seatOf x)) ↔
      p ∈ ms'.map (fun x => ((x.1.l.get x.2).1, seatOf x)))
    (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout) (num : ℕ → ℕ → ℕ) :
    placesOffC cs arr ms N X s layout num = placesOffC cs arr ms' N X s layout num := by
  unfold placesOffC
  simp only [copiesMiss_same cs arr N h]

end

/-- **At every radius the test says the same.** -/
theorem placesOffC_rad (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (N : Numbers) (Z : ProofFile.Pub)
    (rad rad' : ℕ → ℕ → ℕ) (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout)
    (num : ℕ → ℕ → ℕ) :
    placesOffC cs arr (P5T.msAtR Z rad) N X s layout num =
      placesOffC cs arr (P5T.msAtR Z rad') N X s layout num :=
  placesOffC_same cs arr N
    (fun p => (P5T.memsSame_atR Z rad p).trans (P5T.memsSame_atR Z rad' p).symm) X s layout num

end P5J

#print axioms P5J.copiesMiss_same
#print axioms P5J.placesOffC_same
#print axioms P5J.placesOffC_rad
