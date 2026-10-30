-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K1Scope.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K1's TWO LATER PLACES (the reads' · the
digits') AT EVERY ONE OF THE 25 LINKS, IN THE GOALS' SCOPE.
WHY. Johnson/IMR/K1Seat.lean has them in scope at the reads' place of the twelve layers' links alone
(k1_reads_layers); at the other 38 places there was k1_later alone, at which the caller pays the row
of links and hearKinds' entry himself and which ends in «the reads' OR the digits'».
OBJECT. As in Johnson/IMR/K1Seat.lean: (reads) IM.k1Reads Z G₀ l Xl pr reads · (digits) K1.laterAt
G₀.first (K1.gpOf Z) l pd 2 digits, each carried over by Block.retype, at F.first.links[l].hear[3 |
5] (the head's link 24: hear[4 | 6]).
USER. K1's laws (Johnson/Desc/K1/Law/) · this folder's files on the planes · a walk over all addresses. LETTERS. As in Johnson/IMR/K1Seat.lean.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  k1Ix l digits     the index: 3 | 5, one more at l = 24.
  k1_reads_of       in scope, l < 25: c.links[l].hear[k1Ix l false] IS seatedAs sameReply (k1Reads Z G₀ l Xl (k1Ix l false + 1) reads).retype b.name ⟨1, some l, k1Ix l false + 1, K1⟩: ALONE; G₀.built[l]? = some Xl · K1.linkNumbers G₀ Xl = some (k1Ix l false + 1, pd, reads, digits).
  k1_digits_of      the like at k1Ix l true: (K1.laterAt G₀.first (K1.gpOf Z) l (k1Ix l true + 1) 2 digits).retype.

WHO PAYS THE PREMISES: as in K6Seat.lean. What is not claimed: as in K1Seat.lean. No soundness.
-/
import Johnson.IMR.K1Seat
import Johnson.IMR.LinkSeat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-- The index of K1's reads' | digits' place in link l. -/
abbrev k1Ix (l : ℕ) (digits : Bool) : ℕ := (if digits then 5 else 3) + (if l = 24 then 1 else 0)

/-- K1's later address. -/
abbrev k1PlaceL (l : ℕ) (digits : Bool) : Place :=
  { chain := 1, link := some l, piece := k1Ix l digits + 1, kind := .K1 }

theorem k1_kind_at (l : ℕ) (digits : Bool) :
    (kindsBeforeBatching (subAt l) (l == 0))[k1Ix l digits]? = some KindName.K1 := by
  unfold subAt
  by_cases h24 : l = 24
  · subst h24
    cases digits <;> rfl
  · have e : k1Ix l digits = if digits then 5 else 3 := by
      show (if digits then 5 else 3) + (if l = 24 then 1 else 0) = _
      rw [if_neg h24]
      rfl
    rw [e, if_neg h24]
    by_cases he : l % 2 = 0
    · rw [if_pos he]
      cases digits <;> cases (l == 0) <;> rfl
    · rw [if_neg he]
      cases digits <;> cases (l == 0) <;> rfl

theorem k1Ix_range (l : ℕ) (digits : Bool) : 2 ≤ k1Ix l digits + 1 ∧ k1Ix l digits + 1 ≤ 9 := by
  show 2 ≤ (if digits then 5 else 3) + (if l = 24 then 1 else 0) + 1 ∧
    (if digits then 5 else 3) + (if l = 24 then 1 else 0) + 1 ≤ 9
  cases digits <;> by_cases h : l = 24 <;> simp [h]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K1's READS' PLACE AT EVERY LINK: K1's OWN WITH THE QUIET STEP JOINED BY THE LOT: ALONE.** -/
theorem k1_reads_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH) (pd : ℕ)
        (reads digits : Option (List ℕ)),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l false]? = some b ∧ Bs.G₀.built[l]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (k1Ix l false + 1, pd, reads, digits) ∧
      LaidAlone ProofFile.sameReply b (k1Reads Z Bs.G₀ l Xl (k1Ix l false + 1) reads).retype b.name
        (k1PlaceL l false) := by
  intro l hl
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, hX, hn, harm⟩ :=
    k1_later O l (subAt l) (subs_scope hS hR O l hl) (k1Ix l false) (k1_kind_at l false)
      (k1Ix_range l false)
  rcases harm with ⟨e, h⟩ | ⟨e, h⟩
  · subst e
    exact ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, hn, h⟩
  · exfalso
    have e' : (3 + (if l = 24 then 1 else 0)) + 1 = pd := e
    rcases numbers_pieces hn with ⟨-, h'⟩ | ⟨-, h'⟩ <;> split at e' <;> omega

/-- **K1's DIGITS' PLACE AT EVERY LINK: ALONE.** -/
theorem k1_digits_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH) (pr : ℕ)
        (reads digits : Option (List ℕ)),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l true]? = some b ∧ Bs.G₀.built[l]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (pr, k1Ix l true + 1, reads, digits) ∧
      LaidAlone ProofFile.sameReply b
        (VerifiableInference.Desc.K1.laterAt Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z) l
          (k1Ix l true + 1) 2 digits : Block S Unit).retype b.name (k1PlaceL l true) := by
  intro l hl
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, hX, hn, harm⟩ :=
    k1_later O l (subAt l) (subs_scope hS hR O l hl) (k1Ix l true) (k1_kind_at l true)
      (k1Ix_range l true)
  rcases harm with ⟨e, h⟩ | ⟨e, h⟩
  · exfalso
    have e' : (5 + (if l = 24 then 1 else 0)) + 1 = pr := e
    rcases numbers_pieces hn with ⟨h', -⟩ | ⟨h', -⟩ <;> split at e' <;> omega
  · subst e
    exact ⟨Lk, b, Xl, pr, reads, digits, e1, e2, hX, hn, h⟩

end

end IM

#print axioms IM.k1_reads_of
#print axioms IM.k1_digits_of
