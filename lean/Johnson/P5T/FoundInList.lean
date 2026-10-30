-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/FoundInList.lean: **"FOUND IN THE LIST": WHAT THE LAWS ON THE NUMBERING arrOf (planSeatsAll Z D) ASK OF A SEAT, AS TWO TESTS WITH CODE AND THEIR LAWS.** General in the public parameters Z and the three chains' declared rounds D. Definitions, statements and proofs.
What for. arr_apart_chains (Johnson/P5T/ArrApartChains.lean: a seat of the first chain and one of the shared chain never bear one number) and harr_of (Johnson/P5T/ArrApart.lean: two seats of one later chain that bear one number are one) ask, of each seat, that the list's search finds an entry there and
that this entry is the first chain's | the shared chain's. planSeatsAll is an append of three lists and the search goes through an append: so each is a test on the parts.
  atSeat q            the search's test at the seat q.
  foundFirstB Z D q   the first chain's list has an entry at q.
  foundLaterB Z D q   the first chain's list has none at q, and the shared chain's has one.
  found_first | found_later   what each test's accept gives: the entry that the whole list's search finds, and whose it is.
  **arr_ne_of_found**    a seat that passes the first and one that passes the second bear two numbers (where the first chain has at most 1000 sendings) · seat_ne_of_found: and are two seats.
  **harr_of_found**      names whose tenants all pass the second test, and have tenants of their own, bear numbers of their own.
  **far_of_found**       for a list of seats that all pass the first test: no seat of the list bears the number, or is the seat, of a tenant that passes the second.
WHAT IS LEFT: the tests' accepts at the seats of a real list of rounds: closed facts: for an evaluation, or the kernel at typed values.
Limits. It says nothing of any real list. NO SOUNDNESS.

-/
import Johnson.P5T.ArrApartChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T

/-- The search's test at a seat. -/
def atSeat (q : Nat × Nat) : PSeat → Bool := fun x => x.j == q.1 && x.t == q.2

/-- The first chain's list has an entry at the seat. -/
def foundFirstB (Z : ProofFile.Pub) (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (q : Nat × Nat) : Bool := ((planSeats Z D.1).find? (atSeat q)).isSome

/-- The first chain's list has none at the seat, and the shared chain's has one. -/
def foundLaterB (Z : ProofFile.Pub) (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (q : Nat × Nat) : Bool :=
  ((planSeats Z D.1).find? (atSeat q)).isNone &&
    ((chainSeats 1 (rootsBefore D.1 D.1.length) Z.made.proof.2.1 D.2.1).find? (atSeat q)).isSome

theorem found_first (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (q : Nat × Nat)
    (h : foundFirstB Z D q = true) :
    ∃ p, ((planSeatsAll Z D).find? fun x => x.j == q.1 && x.t == q.2) = some p ∧
      p ∈ planSeats Z D.1 := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
  refine ⟨p, ?_, List.mem_of_find?_eq_some hp⟩
  show (planSeatsAll Z D).find? (atSeat q) = some p
  unfold planSeatsAll
  simp only [List.find?_append, hp, Option.some_or]

theorem found_later (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (q : Nat × Nat)
    (h : foundLaterB Z D q = true) :
    ∃ p, ((planSeatsAll Z D).find? fun x => x.j == q.1 && x.t == q.2) = some p ∧
      p ∈ chainSeats 1 (rootsBefore D.1 D.1.length) Z.made.proof.2.1 D.2.1 := by
  unfold foundLaterB at h
  rw [Bool.and_eq_true] at h
  have h0 : (planSeats Z D.1).find? (atSeat q) = none := Option.isNone_iff_eq_none.1 h.1
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h.2
  refine ⟨p, ?_, List.mem_of_find?_eq_some hp⟩
  show (planSeatsAll Z D).find? (atSeat q) = some p
  unfold planSeatsAll
  simp only [List.find?_append, h0, hp, Option.none_or, Option.some_or]

/-- **A seat of the first chain and one of the shared chain bear two numbers.** -/
theorem arr_ne_of_found (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (q q' : Nat × Nat)
    (h : foundFirstB Z D q = true) (h' : foundLaterB Z D q' = true)
    (hlen : Z.made.proof.1.sends.length ≤ 1000) :
    arrOf (planSeatsAll Z D) q.1 q.2 ≠ arrOf (planSeatsAll Z D) q'.1 q'.2 := by
  obtain ⟨p, hp, h0⟩ := found_first Z D q h
  obtain ⟨p', hp', h1⟩ := found_later Z D q' h'
  exact arr_apart_chains Z D q.1 q.2 q'.1 q'.2 p p' hp hp' h0 h1 hlen

/-- And are two seats. -/
theorem seat_ne_of_found (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (q q' : Nat × Nat)
    (h : foundFirstB Z D q = true) (h' : foundLaterB Z D q' = true) : q ≠ q' := by
  rintro rfl
  unfold foundFirstB at h
  unfold foundLaterB at h'
  rw [Bool.and_eq_true] at h'
  rw [Option.isNone_iff_eq_none.1 h'.1] at h
  cases h

/-- **Names whose tenants are the shared chain's bear numbers of their own.** -/
theorem harr_of_found {M : Type} (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (tenant : M → Nat × Nat)
    (h : ∀ m, foundLaterB Z D (tenant m) = true) (hten : ∀ m m', tenant m = tenant m' → m = m') :
    ∀ m m' : M, arrOf (planSeatsAll Z D) (tenant m).1 (tenant m).2 =
      arrOf (planSeatsAll Z D) (tenant m').1 (tenant m').2 → m = m' :=
  harr_of tenant (planSeatsAll Z D) 1 (rootsBefore D.1 D.1.length) Z.made.proof.2.1 D.2.1
    (fun m => found_later Z D (tenant m) (h m)) hten

/-- **No listed seat of the first chain bears the number, or is the seat, of a tenant of the shared chain.** -/
theorem far_of_found {M : Type} (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (tenant : M → Nat × Nat)
    (h : ∀ m, foundLaterB Z D (tenant m) = true) (places : List (Nat × Nat))
    (hp : places.all (foundFirstB Z D) = true) (hlen : Z.made.proof.1.sends.length ≤ 1000) :
    ∀ j t, (j, t) ∈ places → ∀ m,
      arrOf (planSeatsAll Z D) (tenant m).1 (tenant m).2 ≠ arrOf (planSeatsAll Z D) j t ∧
        tenant m ≠ (j, t) := by
  intro j t hjt m
  have hf : foundFirstB Z D (j, t) = true := List.all_eq_true.1 hp _ hjt
  exact ⟨fun e => arr_ne_of_found Z D (j, t) (tenant m) hf (h m) hlen e.symm,
    fun e => seat_ne_of_found Z D (j, t) (tenant m) hf (h m) e.symm⟩

end P5T

#print axioms P5T.found_first
#print axioms P5T.found_later
#print axioms P5T.arr_ne_of_found
#print axioms P5T.seat_ne_of_found
#print axioms P5T.harr_of_found
#print axioms P5T.far_of_found
