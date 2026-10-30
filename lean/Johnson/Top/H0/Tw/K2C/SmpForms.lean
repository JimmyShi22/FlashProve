-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SmpForms.lean: small facts on how an OOD sample is read off a statement, for
the law on the new members behind a code switch (SmpLikeNew.lean). Theorems with their proofs.

Two sub-protocols read the first stored sample row of a message as a linear form, each by its own
text: `K1.formsAt` (Johnson/Desc/K1/Law/GoodSendForms.lean) and `K2.formsAt`
(Johnson/Top/H0/K2Hears/SeedBehind.lean).

Main names:
  `forms_two_texts`, `ans_two_texts`: the two texts give one form, and one target.
  `smpAt_like`: where that form is the sample map of an OOD seed ρ, `K1.smpAt` returns a sample. Its
    seed, which is taken by choice, has ρ's values; its OOD answers are the stored target.
  `nums_of_list`: a list without repeats that holds the seats seatN 0, seatN 1, … from place n0 on:
    each of these seats is in the list, and its place is n0 + i.
  `newSeatsB`, `newSeats_of_test`, `newSeats_can_fail`: these two facts on the list as one test
    with code; its accept gives them; three altered inputs that it rejects.

Limits. Book-keeping. Nothing says that the seed by choice is the seed that was drawn. Nothing on
soundness.

-/
import Johnson.Top.H0.K2Hears.SeedBehind
import Johnson.Desc.K1.Law.GoodSendForms
import Johnson.Desc.Sound.Seed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes Johnson.Pack Cb
open VerifiableInference.Desc

/-- **The two texts of "the first stored sample row, as a linear form" give one form.** -/
theorem forms_two_texts (cs : Codes) (sh : OracleShape) (St : Statement) (o : ℕ) :
    K1.formsAt cs sh St o = formsAt cs sh St o := by
  have e : (fun (row : OnBytes.Row) (_ : Unit) => K1.formRow cs sh o row) =
      fun row _ j => Slice.coefAt row o (partZ cs sh j) (locZ cs sh j) := by
    funext row _ j
    rcases j with j | j <;> rfl
  unfold K1.formsAt formsAt
  rw [e]

/-- And one target. -/
theorem ans_two_texts (St : Statement) (o : ℕ) : K1.ansAt St o = ansAt St o := rfl

/-- **Where the form is the sample map of a seed, the reader returns a sample**: its seed has that
seed's values; its answers are the stored target. -/
theorem smpAt_like (cs : Codes) (sh : OracleShape) (e : ℕ) (St : Statement) (o : ℕ)
    (ρ : (portOmZ cs sh e).Z.D) (h : K1.formsAt cs sh St o = some ((portOmZ cs sh e).Z.mat ρ)) :
    ∃ zz, K1.smpAt cs sh e St o = some zz ∧
      (portOmZ cs sh e).Z.val zz.1 = (portOmZ cs sh e).Z.val ρ ∧ K1.ansAt St o = some zz.2 := by
  have g : ∃ ρ', K1.formsAt cs sh St o = some ((portOmZ cs sh e).Z.mat ρ') := ⟨ρ, h⟩
  obtain ⟨v, hv⟩ : ∃ v, K1.ansAt St o = some v := by
    unfold K1.formsAt at h
    unfold K1.ansAt
    cases hx : St.oracles[o]? with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      cases hr : x.sampleRows[0]? with
      | none =>
        simp only [Option.bind_some, hr, Option.map_none] at h
        cases h
      | some row =>
        refine ⟨fun _ => Slice.readE row.target, ?_⟩
        rw [Option.bind_some, hr]
        rfl
  refine ⟨(g.choose, v), ?_, ?_, hv⟩
  · unfold K1.smpAt
    rw [dif_pos g, hv]
    rfl
  · exact Sound.val_congr _ _ _ (Option.some.inj (g.choose_spec.symm.trans h))

/-- **The places of the new seats**, from two facts on the plain list. -/
theorem nums_of_list {n : ℕ} (seats : List (ℕ × ℕ)) (seatN : Fin n → ℕ × ℕ) (n0 : ℕ)
    (hnd : seats.Nodup) (hs : ∀ i : Fin n, seats[n0 + i.val]? = some (seatN i)) :
    (∀ i, seatN i ∈ seats) ∧ ∀ i : Fin n, seats.idxOf (seatN i) = n0 + i.val := by
  refine ⟨fun i => List.mem_of_getElem? (hs i), fun i => ?_⟩
  obtain ⟨hlt, he⟩ := List.getElem?_eq_some_iff.1 (hs i)
  rw [← he]
  exact hnd.idxOf_getElem _ hlt

/-- **The two facts on the plain list, as one test with code**: seats has no repeats, and holds
seatN i at place n0 + i, for each i. -/
def newSeatsB {n : ℕ} (seats : List (ℕ × ℕ)) (seatN : Fin n → ℕ × ℕ) (n0 : ℕ) : Bool :=
  decide seats.Nodup && (List.finRange n).all fun i => seats[n0 + i.val]? == some (seatN i)

/-- An accept of the test gives the two facts. -/
theorem newSeats_of_test {n : ℕ} (seats : List (ℕ × ℕ)) (seatN : Fin n → ℕ × ℕ) (n0 : ℕ)
    (h : newSeatsB seats seatN n0 = true) :
    seats.Nodup ∧ ∀ i : Fin n, seats[n0 + i.val]? = some (seatN i) := by
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact ⟨of_decide_eq_true h1, fun i => eq_of_beq (List.all_eq_true.1 h2 i (List.mem_finRange i))⟩

/-- **The test can reject**: a seat twice; a seat at another place; a list that is too short. The
first input, unaltered, is accepted. -/
theorem newSeats_can_fail :
    newSeatsB (n := 2) [(0, 0), (1, 0), (1, 1)] ![(1, 0), (1, 1)] 1 = true ∧
      newSeatsB (n := 2) [(0, 0), (1, 0), (1, 0)] ![(1, 0), (1, 0)] 1 = false ∧
      newSeatsB (n := 2) [(0, 0), (1, 0), (1, 1)] ![(1, 0), (1, 1)] 0 = false ∧
      newSeatsB (n := 2) [(0, 0), (1, 0)] ![(1, 0), (1, 1)] 1 = false := by
  decide

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.forms_two_texts
#print axioms VerifiableInference.Desc.First.K2.smpAt_like
#print axioms VerifiableInference.Desc.First.K2.nums_of_list
#print axioms VerifiableInference.Desc.First.K2.newSeats_of_test
#print axioms VerifiableInference.Desc.First.K2.newSeats_can_fail
