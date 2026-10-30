-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FarOfFound.lean: **THE SHARED TABLE's PREMISES ON THE NUMBERING arr, AT arr := P5T.arrOf (P5T.planSeatsAll Z D), FROM THE TESTS "FOUND IN THE LIST"** (Johnson/P5T/FoundInList.lean). Statements and proofs; each is a call.
  mem_places_of_carried   where the book's places are the listed seats as far as the book goes (K12.Door.seatsCarriedB), every place of the book is a listed seat.
  **hfar_of_found**       evKept_of's premise hfar (Johnson/Desc/Sound/EvalKept.lean), to the letter, at every border k: inside the slot's own condition, at a state without a mark: no place of the handed state's book bears the number, or is the seat, of a message that sub-protocol k lays. FROM: the fact
                          "seatsCarried" inside that condition · the listed seats all pass foundFirstB · the three tenants pass foundLaterB · the first chain has at most 1000 sendings.
  **numbers_of_found**    W's and the index masks' numbers are no tenant's (K14's files' nWU | nWS | nIU | nIS; the premises hw | hi of apart_all_of, which is declared nowhere in this library) · harr_sh_of_found: the three tenants bear three numbers (harr).
Limits. The tests' accepts are premises: closed facts on a list of rounds. It closes no row. NO SOUNDNESS.

-/
import Johnson.P5T.FoundInList
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.Sound.BordersSharedFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB atFirstSeats)
open P5T (arrOf planSeatsAll foundFirstB foundLaterB)

/-- Every place of a book whose places are the listed seats is a listed seat. -/
theorem mem_places_of_carried (L : Laid) (B : TreeBook) (h : seatsCarriedB L B = true) (n j t : ℕ)
    (hp : B.place[n]? = some (j, t)) : (j, t) ∈ L.places := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hm : (j, t) ∈ B.place.toList := by
    rw [← Array.getElem?_toList] at hp
    exact List.mem_of_getElem? hp
  rw [h.1.1.1] at hm
  exact List.mem_of_mem_take hm

/-- **evKept_of's hfar.** -/
theorem hfar_of_found {P₀ P₁ : Type} (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (N : NumbersS)
    (Oc : P₁ → Strs → Prop) (get : P₁ → P₀ × First.S) (L : Laid) (split : Bool) (k : ℕ)
    (hcar : ∀ q y, Oc q y → (get q).2.failed = none → atFirstSeats L (get q).2 = true)
    (hten : ∀ m, foundLaterB Z D (N.tenant m) = true)
    (hpl : L.places.all (foundFirstB Z D) = true) (hlen : Z.made.proof.1.sends.length ≤ 1000) :
    ∀ q y, Oc q y → (get q).2.failed = none → ∀ n j t : ℕ,
      (get q).2.book.place[n]? = some (j, t) → ∀ m, Comp.msg m ∈ laysAtS split k →
        arrOf (planSeatsAll Z D) (N.tenant m).1 (N.tenant m).2 ≠ arrOf (planSeatsAll Z D) j t ∧
          N.tenant m ≠ (j, t) :=
  fun q y hoc hun n j t hp m _ =>
    P5T.far_of_found Z D N.tenant hten L.places hpl hlen j t
      (mem_places_of_carried L _ (hcar q y hoc hun) n j t hp) m

/-- **W's and the index masks' numbers are no tenant's.** -/
theorem numbers_of_found (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (N : NumbersS)
    (hw : foundFirstB Z D N.w = true) (hi : foundFirstB Z D N.index = true)
    (hten : ∀ m, foundLaterB Z D (N.tenant m) = true)
    (hlen : Z.made.proof.1.sends.length ≤ 1000) :
    (∀ m, arrOf (planSeatsAll Z D) N.w.1 N.w.2 ≠
      arrOf (planSeatsAll Z D) (N.tenant m).1 (N.tenant m).2) ∧
    ∀ m, arrOf (planSeatsAll Z D) N.index.1 N.index.2 ≠
      arrOf (planSeatsAll Z D) (N.tenant m).1 (N.tenant m).2 :=
  ⟨fun m => P5T.arr_ne_of_found Z D N.w (N.tenant m) hw (hten m) hlen,
    fun m => P5T.arr_ne_of_found Z D N.index (N.tenant m) hi (hten m) hlen⟩

/-- **The three tenants bear three numbers.** -/
theorem harr_sh_of_found (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (N : NumbersS)
    (hten : ∀ m, foundLaterB Z D (N.tenant m) = true)
    (hap : ∀ m m', N.tenant m = N.tenant m' → m = m') :
    ∀ m m' : Msg2, arrOf (planSeatsAll Z D) (N.tenant m).1 (N.tenant m).2 =
      arrOf (planSeatsAll Z D) (N.tenant m').1 (N.tenant m').2 → m = m' :=
  P5T.harr_of_found Z D N.tenant hten hap

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mem_places_of_carried
#print axioms VerifiableInference.Desc.Sound.hfar_of_found
#print axioms VerifiableInference.Desc.Sound.numbers_of_found
#print axioms VerifiableInference.Desc.Sound.harr_sh_of_found
