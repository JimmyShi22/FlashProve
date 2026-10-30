-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastBook.lean: THE FACT `BookAt` (where a member lies by
the data's book, and that its tree there has the shape which the description tells) AT THE LAST
CHAIN's OWN PROXIMITY TEST: a join of the laws at the state
(Johnson/ToldDescR/BookAtW.lean). One theorem.
  `bookAt_W`: inside the book-keeping's yes at border 2, behind the door's yes, at whatever the
    state fixes: `BookAt G (noAt t₁ t₂ n₁ ft nΩ) D j x` FROM: `HandedRoots` (the two earlier books'
    trees' numbers); the member's number sits, by the state's own book, at x's seat; AND, FOR THE
    TREE's SHAPE, ONE OF TWO: x's seat is an elder tree's (its number is below t₁), the first
    chain's last book carries the plan's list of shapes (`seatsCarriedB L`), and that list is what
    the description tells (`PlanShapes G L ft n₁`, a test on the plan with code); OR the clause on
    the shape itself (for Omega's copy: nothing that lies gives it inside the promise).
The first clause holds at every message of the book: `no_of_seat`. That the data's book is the
state's: `book_of_fixes` (first arm: a mask has come from outside) and the
door's own text.
Limits. Premises as named. Nothing on soundness.
-/
import Johnson.LLT25R.LastFive
import Johnson.ToldDescR.BookAtW
import Johnson.Desc.K12.Coin.FirstBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Last VerifiableInference.Desc.Third
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.K12.Door (seatsCarriedB)
open H2K.First (Plain)

/-- **`BookAt` at the last chain's own test.** -/
theorem bookAt_W {Xi : Type} (G : FileDescription Xi) (p : P₁₄) (R : List Fmt.DeclaredRound) (f : Handed)
    (e : SharedOut) (s : S₃) (t : T12) (π : P12) (st : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hk : shapeAt p R 2 f e s = true)
    (ht : enterOwn s = .ok t) (hf : Fixes π t st rest G0 Ly D) (n₁ ft nΩ t₁ t₂ : ℕ)
    (hH : ToldDesc.HandedRoots n₁ ft nΩ f e) (j : Fin D.mems.length) (x : Mem)
    (hs : seatBy (noLast t₁ t₂ s.loc.firstTree) s.book (D.mems.get j).id = some (seatOf x))
    (L : K12.Door.Laid)
    (h2 : ((seatOf x).1 < t₁ ∧ seatsCarriedB L f.book = true ∧ ToldDesc.PlanShapes G L ft n₁) ∨
      ∀ z u T, s.book.place[(D.mems.get j).id]? = some (z, u) → s.book.trees[z]? = some T →
        ∀ o, G.oracleAt (seatOf x).1 = some o → ShapeIs T.shape o) :
    BookAt G (ToldDesc.noAt t₁ t₂ n₁ ft nΩ) D j x := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  have et := ToldDesc.enterOwn_is ht
  have eb : D.book = s.book := by
    rw [book_of_fixes π t (by rw [et]; exact B.mask) st rest G0 Ly D hf, et]
  have K := ToldDesc.bookTwo_of_shape hk (ToldDesc.handedNumbers_of_roots hk hH)
  unfold BookAt
  rw [eb]
  refine ⟨ToldDesc.no_of_seat K t₁ t₂ hs, ?_⟩
  rcases h2 with ⟨he, hL, hP⟩ | h
  · exact ToldDesc.shape_of_elder G K t₁ t₂ hs he hL hP
  · exact h

end LLT25

#print axioms LLT25.bookAt_W
