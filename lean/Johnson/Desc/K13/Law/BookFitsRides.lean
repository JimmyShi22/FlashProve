-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/BookFitsRides.lean: "EVERY MESSAGE STANDS IN ITS TREE's LIST OF PARTS AT ITS
OWN PART NUMBER" (`Book.BookFits`, Johnson/Desc/Book/BookFits.lean) IS KEPT BY
OUR TWO BLOCKS THAT SEND: W's commitment and the first segment's opening. Statements with their
proofs. Why. The proximity test's layer lays a public item "K12.bookFits", open at the chain's
start and dropped
by nobody: so it rides past every block. A block that sends appends to the book: there it is earned.
  `fitsRecv ft`: the relation "if the book in front fits, so does the book behind" is kept by the
  eight
    functions that write the statement alone (they leave the book) and by the receiving
    (`recvP_fits`, Johnson/Desc/Book/BookFitsGround.lean).
  `atM4_bookFits`, `openingZero_bookFits`: **over a yes of the two blocks.** `rider4_fits`,
  `riderG_fits`: so an item whose Bool says just that of the state's book is a rider at
    the two: i the item, fB its Bool on a book, hfB that the Bool says it.
What is not claimed. That the layer's own Bool says it (that is `bookFitsB_iff`,
Johnson/Desc/Sound/BookTestsLaw.lean). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillGFromSentences
import Johnson.Desc.K13.KeepsCore
import Johnson.Desc.K1.KeepsAtSCore
import Johnson.Desc.Book.BookFitsGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Tied (openLayZero_eq)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Ground (Core CoreStill CoreRecv ByC)
open VerifiableInference.Desc.Book (BookFits recvP_fits)

/-- "If the book in front fits, so does the book behind": kept by the eight and by the receiving. -/
theorem fitsRecv (ft : ℕ) : CoreRecv ft fun a b : Core => BookFits a.book → BookFits b.book :=
  { CoreStill.ofBook (Q := fun A B => BookFits A → BookFits B) (fun _ h => h)
      (fun h k x => k (h x)) with
    recv := fun d d' sent ids h hB => recvP_fits ft d d' sent ids h hB }

section
variable {Pp W Cl : Type}

/-- **W's commitment keeps it.** -/
theorem atM4_bookFits {P : Where} {P' : K1.Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s rs gs = .ok s') (h0 : BookFits s.book) :
    BookFits s'.book :=
  RelCore.atM4_keeps (fitsRecv P'.gp.firstTree).toCoreStill P _
    (K1.RelCore.sendAtS_keeps P' (fitsRecv P'.gp.firstTree)) s rs gs s' h h0

/-- **The first segment's opening keeps it.** -/
theorem openingZero_bookFits {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (h0 : BookFits s.book) : BookFits t.book := by
  obtain ⟨s₁, g₁, h1, h2⟩ := K1.openingZero_mid h
  have h3 : BookFits s₁.book :=
    K1.RelCore.firstAtS_keeps q gp (fitsRecv gp.firstTree) s _ g₁ s₁ h1 h0
  obtain ⟨a, e⟩ := openLayZero_eq h2
  rw [e]
  exact h3

/-- The item is a rider at W's commitment. -/
theorem rider4_fits {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub}
    {p : Option Place} {i : Pub} (fB : TreeBook → Bool) (hfB : ∀ B, fB B = true ↔ BookFits B)
    (hm : i ∈ Q) (hM : ∀ x, Mg.pub i x = fB x.2.book) (hP : ∀ x, Mg.pubP i x) :
    Rider4 Cl P P' N Mg Q p i := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hM] at h0
  exact ⟨by rw [hM]; exact (hfB _).2 (atM4_bookFits hd ((hfB _).1 h0)), fun _ => hP x'⟩

/-- The item is a rider at the first segment's opening. -/
theorem riderG_fits {q : Params.First} {gp : GPar} {nm : String} {X : LayPar} {fvs : List Bool}
    {kCol : ℕ} {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub} {p : Option Place} {i : Pub}
    (fB : TreeBook → Bool) (hfB : ∀ B, fB B = true ↔ BookFits B) (hm : i ∈ Q)
    (hM : ∀ x, Mg.pub i x = fB x.2.book) (hP : ∀ x, Mg.pubP i x) :
    RiderG Cl q gp nm X fvs kCol N Mg Q p i := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hM] at h0
  exact ⟨by rw [hM]; exact (hfB _).2 (openingZero_bookFits hd ((hfB _).1 h0)), fun _ => hP x'⟩

end

end VerifiableInference.Desc.K13.Law
