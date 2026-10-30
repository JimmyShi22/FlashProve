-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/BookHoldsAt.lean: "EVERY PLACE OF THE
BOOK NAMES A TREE THAT THE BOOK HOLDS", OFF THE TABLE OF JOINTS' PROMISE IN FRONT OF A BLOCK, WHERE
A PUBLIC ITEM IS OPEN WHOSE Bool SAYS Book.BookFits OF THE STATE's BOOK
(Johnson/Desc/Book/BookFits.lean: every message stands in its tree's list of parts at its own part
number); AND THAT SUCH AN ITEM RIDES OVER A YES OF K1's TWO SORTS OF LATER BLOCK. Statements with
their proofs.

OBJECT. commitAtS, so laterAt (a link's digits); IM.k1Reads (a link's reads with the quiet step).
USER. (BH) the premise hholds of NewAtSending.lean's new_of_onQ: hholds_of's right side is
BookHolds a.1.book, written out (that file is not imported). (P.fits) an arm of the field pub of
FillL at such an item.
LETTERS. i: the item; fB: its Bool on a book; hfB: that the Bool says BookFits; hM: that the
meaning's pub at i is fB of the state's book. MEANT: i := First.moreItem K12.Door.nFits
("K12.bookFits"), fB := Sound.bookFitsB, hfB := Sound.bookFitsB_iff.
Main names:
  LaterFits B · laterFits_commitAtS | _laterAt | _joined | _k1Reads   a yes keeps BookFits: by
      fitsRecv (Johnson/Desc/K13/Law/BookFitsRides.lean) at
      K1.RelCore.commitAtS_keeps; the quiet step leaves the book (QuietP)
  pub_fits_later   **P.fits**
  holds_of_item · hholds_of   **BH**: by placed_of_fits (Johnson/Desc/Book/BookFits.lean)
IS IT EMPTY HERE? ANOTHER VERSION OF THE COMPOSED MEANING LAYS NO SUCH ITEM (by a look through
Lean: the proximity test's door opens two names at the start; "K12.bookFits" is unknown there): the
letters have their meant member once a version names it. Another road to the same sentence
(K1/Law/BookFacts.lean [not in this library]) goes off "K12.seatsCarried" with a test on the plan.
What is not claimed. That the item is open at any border. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K13.Law.BookFitsRides
import Johnson.Desc.K1.KeepsAtSCore
import Johnson.Desc.K13.Law.AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.Book (BookFits)
open OnBytes.Model.Stages (LinkH)

variable {Cl Pp W : Type} {F : Frame}

/-! ## 1 The book fits behind a yes, where it fitted in front -/

/-- A yes of B, on any rounds, keeps "every message stands in its tree's list of parts at its own
part number". -/
def LaterFits (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, B.decide s rs gs = .ok s' → BookFits s.book → BookFits s'.book

theorem laterFits_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterFits (commitAtS P link moment arrays : Block S Cl) :=
  fun s s' rs gs h h0 =>
    RelCore.commitAtS_keeps P (K13.Law.fitsRecv P.gp.firstTree) link moment arrays s rs gs s' h h0

/-- The first member: a segment's later moment at the plan's numbers (a link's digits). -/
theorem laterFits_laterAt (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) :
    LaterFits (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterFits_commitAtS _ _ _ _

theorem laterFits_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) :
    LaterFits (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h h0
  have h' : ((commitAtS P link moment arrays : Block S Cl).decide s
      (rs.take (commitAtS P link moment arrays : Block S Cl).rounds.length)
      (gs.take (commitAtS P link moment arrays : Block S Cl).openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop (commitAtS P link moment arrays : Block S Cl).rounds.length)
        (gs.drop (commitAtS P link moment arrays : Block S Cl).openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  rw [(hq _ _ _ _ h2).2.1]
  exact laterFits_commitAtS P link moment arrays _ _ _ _ h1 h0

/-- The second member: the reads' place's joined block. -/
theorem laterFits_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) : LaterFits (IM.k1Reads Z G l X pr reads) :=
  laterFits_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _)

/-! ## 2 A public item whose Bool says just that of the state's book -/

section
variable (pub : Pub → Pp × S → Bool) (i : Pub) (fB : TreeBook → Bool)
  (hfB : ∀ B, fB B = true ↔ BookFits B) (hM : ∀ a, pub i a = fB a.2.book)
include hfB hM

/-- **P.fits**: the item over the block's own yes. -/
theorem pub_fits_later {B : Block S Cl} (hB : LaterFits B) (x x' : Pp × S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : B.decide x.2 rs gs = .ok x'.2)
    (h0 : pub i x = true) : pub i x' = true := by
  rw [hM] at h0 ⊢
  exact (hfB _).2 (hB _ _ _ _ h ((hfB _).1 h0))

/-- Where the item holds, every place of the book names a tree that the book holds. -/
theorem holds_of_item (x : Pp × S) (h0 : pub i x = true) :
    ∀ (o : ℕ) (u : ℕ × ℕ), x.2.book.place[o]? = some u → u.1 < x.2.book.trees.size := by
  rw [hM] at h0
  exact fun o u hu => Book.placed_of_fits ((hfB _).1 h0) o u hu

end

/-- **BH: hholds OFF THE PROMISE IN FRONT** (the premise of NewAtSending.lean's new_of_onQ;
its right side is BookHolds a.1.book, written out): where such an item is open in front of block k.
-/
theorem hholds_of (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (z : Pp) (i : Pub) (fB : TreeBook → Bool) (hfB : ∀ B, fB B = true ↔ BookFits B)
    (hM : ∀ a, Mg.pub i a = fB a.2.book)
    (hi : i ∈ (First.pubSets Mg.more links ps)[k]?.getD []) (a : S × F.E.Str)
    (ha : Sound.onQ N Mg links ps (fun s : S => (z, s)) k a) (hm : a.1.failed = none) :
    ∀ (o : ℕ) (u : ℕ × ℕ), a.1.book.place[o]? = some u → u.1 < a.1.book.trees.size := by
  unfold Sound.onQ First.onAt at ha
  obtain ⟨_, hr⟩ := ha
  rcases hr with hx | ⟨h1, _, _, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨_, c5⟩, _⟩ := h1
    unfold First.pubHeld at c5
    exact holds_of_item Mg.pub i fB hfB hM (z, a.1)
      (List.all_eq_true.1 c5 i (List.mem_append_left _ hi))

end VerifiableInference.Desc.K1
