-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PileAtPlus13.lean: **aPile**: the
binder aPile of k01_fifty at the wider meaning
`plus13 (d13 Dm) dk (mgAll Dm Mg₀)` and N := Dm.N: the open item `pile` goes back over an accept of
a later sending's sub-protocol. UNDER hM AND hfB ALONE: it does not go through `MgK13`, `PlanK13` or
`reader_four`, as `aPile_of` does.
HOW. The wider meaning's `pile` is `fun x _ w => RowsTrue (Dm.rw13 x) x.2 w` (`mgAll_pile`; the
three layers leave the field), and `Dm.rw13` is `rwBook Dm.arr Dm.mat13`: so `pileBack_book`
(K1/Law/ReaderAtLater.lean) carries it back. Its four conditions on the state in front come off the
promise at the wider meaning:
  `front_four`   "K13.pileMasks" (`hkIn_plus13`); `indexThere`, tied to the open item `pinI`
                 (`pinI_open`); the book's size (`inAt_book`); "K12.bookFits" (`fitsOpen_plus13`,
                 `holds_of_item`)
  `aPile_plus13`   **the binder**; its letter for the base is a function bL, as in `aWo_plus13`
What is not claimed. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.WoAtLater
import Johnson.Desc.K1.Law.DoorFactsAtPlus13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13 (pileMasksC)
open VerifiableInference.Desc.K13.Law (openAt plus13 pileMasksItem)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **What the promise in front of a later place holds of the state**, at the wider meaning. -/
theorem front_four (hM : Mg₀.more = {}) (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B)
    (l : ℕ) (hl : l < 25) (d : Bool) (x : P × S) (y : Strs)
    (hIn : InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
      (noL l d) x y) :
    pileMasksC x.2 = true ∧ x.2.out.indexMasks < x.2.st.oracles.size ∧
      x.2.book.place.size = x.2.st.oracles.size ∧
      ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size := by
  have hOn : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub pileMasksItem x = true :=
    inAt_pub hIn _ (List.mem_append_left _ (hkIn_plus13 Dm dk Mg₀ hM l hl d))
  have hit : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub .indexThere x = true := by
    refine inAt_pub hIn _ (List.mem_append_right _ ?_)
    unfold First.pubOfItems
    rw [List.mem_flatMap]
    exact ⟨.pinI, pinI_open l hl d, by simp⟩
  rw [pub_plus13] at hit
  have hit' : (x.2.st.oracles[x.2.out.indexMasks]?).isSome = true := hit
  refine ⟨hOn, ?_, (inAt_book hIn).1, ?_⟩
  · by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hit'
    cases hit'
  · exact holds_of_item (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub (.more none "K12.bookFits")
      Sound.bookFitsB hfB (fun _ => rfl) x
      (inAt_pub hIn _ (fitsOpen_plus13 Dm dk Mg₀ hM l hl d)) _

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE BINDER aPile OF k01_fifty, AT THE WIDER MEANING.** -/
theorem aPile_plus13 (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B) (bL : ℕ → Bool → ℕ) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X →
      ∀ (x x' : ProofFile.InstPub × S) y y' w, YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l d) x y → KeptBelow (bL l d) y y' →
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pile x' y' w →
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pile x y w := by
  intro l hl d X arrs _ x x' y y' w hy hIn _ hw
  obtain ⟨-, rs, gs, hfit, hd⟩ := hy
  obtain ⟨own, hB⟩ := later_blkL Z Bs.G₀ l d X arrs
  have hlen : rs.length = 2 := (Keeps.fit_length _ _ hfit).trans (rounds_blkL Z Bs.G₀ l d X arrs)
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨hOn, hlt, hsz, htree⟩ := front_four Dm dk Mg₀ hM hfB l hl d x y hIn
  exact pileBack_book hB Dm.arr Dm.mat13 x x' w _ _ gs hd hOn hlt hsz htree hw

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.front_four
#print axioms VerifiableInference.Desc.K1.aPile_plus13
