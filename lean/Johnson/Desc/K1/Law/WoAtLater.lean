-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/WoAtLater.lean: **aWo**: the binder aWo
of k01_fifty, at the wider meaning `plus13 (d13 Dm) dk (mgAll Dm Mg₀)` and
N := Dm.N: the open item `wo m` goes back over an accept of a later sending's sub-protocol.
HOW. The wider meaning's `wo` is `First.FillP1.woAt Dm.d1 Dm.rw13` (`mgAll_wo`; the three layers
leave the field), and `Dm.rw13` is `rwBook Dm.arr Dm.mat13`. `wo_back`
carries `woAt` back over an accept of a member of `KeepsRow`, where the
two readings of the witness agree on the index masks' message (`K13.Law.AgreeAt`).
  `agreeLater`   that agreement at `rwBook`, at both sorts of later sub-protocol: at the digits it
                 is `agreeCommit` (K13/Law/ReaderAtCommit.lean); at the reads that, then
                 `rwBook_same` over the quiet sub-protocol: the steps of `readerAtLater`
                 (K1/Law/ReaderAtLater.lean)
  `aWo_plus13`   **the binder**. The three conditions of `agreeCommit` on the state in front come
                 off the promise: the book's size (`inAt_book`); `indexThere`, which is tied to the
                 open item `pinI` (`pinI_open`, Johnson/Desc/K1/Law/PinIOpen.lean); "K12.bookFits"
                 (`fitsOpen_plus13`, `holds_of_item`)
PREMISES: hM (the base meaning's list of extra public tests is empty) and hfB (the test
`Sound.bookFitsB` says `Book.BookFits`). No other. The binder's own premises on the strings
(`KeptBelow`) and on `wo m` being open are taken and not used; its letter for the base is a function
bL here: at bL := fun l d => baseL aN R₁ R₂ R₃ c l d it is the binder to the letter.
What is not claimed. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RestAtPlus13
import Johnson.Desc.K1.Law.PinIOpen
import Johnson.Desc.K1.Law.ReaderAtLater
import Johnson.Desc.K13.Law.ReaderAtCommit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.K13.Law (openAt plus13 rwBook rwBook_same agreeCommit AgreeAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

/-- **The two readings of the witness agree on the index masks' message**, over an accept on two
rounds of either sort of later sub-protocol. -/
theorem agreeLater {B own : Block S Unit} (hB : Later B own) {Pp Cells Tok : Type} {nR k : ℕ}
    (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin k → Bool) → GE) (x x' : Pp × S)
    (w : Desc.Wit Cells Tok MsgT) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : B.decide x.2 [r₁, r₂] gs = .ok x'.2)
    (hlt : x.2.out.indexMasks < x.2.st.oracles.size)
    (hsz : x.2.book.place.size = x.2.st.oracles.size)
    (htree : ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size) :
    AgreeAt x.2.out.indexMasks (rwBook arr mat x' w) (rwBook arr mat x w) := by
  cases hB with
  | digits q gp l piece digits =>
    exact agreeCommit arr mat _ l 2 digits x x' w r₁ r₂ gs h hlt hsz htree
  | reads Z G l X pr reads =>
    have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide x.2
        ([r₁, r₂].take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          ([r₁, r₂].drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) =
          .ok x'.2 := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    have h1' : (commitAtS (parLater G.first (gpOf Z) l pr 1) l 1 reads : Block S Unit).decide x.2
        [r₁, r₂] _ = .ok s₁ := h1
    obtain ⟨e1, e2⟩ := k1Quiet_book G l X _ _ _ _ h2
    have ew : rwBook arr mat x' w = rwBook arr mat (x.1, s₁) w :=
      rwBook_same arr mat (x.1, s₁) x' e2 (by rw [e1]) (fun o => by rw [e1]) w
    rw [ew]
    exact agreeCommit arr mat _ l 1 reads x (x.1, s₁) w r₁ r₂ _ h1' hlt hsz htree

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE BINDER aWo OF k01_fifty, AT THE WIDER MEANING.** -/
theorem aWo_plus13 (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ BookFits B) (bL : ℕ → Bool → ℕ) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X →
      ∀ (x x' : ProofFile.InstPub × S) y y' w m, YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l d) x y → KeptBelow (bL l d) y y' →
      Item.wo m ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).wo m x' y' w →
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).wo m x y w := by
  intro l hl d X arrs _ x x' y y' w m hy hIn _ _ hw
  obtain ⟨-, rs, gs, hfit, hd⟩ := hy
  obtain ⟨own, hB⟩ := later_blkL Z Bs.G₀ l d X arrs
  have hlen : rs.length = 2 := (Keeps.fit_length _ _ hfit).trans (rounds_blkL Z Bs.G₀ l d X arrs)
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  -- what the promise in front holds
  have hsz := (inAt_book hIn).1
  have hit : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub .indexThere x = true := by
    refine inAt_pub hIn _ (List.mem_append_right _ ?_)
    unfold First.pubOfItems
    rw [List.mem_flatMap]
    exact ⟨.pinI, pinI_open l hl d, by simp⟩
  rw [pub_plus13] at hit
  have hit' : (x.2.st.oracles[x.2.out.indexMasks]?).isSome = true := hit
  have hlt : x.2.out.indexMasks < x.2.st.oracles.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hit'
    cases hit'
  have htree : ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size :=
    holds_of_item (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub (.more none "K12.bookFits")
      Sound.bookFitsB hfB (fun _ => rfl) x
      (inAt_pub hIn _ (fitsOpen_plus13 Dm dk Mg₀ hM l hl d)) _
  have hA := agreeLater hB Dm.arr Dm.mat13 x x' w _ _ gs hd hlt hsz htree
  exact wo_back (keepsRow_blkL Z Bs.G₀ l d X arrs) Dm.d1 Dm.rw13 m x x' y y' w _ gs hd hA hw

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.agreeLater
#print axioms VerifiableInference.Desc.K1.aWo_plus13
