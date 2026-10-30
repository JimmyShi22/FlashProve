-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/ReaderAtCommit.lean: at a later moment's sending, what the rows on the table
behind the block say under the reader at the chain's state BEHIND, they say under the reader at the
chain's state IN FRONT: the reader through the state's own book (rwBook,
Johnson/Desc/K13/Law/ReaderByBook.lean).

  agreeCommit      the two readers agree (AgreeAt) at the state's number of the index masks'
                   message: the code table and that older message's shape stay (Grows:
                   K1.Rel.commitAtS_keeps); its place in the book and the tree there stay
                   (K1.commitAtS_seated): so it has one seat, one table size and the same words.
  ReaderAtCommit, readerAtCommit   the statement and its proof: the rows on the table stay
                   (K1.commitAtS_rows); each names that message's mask entries alone
                   (pileMasksC_iff): so it has one truth value under the two readers.

It follows Johnson/Desc/K13/Law/Reader4.lean, which says the like at W's commitment, step for step.

What is not claimed. The four premises on the chain's state in front (the rows' mask entries; the
message is there; book and statement are in step; the message's place names a tree that is there):
they are the statement's own. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.RowsAtCommit
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.K1.Law.SeatedAtRecord
import Johnson.Desc.K1.KeepsAtS
import Johnson.Goal.Meaning.RecK1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsBy_congr seatBy_frame)
open VerifiableInference.Desc.Ground (groundKeeps_grows)

/-- **Over a yes of a later moment's sending the readers at the two states agree** at the matrix
and at every mask entry of the index masks' message. -/
theorem agreeCommit {Pp Cl Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin k → Bool) → GE) (P : K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) (x x' : Pp × S) (w : Desc.Wit Cells Tok MsgT) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hd : (K1.commitAtS P link moment arrays : Block S Cl).decide x.2 [r₁, r₂] gs = .ok x'.2)
    (hlt : x.2.out.indexMasks < x.2.st.oracles.size)
    (hsz : x.2.book.place.size = x.2.st.oracles.size)
    (htree : ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size) :
    AgreeAt x.2.out.indexMasks (rwBook arr mat x' w) (rwBook arr mat x w) := by
  have G : Grows x.2.st x'.2.st :=
    K1.Rel.commitAtS_keeps groundKeeps_grows P link moment arrays x.2 _ gs x'.2 hd
  have hseat := (K1.commitAtS_seated P link moment arrays x.2 x'.2 r₁ r₂ gs hd).seated
  have hcodes : x'.2.st.codes = x.2.st.codes := G.1
  have hshape : (x'.2.st.oracles[x.2.out.indexMasks]?).map (·.shape) =
      (x.2.st.oracles[x.2.out.indexMasks]?).map (·.shape) := by
    have ha : x.2.st.oracles[x.2.out.indexMasks]? = some x.2.st.oracles[x.2.out.indexMasks] :=
      Array.getElem?_eq_getElem hlt
    obtain ⟨a', ha', hg⟩ := G.2.2 _ _ ha
    rw [ha, ha', Option.map_some, Option.map_some, hg.1]
  have hplace : x'.2.book.place[x.2.out.indexMasks]? = x.2.book.place[x.2.out.indexMasks]? :=
    hseat.places _ (by rw [hsz]; exact hlt)
  have htrees : ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q →
      x'.2.book.trees[q.1]? = x.2.book.trees[q.1]? := fun q hq => hseat.trees q.1 (htree q hq)
  refine ⟨rfl, fun i => ?_⟩
  show maskCut x'.2.st (wordsFirst arr x'.2.st x'.2.book w) ⟨x.2.out.indexMasks, i⟩ =
    maskCut x.2.st (wordsFirst arr x.2.st x.2.book w) ⟨x.2.out.indexMasks, i⟩
  have hw : wordsFirst arr x'.2.st x'.2.book w x.2.out.indexMasks .mask i =
      wordsFirst arr x.2.st x.2.book w x.2.out.indexMasks .mask i := by
    unfold wordsFirst
    exact wordsBy_congr arr _ _ x.2.st x'.2.st w _ _ hcodes
      (seatBy_frame _ x.2.book x'.2.book _ hplace htrees) hshape .mask i
  unfold maskCut
  dsimp only
  rw [tableSize_of_shape hcodes hshape, hw]

/-- **THE READER's PAYER AT A LATER MOMENT's SENDING.** x, x': the chain's states in front of and
behind a yes. The four premises are had from the promise in front. -/
def ReaderAtCommit : Prop :=
  ∀ {Pp Cl Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin k → Bool) → GE) (P : K1.Par) (link moment : Nat)
    (arrays : Option (List Nat)) (x x' : Pp × S) (w : Desc.Wit Cells Tok MsgT) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    (K1.commitAtS P link moment arrays : Block S Cl).decide x.2 [r₁, r₂] gs = .ok x'.2 →
    pileMasksC x.2 = true → x.2.out.indexMasks < x.2.st.oracles.size →
    x.2.book.place.size = x.2.st.oracles.size →
    (∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size) →
    RowsTrue (rwBook arr mat x') x'.2 w → RowsTrue (rwBook arr mat x) x'.2 w

theorem readerAtCommit : ReaderAtCommit := by
  intro Pp Cl Cells Tok nR k arr mat P link moment arrays x x' w r₁ r₂ gs hd hOn hlt hsz htree hT
    r hr
  have hrows := K1.commitAtS_rows P link moment arrays x.2 x'.2 _ gs hd
  rw [hrows] at hr
  exact (holds_congr ρg ((pileMasksC_iff x.2).1 hOn r hr)
    (agreeCommit arr mat P link moment arrays x x' w r₁ r₂ gs hd hlt hsz htree)).1
    (hT r (by rw [hrows]; exact hr))

end VerifiableInference.Desc.K13.Law
