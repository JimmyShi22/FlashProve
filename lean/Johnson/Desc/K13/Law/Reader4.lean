-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Reader4.lean: THE PROOF OF THE STATEMENT THAT
Johnson/Desc/K13/Law/OwedReader4.lean WRITES AS OWED: at W's commitment, what the rows on the table
behind the block say under the reader at the record BEHIND, they say under the reader at the record
IN FRONT (the reader through the record's own book: `rwBook`,
Johnson/Desc/K13/Law/ReaderByBook.lean). One statement on the step, and the owed statement, with
their proofs.
Main names:
  `agree4`: **the two readers agree** (`AgreeAt`) at the record's number of the index masks'
    message: the matrix is read off the witness's cells by both; a mask entry of that message: the
    code table stays (`K1.sendAtS_kept`, `rowsB_same`); so does that message's shape (an older
    message is left whole by the sending; the block behind it leaves every message's shape); its
    place in the book and the tree there stay (`atM4_seated`): so it has one seat
    (`Sound.seatBy_frame`), one table size (`tableSize_of_shape`) and the same words
    (`Sound.wordsBy_congr`).
  `reader4`: the owed statement: the rows on the table and the record's number of the index masks'
    message stay (`atM4_rec`); each row names that message's mask entries alone
    (`pileMasksC_iff`): so it has one truth value under the two readers (`holds_congr`).
What is not claimed. The four premises on the record in front (the rows' mask entries; the message
is there; book and statement are in step; the message's place names a tree that is there): they are
the statement's own. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.OwedReader4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsBy_congr seatBy_frame)

/-- **Over a step of W's commitment the readers at the two records agree** at the matrix and at
every mask entry of the index masks' message. -/
theorem agree4 {Pp Cl Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin k → Bool) → GE) (P : Where) (P' : K1.Par) (x x' : Pp × S)
    (w : Desc.Wit Cells Tok MsgT) (hstep : StepM4 Cl P P' x x')
    (hlt : x.2.out.indexMasks < x.2.st.oracles.size)
    (hsz : x.2.book.place.size = x.2.st.oracles.size)
    (htree : ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q → q.1 < x.2.book.trees.size) :
    AgreeAt x.2.out.indexMasks (rwBook arr mat x' w) (rwBook arr mat x w) := by
  obtain ⟨r₁, r₂, gs, hd⟩ := hstep.decide
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid hd
  have hk := K1.sendAtS_kept P' x.2 s₁ _ g₁ h1
  have hs := rowsB_same h2
  have hseat := (atM4_seated hd).seated
  have hcodes : x'.2.st.codes = x.2.st.codes := hs.1.trans hk.1
  have hshape : (x'.2.st.oracles[x.2.out.indexMasks]?).map (·.shape) =
      (x.2.st.oracles[x.2.out.indexMasks]?).map (·.shape) := by
    have e := congrArg (Option.map fun t : OracleShape × Bool × Array OnBytes.Row ×
      List (OnBytes.Part × ℕ) => t.1) (hs.2 x.2.out.indexMasks)
    unfold sampleOf at e
    rw [hk.2.2 _ hlt] at e
    simpa [Option.map_map, Function.comp_def] using e
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

/-- **The owed statement.** -/
theorem reader4 : OwedReader4 := by
  intro Pp Cl Cells Tok nR k arr mat P P' x x' w hstep hOn hlt hsz htree hT r hr
  obtain ⟨r₁, r₂, gs, hd⟩ := hstep.decide
  obtain ⟨_, _, _, _, hrows⟩ := atM4_rec hd
  rw [hrows] at hr
  exact (holds_congr ρg ((pileMasksC_iff x.2).1 hOn r hr)
    (agree4 arr mat P P' x x' w hstep hlt hsz htree)).1 (hT r (by rw [hrows]; exact hr))

end VerifiableInference.Desc.K13.Law
