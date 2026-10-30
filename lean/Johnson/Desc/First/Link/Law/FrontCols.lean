-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrontCols.lean: THE CODE SWITCH's FRONT's READING OF THE CARRIED ROWS AT
A POSITION (`K2.longFront`, Johnson/Top/H0/K2Hears/LongOne.lean) TAKEN APART: the book, the places,
the text's `rowsAt` on one column a message; and each such column's symbols by name (`keptSym`,
`maskSym`). After the steps of `longFront_kept` (K2Hands/KeptLong.lean), for every
message that is opened, kept or not. Theorems.

  `front_inv`: a yes of longFront: there are the book B and the messages' places in it, and rowsAt
    says yes on the columns `openedOne`.
  `front_col`: **the column number w there is the message o := (singleRowsOracles rows)[w]'s: its
    main symbol j is keptSym … o j q, its mask symbol j is maskSym … o j q; it has as many main and
    mask symbols as o's shape in the front's statement has rows.**
Limits. Book-keeping on the text. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.MaskSeatWord
import Johnson.Desc.First.Link.Law.LongTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Own (rowsAt)
open VerifiableInference.Desc.First.K2Hands (keptSym colAtW_one colOne_size)
open _root_.Tw.K2 (switchNotices)

variable {p : First.K2.P2} {s : First.S} {x : _root_.Tw.K2.Front} {orc : ℕ → ℕ → List UInt64}
  {q : ℕ}

/-- The columns that the front opens at the position q. -/
def frontCols (p : First.K2.P2) (x : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64)
    (B : TreeBook) (places : Array (ℕ × ℕ)) (q : ℕ) : Array (Array Column) :=
  First.K2.openedOne (First.K2.skelOf x) B (First.K2.par9 p).firstTree p.logN orc
    ((singleRowsOracles x.f.rows).zip places) q

theorem front_inv {seg : Array E} (h : First.K2.longFront p s x orc q = some seg) :
    ∃ (B : TreeBook) (places : Array (ℕ × ℕ)),
      First.K2.bookAt (First.K2.par9 p).firstTree x.st s.book s.roots
        (switchNotices x.T x.others) = some B ∧
      ((singleRowsOracles x.f.rows).mapM fun o => B.place[o]?) = some places ∧
      rowsAt x.f.rows (frontCols p x orc B places q) #[] 0 = some seg := by
  unfold First.K2.longFront at h
  obtain ⟨B, hB, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨places, hP, h3⟩ := Option.bind_eq_some_iff.1 h2
  exact ⟨B, places, hB, hP, h3⟩

theorem colOne_maskSize {S : Statement} {B : TreeBook} {ft logN : ℕ} {o : ℕ} {pl : ℕ × ℕ}
    {col : Column} (h : First.K2.colOne S B ft logN orc o pl q = some col) :
    col.mask.size = (S.oracles.getD o default).shape.maskRows := by
  unfold First.K2.colOne at h
  split at h
  · rename_i tree y h1 h2
    cases h
    simp [Blk.columnOf, Array.getD_eq_getD_getElem?, h2]
  · cases h

/-- **EACH COLUMN, BY NAME.** -/
theorem front_col {B : TreeBook} {places : Array (ℕ × ℕ)}
    (hB : First.K2.bookAt (First.K2.par9 p).firstTree x.st s.book s.roots
      (switchNotices x.T x.others) = some B)
    (hP : ((singleRowsOracles x.f.rows).mapM fun o => B.place[o]?) = some places) {w : ℕ}
    (hw : w < (singleRowsOracles x.f.rows).size) {c : Column}
    (hc : colAt (frontCols p x orc B places q) 0 w = some c) :
    (∀ j, c.main.getD j zeroE = keptSym p s x orc (singleRowsOracles x.f.rows)[w] j q) ∧
      (∀ j, c.mask.getD j zeroE = maskSym p s x orc (singleRowsOracles x.f.rows)[w] j q) ∧
      c.main.size = ((First.K2.skelOf x).oracles.getD (singleRowsOracles x.f.rows)[w]
        default).shape.mainRows ∧
      c.mask.size = ((First.K2.skelOf x).oracles.getD (singleRowsOracles x.f.rows)[w]
        default).shape.maskRows := by
  obtain ⟨zs, zp⟩ := OnBytes.Slice.array_mapM_inv _ _ _ hP
  obtain ⟨y, hy, h1⟩ := colAtW_one _ _ _ _ _ _ _ _ _ hc
  have hwp : w < places.size := by rw [zs]; exact hw
  have hwz : w < ((singleRowsOracles x.f.rows).zip places).size := by
    rw [Array.size_zip]
    omega
  rw [Array.getElem?_eq_getElem hwz] at hy
  have ey : y = ((singleRowsOracles x.f.rows)[w], places[w]) := by
    rw [← Option.some.inj hy, Array.getElem_zip]
  have hpl := zp w hw
  rw [Array.getElem?_eq_getElem hwp] at hpl
  rw [ey] at h1
  refine ⟨fun j => ?_, fun j => ?_, colOne_size h1, colOne_maskSize h1⟩
  · unfold keptSym
    simp only [hB, Option.bind_some, hpl, h1, Option.map_some, Option.getD_some]
  · unfold maskSym
    simp only [hB, Option.bind_some, hpl, h1, Option.map_some, Option.getD_some]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.front_inv
#print axioms VerifiableInference.Desc.LinkJoin.colOne_maskSize
#print axioms VerifiableInference.Desc.LinkJoin.front_col
