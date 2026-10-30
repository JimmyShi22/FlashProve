-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/CellIsWord.lean: A CELL THAT THE LIBRARY's ONE ACCESSOR READS
OFF A WITNESS's TABLES IS ONE WORD OF THE RULED READER. One statement and its proof, over files of
the sealed library alone. No definition.

  cell_is_word   (dataQ own p (seatTab cs arr ms v)).cell at an array's element (i, c) is
                 wordsFirst arr p.d.st p.d.book v at the array's message, in its main table, at the
                 index of the row and place at which the layout lays (i, c)

It joins three sealed lemmas: dataOf_cell and laidPlace_one
(Johnson/Desc/First/Att/K05CellAt.lean) and words_tabQ
(Johnson/Desc/First/Link/Law/TieThreeEq.lean), whose seven premises are hT to hreal, to the letter.
The witness v is a bound variable.

Limits. Every premise is asked and none is proved here: four on the layout and the frame of the
state's open part (ha, ho, hok, hrp) and words_tabQ's seven, on the statement, the book and the list
of members. No state is given at which they hold together. Nothing on soundness, on completeness or
on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Att.K05CellAt
import Johnson.Desc.First.Link.Law.TieThreeEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params VerifiableInference.Desc
open VerifiableInference.Desc.Sound (Mem MsgT dataQ tabQ seatTab seatOf tabAt seatBy noFirst
  wordsFirst)
open VerifiableInference.Desc.First.Att.P (tableIndex dataOf_cell laidPlace_one)
open VerifiableInference.Desc.LinkJoin (words_tabQ)

/-- **A cell is a word.** v: any witness. -/
theorem cell_is_word {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (own : List (ℕ × ℕ)) (p : K9.Part) (v : Wit Cells Tok MsgT) (c₀ : ℕ × String) (a : ReqArray)
    (o i c : ℕ) (rp : ℕ × ℕ) (sh : OracleShape) (q : ℕ × ℕ) (y : Mem)
    (ha : reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a)
    (ho : p.L.check.frame.whereIs c₀.1 a.message = some o)
    (hok : laidMatrixOk a (p.d.st.rowBits o .main) (p.d.st.placeBits o .main) = true)
    (hrp : laidAt a i c = some rp)
    (hT : tabAt p.d.st.codes arr (seatBy noFirst p.d.book) p.d.st v o =
      v.tab p.d.st.codes sh (arr q.1 q.2) q.1 q.2)
    (hq : p.d.book.place[o]? = some q) (hown : own.contains q = true)
    (hy : (ms.find? fun y => decide (seatOf y = q)) = some y) (hsh : (y.1.l.get y.2).1 = sh)
    (hcs : p.d.st.codes = cs)
    (hreal : tableIndex (p.d.st.rowBits o .main) rp % 2 ^ p.d.st.rowBits o .main <
      OnBytes.Means.realRows p.d.st o .main) :
    (dataQ own p (seatTab cs arr ms v)).cell c₀.1 c₀.2 i c =
      wordsFirst arr p.d.st p.d.book v o .main (tableIndex (p.d.st.rowBits o .main) rp) := by
  have h1 := dataOf_cell p.L.check.rows p.L.check.frame p.d.st
    (tabQ own p.d.st p.d.book (seatTab cs arr ms v)) c₀.1 c₀.2 i c ha ho hok
  rw [laidPlace_one, hrp] at h1
  exact h1.trans
    (words_tabQ cs arr ms own p.d.st p.d.book v o .main _ sh q y hT hq hown hy hsh hcs hreal).symm

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.cell_is_word
