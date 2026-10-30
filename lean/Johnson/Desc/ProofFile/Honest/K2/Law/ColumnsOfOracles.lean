-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ColumnsOfOracles.lean: the kind "the code switch" (K2): AT A
YES OF THE VERIFIER's READING OF THE OLD ROWS (`ReadIs`, Johnson/Top/H0/Tw/K2C/Closed.lean), WHERE
EVERY COLUMN DEALT IS SOME ORACLES' (`ColsOf`, Johnson/Top/H0/K2Hears/LongCols.lean): THE COLUMN
THAT THE READING HOLDS OF READ MESSAGE NUMBER w AT LISTED POSITION NUMBER j, WRITTEN OUT. One lemma;
NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  **`colB_of_orc`**  `colB opened w j` (OnBytes/Iop/SymbolLaws.lean) is `Blk.columnOf`, at the
      book's two skips, of the oracles' column at the tree's key and at the listed position (at a
      shorter tree: modulo its length)
How. A join of sealed laws: `open_good`, `symbolsAt_one` (LongCols.lean), `array_mapM_inv`
(OnBytes/Slice/BlkOpenN.lean).
Limits. «NOT IN FRONT OF A LAW OVER COINS». THE GROUND, of the first kind: opened and y stand under
k, the columns dealt under hc: letters; whoever lays orc at tables that are made of coins ties all
three to the coins. Made term and lemma that lift the bar: none: the bar is flat. Nothing says whose
columns orc holds; that the dealt columns are its own is asked, not shown. So are the message's
place, tree and entry.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Top.H0.K2Hears.LongCols
import OnBytes.Iop.SymbolLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn)

/-- **The column that the reading holds**, off the oracles. -/
theorem colB_of_orc {i : SwIn} {pos : Positions} {B : TreeBook} {left : List _root_.Tw.K2.Col}
    {y : Array E} {places : Array (Nat × Nat)}
    {cols : Array (Nat × Array Nat × Array (Array F))} {opened : Array (Array Column)}
    (k : ReadIs i pos B left y places cols opened) (orc : Nat → Nat → List UInt64)
    (hc : ColsOf orc i.opened) (w : Nat) (hw : w < (singleRowsOracles i.old).size) (j : Nat)
    (hj : j < pos.all.size) (p : Nat × Nat)
    (hp : i.book.place[(singleRowsOracles i.old)[w]]? = some p) (tree : Tree)
    (ht : i.book.trees[p.1]? = some tree) (x : OnBytes.Oracle)
    (hx : i.st.oracles[(singleRowsOracles i.old)[w]]? = some x) :
    colB opened w j =
      Blk.columnOf x ((tree.shape.mainSymbols.extract 0 p.2).foldl (· + ·) 0)
        (tree.shape.mainWidth + (tree.shape.maskSymbols.extract 0 p.2).foldl (· + ·) 0)
        (orc (tree.number - i.firstTree)
          (if tree.shape.logN == pos.logN then pos.all.getD j 0
            else pos.all.getD j 0 % 2 ^ tree.shape.logN)).toArray := by
  have hg : ∀ m ∈ cols.toList, GoodOpened i.book i.firstTree pos orc m :=
    open_good _ (i.book, i.opened, #[]) (B, left, cols) k.hOpen hc
      (fun m hm => by simp at hm)
  obtain ⟨z1, z2⟩ := OnBytes.Slice.array_mapM_inv _ _ _ k.hSymbols
  obtain ⟨p1, p2⟩ := OnBytes.Slice.array_mapM_inv _ _ _ k.hPlaces
  have hwp : w < places.size := by
    rw [p1]
    exact hw
  have hwz : w < ((singleRowsOracles i.old).zip places).size := by
    rw [Array.size_zip, p1, Nat.min_self]
    exact hw
  have hwo : w < opened.size := by
    rw [z1]
    exact hwz
  have hpw : places[w] = p := by
    have h := p2 w hw
    rw [hp, Array.getElem?_eq_getElem hwp] at h
    exact (Option.some.inj h).symm
  have h3 := z2 w hwz
  rw [Array.getElem_zip, hpw, Array.getElem?_eq_getElem hwo] at h3
  have h4 := symbolsAt_one h3 hg j hj
  unfold colOne at h4
  rw [ht, hx] at h4
  unfold colB
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwo]
  show ((opened[w])[j]?).getD {} = _
  rw [h4]
  rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.colB_of_orc
