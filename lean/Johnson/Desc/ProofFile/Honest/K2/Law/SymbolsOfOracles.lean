-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SymbolsOfOracles.lean: the kind "the code switch" (K2): THE
FIELD `symbols` OF THE RECORD `MadeAsks`, A THIRD EXCHANGE: `symbolsAre_of_written`
(SymbolsOfWritten.lean) AT A YES OF THE VERIFIER's READING (`ReadIs`), ITS PREMISE ON THE LEAVES
PAID BY `colB_of_orc` (ColumnsOfOracles.lean), WHERE EVERY DEALT COLUMN IS SOME ORACLES' AND THESE
ORACLES HOLD THE SENDERS' WRITTEN COLUMNS. Two lemmas; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding.

  `size_oracles`  with two mask rows the messages read are the layout's members and the fresh mask
  **`symbolsAre_of_orc`**  ⊢ `SymbolsAre` as in `symbolsAre_of_written`, at the reading's own old
      rows, positions and Y
WHAT SPEAKS OF WHAT WAS OPENED. k: the reading's yes. hc: `ColsOf orc` at the columns
dealt. horc: at each read message's tree's key, below the tree's length, orc's column is the
sender's written column.
THE OTHERS, ON THE VERIFIER's STATE, THE PLAN AND THE SIZES, beyond those of
`symbolsAre_of_written`. hpl, hor, htr: each read message's place in the book, its entry in the
statement, its tree. hsh, hpt: the tree's shape and the message's part are the sending's own
layout's. hlogM: the tree of a member with a main row is as long as the positions' range. hlogZ: the
tree of a message with a mask row is no shorter than the mask code. hpos: the listed positions lie
in range.
Limits. «NOT IN FRONT OF A LAW OVER COINS». THE GROUND, of the first kind: opened and Y stand under
k; the columns dealt under hc; orc under horc, which ties it to Vw, rows that hold a run's coins.
Made term and lemma that lift the bar: none: the bar is flat. AN IMPLICATION: IT PAYS NOTHING: none
of its premises is shown here of anything; whether they can be met together is not shown. Vw HOLDS A
RUN's COINS (see SymbolsOfColumns.lean, "Limits"): letters under "for all".
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SymbolsOfWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.ColumnsOfOracles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE readL codeOf)
open Johnson.Prover.Send (Rows shapeAt col skipMain skipMask)
open ProofFile.Honest.K2 (frozenLeft)
open VerifiableInference.Desc.First.K2 (ReadIs ColsOf colB_of_orc)
open _root_.Tw.K2 (SwIn)

set_option quotPrecheck false in
/-- The kept rows, by member and row, as `rowOfComplex` lists them. -/
local notation "keptList" Z =>
  ((Sizes.kept Z).zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b))

/-- With two mask rows the messages read are the layout's members and the fresh mask. -/
theorem size_oracles (s : SingleRows) (hm : s.masks = 2) :
    (singleRowsOracles s).size = s.layout.members.size + 1 := by
  unfold singleRowsOracles
  rw [hm]
  simp

/-- **`SymbolsAre` AT A YES OF THE READING, FROM ORACLES.** pw, tw, Xw: each read message's place in
the book, its tree, its entry in the statement. NOT IN FRONT OF A LAW OVER COINS. -/
theorem symbolsAre_of_orc {i : SwIn} {pos : Positions} {B : TreeBook}
    {left : List _root_.Tw.K2.Col} {Y : Array E} {places : Array (Nat × Nat)}
    {cols : Array (Nat × Array Nat × Array (Array F))} {opened : Array (Array Column)}
    (k : ReadIs i pos B left Y places cols opened) (orc : Nat → Nat → List UInt64)
    (hc : ColsOf orc i.opened) (Z : Sizes) (ms : List GroupMember) (γ : List GE)
    (Pw : Nat → K1.Par) (Vw : Nat → Nat → Rows) (kw : Nat → Nat) (Xw : Nat → OnBytes.Oracle)
    (pw : Nat → Nat × Nat) (tw : Nat → Tree)
    (hm : i.old.masks = 2) (hk : i.old.keptRows = (keptList Z).length)
    (hγ : ∀ t, t < i.old.layout.k → γ.getD t zeroG = readL i.old.gamma t)
    (hZk : Z.kept = (Own.keptNos i.old.layout).map (shapeOf ms))
    (hnos : ((List.range ms.length).filter fun w => keptOf ms w) = Own.keptNos i.old.layout)
    (hkept : ∀ w, w < i.old.layout.members.size → i.old.layout.kept.getD w false = true →
      i.old.layout.mainFirst.getD w none = none)
    (hapM : ∀ w w', w < i.old.layout.members.size → w' < i.old.layout.members.size → w ≠ w' →
      ∀ f f', i.old.layout.mainFirst.getD w none = some f →
      i.old.layout.mainFirst.getD w' none = some f' →
      f + (shapeOf ms w).mainRows ≤ f' ∨ f' + (shapeOf ms w').mainRows ≤ f)
    (hapZ : ∀ w w', w < i.old.layout.members.size → w' < i.old.layout.members.size → w ≠ w' →
      ∀ f f', i.old.layout.maskFirst.getD w none = some f →
      i.old.layout.maskFirst.getD w' none = some f' →
      f + (shapeOf ms w).maskRows ≤ f' ∨ f' + (shapeOf ms w').maskRows ≤ f)
    (hP : ∀ w, w ≤ i.old.layout.members.size → K1.planOkOwn (Pw w) = true)
    (hkw : ∀ w, w ≤ i.old.layout.members.size → kw w < (Pw w).sent.size)
    (hX : ∀ w, w ≤ i.old.layout.members.size → (Xw w).shape = shapeAt (Pw w) (kw w))
    (hs : ∀ w, w < i.old.layout.members.size → shapeOf ms w = shapeAt (Pw w) (kw w))
    (hsF : 2 ^ i.old.layout.h ≤
      (shapeAt (Pw i.old.layout.members.size) (kw i.old.layout.members.size)).maskRows)
    (hcd : ∀ w, w < i.old.layout.members.size → (shapeAt (Pw w) (kw w)).mainRows ≠ 0 →
      (Pw w).codes.base.getD (shapeAt (Pw w) (kw w)).code default =
        Z.codes.base.getD Z.code default)
    (hz : ∀ w, w ≤ i.old.layout.members.size → (shapeAt (Pw w) (kw w)).maskRows ≠ 0 →
      (Pw w).codes.mask.getD (shapeAt (Pw w) (kw w)).maskCode default =
        Z.codes.mask.getD Z.maskCode default)
    (hpl : ∀ w (hw : w < (singleRowsOracles i.old).size),
      i.book.place[(singleRowsOracles i.old)[w]]? = some (pw w))
    (hor : ∀ w (hw : w < (singleRowsOracles i.old).size),
      i.st.oracles[(singleRowsOracles i.old)[w]]? = some (Xw w))
    (htr : ∀ w, w ≤ i.old.layout.members.size → i.book.trees[(pw w).1]? = some (tw w))
    (hsh : ∀ w, w ≤ i.old.layout.members.size → (tw w).shape =
      ((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).shapes.getD
        (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).tree.getD (kw w) 0) {})
    (hpt : ∀ w, w ≤ i.old.layout.members.size → (pw w).2 =
      ((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).part.getD (kw w) 0)
    (hlogM : ∀ w, w < i.old.layout.members.size → (shapeOf ms w).mainRows ≠ 0 →
      (tw w).shape.logN = pos.logN)
    (hlogZ : ∀ w, w ≤ i.old.layout.members.size → (shapeAt (Pw w) (kw w)).maskRows ≠ 0 →
      (codeOf (Z.codes.mask.getD Z.maskCode default)).a ≤ (tw w).shape.logN)
    (hpos : ∀ j, j < pos.all.size → pos.all.getD j 0 < 2 ^ pos.logN)
    (horc : ∀ w, w ≤ i.old.layout.members.size → ∀ x, x < 2 ^ (tw w).shape.logN →
      orc ((tw w).number - i.firstTree) x =
        col (Pw w) (Vw w)
          (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).tree.getD (kw w) 0) x) :
    SymbolsAre Z i.old
      (frozenLeft (Z.codes.base.getD Z.code default) (Z.codes.mask.getD Z.maskCode default) Z.kept
        (foldEndAt i.old.layout Z.codes Z.code Z.maskCode ms (fun w => Vw w (kw w))
          (Vw i.old.layout.members.size (kw i.old.layout.members.size)) γ)) pos Y := by
  refine symbolsAre_of_written Z i.old pos opened Y ms γ Pw Vw kw Xw
    (fun w j => if (tw w).shape.logN == pos.logN then pos.all.getD j 0
      else pos.all.getD j 0 % 2 ^ (tw w).shape.logN)
    hm hk k.hLayout hγ hZk hnos hkept hapM hapZ hP hkw hX hs hsF hcd hz ?_ ?_ ?_
  · intro j _ w hw h0
    show (if (tw w).shape.logN == pos.logN then _ else _) = _
    rw [if_pos (by rw [hlogM w hw h0]; exact beq_self_eq_true _)]
  · intro j _ w hw h0
    show (if (tw w).shape.logN == pos.logN then _ else _) % _ = _
    split
    · rfl
    · exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (hlogZ w hw h0))
  · intro j hj w hw
    have hw' : w < (singleRowsOracles i.old).size := by
      rw [size_oracles _ hm]
      omega
    have hin : (if (tw w).shape.logN == pos.logN then pos.all.getD j 0
        else pos.all.getD j 0 % 2 ^ (tw w).shape.logN) < 2 ^ (tw w).shape.logN := by
      by_cases e : ((tw w).shape.logN == pos.logN) = true
      · rw [if_pos e, beq_iff_eq.1 e]
        exact hpos j hj
      · rw [if_neg e]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
    beta_reduce
    rw [colB_of_orc k orc hc w hw' j hj (pw w) (hpl w hw') (tw w) (htr w hw) (Xw w) (hor w hw'),
      horc w hw _ hin, hsh w hw, hpt w hw]
    unfold skipMain skipMask
    rfl

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.size_oracles
#print axioms VerifiableInference.Desc.K2.Honest.symbolsAre_of_orc
