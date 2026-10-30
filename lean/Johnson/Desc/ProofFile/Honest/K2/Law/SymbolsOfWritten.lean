-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SymbolsOfWritten.lean: the kind "the code switch" (K2): THE
FIELD `symbols` OF THE RECORD `MadeAsks`, EXCHANGED ONCE MORE: `symbolsAre_of_columns`
(SymbolsOfColumns.lean) WITH ITS FIVE PREMISES ON THE COLUMNS PAID BY THE LIBRARY's `send_enc`
(Johnson/Prover/Send/Enc.lean), WHERE EACH OPENED COLUMN IS THE CUT OF A SENDING's WRITTEN COLUMN.
No frame and no run. Two lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or
hiding.

  `tailIn_eq`  the two texts of a main row's tail in the extension field (`tailIn`,
      Johnson/Desc/K2/Honest/Carry/FoldEndSums.lean; `Rows.mainTl`, Johnson/Prover/Send/Front.lean)
      are one
  **`symbolsAre_of_written`**  ⊢ `SymbolsAre` as in `symbolsAre_of_columns`, the members' rows being
      the senders': M w := Vw w (kw w), and the fresh mask's Vw n (kw n) at n := the number of the
      layout's members
THE LETTERS, for each of the layout's members and, at the number n, for the fresh mask. Pw:
the place of the sending that sent the message. Vw: that sending's rows. kw: the message's number in
it. Xw: the message's entry in the statement. xw: the position at which its tree was opened, by
listed position.
THE TWO THAT SPEAK OF WHAT WAS OPENED. hY, one of the nine of `symbolsAre_of_columns`: the
verifier's own reading of the opened columns returns Y. hleaf: the column that the reading holds of
the message at a listed position is `Blk.columnOf` (OnBytes/Iop/Ground.lean), at the two skips of
the sending's own layout, of that sending's written column (`col`, Johnson/Prover/Send/Core.lean) at
xw.
THE PUBLIC ONES. The other eight of these nine. hP: the sending's plan passes its test.
hkw: the message is one of the sending's. hX, hs, hsF: the shapes are the sending's; the fresh mask
has at least 2^h mask rows. hc, hz: the code of a message that has main rows, and the mask code of
one that has mask rows, are the sizes' (`Blk.join`, OnBytes/Iop/Ground.lean, asks no more of a
member). hx: a member with a main row was opened at the listed position itself. hxz: the position of
a message with a mask row is the listed one modulo the mask code's length.
Limits. NOT IN FRONT OF A LAW OVER COINS. AN IMPLICATION: IT PAYS NOTHING: none of
its premises is shown here of anything; whether they can be met together is not shown. That the
senders' rows are those that a closing makes anew is not said. Vw HOLDS A RUN's COINS (see
SymbolsOfColumns.lean, "Limits"): letters under "for all".
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SymbolsOfColumns
import Johnson.Prover.Send.Enc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE readL codeOf)
open Johnson.Prover.Send (Rows shapeAt col skipMain skipMask send_enc)
open Johnson.Prover.Link (symG)
open ProofFile.Honest.K2 (frozenLeft)

set_option quotPrecheck false in
/-- The kept rows, by member and row, as `rowOfComplex` lists them. -/
local notation "keptList" Z =>
  ((Sizes.kept Z).zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b))

/-- The two texts of a main row's tail in the extension field are one. -/
theorem tailIn_eq (R : Rows) (e : Bool) (b q : Nat) : tailIn R e b q = R.mainTl e b q := by
  unfold tailIn Johnson.Prover.Send.Rows.mainTl
  split
  · rfl
  · show OnBytes.Slice.toE (Fmt.Fld.ofF (OnBytes.Slice.ofF (R.mainTlF b q))) = _
    rw [OnBytes.Slice.toE_ofF, OnBytes.Slice.toF_ofF]

/-- **`SymbolsAre` FROM WRITTEN COLUMNS.** Pw, Vw, kw, Xw, xw: for each of the layout's members, and
for the fresh mask at the number behind the last: the sending's place, its rows, the message's
number in it, the message's entry in the statement, the position at which its tree was opened.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem symbolsAre_of_written (Z : Sizes) (old : SingleRows) (pos : Positions)
    (opened : Array (Array Column)) (Y : Array E) (ms : List GroupMember) (γ : List GE)
    (Pw : Nat → K1.Par) (Vw : Nat → Nat → Rows) (kw : Nat → Nat) (Xw : Nat → OnBytes.Oracle)
    (xw : Nat → Nat → Nat)
    (hm : old.masks = 2) (hk : old.keptRows = (keptList Z).length)
    (hY : Own.rowsSymbols old opened pos.all.size = some Y)
    (hγ : ∀ t, t < old.layout.k → γ.getD t zeroG = readL old.gamma t)
    (hZk : Z.kept = (Own.keptNos old.layout).map (shapeOf ms))
    (hnos : ((List.range ms.length).filter fun w => keptOf ms w) = Own.keptNos old.layout)
    (hkept : ∀ w, w < old.layout.members.size → old.layout.kept.getD w false = true →
      old.layout.mainFirst.getD w none = none)
    (hapM : ∀ w w', w < old.layout.members.size → w' < old.layout.members.size → w ≠ w' →
      ∀ f f', old.layout.mainFirst.getD w none = some f →
      old.layout.mainFirst.getD w' none = some f' →
      f + (shapeOf ms w).mainRows ≤ f' ∨ f' + (shapeOf ms w').mainRows ≤ f)
    (hapZ : ∀ w w', w < old.layout.members.size → w' < old.layout.members.size → w ≠ w' →
      ∀ f f', old.layout.maskFirst.getD w none = some f →
      old.layout.maskFirst.getD w' none = some f' →
      f + (shapeOf ms w).maskRows ≤ f' ∨ f' + (shapeOf ms w').maskRows ≤ f)
    (hP : ∀ w, w ≤ old.layout.members.size → K1.planOkOwn (Pw w) = true)
    (hkw : ∀ w, w ≤ old.layout.members.size → kw w < (Pw w).sent.size)
    (hX : ∀ w, w ≤ old.layout.members.size → (Xw w).shape = shapeAt (Pw w) (kw w))
    (hs : ∀ w, w < old.layout.members.size → shapeOf ms w = shapeAt (Pw w) (kw w))
    (hsF : 2 ^ old.layout.h ≤
      (shapeAt (Pw old.layout.members.size) (kw old.layout.members.size)).maskRows)
    (hc : ∀ w, w < old.layout.members.size → (shapeAt (Pw w) (kw w)).mainRows ≠ 0 →
      (Pw w).codes.base.getD (shapeAt (Pw w) (kw w)).code default =
        Z.codes.base.getD Z.code default)
    (hz : ∀ w, w ≤ old.layout.members.size → (shapeAt (Pw w) (kw w)).maskRows ≠ 0 →
      (Pw w).codes.mask.getD (shapeAt (Pw w) (kw w)).maskCode default =
        Z.codes.mask.getD Z.maskCode default)
    (hx : ∀ i, i < pos.all.size → ∀ w, w < old.layout.members.size →
      (shapeOf ms w).mainRows ≠ 0 → xw w i = pos.all.getD i 0)
    (hxz : ∀ i, i < pos.all.size → ∀ w, w ≤ old.layout.members.size →
      (shapeAt (Pw w) (kw w)).maskRows ≠ 0 →
      xw w i % 2 ^ (codeOf (Z.codes.mask.getD Z.maskCode default)).a =
        pos.all.getD i 0 % 2 ^ (codeOf (Z.codes.mask.getD Z.maskCode default)).a)
    (hleaf : ∀ i, i < pos.all.size → ∀ w, w ≤ old.layout.members.size →
      colB opened w i =
        Blk.columnOf (Xw w)
          (skipMain (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).shapes.getD
              (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).tree.getD (kw w) 0) {})
            (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).part.getD (kw w) 0))
          (skipMask (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).shapes.getD
              (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).tree.getD (kw w) 0) {})
            (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).part.getD (kw w) 0))
          (col (Pw w) (Vw w)
            (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).tree.getD (kw w) 0)
            (xw w i)).toArray) :
    SymbolsAre Z old
      (frozenLeft (Z.codes.base.getD Z.code default) (Z.codes.mask.getD Z.maskCode default) Z.kept
        (foldEndAt old.layout Z.codes Z.code Z.maskCode ms (fun w => Vw w (kw w))
          (Vw old.layout.members.size (kw old.layout.members.size)) γ)) pos Y := by
  have key := fun (i : Nat) (hi : i < pos.all.size) (w : Nat)
      (hw : w ≤ old.layout.members.size) => by
    have h := send_enc (Pw w) (Vw w) (hP w hw) (kw w) (Xw w) (xw w i) (hkw w hw) (hX w hw)
    dsimp only at h
    rw [← hleaf i hi w hw] at h
    exact h
  refine symbolsAre_of_columns Z old pos opened Y ms (fun w => Vw w (kw w)) _ γ hm hk hY hγ hZk
    hnos hkept hapM hapZ ?_ ?_ ?_ ?_ ?_
  · intro i hi w hw
    rw [hs w hw]
    exact (key i hi w (Nat.le_of_lt hw)).1
  · intro i hi w hw b hb
    have hb' : b < (shapeAt (Pw w) (kw w)).mainRows := by
      rw [← hs w hw]
      exact hb
    have h := (key i hi w (Nat.le_of_lt hw)).2.2.1 b hb'
    rw [hc w hw (by omega), hx i hi w hw (by omega)] at h
    rw [h, hs w hw]
    exact congrArg _ (funext fun q => (tailIn_eq _ _ _ _).symm)
  · intro i hi w hw
    rw [hs w hw]
    exact (key i hi w (Nat.le_of_lt hw)).2.1
  · intro i hi w hw b hb
    have hb' : b < (shapeAt (Pw w) (kw w)).maskRows := by
      rw [← hs w hw]
      exact hb
    have h := (key i hi w (Nat.le_of_lt hw)).2.2.2 b hb'
    rw [hz w (Nat.le_of_lt hw) (by omega), hxz i hi w (Nat.le_of_lt hw) (by omega)] at h
    exact h
  · intro i hi b hb
    have hb' : b < (shapeAt (Pw old.layout.members.size) (kw old.layout.members.size)).maskRows :=
      Nat.lt_of_lt_of_le hb hsF
    have h := (key i hi _ (Nat.le_refl _)).2.2.2 b hb'
    rw [hz _ (Nat.le_refl _) (by omega), hxz i hi _ (Nat.le_refl _) (by omega)] at h
    exact h

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.tailIn_eq
#print axioms VerifiableInference.Desc.K2.Honest.symbolsAre_of_written
