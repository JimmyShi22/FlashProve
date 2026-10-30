-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/CarryWords.lean: the witness's words behind the way in are its words in front of the closing.

What is proved.
  `words_congr`     the witness's words at two statements with the same shapes and one book are the same
  `putRec_book`     the lifted closing's laying back writes no book
  `shapes_begun`    the beginning of the test changes no code and no shape
  **`words_front`**   at the first chain's state behind the lifted closing, wherever the next code switch stands and
                   where the way in and the front return: the words that the witness gives at the front's statement and
                   at the book of the state that the way in returns are the words that it gives at the statement and the
                   book of the state t₀ in front of the closing
  **`carryExact_from_front`**   `carryExact_behind_door` (Johnson/Desc/K10/Honest/CarryAtDoor.lean) with its premises on
                   the words stated at the words in front of the closing, `wordsFirst arr t₀.st t₀.book v`

Limits. Those of CarryAtDoor.lean, but for the one on the words: that the way in and the front return, and, at the
head's sort, that the state does not yet stand in the head, are assumptions; so are `CloseBase`, hlen, hs, hP and the
premises on the rounds. No example is given for `carryExact_from_front`; CarryToy.lean's meets the premises of
`carryExact_behind`, the place's sort aside. Nothing is said on soundness, completeness or hiding of the
protocol.
-/
import Johnson.Desc.K10.Honest.CarryAtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsBy_congr)
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.First.K2 (SameShapes)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase ShapedAll)
open ProofFile.Honest.K10.Values (keptLen)

/-- The witness's words at two statements with the same shapes and one book are the same. -/
theorem words_congr {Cells Tok : Type} {S S' : Statement} (h : SameShapes S S') (arr : ℕ → ℕ → ℕ)
    (B : TreeBook) (v : Wit Cells Tok MsgT) : wordsFirst arr S' B v = wordsFirst arr S B v := by
  funext o part i
  exact wordsBy_congr arr _ _ S S' v o o h.codes rfl (h.shape o) part i

/-- The lifted closing's laying back writes no book. -/
theorem putRec_book (t : First.S) (r : Rec) : (K9.putRec t r).book = t.book := by
  show (t.putLive { t.live with frame := r.frame }).book = t.book
  unfold First.S.putLive
  split
  · unfold First.S.putLink
    split
    · rfl
    · rfl
    · split <;> rfl
    · rfl
  · rfl

/-- The beginning of the test changes no code and no shape. -/
theorem shapes_begun (S : Statement) (g : Nat) (G : Group) : SameShapes S (Slice.begun S g G) :=
  ⟨Slice.closeLedgers_codes G.members.toList S, Slice.closeLedgers_shape G.members.toList S⟩

/-- **The words behind the way in are the words in front of the closing.** -/
theorem words_front {Cells Tok : Type} {Zp : ProofFile.Pub} {n : Nat} (arr : ℕ → ℕ → ℕ) (t₀ : First.S)
    (v : Wit Cells Tok MsgT) {t : First.S} {fx : _root_.Tw.K2.Front} (D : BaseData) (f : ReqFrame)
    (hH : (ProofFile.pAtK2 Zp n).stands = .head →
      ∀ x, (K9.putRec t₀ ⟨none, f, spent (D.S1 (K9.recOf t₀)) D.m⟩).here ≠ .head x)
    (hd : doorZ Zp n (K9.putRec t₀ ⟨none, f, spent (D.S1 (K9.recOf t₀)) D.m⟩) = some t)
    (hf : First.K2.frontAt (ProofFile.pAtK2 Zp n) t = some fx) :
    wordsFirst arr fx.st t.book v = wordsFirst arr t₀.st t₀.book v := by
  have hb : t.book = t₀.book := ((door_reads hH hd).book).trans (putRec_book t₀ _)
  have hs : SameShapes t₀.st fx.st :=
    sameShapes_then (sameShapes_then (shapes_begun t₀.st _ D.G) (sameShapes_spent _ D.m))
      (door_shapes hH hd hf)
  rw [hb]
  exact words_congr hs arr t₀.book v

/-- **The exact carry at the state behind the lifted closing, from premises at the words in front of the closing.** -/
theorem carryExact_from_front {Q Cells Tok Cl : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat)
    (z : Q) (t₀ : First.S) (y : Strs) (v : Wit Cells Tok MsgT) {t : First.S}
    {fx : _root_.Tw.K2.Front} {P : Par} {D : BaseData} (H : CloseBase P (K9.recOf t₀) D)
    (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR))
    {row : GroupRow}
    (hrow : Own.batch (D.S1 (K9.recOf t₀)) (K9.recOf t₀).frame.group
      ⟨Own.layoutOf (K9.recOf t₀).st D.G, runRows (K9.recOf t₀).st D.G⟩ (drawnOf rB) = some row)
    (s₁ : First.S)
    (hs₁ : s₁ = K9.putRec t₀ ⟨none, { (K9.recOf t₀).frame with
      rows := foldOutAt (D.S1 (K9.recOf t₀)) (D.F (K9.recOf t₀)) row D.m (rE :: rR), mask := none
      link := (K9.recOf t₀).frame.link + 1, next := .first },
      spent (D.S1 (K9.recOf t₀)) D.m⟩)
    (hH : (ProofFile.pAtK2 Zp n).stands = .head → ∀ x, s₁.here ≠ .head x)
    (hd : doorZ Zp n s₁ = some t) (hf : First.K2.frontAt (ProofFile.pAtK2 Zp n) t = some fx)
    (hlen : 2 ^ (Own.layoutOf (K9.recOf t₀).st D.G).logEll =
      ((D.S1 (K9.recOf t₀)).codes.base.getD (K9.recOf t₀).frame.shape.code default).ell)
    (hs : AllSay rdE (K9.recOf t₀).st (runRows (K9.recOf t₀).st D.G).toList
      (wordsFirst arr t₀.st t₀.book v))
    (W : HIdx (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g)) → GE)
    (γ : HPt (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g)))
    (hP : Pairs (stageB D (K9.recOf t₀)) (stageB D (K9.recOf t₀)).Z.l W
      (freshB D (K9.recOf t₀) (wordsFirst arr t₀.st t₀.book v)))
    (hσ : readE ((sentOf rE).getD 0 zeroE) =
      hMu (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g)) W)
    (hR : Shows ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g) rR
      (foldQK (stageB D (K9.recOf t₀)) (vecG (stageB D (K9.recOf t₀)) row)
        (msgOf (stageB D (K9.recOf t₀)) (tablesOf (D.S1 (K9.recOf t₀))
          (Own.layoutOf (K9.recOf t₀).st D.G) (wordsFirst arr t₀.st t₀.book v))) W
        (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 (K9.recOf t₀))) (tablesOf (D.S1 (K9.recOf t₀))
          (Own.layoutOf (K9.recOf t₀).st D.G) (wordsFirst arr t₀.st t₀.book v)).kept row.kept) γ) γ) :
    carryExact Zp arr n (z, s₁) y v := by
  subst hs₁
  have e := words_front arr t₀ v D _ hH hd hf
  exact carryExact_behind_door (Cl := Cl) Zp arr n z t₀ y v H rB rE rR gs hl hsh hrow _ rfl hH hd hf
    hlen (by rw [e]; exact hs) W γ (by rw [e]; exact hP) hσ (by rw [e]; exact hR)

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.carryExact_from_front
#print axioms ProofFile.Honest.K10.LeftIs.words_congr
#print axioms ProofFile.Honest.K10.LeftIs.putRec_book
#print axioms ProofFile.Honest.K10.LeftIs.shapes_begun
#print axioms ProofFile.Honest.K10.LeftIs.words_front
