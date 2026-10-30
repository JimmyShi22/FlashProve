-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieLow.lean: THE FILLING
FROM THE TABLE'S LETTERS READS LOW: the decoder decT and its condition condT (TieStated.lean),
pulled back to the riding part, read of the oracles the stored table and the two trees in which the
table's messages 0 and 1 lie: so LowDec holds at every c above these two trees' numbers, where the
table's letter coll reads the stored table's cells alone (CellOnly, KeyKeeps23.lean).

Main names:
  posL_no: a position that the library's posL gives for the tree number j lies in a tree with that
    number.
  cell_low, col_low, word_low: the stored table's symbols, a tree's columns and a tenant's committed
    word are the same at two families of strings that agree on the stored table and below c.
  pinsT_low, condT_low: so for what is pinned, and for the condition.
  pick, decT_pick: the decoder is a choice out of a predicate; equal predicates, one choice.
  lowDec_T: LowDec of the pulled-back pair at c.

Object: the links' laws' letters and the table's; Msg.lean's notions.
User: none yet (it pays the premise LowDec of keeps_layer and keeps_k3, KeepsAtRows.lean, up to the
two premises on at_).
Letters: the table's B, at_, coll. Premises: (at_ 0).1 < c · (at_ 1).1 < c · CellOnly coll.

Limits. That the two trees' numbers lie below a piece's place is not shown. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieStated
import Johnson.RunOne.KeyKeeps23

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.TieLow
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi FirstState Source Where FreeAt)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ CellOnly)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.TieStated

/-- A position that posL gives for the tree number j lies in a tree with that number. -/
theorem posL_no {L : List LeftT} {j x : ℕ} {p : PosL L} (h : posL L j x = some p) :
    (L.get p.1).no = j := by
  unfold posL at h
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
  split at hi
  · rename_i hn
    split at hi
    · obtain rfl := Option.some.inj hi
      exact hn
    · cases hi
  · cases hi

variable {Fr : Frame} {c : ℕ} {y y' : Fr.E.Str}

theorem cell_low (h1 : y.1 = y'.1) : cellAt Fr y = cellAt Fr y' := by
  funext x
  unfold cellAt
  rw [h1]

theorem col_low (h2 : ∀ q : PosL Fr.all, (Fr.all.get q.1).no < c → y.2 q = y'.2 q) {j : ℕ}
    (hj : j < c) (x : ℕ) : colAt Fr y j x = colAt Fr y' j x := by
  unfold colAt
  cases hp : posL Fr.all j x with
  | none => rfl
  | some p =>
    show y.2 p = y'.2 p
    exact h2 p (by rw [posL_no hp]; exact hj)

theorem word_low {XI : Type} (F : FileDescription XI)
    (h2 : ∀ q : PosL Fr.all, (Fr.all.get q.1).no < c → y.2 q = y'.2 q) {j : ℕ} (hj : j < c)
    (t : ℕ) : wordOf F (strsOf Fr y) j t = wordOf F (strsOf Fr y') j t := by
  funext x
  show (F.oracleAt j).bind (fun o => o.cut t (colAt Fr y j x)) = _
  rw [col_low h2 hj x]
  rfl

variable {Cells Mm Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {D : WholeD} {B : BaseSt Cells Mm Smp Rec}
  {at_ : Where} {coll : Strs → Rec → Prop}

/-- Two families of strings at which a tenant's committed word is one have one PIN there. -/
theorem pin_word {A : Type} (G : Reading A Cells Mm Smp Rec) {XI : Type} (F : FileDescription XI)
    (j t : ℕ) (a : A) (z z' : Strs) (h : wordOf F z j t = wordOf F z' j t)
    (w : Wit Cells Unit Mm) : PIN F G j t a z w ↔ PIN F G j t a z' w := by
  unfold PIN Member
  rw [h]

theorem noColl_word {A : Type} (G : Reading A Cells Mm Smp Rec) {XI : Type} (F : FileDescription XI)
    (j t : ℕ) (a : A) (z z' : Strs) (h : wordOf F z j t = wordOf F z' j t) :
    NoColl F G j t a z ↔ NoColl F G j t a z' := by
  unfold NoColl Member
  rw [h]

section
variable {c : ℕ} {y y' : (fr₁ D).E.Str}

/-- What is pinned is the same at strings that agree on the stored table and below c. -/
theorem pinsT_low (h1 : y.1 = y'.1)
    (h2 : ∀ q : PosL (fr₁ D).all, ((fr₁ D).all.get q.1).no < c → y.2 q = y'.2 q)
    (h0 : (at_ 0).1 < c) (h1' : (at_ 1).1 < c) (q : Xi × Statement) (w : Wit Cells Unit Mm) :
    PinsT X N P B at_ q (strsOf (fr₁ D) y) w ↔ PinsT X N P B at_ q (strsOf (fr₁ D) y') w := by
  unfold PinsT
  rw [pin_word B.h₁ (Fk X N P) _ _ _ _ _ (word_low (Fk X N P) h2 h0 _) w,
    pin_word B.h₁ (Fk X N P) _ _ _ _ _ (word_low (Fk X N P) h2 h1' _) w]
  have e : (strsOf (fr₁ D) y).cell = (strsOf (fr₁ D) y').cell := cell_low h1
  unfold PINW
  rw [e]

/-- The condition likewise, where coll reads the stored table's cells alone. -/
theorem condT_low (hc : CellOnly coll) (h1 : y.1 = y'.1)
    (h2 : ∀ q : PosL (fr₁ D).all, ((fr₁ D).all.get q.1).no < c → y.2 q = y'.2 q)
    (h0 : (at_ 0).1 < c) (h1' : (at_ 1).1 < c) (q : Xi × Statement) :
    condT X N P D B at_ coll (q, y) ↔ condT X N P D B at_ coll (q, y') := by
  unfold condT
  rw [noColl_word B.h₁ (Fk X N P) _ _ _ _ _ (word_low (Fk X N P) h2 h0 _),
    noColl_word B.h₁ (Fk X N P) _ _ _ _ _ (word_low (Fk X N P) h2 h1' _)]
  have e : (strsOf (fr₁ D) y').cell = (strsOf (fr₁ D) y).cell := (cell_low h1).symm
  have ef : FreeAt B.h₁ coll (atSt q) (strsOf (fr₁ D) y) ↔
      FreeAt B.h₁ coll (atSt q) (strsOf (fr₁ D) y') :=
    exists_congr fun r => and_congr_right fun _ => not_congr (hc _ _ r e).symm
  rw [ef]

end

open Classical in
/-- A choice out of a predicate. -/
def pick {α : Type} (Q : α → Prop) : Option α := if h : ∃ w, Q w then some h.choose else none

/-- The decoder is that choice. -/
theorem decT_pick (a : (Xi × Statement) × (fr₁ D).E.Str) :
    decT X N P D B at_ a = pick fun w => PinsT X N P B at_ a.1 (strsOf (fr₁ D) a.2) w := rfl

/-- **The pulled-back decoder and condition read below c.** -/
theorem lowDec_T {c : ℕ} (hc : CellOnly coll) (h0 : (at_ 0).1 < c) (h1' : (at_ 1).1 < c) :
    LowDec (fun a : TK Xi × (fr₁ D).E.Str => decT X N P D B at_ (pullK a.1, a.2))
      (fun a => condT X N P D B at_ coll (pullK a.1, a.2)) c :=
  lowDec_pull _ _ fun q y y' h1 h2 =>
    ⟨by
      rw [decT_pick, decT_pick]
      exact congrArg pick (funext fun w => propext (pinsT_low h1 h2 h0 h1' q w)),
      condT_low hc h1 h2 h0 h1' q⟩

end Johnson.RunOne.Law.TieLow

#print axioms Johnson.RunOne.Law.TieLow.posL_no
#print axioms Johnson.RunOne.Law.TieLow.word_low
#print axioms Johnson.RunOne.Law.TieLow.pinsT_low
#print axioms Johnson.RunOne.Law.TieLow.condT_low
#print axioms Johnson.RunOne.Law.TieLow.lowDec_T
