-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ReaderMaskScript.lean: UNDER FIVE PUBLIC TESTS ON THE VERIFIER's
STATE AND SIX FACTS ON PUBLIC LISTS, AT EVERY NUMBER k BELOW THE COUNT OF FREE ENTRIES: WHAT THE
READER OF THE ROWS ON THE TABLE (`rwBook`, Johnson/Desc/K13/Law/ReaderByBook.lean) READS, OFF A
SCRIPT's WITNESS (`Script.wit`, Honest/Thread/First.lean), AT THE MASK ENTRY THAT A LEDGER's TAKE
NUMBER k HANDS OUT, IS ONE ENTRY OF THE SCRIPT's MESSAGE: mask row k % R, place k / R, of the
message whose number is `arr` at the message's place in the book of trees. Two statements with their
proofs; no definition.

Main names: `reader_mask_script`: **the entry read is `Q.msg n c w (hd.take (Q.fixedMsg n)) true (k
% R) (k / R)`, n := arr q.1 q.2**: the left side of `OwnMsgs` (Honest/Thread/ScriptLots.lean), to
the letter. `reader_mask_own`: **so under `OwnMsgs` at that number, where the text answers y at that
row and place: the entry read is y.**

TWO NUMBERS, NOT ONE. o is the message's number among the statement's oracle messages; n := arr q.1
q.2 is its number in the witness, q the pair (tree, part of the tree) that the public list L has for
o. No statement here says that the two are equal.

How. `OnBytes.Road.K4.Rec.mask_entry_at` (Johnson/Road/K4/Rec/MaskEntry.lean), whose premises these
are, to the letter: it ends at the witness's one accessor `Wit.tab`
(Johnson/Desc/Sound/MsgSig.lean), which reads the pad's component at the pad's places and the
message's elsewhere; `free_off_pad` (Johnson/Desc/K13/Honest/TakenList.lean): a free entry is no
place of the pad; the rest is `Script.wit`'s text.

Why. Three kinds spend entries of the index masks' message (K4, K11, K13), and each ties what the
reader reads there to what the book lends. K13 reads 1 + 2 kCol entries through the reader at the
one state in front of its taking: so the statement is wanted at every k, not at the next take alone.

Limits. Conditional: that a state passes the five tests is shown here of no state. General in the
Script: nothing says what a Script's message holds. An entry is called neither a coin nor fresh nor
masked here.

What is not claimed. That any Script has `OwnMsgs` at any text. Which member sends the message. It
is none of the library's goals. Nothing on soundness, completeness or hiding.
-/
import Johnson.Road.K4.Rec.MaskEntry
import Johnson.Desc.K13.Honest.TakenList
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB)
open VerifiableInference.Desc.K13.Law (rwBook)
open VerifiableInference.Desc.K13.Honest (free_off_pad)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script OwnMsgs)

variable {Bk : ProverCoinCounts} {W Pp Cells Tok : Type} {nR kC : ℕ}

/-- **THE ENTRY THAT THE READER READS AT THE TAKE NUMBER k IS ONE ENTRY OF THE SCRIPT's MESSAGE.**
CONDITIONAL: the five tests on the state s (h₁ h₂ h₃ hs hb); the message o is there, with the shape
sh and the pair q of the public lists; it has a mask row and an answer; k is below its count of free
entries. -/
theorem reader_mask_script (Q : Script Bk W Cells Tok MsgT) (c : Coins Bk) (w : W)
    (hd : List Fmt.Drawn) (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin kC → Bool) → GE)
    (M : List OracleShape) (L : Laid) (z : Pp) (s : S) (o k : ℕ) (sh : OracleShape) (q : ℕ × ℕ)
    (h₁ : msgShapesB M s.st = true) (h₂ : bookInOrderB 0 s.book s.roots = true)
    (h₃ : seatsCarriedB L s.book = true) (hs : s.book.place.size = s.st.oracles.size)
    (hb : placesBelowB L s.book.place.size s.book.trees.size = true)
    (ho : o < s.st.oracles.size) (hsh : M[o]? = some sh) (hq : L.places[o]? = some q)
    (hm : 0 < sh.maskRows) (h1 : 1 ≤ sh.answers)
    (hk : k < Send.freeMaskEntries sh.maskRows (s.st.codes.mask.getD sh.maskCode default).ell
      sh.answers) :
    (rwBook arr mat (z, s) (Q.wit c w hd)).mask ⟨o, takenNo sh.maskRows k⟩ =
      Q.msg (arr q.1 q.2) c w (hd.take (Q.fixedMsg (arr q.1 q.2))) true (k % sh.maskRows)
        (k / sh.maskRows) := by
  rw [OnBytes.Road.K4.Rec.mask_entry_at arr mat M L z s (Q.wit c w hd) o k sh q h₁ h₂ h₃ hs hb ho
    hsh hq hm h1 hk]
  unfold VerifiableInference.Desc.Wit.tab
  rw [free_off_pad s.st.codes sh k h1 hk, if_neg Bool.false_ne_true]
  rfl

/-- **SO UNDER `OwnMsgs` AT THAT NUMBER THE ENTRY READ IS WHAT THE TEXT ANSWERS.** CONDITIONAL: as
`reader_mask_script`; the input is one that Vd admits; at least N challenges; the text answers y at
that row and place. -/
theorem reader_mask_own (Q : Script Bk W Cells Tok MsgT) (c : Coins Bk) (w : W)
    (hd : List Fmt.Drawn) (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin kC → Bool) → GE)
    (M : List OracleShape) (L : Laid) (z : Pp) (s : S) (o k : ℕ) (sh : OracleShape) (q : ℕ × ℕ)
    (h₁ : msgShapesB M s.st = true) (h₂ : bookInOrderB 0 s.book s.roots = true)
    (h₃ : seatsCarriedB L s.book = true) (hs : s.book.place.size = s.st.oracles.size)
    (hb : placesBelowB L s.book.place.size s.book.trees.size = true)
    (ho : o < s.st.oracles.size) (hsh : M[o]? = some sh) (hq : L.places[o]? = some q)
    (hm : 0 < sh.maskRows) (h1 : 1 ≤ sh.answers)
    (hk : k < Send.freeMaskEntries sh.maskRows (s.st.codes.mask.getD sh.maskCode default).ell
      sh.answers)
    {Vd : W → Prop} {N fx : ℕ}
    {txt : Coins Bk → W → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE} {y : GE}
    (hO : OwnMsgs Q Vd N (arr q.1 q.2) fx txt) (hv : Vd w) (hN : N ≤ hd.length)
    (ht : txt c w (hd.take fx) true (k % sh.maskRows) (k / sh.maskRows) = some y) :
    (rwBook arr mat (z, s) (Q.wit c w hd)).mask ⟨o, takenNo sh.maskRows k⟩ = y :=
  (reader_mask_script Q c w hd arr mat M L z s o k sh q h₁ h₂ h₃ hs hb ho hsh hq hm h1 hk).trans
    (hO c w hd hv hN true _ _ y ht)

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.reader_mask_script
#print axioms ProofFile.Honest.K13.reader_mask_own
