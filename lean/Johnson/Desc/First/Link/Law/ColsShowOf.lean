-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/ColsShowOf.lean: WHO PAYS `ColsShow` (OpenWordAt.lean) AT THE PORTED
GROUP AND THE TABLE's OWN WORDS: the members' columns that the code switch's text cuts at a position
are what `view` shows of the group's word made of the table of joints' reader `wordsOf`
(Johnson/Desc/Sound/MsgSig.lean). By calls: `keptSym_seat`
(Johnson/Top/H0/K2Caller/SeatWord.lean) · `maskSym_seat` (MaskSeatWord.lean) ·
`membPort_wd_main`, `membPort_wd_mask` (Johnson/Desc/First/Close/Law/ViewWord.lean). A theorem. No
other file turns.

  `colsShow_of`: **at R := (rowsPort cs l mem s e oM oZ hM hZ).keep kp and W := R.G.word (wordsOf G
    cs l seat Y): each member a's column at the position q has the written shape's rows, its symbols
    are keptSym | maskSym at the message number no a · KeptSeat and MaskSeat at every member ⊢
    ColsShow R ix opened i W ‹q as a main position› () ‹q as a mask position› ().**
Limits. `KeptSeat` and `MaskSeat` at every member are premises, shown at no value. That the columns
are keptSym | maskSym's is a premise (the book's places: `colAtW_one`). Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.OpenWordAt
import Johnson.Desc.First.Link.Law.MaskSeatWord
import Johnson.Desc.First.Close.Law.ViewWord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Johnson.Top.H Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs wordOf)
open VerifiableInference.Desc.Sound (rowAt wordsOf wordAt)
open VerifiableInference.Desc.First.K2Caller (KeptSeat keptSym_seat)
open VerifiableInference.Desc.First.K2Hands (keptSym)
open VerifiableInference.Desc.First.Close (membPort_wd_main membPort_wd_mask)

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]

local notation "RP" => Johnson.Top.H.Rows.keep (rowsPort cs l mem s e oM oZ hM hZ) kp

/-- **ColsShow AT THE PORTED GROUP AND THE TABLE's WORDS.** -/
theorem colsShow_of {Xi : Type} (G : FileDescription Xi) (seat : Fin l.length → ℕ × ℕ) (Y : Strs)
    (p : First.K2.P2) (t : First.S) (fx : _root_.Tw.K2.Front) (orc : ℕ → ℕ → List UInt64)
    (no : {i // mem i} → ℕ) (ix : {i // mem i} → ℕ) (opened : Array (Array Column)) (i : ℕ)
    (q : Fin (2 ^ s.C.a))
    (hc : ∀ a c, colAt opened i (ix a) = some c →
      c.main.size = (l.get a.1).1.mainRows ∧ c.mask.size = (l.get a.1).1.maskRows ∧
      (∀ j, c.main.getD j zeroE = keptSym p t fx orc (no a) j q.val) ∧
      ∀ j, c.mask.getD j zeroE = maskSym p t fx orc (no a) j q.val)
    (KS : ∀ a : {i // mem i}, (l.get a.1).1.mainRows ≠ 0 →
      KeptSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1) (2 ^ (cMain cs (l.get a.1).1).a))
    (MS : ∀ a : {i // mem i}, MaskSeat G p t fx orc Y (no a) (l.get a.1).1 (seat a.1)
      (2 ^ s.C.a) fun x => x % 2 ^ aOf cs (l.get a.1).1) :
    ColsShow RP ix opened i ((RP).G.word (wordsOf G cs l seat Y)) q () q () where
  nM := fun a c h => (hc a c h).1
  nZ := fun a c h => (hc a c h).2.1
  main := fun a c j h => by
    have h0 : (l.get a.1).1.mainRows ≠ 0 := fun e0 => absurd j.isLt (by
      show ¬ j.val < (l.get a.1).1.mainRows
      omega)
    have eC := hM a.1 a.2 h0
    have hq : q.val < 2 ^ (cMain cs (l.get a.1).1).a := by rw [eC]; exact q.isLt
    have e1 : readV c.main j.val = readE (keptSym p t fx orc (no a) j.val q.val) :=
      congrArg readE ((hc a c h).2.2.1 j.val)
    rw [e1, keptSym_seat (KS a h0) j.val q.val j.isLt hq]
    exact (membPort_wd_main cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2)
      (hZ a.1 a.2) (fun x => (RP).G.word (wordsOf G cs l seat Y) ⟨a, x⟩) q ⟨q.val, hq⟩ rfl j).symm
  mask := fun a c j h => by
    have e1 : readV c.mask j.val = readE (maskSym p t fx orc (no a) j.val q.val) :=
      congrArg readE ((hc a c h).2.2.2 j.val)
    rw [e1, maskSym_seat (MS a) j.val q.val j.isLt q.isLt]
    exact (membPort_wd_mask cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2)
      (hZ a.1 a.2) (fun x => (RP).G.word (wordsOf G cs l seat Y) ⟨a, x⟩) q j).symm

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.colsShow_of
