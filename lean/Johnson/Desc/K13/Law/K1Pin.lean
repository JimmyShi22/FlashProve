-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/K1Pin.lean: the two pieces of kind K13's row, with the sending kind's block as
W's commitment, at the pin of Johnson/Desc/K13/Law/PinDec.lean: every premise on the pin is brought
down to `ReadsA`. Statements with their proofs.
Main names:
  `sameAll_size`: two statements with the same part of the record have as many messages.
  `send_below`: the sending kind's block leaves the codes, and of each older message the shape, the
    mark, the sample rows and the pad.
  `pinOfA_backW`: so the pin goes back over W's commitment, where the fence n is at most the number
    of messages in front.
  `commit_goodIn_dec`, `atM3_goodIn_decK`: the two pieces' laws with that condition carried.
  `joint_decA`: **the two pieces in a row at that pin.**
Used of the sending kind's laws: `sendAtS_kept` (Johnson/Desc/K1/Law/KeptAtRecord.lean); what
Johnson/Desc/K13/Law/K1Ids.lean and Johnson/Desc/K13/Law/K1Keeps.lean name.

What is not claimed. decA stays a letter: that a decoder of the release's codes, read off a
statement, meets `ReadsA` is typed nowhere; that the witness which matters has the pin is to be
shown, and priced, where the message is sent and where the pin is closed. No piece in front is shown
to promise the condition in front (the record's number of the index masks' message is idx; the
statement has at least n messages). `WIs` is given by no law yet. `Declared`: see
Johnson/Desc/K13/Law/PinA.lean. The number nR of the matrix's rows is a free letter. The premise of
`jointA` (Johnson/Desc/K13/Law/PinA.lean) that the pin goes back over W's commitment is not met at
`pinOfA`, and cannot be: the pin is unguarded, and a sending appends messages: `joint_decA` is a
sibling of `jointA`, not an instance: it carries in its conditions that n is at most the number of
messages. No statement ties idx to n.

-/
import Johnson.Desc.K13.Law.K1Ids
import Johnson.Desc.K13.Law.K1Keeps
import Johnson.Desc.K13.Law.PinDec
import Johnson.Desc.K1.Law.KeptAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Maker
open OnBytes.Means (Words)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)

variable {Cl W : Type} {nR : ℕ}

/-- Two statements with the same part of the record have as many messages. -/
theorem sameAll_size {St St' : Statement} (h : SameAll St St') :
    St'.oracles.size = St.oracles.size := by
  have key : ∀ (A B : Statement), (∀ j, sampleOf B j = sampleOf A j) →
      B.oracles.size ≤ A.oracles.size := by
    intro A B hj
    by_contra hc
    have h1 := hj A.oracles.size
    unfold sampleOf at h1
    rw [Array.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem (by omega)] at h1
    cases h1
  exact le_antisymm (key St St' h.2) (key St' St fun j => (h.2 j).symm)

/-- The sending kind's block leaves the codes and the older messages' part of the record. -/
theorem send_below (P' : K1.Par) (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (K1.sendAtS P' : Block S Cl).decide s [r₁, r₂] gs = .ok s') (n : ℕ)
    (hn : n ≤ s.st.oracles.size) : SameSampled n s.st s'.st :=
  ⟨(K1.sendAtS_kept P' s s' _ gs h).1, fun j hj => by
    unfold sampleOf
    rw [(K1.sendAtS_kept P' s s' _ gs h).2.2 j (by omega)]⟩

/-- **The pin goes back over W's commitment.** -/
theorem pinOfA_backW {F : Frame} (P' : K1.Par) (pcW : Piece (ckP .two) F S Cl W)
    (hb : pcW.b = K1.sendAtS P') (n idx : ℕ) {k : ℕ} (rw : W → Wit GE nR k)
    (decA : S × F.E.Str → Wit GE nR k) (hR : ReadsA pcW.base n decA) (a : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) pcW.ds)) (b : S × F.E.Str) (w : W) (hn : n ≤ a.1.st.oracles.size)
    (ho : pcW.ior.red.out a τ = some b) (hw : pinOfA idx rw decA b w) :
    pinOfA idx rw decA a w := by
  obtain ⟨rs, gs, hl, hdec⟩ := piece_ok_len pcW ho
  rw [hb] at hl hdec
  have h2 : rs.length = 2 := hl
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, h2 with
    | [x, y], _ => exact ⟨x, y, rfl⟩
  have hy := out_imp _ ho
  have e : decA b = decA a := hR a b (by rw [hy])
    (fun j x hj => by rw [hy]; exact old_kept _ _ _ j x hj)
    (send_below P' a.1 b.1 r₁ r₂ gs hdec n hn)
  show AgreeAt idx (rw w) (decA a)
  rw [← e]
  exact hw

/-- W's commitment's piece has what it owes at that pin, where the statement in front has at least n
messages. -/
theorem commit_goodIn_dec {F : Frame} (P : Where) (P' : K1.Par) (pcW : Piece (ckP .two) F S Cl W)
    (hb : pcW.b = K1.sendAtS P') (hext : ∀ a τ w, pcW.ext a τ w = w) (n idx : ℕ) {k : ℕ}
    (rw : W → Wit GE nR k) (decA : S × F.E.Str → Wit GE nR k) (hR : ReadsA pcW.base n decA) :
    pcW.GoodIn (fun a => FrontOk P a ∧ n ≤ a.1.st.oracles.size) (FrontOk P)
      (RowsHoldA rw (pinOfA idx rw decA)) (RowsHoldA rw (pinOfA idx rw decA)) := by
  intro a ha
  refine Doomed.mono _ _ ?_ (commit_goodIn P pcW hext (by rw [hb]; exact sendAtS_keepsEnd P') rw
    (fun _ _ => True) (fun _ _ _ _ _ h => h) a ha.1)
  intro τ hτ b ho
  obtain ⟨h1, h2⟩ := hτ b ho
  refine ⟨h1, fun w hw => ?_⟩
  have h3 := h2 w ⟨trivial, hw.2⟩
  rw [hext] at h3 ⊢
  exact ⟨pinOfA_backW P' pcW hb n idx rw decA hR a τ b w ha.2 ho hw.1, h3.2⟩

/-- The batching's piece at that pin, with "the statement has at least n messages" carried. -/
theorem atM3_goodIn_decK (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (idx n : ℕ) (rw : W → Wit GE nR P.lin.kCol)
    (decA : S × F.E.Str → Wit GE nR P.lin.kCol) (hR : ReadsA base n decA) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn
      (fun a => a.1.out.indexMasks = idx ∧ n ≤ a.1.st.oracles.size)
      (fun b => FrontOk P b ∧ n ≤ b.1.st.oracles.size)
      (RowsHoldA rw (pinOfA idx rw decA)) (RowsHoldA rw (pinOfA idx rw decA)) :=
  goodIn_keep _ _ _ (fun a => n ≤ a.1.st.oracles.size) _ _
    (atM3_goodIn_decA F P base dZ d0 ds hD idx n rw decA hR) fun a τ b ho hn => by
      obtain ⟨rs, gs, hdec⟩ := piece_ok _ ho
      rw [sameAll_size (atM3_same hdec)]
      exact hn

/-- The conditions at the three places of the row. -/
def jointOnD {F : Frame} (P : Where) (idx n : ℕ) : ℕ → S × F.E.Str → Prop
  | 0 => fun a => a.1.out.indexMasks = idx ∧ n ≤ a.1.st.oracles.size
  | 1 => fun a => FrontOk P a ∧ n ≤ a.1.st.oracles.size
  | _ => fun b => EvalLaid P b.1

/-- **The two pieces in a row at that pin**: the batching's joined block; the sending kind's block
with kind K13's block behind it. -/
theorem joint_decA (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (idx n : ℕ) (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE)
    (rwW : W → Words GE) (decA : S × F.E.Str → Wit GE nR P.lin.kCol) (hR : ReadsA base n decA)
    (P' : K1.Par) (pcW : Piece (ckP .two) F S Cl W) (hb : pcW.b = K1.sendAtS P')
    (hext : ∀ a τ w, pcW.ext a τ w = w) (hRW : ReadsA pcW.base n decA) :
    EachGoodIn (jointOnD P idx n)
      (jointRA P rwM rwW (pinOfA idx (fun w => witOf (rwM w) (rwW w)) decA)) 0
      [pieceM3 F P base dZ d0 ds,
        Piece.then pcW "W's commitment, the own group and (Eval)" (rowsB atS P)] :=
  ⟨atM3_goodIn_decK F P base dZ d0 ds hD idx n _ decA hR,
    atM4_goodInA P pcW _ _ rwM rwW _
      (fun s s' y w hd hw => pinOfA_backR P base n idx _ decA hR s s' y w hd hw)
      (commit_goodIn_dec P P' pcW hb hext n idx _ decA hRW),
    trivial⟩

end VerifiableInference.Desc.K13.Law
