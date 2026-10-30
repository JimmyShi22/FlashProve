-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FramesMeet.lean: THE TWO FRAMES MEET AT A MEMBER's WORD. One theorem, proved.
  `wordsOf_is_strOf`: a member's word off the plain strings of a frame's oracles (`wordsOf`,
    MsgSig.lean, at
    `strsOf F y`) IS "the word as sent" (`strOf`, Johnson/Desc/K12/Law/StrOf.lean) off the written
    oracle that Johnson/Desc/K12/Coin/Sheet.lean's `W0` reads at the member's tree, at the record
    `layOf m`:
    `wordsOf_eq_strOf` (CandOfTuple.lean) with its two premises hM, hZ paid by `hM_at`, `hZ_at`
    (Johnson/Desc/K12/Coin/FramesTie.lean).
Limits: those of the files named. PREMISES: the seats fit (`SeatFits`); every leaf of the member's
word is shown (`ShownAt`); `SeatIs`: six equations between the record's book at the member and what
the description tells of the tree; no listed depth of the tree is beyond the told length. The main
degree is 1 or 3: out of `SeatFits`. Called at no value.
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.CandOfTuple
import Johnson.Desc.K12.Coin.FramesTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open H2K.First (Seat1)
open H2K.Pin (layOf)

/-- **The two frames meet at a member's word.** -/
theorem wordsOf_is_strOf (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (F : Frame) (no : ℕ → ℕ)
    (book : TreeBook) (y : F.E.Str) (i : Fin l.length) (m : Seat1)
    (hF : SeatFits G cs l seat) (hS : ShownAt G cs l seat (strsOf F y) i)
    (hI : ∀ o, G.oracleAt (seat i).1 = some o → SeatIs no book m (seat i).1 (seat i).2 o)
    (hd : ∀ o, G.oracleAt (seat i).1 = some o →
      ∀ e ∈ F.all, e.no = (seat i).1 → e.a ≤ o.logLength) :
    wordsOf G cs l seat (strsOf F y) i =
      H2K.Pin.strOf cs (l.get i).1 (l.get i).2 (layOf m) (W0 F no book y m.t).1
        (W0 F no book y m.t).2 :=
  wordsOf_eq_strOf cs G l seat (strsOf F y) i (layOf m) _ _
    (by obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := hF i; exact h)
    (hM_at cs G l seat F no book y i m hF hS hI hd) (hZ_at cs G l seat F no book y i m hF hS hI hd)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.wordsOf_is_strOf
