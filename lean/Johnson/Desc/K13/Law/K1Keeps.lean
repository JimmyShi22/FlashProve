-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/K1Keeps.lean: W's commitment, the sending kind's block at the first chain's
state, keeps what kind K13's row asks of it; so the two pieces in a row have what they owe with no
premise left on that block's decision. Statements with their proofs.
Main names:
  `sendAtS_keepsEnd`: `KeepsEnd` (Johnson/Desc/K13/Law/Joint.lean) of the sending kind's block
    `K1.sendAtS`.
  `joint_send`: `joint` at a piece that holds that block.
Used of the sending kind's laws: `sendAtS_here`, `sendAtS_rows`
(Johnson/Desc/K1/Law/HereAtRecord.lean).

What is not claimed. What Johnson/Desc/K13/Law/Joint.lean says is not claimed, but for `KeepsEnd`.
The piece's extractor is the identity, and nothing is promised of W's own pin behind it.

-/
import Johnson.Desc.K13.Law.Joint
import Johnson.Desc.K1.Law.HereAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice Run
open OnBytes.Maker
open OnBytes.Means (Words)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)

variable {Cl W : Type} {nR : ℕ}

/-- **W's commitment keeps the chain's end.** -/
theorem sendAtS_keepsEnd (P' : K1.Par) : KeepsEnd (K1.sendAtS P' : Block S Cl) := by
  intro s s' rs gs hl h
  have h2 : rs.length = 2 := hl
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, h2 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨hc, hr⟩ := K1.sendAtS_rows P' s s' r₁ r₂ gs h
  obtain ⟨a, ids, h1, _, h3, _⟩ := K1.sendAtS_here P' s s' _ gs h
  exact ⟨hc, hr, by unfold linAt; rw [h1, h3]⟩

/-- **The two pieces in a row**, at a piece that holds the sending kind's block. -/
theorem joint_send (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (idx : ℕ) (rwM : W → Fin nR → (Fin P.lin.kCol → Bool) → GE)
    (rwW : W → Words GE) (dec : F.E.Str → Wit GE nR P.lin.kCol) (hloc : Local base dec)
    (P' : K1.Par) (pcW : Piece (ckP .two) F S Cl W) (hb : pcW.b = K1.sendAtS P')
    (hext : ∀ a τ w, pcW.ext a τ w = w) (hlocW : Local pcW.base dec) :
    EachGoodIn (jointOn P idx) (jointR P idx rwM rwW dec) 0
      [pieceM3 F P base dZ d0 ds,
        Piece.then pcW "W's commitment, the own group and (Eval)" (rowsB atS P)] :=
  joint F P base dZ d0 ds hD idx rwM rwW dec hloc pcW hext (by rw [hb]; exact sendAtS_keepsEnd P')
    hlocW

end VerifiableInference.Desc.K13.Law
