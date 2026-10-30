-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/CallsE2.lean: K01_law: AT THE KIND's TWO OTHER PLACES (number 2: the first chain's opening
sending; number 356: W's sending) THE TABLE's OWN EXTRACTOR extQAt (Johnson/Desc/Sound/BordersFill.lean)
IS THE IDENTITY: the table's row lays nothing there. On the pattern of extQAt_fifty
(Johnson/Desc/K1/Law/CallsE.lean). Six theorems; the four facts on the table by the kernel.
Nothing on soundness.
-/
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (Frame Mem MsgT linksFull extQAt extQ_id)

set_option maxRecDepth 1000000 in
theorem place_two : (flatPlacesOf linksFull true)[2]? = some ⟨1, some 0, 1, .K1⟩ := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem place_w : (flatPlacesOf linksFull true)[356]? = some ⟨1, none, 4, .K1⟩ := by
  decide +kernel

theorem lays_two : (First.rowOf linksFull ⟨1, some 0, 1, .K1⟩).lays = false := by decide +kernel

theorem lays_w : (First.rowOf linksFull ⟨1, none, 4, .K1⟩).lays = false := by decide +kernel

section
variable (cs : OnBytes.Codes) {A Xi Pp Cells Tok : Type} {Fr : Frame} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (c₀ : Cells)
  (tokOf : Pp × S → Tok)

/-- The table's own extractor lays nothing at the opening sending. -/
theorem extQAt_two (N : Numbers) (get : A → Pp × S) (a b : A × Fr.E.Str)
    (w : Desc.Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true) get 2 a b w =
      w := by
  unfold extQAt
  rw [place_two]
  exact extQ_id cs G arr smp ms decT c₀ tokOf N linksFull _ lays_two _ _ _ w

/-- Nor at W's sending. -/
theorem extQAt_w (N : Numbers) (get : A → Pp × S) (a b : A × Fr.E.Str)
    (w : Desc.Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true) get 356 a b w =
      w := by
  unfold extQAt
  rw [place_w]
  exact extQ_id cs G arr smp ms decT c₀ tokOf N linksFull _ lays_w _ _ _ w

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.extQAt_two
#print axioms VerifiableInference.Desc.K1.extQAt_w
