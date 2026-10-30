-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3ExtIdle.lean: the kind "lookup" (K3): THE TABLE OF JOINTS' OWN EXTRACTOR
LAYS NOTHING AT THE KIND's FIFTY NUMBERS of the full size's written list: so the premise hE of
`k03_law_ofR` (Johnson/Desc/First/Look/K3LawOfR.lean) is paid at E := `extQAt`, at every filling of
its letters.

Main name:
  `k03_ext_idle`: `extQAt … linksFull (flatPlacesOf linksFull true) get (k3K l d) a b w = w`.

A joining of three that lie: `K3Lot.k03_at_full` (the number holds the address), and
Johnson/Desc/Sound/ExtQuiet.lean's `lays_nothing` (a place of any kind but K2, K7, K10, K12 lays
nothing) and `extQAt_quiet` (a row that lays nothing leaves the witness as it is).

Limits: the full size's written list alone. It says nothing of any block. Nothing on soundness by
itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.Sound.ExtQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (Wit FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers flatPlacesOf)

/-- **THE TABLE's EXTRACTOR IS THE IDENTITY AT THE KIND's FIFTY NUMBERS.** -/
theorem k03_ext_idle {Xi P Cells Tok A : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : P × Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × Desc.First.S → Option Cells)
    (c₀ : Cells) (tokOf : P × Desc.First.S → Tok) (N : Numbers) (get : A → P × Desc.First.S)
    (l : ℕ) (hl : l < 25) (d : Bool) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true) get (k3K l d) a
      b w = w := by
  have hk : (IM.k3Place l d).kind = .K3 := rfl
  obtain ⟨h1, h2, h3⟩ := lays_nothing N linksFull (IM.k3Place l d) (by rw [hk]; decide)
    (by rw [hk]; decide) (by rw [hk]; decide) (by rw [hk]; decide)
  exact extQAt_quiet cs G arr smp ms decT c₀ tokOf N linksFull _ get (k3K l d) (IM.k3Place l d)
    (K3Lot.k03_at_full l hl d) h1 h2 h3 a b w

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k03_ext_idle
