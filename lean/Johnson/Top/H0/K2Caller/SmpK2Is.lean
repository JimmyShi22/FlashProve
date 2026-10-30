-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SmpK2Is.lean: the code switch: SmpK2.lean's CLOSED TERM IS THE MADE
HELD OOD SAMPLES.
  smpMade_is   smpMade (Johnson/Top/H/SwitchInXMade.lean) at the typed structure r, the plain
               letters, the three readings memK | rowK | «place in r.kept», answer number 0 and the
               stand-in smp₀, AT EVERY TWO MAPS OF NAMES AND EVERY NUMBER OF POSITIONS, is smpK2: by
               definition (rfl): these three letters stand in a type alone
WHAT IT IS FOR. The laws on smpMade and on smpTop (Johnson/G/SwitchSampleTop.lean, which is
smpMade at these very readings, by its text) apply to smpK2 as they lie.
LIMITS. One equation. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.SmpK2
import Johnson.Top.H.SwitchInXMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Johnson.Pack Johnson.Top.H Cb Iop IOR
open OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.First.K2Hands

variable (r : SwRow) (H : r.OK)
  (jN : (plainR r H).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (qN : (plainR r H).Sh.Cf.Q → (sigOf r.cs r.l).Ent) (t : ℕ)

/-- **The made held samples, at the plain letters, at every two maps of names, are smpK2.** -/
theorem smpMade_is (fx : _root_.Tw.K2.Front) (W : SwitchFrame) :
    smpMade (plainR r H) (heldAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM
        (Letters.plain r H).oZ (Letters.plain r H).kq) (Letters.plain r H).Sb (Letters.plain r H).sl
      (Letters.plain r H).Z (Letters.plain r H).A₀ r.cs r.l jN qN t (Letters.plain r H).w₀ W
      ⟨0, 0, 0, 0, [], 0⟩ memK rowK (fun k => r.kept.idxOf k.1.1.val) (fun _ _ => 0) (smp₀ r H)
      fx.st = smpK2 r H fx W := rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.smpMade_is
