-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/CloseKnowProofs.lean: the proofs of the statements of Cb/Ent/CloseKnow.lean: the blocks of
the closing of a link, each with its round-by-round knowledge soundness alone.

Proofs only. Each is taken out of a bundle of the library whose premises name no honest side
(`ldBat_ex`, `ldBat_ex_beside`, `ldBat_step`, `ldBat_bridge`).
Main names: `know_bat`, `know_bat_beside`, `back_bridge`, `know_bridge`, `codesOK_iff`, `errOK_iff`,
`qwDeg_iff`, `ok_powers_comap`.
Limits: see Limits in the head of Cb/Ent/CloseKnow.lean.

-/
import Cb.Ent.CloseKnow
import Cb.Ld.LdBatProofs
import Cb.Ld.LdBatSigProofs
import Cb.Ld.LdLinProofsChain
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false

namespace Cb
open Iop Prob

section
variable (E P B : Type) [Field E] [Fintype E] [Fintype P] [Fintype B]

theorem know_bat : Spec.know_bat E P B := fun C S sl Z e L hZ hL =>
  (ldBat_ex E P B Unit C S sl Z e L (fun _ => ()) (fun _ => True) hZ hL).good.know

theorem know_bat_beside : Spec.know_bat_beside E P B := fun Kc Xc Wc C S sl Z e L Ec Bc hZ hL =>
  (ldk_pieceTr_cf
    (ldBat_ex_beside E P B Kc Xc Wc C S sl Z e L Ec Bc (fun _ => True) hZ hL)).good.know

end

section
variable (E B Kc St₀ Wp : Type) [Field E] [Fintype E] [Fintype B]

theorem back_bridge : Spec.back_bridge E B Kc St₀ Wp :=
  fun S G kp _ Sb sl E₀ A₀ hc hF x y w' hcf hA h =>
    (ldBat_step E B Kc St₀ Wp S G kp Sb sl E₀ A₀ hc hF).know x y _ w' ⟨hcf, hA⟩ rfl h

theorem know_bridge : Spec.know_bridge E B Kc St₀ Wp :=
  fun S G kp _ Sb sl E₀ A₀ hc Z L hZ hL hF =>
    (ldk_pieceTr_cf (ldBat_bridge E B Kc St₀ Wp S G kp Sb sl Z L E₀ A₀ hc (fun _ => True)
      (fun _ => True) hZ hL hF fun _ _ => trivial)).good.know

end

section
variable (E P : Type) [Field E] [Fintype E] [Fintype P]

omit [Fintype E] in
theorem codesOK_iff : Spec.codesOK_iff E P := fun _ _ _ _ _ => Iff.rfl

theorem errOK_iff : Spec.errOK_iff E P := fun _ _ _ _ _ _ =>
  ⟨fun h => ⟨h.list, h.mcaC, h.mcaS, h.mcaW⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

omit [Fintype E] [Fintype P] in
theorem qwDeg_iff : Spec.qwDeg_iff E P := fun _ => Iff.rfl

end

theorem ok_powers_comap : Spec.ok_powers_comap := fun E J _ _ _ n f hf =>
  ok_comap E J (Fin n) (Evader.powers E n) f hf (ok_powers E n)

end Cb
