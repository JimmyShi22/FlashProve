-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDBodyProofs.lean: the proofs of Cb/Ld/LdLayDBody.lean's two statements: assemblies of
Cb/Req1/LdReqRefLayWide.lean (the body's clause from wide facts; the set of facts that a move hands
on is closed) and of the rules of Cb/Ld/LdLayDKitProofs.lean (a standard sender whose data map does
not look does not look; a step's own condition hands a pending block on). What is said and what is
not: the head of Cb/Ld/LdLayDBody.lean.

Main names:
  `ldLayD_body`: see its statement in Cb/Ld/LdLayDBody.lean.
  `ldLayD_enter`: see its statement in Cb/Ld/LdLayDBody.lean.
-/
import Cb.Ld.LdLayDBody
import Cb.Ld.LdLayDKitProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

theorem ldLayD_body : Spec.ldLayD_body := by
  intro E Kc _ _ I A Q pp X X' hX hC ⟨hne, W, F, P, κ, RdL, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ldReqRefLayW_zk E Kc I A pp X' hC
    ⟨hne, W, F, P, κ, RdL, h1, h2, h3, h4, h5, h6,
      ⟨hX _ h7.lk, hX _ h7.s0, fun i hi => hX _ (h7.s i hi)⟩, ?_⟩
  exact
    { maskL := h8.maskL, rdL := h8.rdL, inL := h8.inL, wideL := h8.wideL
      factL := hX _ h8.pendL
      blL := h8.blL
      s1L := ldLayD_noLook _ _ _ _ _ _ h8.s1L
      s3L := ldLayD_noLook _ _ _ _ _ _ h8.s3L
      ownT := h8.ownT, inT := h8.inT, wideT := h8.wideT
      factT := hX _ h8.pendT
      blT := h8.blT
      s1T := ldLayD_noLook _ _ _ _ _ _ h8.s1T
      s3T := ldLayD_noLook _ _ _ _ _ _ h8.s3T
      apart := h8.apart }

theorem ldLayD_enter : Spec.ldLayD_enter := by
  intro E Kc _ _ I A Q pp a f g₀ m back G P hG hP hZ
  refine ldLayD_body E Kc I A Q pp _ _ (fun γ ⟨β, hβ, hs⟩ => ?_)
    (ldReqRefLayW_closed E Kc _ _ (LdMv.step a A.V.Fp.s0 f g₀ m back) G) hZ
  exact ldLayD_step f g₀ m back G hG β γ (hP β hβ) hs

end Cb
