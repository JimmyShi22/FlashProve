-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFrontRefWideProofs.lean: the proofs of the statements of
Cb/Req1/LdSegFrontRefWide.lean.

Main names:
  `frontWide_psc`: see its statement in Cb/Req1/LdSegFrontRefWide.lean.
  `frontWide_lkp`: see its statement in Cb/Req1/LdSegFrontRefWide.lean.
-/
import Cb.Req1.LdSegFrontRefWide
import Cb.Ld.LdLkpMaskPutLkp2

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain Cb.LdLkp

theorem frontWide_psc : Spec.frontWide_psc := by
  classical
  intro E Kc _ _ A a c base Rd Rr own T A0 msg RdT val at' hinj hRd p1 p2 ho hr hv h
  exact segWide_readG E Kc A a c base Rd Rr own (T.own RdT).Mk val T.J _ (T.own RdT).at at'
    (fun M => Sum.elim M.1 M.2) RdT (fun w => msg w.1) (frFact Kc T a.S a.E₀ a.Wp A0 msg RdT).kc
    (frFact Kc T a.S a.E₀ a.Wp A0 msg RdT).put hinj (fun m _ i => p1 m i)
    (fun m m' _ j hj hn hm => p2 m m' j hj hn hm) (fun _ _ hj => if_pos hj)
    (fun _ _ hj => if_neg hj) (fun _ _ => rfl) ho hr hv hRd h

theorem frontWide_lkp : Spec.frontWide_lkp := by
  classical
  intro E Kc _ _ S E₀ Wp F St' E₀' A' A c base Rd Rr own Dt RdK C val at' hM hRd p1 p2 ho hr hv h
  have hP := (ldLkpPl2_asm E F.A E₀ S.Msg Wp Kc F.msg RdK Dt hM).1.1
  exact segWide_readG E Kc A ⟨S, St', E₀', Wp, A'⟩ c base Rd Rr own (F.dm RdK C).Mk val F.A0.J _
    (F.A.plChain E₀ S.Msg Wp Kc F.msg RdK).pl at'
    (fun M => (F.A.plChain E₀ S.Msg Wp Kc F.msg RdK).ve M) RdK (fun w => F.msg w.1) (F.dm RdK C).kc
    (F.dm RdK C).put hP.inj (fun m _ i => p1 m i) (fun m m' _ j hj hn hm => p2 m m' j hj hn hm)
    (fun _ _ hj => if_pos hj) (fun _ _ hj => if_neg hj) (fun M k => hP.put M k) ho hr hv hRd h

end Cb
