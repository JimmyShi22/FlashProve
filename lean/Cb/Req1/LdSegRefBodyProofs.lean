-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefBodyProofs.lean: the statements of Cb/Req1/LdSegRefBody.lean, proved.

The proofs use the three parts' theorems (Cb/Req1/LdSegRefRngProofs.lean,
Cb/Req1/LdSegRefDigProofs.lean, Cb/Req1/LdSegRefRowsProofs.lean) and the rules for two lists in a
row (Cb/Req1/LdSegRefKit.lean).
What each statement says, and the limits: the head of Cb/Req1/LdSegRefBody.lean.
-/
import Cb.Req1.LdSegRefBody
import Cb.Req1.LdSegRefRowsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain
open scoped ENNReal

theorem ldSegRef_body_kinds : Spec.ldSegRef_body_kinds := by
  intro E Kc E₀ Wp _ _ Y z tensor hf ht
  unfold LdBodyD.body
  rw [ldProg_app_all, LdProg.all_snoc, ldProg_app_all, ldProg_app_all]
  exact ⟨⟨⟨⟨hf, ldSegRef_rr_kinds E Kc _ _ Y.G.Q.D⟩,
        ldSegRef_dg_kinds E Kc _ _ Y.G.Q Y.mult Y.G.ent Y.G.n Y.lk⟩,
      Or.inr (Or.inr rfl)⟩,
    ht⟩

theorem ldSegRef_body_hyp : Spec.ldSegRef_body_hyp := by
  intro E Kc E₀ Wp _ _ pp _ Y z tensor hf h hl hten
  unfold LdBodyD.body
  rw [ldProg_app_hyp, LdProg.hyp_snoc, ldProg_app_hyp, ldProg_app_hyp]
  exact ⟨⟨⟨⟨hf, ldSegRef_rr_hyp E Kc _ _ pp Y.G.Q.D h.ok h.uniq h.send1 h.send3⟩,
        ldSegRef_dg_hyp E Kc _ _ Y.G.Q Y.mult Y.G.ent Y.G.n Y.lk h.ok h.places h.tabQ h.tabH
          h.keys h.tags h.mult hl⟩,
      ldSegRef_ga_hyp E Kc _ _ Y.G Y.St₀ Y.g₀ Y.Ar h.reads h.rest h.keys⟩,
    hten⟩

theorem ldSegRef_body_zk : Spec.ldSegRef_body_zk := by
  intro E Kc E₀ Wp _ _ Y z tensor base h ht hf hl hten
  unfold LdBodyD.body
  rw [ldProg_app_zk, LdProg.zk_snoc, ldProg_app_zk, ldProg_app_zk, LdProg.after_snoc,
    ldProg_app_after, ldProg_app_after]
  refine ⟨⟨⟨⟨hf, ldSegRef_rr_zk E Kc _ _ Y.G.Q.D _ h⟩,
        ldSegRef_dg_zk E Kc _ _ Y.G.Q Y.mult Y.G.ent Y.G.n Y.lk _ ht hl⟩,
      ?_⟩,
    ?_⟩
  · unfold LdBodyD.step LdGaP.step
    rw [LdMv.Zk]
    trivial
  · rw [ldProg_app_after]
    exact hten

theorem ldSegRef_body_nums : Spec.ldSegRef_body_nums := by
  intro E Kc E₀ Wp _ _ Y z tensor
  obtain ⟨_, _, _, _, _, hp⟩ := ldSeg_rounds E Kc
  have a1 := hp (Y.G.Q.lkT Y.G.ent Y.G.n) Y.tgt
    (fun x => if x.1.2.2.length = Y.G.n then some (Y.G.fd Y.St₀ Y.g₀ x.1, x.2) else none)
    (sideG Y.G.Q.T (ExtMap.id E₀)) (sideM Y.G.Q.T (Y.G.fd Y.St₀ Y.g₀) fun _ w => w.2)
    (sideB Y.G.Q.T fun _ w => w.2)
  obtain ⟨n0, _, b0, d0⟩ := ldProg_app_nums E Kc _ _ _
    (((Y.front.app Y.G.Q.D.prog).app (Y.G.Q.prog Y.mult Y.G.ent Y.G.n Y.lk)).snoc Y.step) tensor
  obtain ⟨n1, _, b1, d1⟩ :=
    ldProg_app_nums E Kc _ _ _ (Y.front.app Y.G.Q.D.prog) (Y.G.Q.prog Y.mult Y.G.ent Y.G.n Y.lk)
  obtain ⟨n2, _, b2, d2⟩ := ldProg_app_nums E Kc _ _ _ Y.front Y.G.Q.D.prog
  obtain ⟨n3, b3, d3⟩ := ldSegRef_rr_nums E Kc _ _ Y.G.Q.D
  obtain ⟨n4, b4, d4⟩ := ldSegRef_dg_nums E Kc _ _ Y.G.Q Y.mult Y.G.ent Y.G.n Y.lk
  have s1 : Y.step.chain.nAll = 0 := a1.1
  have s2 : Y.step.chain.pBad = 0 := a1.2.2.1
  have s3 : Y.step.chain.pHid = 0 := a1.2.2.2
  unfold LdBodyD.body
  refine ⟨?_, ?_, ?_⟩
  · rw [n0, LdProg.nAll_snoc, s1, n1, n2, n3, n4]
    ring
  · rw [b0, LdProg.pBad_snoc, s2, b1, b2, b3, b4]
    ring
  · rw [d0, LdProg.pHid_snoc, s3, d1, d2, d3, d4]
    ring

end Cb
