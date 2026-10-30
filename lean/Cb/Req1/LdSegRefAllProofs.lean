-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAllProofs.lean: the statements of Cb/Req1/LdSegRefAll.lean, proved.

The proofs use the parts' theorems (Cb/Req1/LdSegFrontRef.lean, Cb/Req1/LdSegRefBodyProofs.lean,
Cb/Req1/LdSegRefAsmProofs.lean, Cb/Req1/LdSegRefTenProofs.lean, Cb/Req1/LdSegRefProofs.lean).
What each statement says, and the limits: the head of Cb/Req1/LdSegRefAll.lean.
-/
import Cb.Req1.LdSegRefAll

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

theorem ldSegRefAll_meet : Spec.ldSegRefAll_meet := fun _ _ _ _ _ _ => rfl

theorem ldSegRefAll_kinds : Spec.ldSegRefAll_kinds := fun E Kc _ _ _ A St₁ fz Az =>
  ldSegRef_body_kinds E Kc _ _ A.Y (A.X.tgt St₁ Az) (A.X.prog St₁ fz Az)
    (ldSegFrontRef_kinds E Kc _ A.V) (ldSegRef_tn_kinds E Kc A.X St₁ fz Az)

namespace LdRefD
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)

/-- what the body's data ask, from A.OK (pp the characteristic of E) and whatever the arguments hold
as proofs -/
theorem hypY (pp : ℕ) [CharP E pp] (h : A.OK pp) : A.Y.Hyp pp :=
  ⟨h.ok, h.places, h.uniq, h.send1, h.send3, h.tabQ, h.tabH, h.keys, h.tags,
    ldSegRef_asm_mult E Kc _ _ A.Xa h.ok h.tabQ h.tabH h.keys
      (lt_trans (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)) h.adm.2.1) h.adm.1 h.bits,
    h.reads, h.rest⟩

end LdRefD

theorem ldSegRefAll_body : Spec.ldSegRefAll_body := fun E Kc _ _ pp _ _ A St₁ fz Az h hE =>
  ldSegRef_body_hyp E Kc _ _ pp A.Y (A.X.tgt St₁ Az) (A.X.prog St₁ fz Az)
    (ldSegFrontRef_hyp E pp Kc _ A.V h.front) (A.hypY pp h)
    (ldSegRef_asm_allB E Kc _ _ pp A.Xa h.inj h.named h.adm)
    (ldSegRef_tn_hyp E Kc A.X St₁ fz Az h.deg h.ev hE)

theorem ldSegRefAll_one : Spec.ldSegRefAll_one := fun E Kc _ _ pp _ _ A K l Qc h hE hZ hs hf hq =>
  ldSegRef_hyp E Kc _ _ pp K.R K.tensor K.kinds l Qc (ldSegFrontRef_hyp E pp Kc _ A.V h.front)
    (A.hypY pp h) (ldSegRef_asm_allB E Kc _ _ pp A.Xa h.inj h.named h.adm)
    (ldSegRef_tn_hyp E Kc A.X K.St₁ K.fz K.Az h.deg h.ev hE) hZ hs hf hq

theorem ldSegRefAll_noLook : Spec.ldSegRefAll_noLook :=
  fun _ _ _ _ _ _ _ h _ _ m m' wp _ => by rw [h (m', wp), h (m, wp)]

end Cb
