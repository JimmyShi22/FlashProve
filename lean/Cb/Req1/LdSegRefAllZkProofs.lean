-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAllZkProofs.lean: the statement of Cb/Req1/LdSegRefAllZk.lean, proved.

The front is treated by Cb/Req1/LdSegFrontRefZk.lean. The two late blocks are masked blocks by
Cb/Req1/LdSegRefAsmZk.lean, Cb/Req1/LdSegRefTenProofs.lean. Their facts: the wide facts cross
(Cb/Req1/LdSegRefCross.lean) and give the blocks' facts (Cb/Req1/LdSegRefFact.lean; the places of
the lookup's masks: Cb/Ld/LdLkpMaskPutLkp2.lean). Each of these under the hypotheses of its
statements.
What the statement says, and the limits: the head of Cb/Req1/LdSegRefAllZk.lean.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldSegRefAll_zk` can be met
   together. -/
import Cb.Req1.LdSegRefAllZk
import Cb.Ld.LdLkpMaskPutLkp2

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain

namespace LdRefD
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} (A : LdRefD E Kc I)

/-- under `h`: for a set P of entries all of which are in messages at the entry, `A.own2` of P read
through `A.up` is P -/
theorem own2_iff (P : A.Xa.Q.T.Ent → Prop) (h : ∀ j, P j → ∃ n, A.up n = j) (j : A.Xa.Q.T.Ent) :
    A.own2 (fun n => P (A.up n)) j ↔ P j := by
  obtain ⟨o, e⟩ := j
  rcases o with (o | o) | o
  · exact Iff.rfl
  · refine ⟨fun hf => hf.elim, fun hp => ?_⟩
    obtain ⟨n, hn⟩ := h _ hp
    have := congrArg Sigma.fst hn
    simp [LdRefD.up] at this
  · refine ⟨fun hf => hf.elim, fun hp => ?_⟩
    obtain ⟨n, hn⟩ := h _ hp
    have := congrArg Sigma.fst hn
    simp [LdRefD.up] at this

theorem val2_up {Mk : Type} (val : Mk → A.Xa.Q.D.S.Ent → E) (M : Mk) (n : A.Xa.Q.D.S.Ent) :
    A.val2 val M (A.up n) = val M n := rfl

end LdRefD

open Classical in
theorem ldSegRefAll_zk : Spec.ldSegRefAll_zk := by
  intro E Kc _ _ pp _ I A _ W F κ RdL St₁ fz Az base h hG hF hFF hL
  -- the front
  have zF : A.V.prog.Zk base :=
    ldSegFrontRefZk E pp Kc A.Xa.Q.D.s0 A.V F.Dt F.RdK F.Cc F.Rd0 F.RdS base h.front hF.lk hF.own0
      hF.own hFF.lk hFF.f0 hFF.q0 hFF.f hFF.qL hFF.qZ hFF.qS
  -- the digits' lookup: its fact
  have pOK : (A.plL RdL).OK :=
    (ldLkpPl2_asm E A.Xa.A I.C.E0 A.Xa.Q.T.Msg (I.C.PIdx × (A.W₁ × A.Gh))
      Kc A.Xa.Q.T.ents RdL A.Xa.Dt hL.maskL).1.1
  have pAt : ∀ j, (A.plL RdL).At j ↔ A.Xa.A.swAll j :=
    (ldLkpPl2_asm E A.Xa.A I.C.E0 A.Xa.Q.T.Msg (I.C.PIdx × (A.W₁ × A.Gh))
      Kc A.Xa.Q.T.ents RdL A.Xa.Dt hL.maskL).1.2
  have wL :=
    ldSegRefX_lk E Kc pp _ A W F κ base A.ownL (A.Xa.dm RdL).Mk (A.valL RdL) h hG hF hL.passL
  have fL : (A.Xa.Q.pre A.Xa.mult).After
      (A.Xa.Q.D.prog.After (A.V.prog.After base)) (A.Xa.dm RdL).fact := by
    unfold LdDgP.pre at wL ⊢
    rw [LdProg.after_snoc] at wL ⊢
    refine segWide_read E Kc _ (A.Xa.Q.lkS A.Xa.mult) _ _ W.Rd2 W.Rr2 (A.own2 A.ownL)
      (A.Xa.dm RdL).Mk (A.val2 (A.valL RdL)) A.Xa.Q.T.Ent (A.plL RdL).I id (A.plL RdL).pl
      (fun M => (A.plL RdL).ve M) RdL (fun w => A.Xa.Q.T.ents w.1) (A.Xa.dm RdL).kc
      (A.Xa.dm RdL).put Function.injective_id pOK.inj (fun _ _ _ => rfl)
      (fun _ _ _ j hj => absurd rfl (hj j)) ?_ ?_ (fun M k => pOK.put M k) ?_ ?_ hL.wideL ?_ wL
    · intro w j hj
      exact if_pos hj
    · intro w j hj
      exact if_neg hj
    · intro n
      exact (A.own2_iff A.Xa.A.swAll hL.inL n).trans (pAt n).symm
    · intro M i
      obtain ⟨n, hn⟩ := hL.inL ((A.plL RdL).pl i) ((pAt _).1 ⟨i, rfl⟩)
      rw [← hn, A.val2_up]
      show Function.extend (A.plL RdL).pl ((A.plL RdL).ve M) (fun _ => 0) (A.up n) = _
      rw [hn]
      exact pOK.inj.extend_apply _ _ i
    · intro i
      exact hL.rdL _ (Or.inr ((pAt _).1 ⟨i, rfl⟩))
  have zL : A.Y.lk.OkGiven
      ((A.Xa.Q.pre A.Xa.mult).After (A.Xa.Q.D.prog.After (A.V.prog.After base))) :=
    (okGiven_one A.Xa.link _).2
      (Or.inr ⟨A.Xa.dm RdL,
          ldSegRef_asm_goodM E Kc _ _ pp A.Xa RdL h.inj h.named h.adm hL.maskL hL.rdL,
          fL⟩)
  -- the batching: its fact
  have wT :=
    ldSegRefX_tn E Kc pp _ A W F κ base A.ownT A.X.mask.Mk A.valT h hG hF hL.passT hL.maskL hL.apart
  have fT : A.X.stepIn.After
      (A.Y.step.After
        ((A.Xa.Q.prog A.Xa.mult A.Xa.ent A.Xa.A.nRows A.Xa.lk).After
          (A.Xa.Q.D.prog.After (A.V.prog.After base))))
      A.X.mask.fact := by
    refine segWide_read E Kc _ A.X.m0 _ _ W.Rd2 W.Rr2 (A.own2 A.ownT) A.X.mask.Mk (A.val2 A.valT)
      A.X.bt.J _ Sum.inr A.wAt (fun M => M) A.X.RdJ (fun w => A.X.msg (w.2.1.1.1, w.1))
      A.X.mask.kc A.X.mask.put Sum.inr_injective hL.ownT.inj (fun _ _ _ => rfl) ?_ ?_ ?_
      (fun _ _ => rfl) ?_ ?_ hL.wideT hL.ownT.own wT
    · rintro m m' wp (a | n) hj
      · rfl
      · exact absurd rfl (hj n)
    · intro w j hj
      exact if_pos hj
    · intro w j hj
      exact if_neg hj
    · intro n
      exact A.own2_iff (fun j => ∃ i, A.wAt i = j) (fun j ⟨i, hi⟩ => hi ▸ hL.inT i) n
    · intro M i
      obtain ⟨n, hn⟩ := hL.inT i
      rw [← hn, A.val2_up]
      show Function.extend A.wAt M (fun _ => 0) (A.up n) = _
      rw [hn]
      exact hL.ownT.inj.extend_apply _ _ i
  exact ldSegRef_body_zk E Kc _ _ A.Y (A.X.tgt St₁ Az) (A.X.prog St₁ fz Az) base h.ok h.tags zF zL
    (ldSegRef_tn_zk E Kc A.X St₁ fz Az _ h.deg h.ev hL.ownT fT)

end Cb
