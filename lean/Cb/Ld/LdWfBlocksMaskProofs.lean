-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfBlocksMaskProofs.lean: the proofs of the statements of Cb/Ld/LdWfBlocksMask.lean (the
zero-knowledge item of the lookups of the preamble of weights-formedness).

`LdWfP.Lks.in_rel` is glue: see its docstring.

Limits: what the head of Cb/Ld/LdWfBlocksMask.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfBlocksMask
import Cb.Ld.LdWfBlocksProofs
import Cb.Ld.LdLkpAsm2GoodMProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]
open LdWfP

theorem ldWfB_reads : Spec.ldWfB_reads E := by
  intro C P K f st k k' hk h
  have e1 : (K.asm f).key st k = (K.asm f).key st k' := by
    show P.keyE f (fun rc => k (Sum.inl rc)) = P.keyE f (fun rc => k' (Sum.inl rc))
    exact congrArg (P.keyE f) (funext fun rc => hk _ (Or.inl ⟨rc, rfl⟩))
  have e2 : (K.asm f).H.bit k = (K.asm f).H.bit k' :=
    funext fun u => funext fun i => hk _ (Or.inr ⟨u, i, rfl⟩)
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · have h1 : Lkp.InTable ((K.asm f).v' + 1) (K.asm f).d ((K.asm f).key st k) ((K.asm f).tab st) :=
      h.1.1
    rw [e1] at h1
    exact h1
  · have h2 : Valid ((K.asm f).v' + 1) (K.asm f).d (K.asm f).w ((K.asm f).n + 1)
        ((K.asm f).key st k) ((K.asm f).tab st) ((K.asm f).H.bit k) := h.2
    rw [e1, e2] at h2
    exact h2

theorem ldWfB_mm : Spec.ldWfB_mm E := by
  intro p _ C _ P K Rd hK hM l hl
  exact (ldLkpAsm2M_subIN E p (K.asm l) P.N Sum.inr (K.asm l).ValidMu C P.S
    (fun st : P.WSt => st.1) (P.rideL l) P.msg (K.Dt l) (Rd l) Sum.inr_injective
    (K.places l) (hK.adm l hl) (ldLkpAsm2_muValid E (K.asm l) (hK.adm l hl).1)
    (hM.mask l hl) (hM.rd l hl) (ldWfB_reads E C P K l)).mm

/-- Glue: under `hL`, `hK`, `hl`, the exact input relation of the lookup sub-protocol's statement
(`Sub.OK`, Cb/Ld/LdLkp.lean) at the lookup claim `P.lk l` (Cb/Ld/LdWf.lean) gives the exact input
relation of the assembled lookup `K.asm l`. -/
theorem LdWfP.Lks.in_rel {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C} (K : P.Lks) (p : ℕ) (hL : P.Laws) (hK : K.OK p)
    (l : ℕ) (hl : l ≤ P.n) (x : P.X) (y : P.Ex.Str) (w : P.W)
    (h : (jt2 P.S C.E0 P.Wp P.onW (P.honAt l) ((P.lk l).inP (P.multAt l)) (P.lk l).inR).rel x y w) :
    (P.S.over (idxAt C (fun st : P.WSt => st.1)
          (cj (P.rideL l) P.msg id ((K.asm l).lk.inP (K.asm l).ValidMu) (K.asm l).lk.inR))).rel
      x y w := by
  obtain ⟨hE, hAns, ⟨⟨hT, hMore⟩, hMu⟩, hEnc, hLater⟩ := h
  have hv := hK.v l hl
  have hd := dcd_of_enc hL hEnc
  have hMore' := (via_enc hL hEnc _).1 hMore
  have hMu' := (via_enc hL hEnc _).1 hMu
  have hLater' := (via_enc hL hEnc _).1 hLater
  have hT' : Lkp.InTable (P.v l) (P.d l) (P.keyAt l x.1 (y.1, P.S.msgs w.1)) (P.tab l) := hT
  rw [keyAt_eq l (ym := (y.1, P.S.msgs w.1)) hd, hv] at hT'
  refine ⟨hE, hAns, hEnc, ⟨hMore', hLater'⟩, ⟨?_, trivial⟩, hK.mult l hl x.1 _ _ hMu'⟩
  exact (inTable_congr fun b hb => ldWfB_key E C P hL l hl _ b (hv ▸ hb)).1 hT'

theorem ldWfB_cl : Spec.ldWfB_cl E := by
  intro p C P K Rd hL hK hM l hl x y w h
  exact mjLift2_clIN E (K.asm l) P.N Sum.inr (K.asm l).ValidMu C P.S
    (fun st : P.WSt => st.1) (P.rideL l) P.msg _ _ _
    (fun st w h =>
      (K.asm l).cut_claim E (K.asm l).ValidMu (K.Dt l) (Rd l) (hM.rd l hl)
        (ldWfB_reads E C P K l) st _ h)
    x y w (K.in_rel E p hL hK l hl x y w h)

end
end Cb
