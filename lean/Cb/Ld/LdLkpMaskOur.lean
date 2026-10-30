-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskOur.lean: the sumcheck with the dummy variable as a link of a chain over common
entries (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean).
This file is about the sumcheck protocol for a polynomial summand with one dummy last variable, as
one step of a chain of reductions that all speak of the same entries.

Definitions, statements and proofs. Glue.
A chain has one naming J of the entries and one reading of a witness: the entries in Rd, all others
forgotten (`mjCut Rd`). A sumcheck `T : PscOur E` (Cb/Ld/LdPsc.lean) of the chain names its entries
`T.J`; e : T.J ≃ J says which is which.

Main names:
  `mjsp_good`: under the hypotheses of its statement, completeness of a block at the base carries
    "the joint holds of the entries" through it.
  `mjl_reJ`, `mjsp_reJ`: the rules for a renaming of the entries, for links.
  `T.mjJ Ex e Rd`: the `MJ` record of the sumcheck over J.
  `mjl_our`: under `hV`, `hX`, `hY`: it is a link, started with any claim C that gives its true sum
    claim and does not read its own masks. Its messages read RdT (any set for which T's conditions
    `OwnOur` hold, inside Rd); its own masks lie at the places `wAt`, `cAt`.
  `mjOur_out`: under `hV`, `hX`, `hY`: at what the honest messages fix, its output rows
    (`PscPar.OutHolds`, Cb/Ld/LdPsc.lean) hold of the entries, and the state is handed on.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskSpChain
import Cb.Ld.LdPscZkOur
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Prob Hiop

open Classical in
/-- The entries in Rd; all others forgotten. -/
def mjCut {E J : Type} [Zero E] (Rd : J → Prop) (m : J → E) : J → E := fun j =>
  if Rd j then m j else 0

/-- Under the hypotheses below, completeness of a block at the base carries "the joint holds of the
entries" (Cb/Ld/LdLkpMaskSp.lean: `mjsp_sound`), for a block with its data. -/
theorem mjsp_good {E J K X₁ X₂ : Type} {Ex : ExtSpec} {b : BkA K (J → E) X₁ X₂ Ex Unit}
    {D : MJ E J b.R} {A : Rels K X₁ Ex ((J → E) × Unit)} {B : Rels K X₂ Ex ((J → E) × Unit)}
    {rd : (J → E) × Unit → J → E} {Sr Sw : J → Prop} {C : X₁ → (J → E) → Prop}
    (hl : D.Link b.H rd rd Sr Sw C) (hrd : ∀ w j, Sr j → rd w j = w.1 j) (hp : b.Plain)
    (hg : b.Good A B) (hC : ∀ x k, C x k → mjClOf A x k) :
    ∀ x' k, D.sp C x' k → mjClOf B x' k :=
  mjsp_sound hl hrd hp.keepsW hp.copies.copy hg.acc hC

theorem mjCut_of {E J : Type} [Zero E] {Rd : J → Prop} (m : J → E) {j : J} (h : Rd j) :
    mjCut Rd m j = m j := if_pos h

section ReJ
variable {E J J' : Type} {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}

theorem mjsp_reJ (D : MJ E J' R) (e : J' ≃ J) (C : Xi → (J → E) → Prop) (x' : Xo) (k : J → E) :
    (D.reJ e).sp C x' k ↔ D.sp (fun x k' => C x fun j => k' (e.symm j)) x' fun j' => k (e j') := by
  have ek : (fun j => k (e (e.symm j))) = k := funext fun j => by rw [e.apply_symm_apply]
  constructor
  · rintro ⟨x, ρ, hc, rfl⟩
    exact ⟨x, ρ, by show C x fun j => k (e (e.symm j)); rwa [ek], rfl⟩
  · rintro ⟨x, ρ, hc, rfl⟩
    exact ⟨x, ρ, by have h : C x fun j => k (e (e.symm j)) := hc; rwa [ek] at h, rfl⟩

theorem mjl_reJ {D : MJ E J' R} {H : R.Honest Wi Wo} (e : J' ≃ J) {rdi : Wi → J → E}
    {rdo : Wo → J → E} {Sr Sw : J' → Prop} {C : Xi → (J → E) → Prop}
    (h : D.Link H (fun w j' => rdi w (e j')) (fun w j' => rdo w (e j')) Sr Sw
      fun x k' => C x fun j => k' (e.symm j)) :
    (D.reJ e).Link H rdi rdo (fun j => Sr (e.symm j)) (fun j => Sw (e.symm j)) C := by
  have ek : ∀ k : J → E, (fun j => k (e (e.symm j))) = k := fun k =>
    funext fun j => by rw [e.apply_symm_apply]
  have e1 : ∀ (M : D.Mk) (k : J → E), (fun j' => (D.reJ e).put M k (e j')) =
      D.put M fun j' => k (e j') := fun M k => funext fun j' => by
    show D.put M (fun j' => k (e j')) (e.symm (e j')) = _
    rw [e.symm_apply_apply]
  have up : ∀ x k, C x k → C x fun j => k (e (e.symm j)) := fun x k hc => by rwa [ek]
  refine ⟨⟨⟨h.fits.mm.noOrc,
        h.fits.mm.free, h.fits.mm.run,
        fun x k M hc => h.fits.mm.stable x (fun j' => k (e j')) M (up x k hc),
        fun k x ρ hc => ?_⟩,
      fun w x c ρ => ?_, h.fits.hand⟩,
    fun k k' x ρ hk => h.reads _ _ x ρ fun j' hj => hk (e j') (by rwa [e.symm_apply_apply]),
    fun M k j hj => ?_⟩
  · show (unif D.Mk).map (fun M => D.msg (fun j' => (D.reJ e).put M k (e j')) x ρ) = D.sim x ρ
    simp only [e1]
    exact h.fits.mm.law _ x ρ (up x k hc)
  · funext j
    have h' := congrFun (h.fits.same w x c ρ) (e.symm j)
    simpa using h'
  · show D.put M (fun j' => k (e j')) (e.symm j) = k j
    rw [h.writes M _ _ hj, e.apply_symm_apply]

end ReJ

section Our
variable {E : Type} [Field E] [Fintype E]

/-- The `MJ` record of the sumcheck over the chain's entries. -/
def PscOur.mjJ
    (T : PscOur E) (Ex : ExtSpec) {J : Type} (e : T.J ≃ J) (Rd : J → Prop) :
    MJ E J (T.par.psc Ex) :=
  (T.par.mj Ex (T.own fun j' => Rd (e j'))).reJ e

variable (E)

theorem mjl_our (T : PscOur E) (Ex : ExtSpec) (J : Type) (e : T.J ≃ J) (Wt : Type)
    (msg : Wt → J → E) (Rd RdT : J → Prop) (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY)
    (hO : T.OwnOur fun j' => RdT (e j')) (hsub : ∀ j, RdT j → Rd j) (C : E × T.St → (J → E) → Prop)
    (hC : ∀ x k, C x k → T.SumHolds x fun j' => k (e j'))
    (hs : MjStab C fun j => ∃ i, j = e (Sum.elim T.wAt T.cAt i)) :
    (T.mjJ Ex e Rd).Link (T.par.hon Ex fun w j' => msg w (e j')) (fun w => mjCut Rd (msg w))
      (fun w => mjCut Rd (msg w)) RdT (fun j => ∃ i, j = e (Sum.elim T.wAt T.cAt i)) C := by
  have hO1 := psc_our_own E T _ (mjOur_mono E T _ (fun j' => Rd (e j')) (fun j' => hsub (e j')) hO)
  have hO2 := psc_our_own E T _ hO
  have h := mjl_psc E T.par Ex Wt (fun w j' => msg w (e j'))
    (T.own fun j' => Rd (e j')) (T.own fun j' => RdT (e j')) ((psc_our_ok E T).1 hV)
    (psc_our_deg E T hX hY) hO1 hO2 (mjOur_ne E T)
    (fun x k' => C x fun j => k' (e.symm j)) (fun x k' hc => (psc_our_sum E T x k').2 (by
      have h1 := hC x _ hc
      simpa using h1)) (fun x k k' hk hc => hs x _ _ (fun j hj => hk (e.symm j) fun ⟨i, hi⟩ => hj ⟨i, (e.apply_symm_apply j).symm.trans (congrArg e hi)⟩) hc)
  refine mjl_mono (mjl_reJ e h) (fun j hj => ?_) fun j ⟨i, hi⟩ =>
    ⟨i, (e.apply_symm_apply j).symm.trans (congrArg e hi)⟩
  have h2 : RdT (e (e.symm j)) := hj
  rwa [e.apply_symm_apply] at h2

theorem mjOur_out (T : PscOur E) (Ex : ExtSpec) (J : Type) (e : T.J ≃ J)
    (Rd : J → Prop) (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (k : J → E)
    (x : E × T.St) (ρ : Rho (T.par.psc Ex).shape) :
    T.par.OutHolds ((T.mjJ Ex e Rd).nxt x ((T.mjJ Ex e Rd).msg k x ρ) ρ) (fun j' => k (e j')) ∧
    ((T.mjJ Ex e Rd).nxt x ((T.mjJ Ex e Rd).msg k x ρ) ρ).st = x.2 :=
  mjPsc_out E T.par Ex (T.own fun j' => Rd (e j')) ((psc_our_ok E T).1 hV) (psc_our_deg E T hX hY)
    (mjOur_ne E T) (fun j' => k (e j')) x ρ

end Our
end Cb
