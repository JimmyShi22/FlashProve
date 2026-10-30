-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinProofs.lean: proofs of the statements of Cb/Obj/LdObjectLin.lean. Every
"Spec.name" there is "theorem name" here.

Main names: `ldOL_items`, `ldOL_lin`: see their statements in Cb/Obj/LdObjectLin.lean.
The four bridging facts are read off the definitions, with three lemmas of the configuration
(Cb/Obj/LdObjectConfProofs.lean: `tab_enc`, `view_full`, `ldCf_dcd_iff`) and two on decoders
(`Cb.sig_dec_cand`, `Cb.ldClose_decAll`); the two items come from `Cb.ldLin_tail` through the
generic rule `Cb.ldObj_lin` (Cb/Obj/LdObjectTail.lean).
-/
import Cb.Obj.LdObjectLin
import Cb.Ld.LdLinProofsChain

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype E] in
theorem ldOL_types : Spec.ldOL_types F E := fun _ => ⟨rfl, rfl, fun _ => rfl⟩

omit [Fintype E] in
theorem ldOL_rel : Spec.ldOL_rel F E := by
  intro O x y w h
  obtain ⟨⟨hy, -, hans⟩, hE, hA, hCl, hm⟩ := h
  refine ⟨?_, ?_, ⟨hE, hA, hm⟩, ?_⟩
  · show O.Cf.tab y.1 = _
    rw [show y.1 = O.Cf.enc w.1.1.1 w.1.1.2 from hy]
    exact O.Cf.tab_enc w.1.1.1 w.1.1.2
  · show O.Cf.X.ZR.val x.2.1 (O.Cf.X.view fun r => Code.liftWord E (O.Cf.full w.1.1.1 w.1.1.2 r)) =
      x.2.2
    rw [O.Cf.view_full]
    exact hans.symm
  · show O.D.Claim (O.Cf.X.view fun r => Code.liftWord E (O.Cf.full w.1.1.1 w.1.1.2 r)) (O.g x.1.1)
      (O.ψ x.1.1) (O.restM x.1.1 w.2.1) (O.τ x.1.1)
    rw [O.Cf.view_full]
    exact hCl

omit [Fintype E] in
theorem ldOL_on : Spec.ldOL_on F E := fun _ _ => Iff.rfl

omit [Fintype E] in
theorem ldOL_relR : Spec.ldOL_relR F E := by
  intro O hd he a w h
  obtain ⟨⟨hdec, hm⟩, U, hU, hCl⟩ := h
  have hU' : O.Cf.X.dec (O.Cf.tab a.2.1) a.1.2 = some U := hU
  have h1 : O.Cf.conf.dcd a.2.1 a.1.2 = some (O.Cf.dnM U) := by
    show (O.Cf.X.dec (O.Cf.tab a.2.1) a.1.2).map O.Cf.dnM = _
    rw [hU']
    rfl
  have h2 := (ldCf_dcd_iff F E O.Cf hd he a.2.1 a.1.2 (O.Cf.dnM U)).1 h1
  have hUU : O.Cf.upM (O.Cf.dnM U) = U := Option.some.inj (h2.symm.trans hU')
  refine ⟨O.Cf.dnM U, h1, (ldClose_decAll E O.S a.1.1.2 a.2.2 (O.S.msgs w.2)).2 hdec,
    fun i => (sig_dec_cand E (O.S.om i) (a.2.2 i) (a.1.1.2 i) _ (hdec i)).2, ?_, hm⟩
  show O.D.Claim (O.Cf.upM (O.Cf.dnM U)) _ _ _ _
  rw [hUU]
  exact hCl

omit [Fintype F] [Fintype E] in
open Classical in
theorem ldOL_reads : Spec.ldOL_reads F E := by
  intro O qa U h
  have e : (U.filter fun p => p.isLeft) = U.toLeft.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext p
    rcases p with p | p <;> simp
  rw [e, Finset.card_map]
  exact h.1

/-- fixed values for the chain's extractor, where a verifier has rejected -/
def LdOL.dflt {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E) :
    O.P.W0 × O.P.WA × O.P.W1 × O.P.W2 × O.P.W3 × O.P.W4 :=
  let w0 : O.P.W0 := (fun _ _ => 0, fun _ => (fun _ => 0, fun _ => 0))
  let w1 : O.P.W1 := (fun _ => (fun _ => 0, fun _ => 0), w0)
  let w3 : O.P.W3 := (fun _ => (fun _ => 0, fun _ => 0), w1)
  (w0, (fun _ => 0, w0), w1, (fun _ => 0, w1), w3, (fun _ => 0, w3))

/-- the two items together, from the generic rule (Cb/Obj/LdObjectTail.lean) and the four bridging
facts. (not all hypotheses are named here: see the statement below) -/
theorem ldOL_both (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.P.Snd)
    (qa : Finset O.P.Ea.Pos → Prop) (Z : O.P.Closing) (d0 : O.left.AMsg)
    (hc : ∀ (a : O.left.St) (w : O.P.W0), (O.P.j0 O.on0).relR a w → O.left.RlinR a (O.S.msgs w.2))
    (hF : O.P.FoldErr O.on0 εf) (hpy : Function.Injective O.py) (hS : Sn.OK)
    (hZ : TailTr Z.T Z.H O.P.j6.cf trivRels Z.ext Z.N (O.P.q5 Sn qa)) :
    LinListR O.left (O.lin Z) (O.hLin Sn Z) (O.nums Sn Z εf) ∧
    LinKnowR O.left (O.lin Z) d0 (O.nums Sn Z εf).err :=
  ldObj_lin O.Cf.conf O.left O.P.W0 (O.lin Z) (O.P.hLin Sn Z) (O.P.j0 O.on0) (O.P.extLin Z O.dflt)
    (O.P.numsLin Sn Z εf) (O.P.q0 qa) O.t O.fi (fun w => O.S.msgs w.2) d0
    (ldLin_tail O.P O.on0 εf Sn qa O.dflt Z hF hpy hS hZ) (ldOL_rel F E O)
    (fun a => (ldOL_on F E O a).1) (fun a w _ => hc a w) (ldOL_reads F E O qa)

theorem ldOL_items : Spec.ldOL_items F E := fun O _ εf Sn qa Z d0 hd he hF hpy hS hZ =>
  ldOL_both F E O εf Sn qa Z d0 (ldOL_relR F E O hd he) hF hpy hS hZ

theorem ldOL_lin : Spec.ldOL_lin F E := by
  intro O _ bad L Sn qa Z d0 hd hdX he he' hm hL hpy hS hZ
  exact ldOL_both F E O _ Sn qa Z d0 (ldOL_relR F E O hd he)
    (ldLin_foldErr O.P O.Cf.C₀.d bad L hdX he he' hm hL) hpy hS hZ

end
end Cb
