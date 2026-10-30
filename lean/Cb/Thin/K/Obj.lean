-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K/Obj.lean.
THE THIN ROAD: THE TWO LIFTINGS: the last bullets of `ldObj_lin` (Cb/Obj/LdObjectTail.lean:128-133)
and `ldObj_link` (:150) as lemmas of their own: the «know» item of the list from a bare `Know` and
two facts on relations: no bundle (TailTr, GoodT), no honest prover in the statement. So all five
«know» items of `S.HypK P` have a door of their own: ldClose_know (wf, req), ldOB_know (linOn), and
these two (linOff, link).
The controls prove the second halves of the library's two statements again, from its own premises,
through the lifted lemmas.

-/
import Cb.Obj.LdObjectTail

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-- The «know» half of `ldObj_lin`. -/
theorem ldObj_lin_know (C : ConfigurationWithOutOfDomainSample) (S : C.Left) (Wi : Type)
    (Q : IOR (S.Xl × C.Rec) S.El Unit extNone) (on : (S.Xl × C.Rec) × S.El.Str → Prop)
    (relR : (S.Xl × C.Rec) × S.El.Str → Wi → Prop)
    (ext : (S.Xl × C.Rec) × S.El.Str → Tr Q.shape → Unit → Wi) (ε : Err Q.shape)
    (fr : Wi → S.AMsg) (d0 : S.AMsg)
    (hknow : Q.red.Know on relR (fun _ _ => True) ext ε) (hb : ∀ a, S.cond a → on a)
    (hc : ∀ a w, S.cond a → relR a w → S.RlinR a (fr w)) : LinKnowR S Q d0 ε := by
  refine know_of_det _ _ _ _ _ _ _ _ _ _ (fun a => S.decA d0 a.1.1 a.2.2)
    ?_ (know_mapW fr hknow hb hc)
  rintro a w - ⟨U, -, h2, -⟩
  show w = (S.adec a.1.1 a.2.2).getD d0
  rw [h2]
  rfl

/-- The «know» half of `ldObj_link`. -/
theorem ldObj_link_know (C : ConfigurationWithOutOfDomainSample) (Wi : Type)
    (Q : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone)
    (on : (C.Rec × C.Rec) × (twoExternalStrings C.n C.Sg).Str → Prop)
    (relR : (C.Rec × C.Rec) × (twoExternalStrings C.n C.Sg).Str → Wi → Prop)
    (ext : (C.Rec × C.Rec) × (twoExternalStrings C.n C.Sg).Str → Tr Q.shape → Unit → Wi) (ε : Err Q.shape)
    (hknow : Q.red.Know on relR (fun _ _ => True) ext ε) (hb : ∀ a, C.onEq a → on a)
    (hc : ∀ a w, C.onEq a → relR a w → C.ReqR a ()) : LinkKnowR Q ε :=
  know_mapW (fun _ => ()) hknow hb hc

/-- CONTROL: under `ldObj_lin`'s own premises its second half, through the lifted lemma; of the
bundle `h.good.know` ALONE is read. -/
theorem ldObj_lin_know_ofOld (C : ConfigurationWithOutOfDomainSample) (S : C.Left) (Wi : Type)
    (Q : IOR (S.Xl × C.Rec) S.El Unit extNone) (H : Q.Honest Wi Unit)
    (A : Rels Unit (S.Xl × C.Rec) S.El Wi)
    (ext : (S.Xl × C.Rec) × S.El.Str → Tr Q.shape → Unit → Wi) (P : Nums Unit Q)
    (qi : Finset S.El.Pos → Prop) (fr : Wi → S.AMsg) (d0 : S.AMsg)
    (h : TailTr Q H A trivRels ext P qi) (hb : ∀ a, S.cond a → A.on a)
    (hc : ∀ a w, S.cond a → A.relR a w → S.RlinR a (fr w)) : LinKnowR S Q d0 P.err :=
  ldObj_lin_know C S Wi Q A.on A.relR ext P.err fr d0 h.good.know hb hc

theorem ldObj_link_know_ofOld (C : ConfigurationWithOutOfDomainSample) (Wi : Type)
    (Q : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone) (H : Q.Honest Wi Unit)
    (A : Rels Unit (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Wi)
    (ext : (C.Rec × C.Rec) × (twoExternalStrings C.n C.Sg).Str → Tr Q.shape → Unit → Wi) (P : Nums Unit Q)
    (qi : Finset (twoExternalStrings C.n C.Sg).Pos → Prop)
    (h : TailTr Q H A trivRels ext P qi) (hb : ∀ a, C.onEq a → A.on a)
    (hc : ∀ a w, C.onEq a → A.relR a w → C.ReqR a ()) : LinkKnowR Q P.err :=
  ldObj_link_know C Wi Q A.on A.relR ext P.err h.good.know hb hc

end Cb

