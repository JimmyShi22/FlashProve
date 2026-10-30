-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K4/BatchK.lean.
D3 LinBK: five of LinBT.OK's fifteen fields (Cb/Obj/LdObjectOnB.lean:67-84), in its words: what the
thin road wants of the test at N instances. T3 ldOnT_okK: the library's ldOnT_ok
(Cb/Obj/LdObjectOnBTerm.lean:134) for these five fields, UNDER SEVEN PREMISES FOR TWELVE: kept in
its words: Fits, FoldErr, Injective, Sn.OK, KB of the closing, Coh of the closing; new: every link
of the closing has Link.PL. T4 linBK_local, T6 objT_linOn: the door to ObjK's fields linOn, coh,
pLinOn.
THE ITEM LinBKnowR IS NOT HERE (it is ldOBT_object: one call of ldOB_know from LinBK's fits | know).
T3 IS A THIN TWIN OF ONE OF THE OLD FEEDERS UNDER ldObjT_ok: it is laid because its premises end at
«the closing chain has KB | Coh | Each PLk»: where a new closing would enter.
T3's PROOF READS TWO BUNDLES, BOTH CONCLUSIONS OF THEOREMS: LdOL.enterPiece (no premise) and
ldLinC_allT (under FoldErr, Injective, Sn.OK: three of the seven). ITS LINES FOR know AND coherent
ARE ldOnT_ok's OWN (Cb/Obj/LdObjectOnBTermProofs.lean:132, :142-147, :169-182): COPIES.
Does not say: WHERE THE CLOSING's KB COMES FROM: THE FLOOR BENEATH IS THICK (the plan's rules take
D.OK, whose field tail is a bundle: Cb/Ld/LdTower.lean:168); that LinBK has a member but through the
library's twelve premises (the controls' c2); anything on the other ten fields. cZ and T are data
that hold the other side's terms in their types: no property of these is asked. Nothing here is
about the protocol that the programs run.

-/
import Cb.Thin.K4.PLOf
import Cb.Obj.LdObjectOnBTermProofs
import Cb.Obj.LdObjectTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- D3: what the thin road wants of a term for the test at N instances. -/
structure LdOL.LinBT.LinBK {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E]
    {O : LdOL F E} {N : ℕ} (T : O.LinBT N) : Prop where
  point    : Nonempty T.R.shape.IsPoint
  isLocal  : T.R.IsLocal
  coherent : T.A.Coherent
  fits     : O.Fits T.on0
  know     : T.R.KnowB T.A N (SameKey fun a => (a.2.1, a.1.2)) (O.P.j0 T.on0).on (O.P.j0 T.on0).relR
    (fun _ (_ : Unit) => True) T.ext T.P.err

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- T3: the five fields of the library's term, from what its closing chain has on the «know» side.
-/
theorem ldOnT_okK (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
    (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
    (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) (VT : JV N LdLinP.JT)
    (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (kT : JKey LdLinP.JT) (d : O.toC.P.W0)
    (d₀ : O.P.W0)
    (hFit : O.Fits on0) (hF : O.toC.P.FoldErr on0 εf) (hpy : Function.Injective O.py) (hS : Sn.OK)
    (hKB : cZ.forget.KB N O.toC.P.key6 kT) (hCoh : cZ.forget.Coh)
    (hPL : cZ.forget.forget.Each (PLk Unit)) : (O.termT on0 Sn qa εf N cZ d d₀).LinBK := by
  classical
  obtain ⟨e1, e2⟩ := ldLinT_same O.toC.P on0 εf N Sn qa VT cZ d
  -- point oracles, locality: link by link
  have hL : (O.toC.P.linC on0 Sn εf cZ.forget.forget d).PL := by
    unfold LdLinP.linC
    exact chain_pl _ d
      ((ldLayW_append Unit (PLk Unit) _ _ _ (O.toC.P.chain on0 Sn εf) cZ.forget.forget).2
        ⟨each_pl_of_allT _ (ldLinC_allT O.toC.P on0 εf Sn hF hpy hS), hPL⟩)
  rw [← e2] at hL
  have hE : (O.lkE on0).PL :=
    ⟨(O.enterPiece on0 qa).good.point, (O.enterPiece on0 qa).good.isLocal⟩
  have hPt := pl_seq (O.lkE on0) (O.toC.P.linCV Sn qa N on0 εf cZ d).a.l d₀ hE hL
  -- the encoded index
  have hIdx : (O.termV on0 Sn qa εf N cZ d d₀).a.Idx
      (fun j : Fin O.Cf.C₀.n => (Sum.inl j : O.P.E0.Pos)) O.t := by
    have h1 := O.toC.P.idxAll on0 εf N Sn cZ.forget d hCoh
    rw [← e1] at h1
    exact idx_pre Unit _ (O.P.J0 on0) (O.toC.P.J0 on0) LdLinP.JT ⟨O.lkE on0, PUnit.unit, ()⟩
      (O.toC.P.linCV Sn qa N on0 εf cZ d).a d₀ _ _ O.t O.enterKeeps trivial h1
  -- knowledge soundness in a batch
  have hKE : (⟨O.lkE on0, PUnit.unit, ()⟩ : LinkA Unit (O.P.J0 on0) (O.toC.P.J0 on0)).KB
      N ⟨_, O.P.k0⟩ (O.toC.P.key0 on0) :=
    ⟨ldk_knowB_adm _
        (knowB_local _ _ _ _ _ _ O.enter RAnn.allLocal (fun _ => rfl) N _ _ _ _ _
          (ldk_pieceTr_cf (O.enterPiece on0 qa)).good.know),
      fun _ ha τ =>
        ldk_sameKey_bind (fun j aj => O.enter.red.out aj (τ.slot j)) id
          (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩
  have hKL : (O.toC.P.linCV Sn qa N on0 εf cZ d).a.KB N (O.toC.P.key0 on0) kT := by
    rw [e1]
    exact chainA_kb Unit _ _ _ d N _ _
      (chainA_kb_append Unit _ _ _ _ cZ.forget N _ _ kT
        (ldLinCB_core O.toC.P on0 εf N Sn hF hpy hS) hKB)
  have hK := (ldk_linkB_seq d₀ hKE hKL).know
  exact
    { point := hPt.point
      isLocal := hPt.isLocal
      coherent := hIdx.coh
      fits := hFit
      know := (knowB_iff_orOff _ _ _ _ _ _ _ _ N _ (O.P.j0 on0).on (O.P.j0 on0).relR _ _ _).2 hK }

end

/-- T4: the door: what L10 and ObjK take of the batch protocol T.Q beside the item on knowledge
soundness. -/
theorem linBK_local {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {O : LdOL F E}
    {N : ℕ} (T : O.LinBT N) (h : T.LinBK) :
    T.Q.ior.IsLocal ∧ T.Q.ann.Coherent ∧ Nonempty T.Q.ior.shape.IsPoint :=
  ⟨h.isLocal, h.coherent, h.point⟩

/-- T6: the same at an object `T : LdObjT`: ObjK's fields linOn, coh, pLinOn. -/
theorem objT_linOn {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (T : LdObjT F E) (h : T.linB.LinBK) :
    T.obj.subs.linOn.ior.IsLocal ∧ T.obj.subs.linOn.ann.Coherent ∧
      Nonempty T.obj.subs.linOn.ior.shape.IsPoint :=
  ⟨h.isLocal, h.coherent, h.point⟩

end Cb

