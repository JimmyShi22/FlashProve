-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOnBTermProofs.lean: the proofs of the statements of Cb/Obj/LdObjectOnBTerm.lean: an
assembly.

The step in front of the test is a piece for one instance (as in Cb/Obj/LdObjectLinFullProofs.lean,
here for every condition on the index), a link with knowledge soundness in a batch (a link with the
empty shape), a piece of a chain of batch links (Cb/Ld/LdStepV.lean), and hands the encoded index
on. The proofs also use the theorems on the test (Cb/Ld/LdLinBHonTop.lean and the files of Cb/Ld/
that it stands on) and the rules for two in a row.

Main names (statements and hypotheses: Cb/Obj/LdObjectOnBTerm.lean):
  `ldOnT_same`: the term's link and reduction, in the forms of `O.fullB` and `O.full`.
  `ldOnT_ok`: all that is used of the term: the record `LinBT.OK`.
  `ldOnT_object`, `ldOnT_object_far`: both items of the object's list, `LinBListR` and `LinBKnowR`,
    of one term.
-/
import Cb.Obj.LdObjectOnBTerm
import Cb.Obj.LdObjectLinFullProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E)

/-- where a position of the oracles before the step is a source -/
theorem LdOL.enG_mem (U : Finset O.toC.P.E0.Pos) (V : Finset O.P.E0.Pos)
    (hV : ∀ p, p ∈ V ↔ ∃ u ∈ U, p ∈ O.enG.src u) :
    (∀ i, (Sum.inl i : O.P.E0.Pos) ∈ V ↔ (Sum.inl i : O.toC.P.E0.Pos) ∈ U) ∧
    ∀ z, (Sum.inr z : O.P.E0.Pos) ∈ V ↔ (Sum.inr (Sum.inr z) : O.toC.P.E0.Pos) ∈ U := by
  refine ⟨fun i => ?_, fun z => ?_⟩
  · rw [hV]
    constructor
    · rintro ⟨u, hu, hp⟩
      rcases u with u | u | u
      · rw [Sum.inl.inj (Finset.mem_singleton.1 hp)]
        exact hu
      · exact u.elim
      · exact absurd (Finset.mem_singleton.1 hp) (by simp)
    · exact fun h => ⟨_, h, Finset.mem_singleton_self _⟩
  · rw [hV]
    constructor
    · rintro ⟨u, hu, hp⟩
      rcases u with u | u | u
      · exact absurd (Finset.mem_singleton.1 hp) (by simp)
      · exact u.elim
      · rw [Sum.inr.inj (Finset.mem_singleton.1 hp)]
        exact hu
    · exact fun h => ⟨_, h, Finset.mem_singleton_self _⟩

/-- the demand on the oracles left, read on the two sides of the step -/
theorem LdOL.qaIn_of (qa : Finset O.toC.P.Ea.Pos → Prop) (U : Finset O.toC.P.E0.Pos)
    (V : Finset O.P.E0.Pos) (hV : ∀ p, p ∈ V ↔ ∃ u ∈ U, p ∈ O.enG.src u) (h : qa U.toRight) :
    O.qaIn qa V.toRight := by
  refine (congrArg qa ?_).mpr h
  ext p
  rw [Finset.mem_map, Finset.mem_toRight]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ((O.enG_mem U V hV).2 r).1 (Finset.mem_toRight.1 hr)
  · intro hp
    rcases p with p | p
    · exact p.elim
    · exact ⟨p, Finset.mem_toRight.2 (((O.enG_mem U V hV).2 p).2 hp), rfl⟩

/-- The step is a piece of a chain, for every condition on the index. -/
theorem LdOL.enterPiece (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop)
    (qa : Finset O.toC.P.Ea.Pos → Prop) :
    PieceTr O.enter O.hEnter (O.P.j0 on0) (O.toC.P.j0 on0) (fun _ _ w => (w.1, w.2.1))
      (Nums.pure Unit some O.enG) (O.P.q0 (O.qaIn qa)) (O.toC.P.q0 qa) := by
  classical
  refine pieceTr_pure Unit O.P.X0 O.toC.P.X0 O.P.E0 O.toC.P.E0 O.P.W0 O.toC.P.W0 (O.P.j0 on0)
    (O.toC.P.j0 on0) some O.enG (fun a => (a.1, (a.2.1, (a.2.2, ())))) (fun _ w => (w.1, w.2.1))
    (O.P.q0 (O.qaIn qa)) (O.toC.P.q0 qa)
    { isLocal := ?_
      acc := fun x y w h => ⟨rfl, h⟩
      onOut := ?_
      keeps := fun _ _ => rfl
      know := ?_ } ?_
  · intro y y' q h
    rcases q with p | p | p
    · exact congrArg _ (Sum.inl.inj (h (Sum.inl p) (Finset.mem_singleton_self _)))
    · exact p.elim
    · exact congrArg (fun s => Sum.inr (Sum.inr s))
        (Sum.inr.inj (h (Sum.inr p) (Finset.mem_singleton_self _)))
  · intro x y x' h hx
    obtain rfl := Option.some.inj hx
    exact ⟨h.1, h.2, trivial⟩
  · intro x y x' w' _ hx h
    obtain rfl := Option.some.inj hx
    exact h
  · intro U hU
    refine ⟨le_trans (Finset.card_le_card fun i hi => ?_) hU.1,
      O.qaIn_of qa U _ (fun p => ldLkC_mem_biUnion _) hU.2⟩
    exact Finset.mem_toLeft.2
      (((O.enG_mem U _ fun p => ldLkC_mem_biUnion _).1 i).1 (Finset.mem_toLeft.1 hi))

/-- the step hands the encoded index on -/
theorem LdOL.enterKeeps :
    O.enter.KeepsAt (fun j : Fin O.Cf.C₀.n => (Sum.inl j : O.P.E0.Pos))
      (fun j => (Sum.inl j : O.toC.P.E0.Pos)) := by
  refine ⟨fun _ _ h => absurd h (Finset.notMem_empty _), fun _ q j => ?_⟩
  rcases q with q | q | q
  · exact ⟨fun h => congrArg Sum.inl (Sum.inl.inj (Finset.mem_singleton.1 h)).symm,
      fun h => Finset.mem_singleton.2 (congrArg Sum.inl (Sum.inl.inj h).symm)⟩
  · exact q.elim
  · exact ⟨fun h => absurd (Finset.mem_singleton.1 h) (by simp), fun h => by cases h⟩

end

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOnT_same : Spec.ldOnT_same F E := by
  intro O _ on0 Sn qa εf N VT cZ d d₀
  obtain ⟨e1, e2⟩ := ldLinT_same O.toC.P on0 εf N Sn qa VT cZ d
  refine ⟨?_, ?_⟩
  · show (⟨O.lkE on0, PUnit.unit, ()⟩ : LinkA Unit (O.P.J0 on0) (O.toC.P.J0 on0)).seq
        (O.toC.P.linCV Sn qa N on0 εf cZ d).a d₀ = _
    rw [e1]
  · show O.enter.seq (O.toC.P.linCV Sn qa N on0 εf cZ d).a.l.R = _
    rw [e2]

theorem ldOnT_ok : Spec.ldOnT_ok F E := by
  classical
  intro O _ on0 Sn qa εf N VT cZ kT d d₀ ya hFit hF hpy hS hA hmono hOk hSd hKB hOkV hCoh hq
  obtain ⟨e1, e2⟩ := ldLinT_same O.toC.P on0 εf N Sn qa VT cZ d
  obtain ⟨-, -, hc, -, -, -, -, -, -, hwh⟩ :=
    ldLinT_all O.toC.P on0 εf N Sn qa ya VT cZ kT d hF hpy hS hA hOk hSd hKB hOkV hCoh hq
  -- one instance: a piece, then a tail
  have hT := ldLinC_tail O.toC.P on0 εf Sn qa d cZ.forget.forget hF hpy hS hOk hSd
  rw [← e2] at hT
  have hTail := tailTr_cons Unit _ _ _ _ _ O.enter (O.toC.P.linCV Sn qa N on0 εf cZ d).a.l.R _ _ _
    O.hEnter (O.toC.P.linCV Sn qa N on0 εf cZ d).a.l.H _ _ _ _ _ d₀ _ _ _ _ (O.enterPiece on0 qa) hT
  obtain ⟨hpt, hloc, -, -, -, -, -, htied, hreads⟩ := tailTr_end _ _ _ _ _ _ _ _ _ _ _ _ _ hTail
  -- the encoded index
  have hIdx : (O.termV on0 Sn qa εf N cZ d d₀).a.Idx
      (fun j : Fin O.Cf.C₀.n => (Sum.inl j : O.P.E0.Pos)) O.t := by
    have h1 := O.toC.P.idxAll on0 εf N Sn cZ.forget d hCoh
    rw [← e1] at h1
    exact idx_pre Unit _ (O.P.J0 on0) (O.toC.P.J0 on0) LdLinP.JT ⟨O.lkE on0, PUnit.unit, ()⟩
      (O.toC.P.linCV Sn qa N on0 εf cZ d).a d₀ _ _ O.t O.enterKeeps trivial h1
  -- the honest side of a batch: a piece, then a piece
  have hLV : (O.toC.P.linCV Sn qa N on0 εf cZ d).PV :=
    chainV_ok Unit N _ _ _ VT ((O.toC.P.chainV Sn qa N on0 εf).append cZ) d
      ((chainV_ok_append _ _ _ _ _ _ _ _ _ cZ).2
        ⟨okV_of_allPV _ _ _ _ _ _ _ (ldLinV_core O.toC.P on0 εf N Sn qa ya hF hpy hS hA), hOkV⟩)
  have hEV : (O.lvE on0 qa N).PV := by
    refine ⟨stepV_piece O.P.X0 O.toC.P.X0 O.P.E0 O.toC.P.E0 O.P.W0 O.toC.P.W0 O.Cf.conf.PIdx
        O.toC.P.Sh0 some O.enG (fun a => (a.1, (a.2.1, (a.2.2, ())))) O.shIn N (O.VIn on0 qa N).rel
        (O.toC.P.V0 qa N on0).rel (O.P.qv0 (O.qaIn qa) N) (O.toC.P.qv0 qa N)
        (O.enterPiece on0 qa).good.isLocal (fun x y w h => ⟨rfl, h.1, h.2⟩)
        (fun J Us Vs hU hV => ⟨fun T hT => ?_, fun j => ?_⟩),
      O.toC.P.her0 qa N⟩
    · exact hU.1 T fun i hi =>
        (hT i hi).elim fun j hj => ⟨j, ((O.enG_mem (Us j) (Vs j) (hV j)).1 i).1 hj⟩
    · exact O.qaIn_of qa (Us j) (Vs j) (hV j) (hU.2 j)
  have hPV :=
    linkV_seq Unit N _ _ _ _ _ _ (O.lvE on0 qa N) (O.toC.P.linCV Sn qa N on0 εf cZ d) d₀ hEV hLV
  obtain ⟨-, hacc, hex, -⟩ :=
    pieceV_end _ _ _ _ _ _ _ _ _ _ (O.termV on0 Sn qa εf N cZ d d₀).hv N (O.VIn on0 qa N).rel VT.rel
      (O.termV on0 Sn qa εf N cZ d d₀).bud (O.VIn on0 qa N).q VT.q hPV.1 hq
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
    { point := hpt
      isLocal := hloc
      coherent := hIdx.coh
      tied := htied
      idxShared := fun ρ ρ' hρ => by
        ext p
        rw [Finset.mem_filter, Finset.mem_filter]
        rcases p with j | p
        · exact and_congr_left fun _ => hIdx.shared ρ ρ' j hρ
        · exact ⟨fun hp => absurd hp.2 (by simp), fun hp => absurd hp.2 (by simp)⟩
      idxReads := fun ρ =>
        le_of_eq_of_le (ldk_card_filter_isLeft (α := Fin O.Cf.C₀.n) (β := O.P.Ea.Pos) _)
          (hIdx.few ρ _ fun j hj => Finset.mem_toLeft.1 hj)
      acc := hacc
      exact := hex
      bud0 := fun _ _ _ => rfl
      prBad := by
        have e : (O.termV on0 Sn qa εf N cZ d d₀).hv.withheld =
            Rho.cylFst (O.toC.P.linCV Sn qa N on0 εf cZ d).a.l.R.shape
                (O.lvE on0 qa N).hv.withheld ∪
              Rho.cylSnd O.enter.shape (O.toC.P.linCV Sn qa N on0 εf cZ d).hv.withheld :=
          Set.ext fun ρ =>
            LinkVSeq.mem_withheld (O.lvE on0 qa N).hv (O.toC.P.linCV Sn qa N on0 εf cZ d).hv ρ
        show prRho (O.termV on0 Sn qa εf N cZ d d₀).hv.withheld ≤ cZ.pWh
        rw [e]
        have z : prRho
              (Rho.cylFst (O.toC.P.linCV Sn qa N on0 εf cZ d).a.l.R.shape
                (O.lvE on0 qa N).hv.withheld) = 0 := by
          rw [prRho_cylFst]
          exact le_antisymm (prRho_empty _ fun ρ hρ => by
            have h0 : (O.lvE on0 qa N).hv.withheld = ∅ := stepV_wh _ _ _ _ _ _ _ _ _ _ _ _
            rw [h0] at hρ
            exact hρ) (zero_le _)
        exact (pr_union_le _ _ _).trans
          ((add_le_add (le_of_eq z) ((le_of_eq (prRho_cylSnd _ _)).trans hwh)).trans
            (le_of_eq (zero_add _)))
      bridge := fun x y w h => ⟨ldOL_rel F E O x y w h, ⟨h.1.1, rfl⟩, h.1.2.1.symm⟩
      fits := hFit
      know := (knowB_iff_orOff _ _ _ _ _ _ _ _ N _ (O.P.j0 on0).on (O.P.j0 on0).relR _ _ _).2 hK
      reads := hreads
      mono := fun U V hVU hU => ⟨(Finset.card_le_card fun i hi =>
        Finset.mem_toLeft.2 (hVU (Finset.mem_toLeft.1 hi))).trans hU.1,
        ldOLF_sub F E O qa hmono _ _
          (fun i hi => Finset.mem_toRight.2 (hVU (Finset.mem_toRight.1 hi))) hU.2⟩ }

theorem ldOnT_object :
    Spec.ldOnT_object F
      E := fun O _ on0 Sn qa εf N VT cZ kT d d₀ ya d0 hd he hFit hF hpy hS hA hmono hOk hSd hKB hOkV hCoh hq =>
  ldOBT_object F E O N (O.termT on0 Sn qa εf N cZ d d₀) d0 hd he
    (ldOnT_ok F E O on0 Sn qa εf N VT cZ kT d d₀ ya hFit hF hpy hS hA hmono
      hOk hSd hKB hOkV hCoh hq)

theorem ldOnT_object_far :
    Spec.ldOnT_object_far F
      E := fun O _ Sn qa N VT cZ kT d d₀ ya d0 hd he hpy hS hA hmono hOk hSd hKB hOkV hCoh hq =>
  ldOnT_object F E O O.onDec Sn qa 0 N VT cZ kT d d₀ ya d0 hd
    (lt_of_le_of_lt (Nat.le_add_left _ _) he) (ldOB_fits F E O).1 (ldOB_foldErr F E O hd he)
    hpy hS hA hmono hOk hSd hKB hOkV hCoh hq

end
end Cb
