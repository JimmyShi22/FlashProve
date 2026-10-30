-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseSplitProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseSplit.lean (the
closing of the test for linear constraints on the encoded index, with any number of splittings in
front of its tests).
`ldLinSp_freshO`, `ldLinSp_freshU`, `ldLinSp_freshW` have one plan: `LdLinC.fresh_step` takes the
step without rounds off; the core's theorem (`ldLinC_freshO`, `ldLinC_freshU`, `ldLinC_freshW`) is
carried through a map g of readings (`freshFor_conseq`); the rest shows, summand by summand of
`C.S`, the premise of `freshFor_conseq` (g carries the one `put` to the other) and that the two
readings agree. The proofs for U and W differ from that for O, among other things, in the place of
the family in the sum, in the further hypotheses that they hand on, and in the map `keep` (here
`Prod.snd`, with its two laws) that the core's theorems for U and W take.
`ldLinSp_chain`: the step is a piece (`ldLinPre_step_cf`, `pieceTr_pure`); the core is a chain of
the two kinds (`Chain.Ok`, Ior/KnowCollRulesChain.lean; by `ldLinC_allT`, `ok_of_allT`); the front
stands behind it (`front_okFrom`) and has its halves (`front_sides`); `ldChain_front` puts the plan
behind them; each under the hypotheses of its statement. `ldLinSp_tail`: from `ldLinSp_chain`, by
`ldLinC_tail`.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldLinSp_tail` can be met
   together. -/
import Cb.Ld.LdLinCloseSplit
import Cb.Ld.LdFrontProofs
import Cb.Ld.LdLinCloseLinProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

theorem own_laws_cut : Spec.own_laws_cut := by
  classical
  intro E _ N W W' D Mb U Sd Rd own val hsub hown hoff hpad
  refine ⟨fun M M' k => Prod.ext (funext fun a => funext fun j => ?_) rfl,
    ⟨fun w k₀ =>
        (fun a j =>
            if h : Nonempty Mb then
              N.cut Rd (D.upM (D.put w (U.mk' h.some k₀ (Classical.arbitrary _)))) a j
            else 0,
          D.rest w),
      fun w M k₀ η => Prod.ext (funext fun a => funext fun j => ?_) rfl⟩,
    hpad⟩
  · unfold Sig.ow
    by_cases h : own ⟨a, j⟩
    · simp only [if_pos h]
    · simp only [if_neg h]
  · have hne : Nonempty Mb := ⟨M⟩
    unfold Sig.ow Sig.cut
    by_cases h : own ⟨a, j⟩
    · simp only [if_pos h, if_pos (hsub _ h)]
      exact hown w M k₀ η ⟨a, j⟩ h
    · simp only [if_neg h, dif_pos hne]
      by_cases hr : Rd ⟨a, j⟩
      · simp only [if_pos hr]
        exact hoff w M _ k₀ η _ ⟨a, j⟩ hr h
      · simp only [if_neg hr]

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- For ι and Mb nonempty: the step without rounds does not look (exactly: `Honest.Blind`,
Ior/KnowCollRulesMask.lean): the reading before it is the reading after it (kc), of the re-bracketed
witness (`C.toW v`); premise (`h`) and conclusion: see the statement. -/
theorem LdLinC.fresh_step {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι]
    [Fintype κ] [Fintype J] [Fintype Y] (C : LdLinC E ι κ J Y)
    (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (S : C.P.Snd)
    (x : FSt C.S C.E₀ C.Wpa Unit) (fq : C.St6 → x.St) {Kc : Type} (kc : C.S.Wit × C.Wpa → Kc)
    (Mb : Type) [Fintype Mb] [Nonempty Mb] (put : Mb → Kc → Kc)
    (h : (C.P.chain on0 S εf).FreshFor (fun v : C.P.W5 => kc (C.toW v)) Mb put) :
    ((C.P.chain on0 S εf).append (C.chain fq x.A)).FreshFor kc Mb put := by
  show ((C.P.chain on0 S εf).append (Chain.one (C.link fq x.A))).FreshFor kc Mb put
  rw [append_one]
  exact (freshFor_snoc _ (C.link fq x.A) kc Mb put).2
    (Or.inr ⟨Kc,
        fun v : C.P.W5 => kc (C.toW v),
        put, h,
        blind_stepPure _ _ _ _ _ _ (C.stepF fq) C.toE (C.stepM fq) _ _
          (fun v : C.P.W5 => kc (C.toW v)) kc Mb put put fun _ _ _ _ hk => ⟨rfl, hk⟩⟩)

theorem ldLinSp_freshO : Spec.ldLinSp_freshO E ι κ J Y := by
  classical
  intro C on0 εf S x fq Mb _ _ U Rd Rr own val hU hH hRr hown
  refine C.fresh_step on0 εf S x fq _ Mb _ ?_
  have h0 := ldLinC_freshO C.P on0 εf S Mb U _ (fun m w' => (C.NO.cut (fun n => Rd (C.eO n)) m, w'))
    (fun M k => (C.NO.ow own (val M) k.1, k.2)) hU hH
  let g : C.NO.Msg × C.P.W3 → C.S.Msg × (∀ o, Option (C.S.om o).Rnd) × C.Wpa := fun k =>
    C.S.wide C.Wpa Rd Rr (C.toW ((fun a => (k.1 a, fun _ => 0)), k.2))
  have h1 := freshFor_conseq Unit _ _ (C.P.chain on0 S εf) _ _
    (fun v : C.P.W5 => (C.NO.cut (fun n => Rd (C.eO n)) (C.NO.msgs v.1), v.2)) g Mb
    (fun M k => (C.NO.ow own (val M) k.1, k.2))
    (x.stage.wideFact Rd Rr (C.liO False own) Mb fun M => C.liO 0 (val M)).put ?_ h0
  · have e : (fun v : C.P.W5 => g (C.NO.cut (fun n => Rd (C.eO n)) (C.NO.msgs v.1), v.2)) =
        fun v : C.P.W5 =>
          (x.stage.wideFact Rd Rr (C.liO False own) Mb fun M => C.liO 0 (val M)).kc (C.toW v) := by
      funext v
      refine Prod.ext (funext fun o => funext fun j => ?_) (Prod.ext (funext fun o => ?_) rfl)
      · rcases o with o | a
        · rfl
        · show (if Rd ⟨.inr a, j⟩ then (if Rd ⟨.inr a, j⟩ then (v.1 a).1 j else 0) else 0) =
            if Rd ⟨.inr a, j⟩ then (v.1 a).1 j else 0
          by_cases hr : Rd ⟨.inr a, j⟩
          · simp only [if_pos hr]
          · simp only [if_neg hr]
      · rcases o with o | a
        · rfl
        · exact (if_neg (hRr a)).trans (if_neg (hRr a)).symm
    exact e ▸ h1
  · intro M k
    refine Prod.ext (funext fun o => funext fun j => ?_)
      (Prod.ext (funext fun o => by rcases o with o | a <;> rfl) rfl)
    rcases o with o | a
    · exact (if_neg (fun h : False => h)).symm
    · show (if Rd ⟨.inr a, j⟩ then (if own ⟨a, j⟩ then val M ⟨a, j⟩ else k.1 a j) else 0) =
        if own ⟨a, j⟩ then val M ⟨a, j⟩ else (if Rd ⟨.inr a, j⟩ then k.1 a j else 0)
      by_cases ho : own ⟨a, j⟩
      · have hr : Rd ⟨.inr a, j⟩ := hown ⟨a, j⟩ ho
        simp only [if_pos ho, if_pos hr]
      · simp only [if_neg ho]

theorem ldLinSp_freshU : Spec.ldLinSp_freshU E ι κ J Y := by
  classical
  intro C on0 εf S x fq Mb _ _ U Rd Rr own val hU hH hLO hA hRr hown
  refine C.fresh_step on0 εf S x fq _ Mb _ ?_
  have h0 := ldLinC_freshU C.P on0 εf S Mb U _ (fun m w' => (C.NU.cut (fun n => Rd (C.eU n)) m, w'))
    (fun M k => (C.NU.ow own (val M) k.1, k.2)) Prod.snd (fun _ _ => rfl) (fun _ _ => rfl) hU hH hLO
    hA
  let g : C.NO.Wit × (C.NU.Msg × C.P.W1) → C.S.Msg × (∀ o, Option (C.S.om o).Rnd) × C.Wpa :=
    fun k => C.S.wide C.Wpa Rd Rr (C.toW (k.1, ((fun a => (k.2.1 a, fun _ => 0)), k.2.2)))
  have h1 := freshFor_conseq Unit _ _ (C.P.chain on0 S εf) _ _
    (fun v : C.P.W5 => (v.1, (C.NU.cut (fun n => Rd (C.eU n)) (C.NU.msgs v.2.1), v.2.2))) g Mb
    (fun M k => (k.1, (C.NU.ow own (val M) k.2.1, k.2.2)))
    (x.stage.wideFact Rd Rr (C.liU False own) Mb fun M => C.liU 0 (val M)).put ?_ h0
  · have e : (fun v : C.P.W5 =>
          g (v.1, (C.NU.cut (fun n => Rd (C.eU n)) (C.NU.msgs v.2.1), v.2.2))) =
        fun v : C.P.W5 =>
          (x.stage.wideFact Rd Rr (C.liU False own) Mb fun M => C.liU 0 (val M)).kc (C.toW v) := by
      funext v
      refine Prod.ext (funext fun o => funext fun j => ?_) (Prod.ext (funext fun o => ?_) rfl)
      · rcases o with (o | a) | o
        · rfl
        · show (if Rd ⟨.inl (.inr a), j⟩ then (if Rd ⟨.inl (.inr a), j⟩ then (v.2.1 a).1 j else 0)
              else 0) =
            if Rd ⟨.inl (.inr a), j⟩ then (v.2.1 a).1 j else 0
          by_cases hr : Rd ⟨.inl (.inr a), j⟩
          · simp only [if_pos hr]
          · simp only [if_neg hr]
        · rfl
      · rcases o with (o | a) | o
        · rfl
        · exact (if_neg (hRr a)).trans (if_neg (hRr a)).symm
        · rfl
    exact e ▸ h1
  · intro M k
    refine Prod.ext (funext fun o => funext fun j => ?_)
      (Prod.ext (funext fun o => by rcases o with (o | a) | o <;> rfl) rfl)
    rcases o with (o | a) | o
    · exact (if_neg (fun h : False => h)).symm
    · show (if Rd ⟨.inl (.inr a), j⟩ then (if own ⟨a, j⟩ then val M ⟨a, j⟩ else k.2.1 a j) else 0) =
        if own ⟨a, j⟩ then val M ⟨a, j⟩ else (if Rd ⟨.inl (.inr a), j⟩ then k.2.1 a j else 0)
      by_cases ho : own ⟨a, j⟩
      · have hr : Rd ⟨.inl (.inr a), j⟩ := hown ⟨a, j⟩ ho
        simp only [if_pos ho, if_pos hr]
      · simp only [if_neg ho]
    · exact (if_neg (fun h : False => h)).symm

theorem ldLinSp_freshW : Spec.ldLinSp_freshW E ι κ J Y := by
  classical
  intro C on0 εf S x fq Mb _ _ U Rd Rr own val hU hH hLU hLO hA hRr hown
  refine C.fresh_step on0 εf S x fq _ Mb _ ?_
  have h0 := ldLinC_freshW C.P on0 εf S Mb U _ (fun m w' => (C.NW.cut (fun n => Rd (C.eW n)) m, w'))
    (fun M k => (C.NW.ow own (val M) k.1, k.2)) Prod.snd (fun _ _ => rfl) (fun _ _ => rfl) hU hH hLU
    hLO hA
  let g : C.NO.Wit × C.NU.Wit × (C.NW.Msg × C.P.W0) →
      C.S.Msg × (∀ o, Option (C.S.om o).Rnd) × C.Wpa :=
    fun k =>
      C.S.wide C.Wpa Rd Rr (C.toW (k.1, (k.2.1, ((fun a => (k.2.2.1 a, fun _ => 0)), k.2.2.2))))
  have h1 := freshFor_conseq Unit _ _ (C.P.chain on0 S εf) _ _
    (fun v : C.P.W5 => (v.1, v.2.1, (C.NW.cut (fun n => Rd (C.eW n)) (C.NW.msgs v.2.2.1), v.2.2.2)))
    g Mb (fun M k => (k.1, k.2.1, (C.NW.ow own (val M) k.2.2.1, k.2.2.2)))
    (x.stage.wideFact Rd Rr (C.liW False own) Mb fun M => C.liW 0 (val M)).put ?_ h0
  · have e : (fun v : C.P.W5 =>
          g (v.1, v.2.1, (C.NW.cut (fun n => Rd (C.eW n)) (C.NW.msgs v.2.2.1), v.2.2.2))) =
        fun v : C.P.W5 =>
          (x.stage.wideFact Rd Rr (C.liW False own) Mb fun M => C.liW 0 (val M)).kc (C.toW v) := by
      funext v
      refine Prod.ext (funext fun o => funext fun j => ?_) (Prod.ext (funext fun o => ?_) rfl)
      · rcases o with ((o | a) | o) | o
        · rfl
        · show (if Rd ⟨.inl (.inl (.inr a)), j⟩ then
                (if Rd ⟨.inl (.inl (.inr a)), j⟩ then (v.2.2.1 a).1 j else 0)
              else 0) =
            if Rd ⟨.inl (.inl (.inr a)), j⟩ then (v.2.2.1 a).1 j else 0
          by_cases hr : Rd ⟨.inl (.inl (.inr a)), j⟩
          · simp only [if_pos hr]
          · simp only [if_neg hr]
        · rfl
        · rfl
      · rcases o with ((o | a) | o) | o
        · rfl
        · exact (if_neg (hRr a)).trans (if_neg (hRr a)).symm
        · rfl
        · rfl
    exact e ▸ h1
  · intro M k
    refine Prod.ext (funext fun o => funext fun j => ?_)
      (Prod.ext (funext fun o => by rcases o with ((o | a) | o) | o <;> rfl) rfl)
    rcases o with ((o | a) | o) | o
    · exact (if_neg (fun h : False => h)).symm
    · show (if Rd ⟨.inl (.inl (.inr a)), j⟩ then (if own ⟨a, j⟩ then val M ⟨a, j⟩ else k.2.2.1 a j)
          else 0) =
        if own ⟨a, j⟩ then val M ⟨a, j⟩
        else (if Rd ⟨.inl (.inl (.inr a)), j⟩ then k.2.2.1 a j else 0)
      by_cases ho : own ⟨a, j⟩
      · have hr : Rd ⟨.inl (.inl (.inr a)), j⟩ := hown ⟨a, j⟩ ho
        simp only [if_pos ho, if_pos hr]
      · simp only [if_neg ho]
    · exact (if_neg (fun h : False => h)).symm
    · exact (if_neg (fun h : False => h)).symm

theorem ldLinSp_entO : Spec.ldLinSp_entO E ι κ J Y := by
  classical
  intro C on0 εf S x fq U Rd Rr n₀ hU hH hRr hR
  have h := ldLinSp_freshO E ι κ J Y C on0 εf S x fq E U Rd Rr (fun n => n = n₀) (fun u _ => u)
    hU hH hRr (fun n hn => hn ▸ hR)
  have e : (x.stage.wideFact Rd Rr (C.liO False fun n => n = n₀) E fun M =>
        C.liO 0 fun _ => M).put =
      (x.stage.wideFact Rd Rr (fun n => n = C.eO n₀) E fun u _ => u).put := by
    funext M k
    refine Prod.ext (funext fun o => funext fun j => ?_) rfl
    obtain ⟨a₀, j₀⟩ := n₀
    rcases o with o | a
    · refine (if_neg (fun h : False => h)).trans (if_neg fun h => ?_).symm
      exact Sum.inl_ne_inr (Sigma.mk.inj h).1
    · by_cases hn : (⟨a, j⟩ : C.NO.Ent) = ⟨a₀, j₀⟩
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj hn
        subst h1
        obtain rfl := eq_of_heq h2
        exact (if_pos rfl).trans (if_pos rfl).symm
      · refine (if_neg hn).trans (if_neg fun h => hn ?_).symm
        obtain ⟨h1, h2⟩ := Sigma.mk.inj h
        obtain rfl := Sum.inr.inj h1
        obtain rfl := eq_of_heq h2
        rfl
  exact e ▸ h

theorem ldLinSp_entU : Spec.ldLinSp_entU E ι κ J Y := by
  classical
  intro C on0 εf S x fq U Rd Rr n₀ hU hH hLO hA hRr hR
  have h := ldLinSp_freshU E ι κ J Y C on0 εf S x fq E U Rd Rr (fun n => n = n₀) (fun u _ => u)
    hU hH hLO hA hRr (fun n hn => hn ▸ hR)
  have e : (x.stage.wideFact Rd Rr (C.liU False fun n => n = n₀) E fun M =>
        C.liU 0 fun _ => M).put =
      (x.stage.wideFact Rd Rr (fun n => n = C.eU n₀) E fun u _ => u).put := by
    funext M k
    refine Prod.ext (funext fun o => funext fun j => ?_) rfl
    obtain ⟨a₀, j₀⟩ := n₀
    rcases o with (o | a) | o
    · refine (if_neg (fun h : False => h)).trans (if_neg fun h => ?_).symm
      exact Sum.inl_ne_inr (Sum.inl.inj (Sigma.mk.inj h).1)
    · by_cases hn : (⟨a, j⟩ : C.NU.Ent) = ⟨a₀, j₀⟩
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj hn
        subst h1
        obtain rfl := eq_of_heq h2
        exact (if_pos rfl).trans (if_pos rfl).symm
      · refine (if_neg hn).trans (if_neg fun h => hn ?_).symm
        obtain ⟨h1, h2⟩ := Sigma.mk.inj h
        obtain rfl := Sum.inr.inj (Sum.inl.inj h1)
        obtain rfl := eq_of_heq h2
        rfl
    · refine (if_neg (fun h : False => h)).trans (if_neg fun h => ?_).symm
      exact Sum.inr_ne_inl (Sigma.mk.inj h).1
  exact e ▸ h

theorem ldLinSp_entW : Spec.ldLinSp_entW E ι κ J Y := by
  classical
  intro C on0 εf S x fq U Rd Rr n₀ hU hH hLU hLO hA hRr hR
  have h := ldLinSp_freshW E ι κ J Y C on0 εf S x fq E U Rd Rr (fun n => n = n₀) (fun u _ => u)
    hU hH hLU hLO hA hRr (fun n hn => hn ▸ hR)
  have e : (x.stage.wideFact Rd Rr (C.liW False fun n => n = n₀) E fun M =>
        C.liW 0 fun _ => M).put =
      (x.stage.wideFact Rd Rr (fun n => n = C.eW n₀) E fun u _ => u).put := by
    funext M k
    refine Prod.ext (funext fun o => funext fun j => ?_) rfl
    obtain ⟨a₀, j₀⟩ := n₀
    rcases o with ((o | a) | o) | o
    · refine (if_neg (fun h : False => h)).trans (if_neg fun h => ?_).symm
      exact Sum.inl_ne_inr (Sum.inl.inj (Sum.inl.inj (Sigma.mk.inj h).1))
    · by_cases hn : (⟨a, j⟩ : C.NW.Ent) = ⟨a₀, j₀⟩
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj hn
        subst h1
        obtain rfl := eq_of_heq h2
        exact (if_pos rfl).trans (if_pos rfl).symm
      · refine (if_neg hn).trans (if_neg fun h => hn ?_).symm
        obtain ⟨h1, h2⟩ := Sigma.mk.inj h
        obtain rfl := Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h1))
        obtain rfl := eq_of_heq h2
        rfl
    · refine (if_neg (fun h : False => h)).trans (if_neg fun h => ?_).symm
      exact Sum.inr_ne_inl (Sum.inl.inj (Sigma.mk.inj h).1)
    · refine (if_neg (fun h : False => h)).trans (if_neg fun h => ?_).symm
      exact Sum.inr_ne_inl (Sigma.mk.inj h).1
  exact e ▸ h

theorem ldLinSp_chain : Spec.ldLinSp_chain E ι κ J Y := by
  classical
  intro C on0 εf S qa x Q fq p Rd Rr hF hpy hS hSays hQ hq hH hSd hZ
  have hT := ldLinPre_step_cf E ι κ J Y C x.St x.A fq hSays
  have hp := pieceTr_pure Unit _ _ _ _ _ _ C.P.j6.cf (C.S.over x.A).cf (C.stepF fq) C.toE
    (C.stepM fq) (fun _ w => C.back w) (C.P.q5 S qa) Q.q
    ⟨hT.isLocal, hT.acc, hT.onOut, hT.keeps, hT.know⟩ hq
  have hc : (C.P.chain on0 S εf).Ok :=
    (ok_of_allT Unit _ _ _).1 (ldLinC_allT C.P on0 εf S hF hpy hS)
  have h1 : (p.prog.onto (C.chain fq x.A)).OkFrom (C.P.chain on0 S εf) :=
    front_okFrom E Unit C.S C.E₀ C.Wpa x _ p _ _ (C.P.chain on0 S εf) (C.chain fq x.A) Rd Rr hc
      ((Chain.okFrom_one (C.P.chain on0 S εf) _).2 (Or.inl hp.good)) hH hZ
  have s1 : (p.prog.onto (C.chain fq x.A)).SidesC (C.P.q5 S qa) Q.q :=
    front_sides E Unit C.S C.E₀ C.Wpa x _ p _ (C.chain fq x.A) (C.P.q5 S qa) Q.q
      ((Chain.sidesC_one _ _ _).2
        (sideC_of_side _ _ _ _ _ _ _ _ _ _ _ ⟨hp.noHid, hp.noTie, hp.bears⟩))
      hH hSd
  exact ldChain_front Q (C.P.chain on0 S εf) (p.prog.onto (C.chain fq x.A)) (C.P.q5 S qa) hQ h1 s1

theorem ldLinSp_tail : Spec.ldLinSp_tail E ι κ J Y := by
  intro C on0 εf S qa d x Q fq p Rd Rr hF hpy hS hSays hQ hq hH hSd hZ
  obtain ⟨h1, h2⟩ :=
    ldLinSp_chain E ι κ J Y C on0 εf S qa x Q fq p Rd Rr hF hpy hS hSays hQ hq hH hSd hZ
  exact ldLinC_tail C.P on0 εf S qa d (C.cZf x Q fq p) hF hpy hS h1 h2

end
end Cb
