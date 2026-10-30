-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscZkProofs.lean: the proofs of the statements of Cb/Ld/LdPscZk.lean, but for the two on the
instance with the dummy variable, which are in Cb/Ld/LdPscZkOur.lean (here: `psc_our_own_of`, which
gives `Spec.psc_our_own` from "the dummy variable and the inner masks do not change the sum",
`Spec.psc_our_sum`, Cb/Ld/LdPsc.lean).
-/
import Cb.Ld.LdPscZk
import Cb.Ld.LdPscMaskProofs
import Cb.Ld.LdPscProofs
import Ior.SeqProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section Fmt
variable {E : Type} [Field E]

theorem pPl_pQ :
    ∀ (l : List (PFmt E)) (d : PDats l) (pl : Plains (pRounds l)), pPl l d (pQ l d pl) = pl
  | [], _, _ => rfl
  | _ :: l, d, pl => Prod.ext rfl (pPl_pQ l d.2 pl.2)

theorem noOrc_rounds :
    ∀ (l : List (PFmt E)) (t : Shape), IsEmpty (OPos t) → IsEmpty (OPos (pRounds l ++ t))
  | [], _, h => h
  | _ :: l, t, h => ⟨fun p => match p with
      | .inl e => e.elim
      | .inr p => (noOrc_rounds l t h).false p⟩

end Fmt

namespace PscPar

section NoFin
variable {E : Type} [Field E] {Y : PscPar E}

/-- The summand reads the entries through the maps (`Y.G`, `Y.Gb`). -/
theorem sum_congr {st : Y.St} {m m' : Y.J → E}
    (h : Y.G st m = Y.G st m') (hb : Y.Gb st m = Y.Gb st m') : Y.sum st m = Y.sum st m' := by
  funext X
  unfold PscPar.sum
  rw [h, hb]

theorem inc_congr {st : Y.St} {m m' : Y.J → E} (h : ∀ j, Y.slS st j ≠ 0 → m j = m' j) :
    Y.inc st m = Y.inc st m' := by
  unfold PscPar.inc
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : Y.slS st j = 0
  · rw [hj, zero_mul, zero_mul]
  · rw [h j hj]

theorem whole_congr {st : Y.St} {m m' : Y.J → E} (hW : Y.W st m = Y.W st m')
    (hi : Y.inc st m = Y.inc st m') (hs : Y.sum st m = Y.sum st m') :
    Y.whole st m = Y.whole st m' := by
  funext ε X
  unfold PscPar.whole
  rw [hW, hi, hs]

theorem honQ_congr {st : Y.St} {m m' : Y.J → E} (hW : Y.W st m = Y.W st m')
    (hi : Y.inc st m = Y.inc st m') (hs : Y.sum st m = Y.sum st m') :
    Y.honQ st m = Y.honQ st m' := by
  funext ε γ i
  unfold PscPar.honQ
  rw [hW, hi, hs]

/-- Under `hV`, `hD`, `h`: the round polynomials of "summand and incoming masks" (the scalar `s`)
pass the checks for the target `τ`. -/
theorem rest_cons (hV : Y.VarsOK) (hD : Y.DegOK) (st : Y.St) (m : Y.J → E) (s τ : E)
    (γ : HPt (Y.vars st)) (h : hSumAll (Y.vars st) (Y.sum st m) + s = τ) :
    HCons (Y.vars st) τ (hTr (Y.vars st) s 0 γ + hTrOf (Y.vars st) (Y.sum st m) γ) γ := by
  have h1 : HCons (Y.vars st) s (hTr (Y.vars st) s (0 : HIdx (Y.vars st) → E) γ) γ := by
    have h := hide_cons E E (Y.vars st) (hV st) s 0 γ
    rwa [hMu_zero, add_zero] at h
  have h2 :=
    rounds_cons E E (Y.vars st) (Y.sum st m) _ γ (psc_trOf (Y.vars st) (Y.sum st m) γ (hD st m))
  have h3 := HCons.add (Y.vars st) h1 h2
  rwa [add_comm s, h] at h3

end NoFin

variable {E : Type} [Field E] [Fintype E] {Y : PscPar E}

theorem noOrc_core (Ex : ExtSpec) : IsEmpty (OPos (Y.core Ex).shape) :=
  ⟨fun p => match p with
    | .inl e => e.elim
    | .inr p => by
        have h := noOrc_rounds Y.fmt [] ⟨fun e : Empty => e.elim⟩
        rw [List.append_nil] at h
        exact h.false p⟩

theorem noOrc_psc (Ex : ExtSpec) : IsEmpty (OPos (Y.psc Ex).shape) :=
  ⟨fun p => match p with
    | .inl e => e.elim
    | .inr p => (noOrc_rounds Y.fmt [pRoundV E Y.A] ⟨fun q => match q with
        | .inl e => e.elim
        | .inr e => e.elim⟩).false p⟩

section Own
variable {O : Y.Own}

theorem put_at (hO : Y.OwnOK O) (M : O.Mk) (m : Y.J → E) (i : PIdx Y.fmt ⊕ O.Cx) :
    O.put M m (O.at i) = Sum.elim M.1 M.2 i :=
  hO.inj.extend_apply _ _ _

omit [Fintype E] in
theorem put_off (M : O.Mk) (m : Y.J → E) (j : Y.J) (h : ∀ i, j ≠ O.at i) : O.put M m j = m j :=
  Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact h i rfl)

theorem cAt_inj (hO : Y.OwnOK O) : Function.Injective O.cAt := fun a b h =>
  Sum.inr_injective (hO.inj (show O.at (.inr a) = O.at (.inr b) from h))

theorem put_eq_ext (hO : Y.OwnOK O) (M : O.Mk) (m : Y.J → E) (j : Y.J) (h : ∀ i, j ≠ Y.wAt i) :
    O.put M m j = Function.extend O.cAt M.2 m j := by
  by_cases hc : ∃ c, O.cAt c = j
  · obtain ⟨c, rfl⟩ := hc
    rw [(cAt_inj hO).extend_apply]
    exact put_at hO M m (.inr c)
  · rw [Function.extend_apply' _ _ _ hc]
    refine put_off M m j fun i => ?_
    cases i with
    | inl i => exact h i
    | inr c => exact fun e => hc ⟨c, e.symm⟩

theorem W_put (hO : Y.OwnOK O) (st : Y.St) (M : O.Mk) (m : Y.J → E) :
    Y.W st (O.put M m) = fun i => M.1 (pIx Y.fmt (Y.dat st) i) :=
  funext fun i => put_at hO M m (.inl (pIx Y.fmt (Y.dat st) i))

theorem inc_put (hO : Y.OwnOK O) (st : Y.St) (M : O.Mk) (m : Y.J → E) :
    Y.inc st (O.put M m) = Y.inc st m :=
  inc_congr fun j hj => put_off M m j fun i e => hj (e ▸ hO.sS st i)

theorem G_put (hO : Y.OwnOK O) (st : Y.St) (M : O.Mk) (m : Y.J → E) :
    Y.G st (O.put M m) = Y.G st (Function.extend O.cAt M.2 m) :=
  hO.wG st _ _ (put_eq_ext hO M m)
theorem Gb_put (hO : Y.OwnOK O) (st : Y.St) (M : O.Mk) (m : Y.J → E) :
    Y.Gb st (O.put M m) = Y.Gb st (Function.extend O.cAt M.2 m) :=
  hO.wGb st _ _ (put_eq_ext hO M m)

theorem sumAll_put (hO : Y.OwnOK O) (st : Y.St) (M : O.Mk) (m : Y.J → E) :
    hSumAll (Y.vars st) (Y.sum st (O.put M m)) = hSumAll (Y.vars st) (Y.sum st m) :=
  hO.sum st _ _ (put_off M m)

theorem sumAll_ext (hO : Y.OwnOK O) (st : Y.St) (c : O.Cx → E) (m : Y.J → E) :
    hSumAll (Y.vars st) (Y.sum st (Function.extend O.cAt c m)) = hSumAll (Y.vars st) (Y.sum st m) :=
  hO.sum st _ _ fun j h => Function.extend_apply' _ _ _ (by rintro ⟨a, rfl⟩; exact h (.inr a) rfl)

omit [Fintype E] in
theorem cut_rd (m : Y.J → E) (j : Y.J) (h : O.Rd j) : O.cut m j = m j := if_pos h

theorem W_cut (hO : Y.OwnOK O) (st : Y.St) (m : Y.J → E) : Y.W st (O.cut m) = Y.W st m :=
  funext fun i => cut_rd m _ (hO.own (.inl (pIx Y.fmt (Y.dat st) i)))
theorem inc_cut (hO : Y.OwnOK O) (st : Y.St) (m : Y.J → E) : Y.inc st (O.cut m) = Y.inc st m :=
  inc_congr fun j hj => cut_rd m j (by by_contra h; exact hj (hO.rdS st j h))
theorem G_cut (hO : Y.OwnOK O) (st : Y.St) (m : Y.J → E) : Y.G st (O.cut m) = Y.G st m :=
  hO.rdG st _ _ fun j h => cut_rd m j h
theorem Gb_cut (hO : Y.OwnOK O) (st : Y.St) (m : Y.J → E) : Y.Gb st (O.cut m) = Y.Gb st m :=
  hO.rdGb st _ _ fun j h => cut_rd m j h

theorem sent_cut (hO : Y.OwnOK O) (st : Y.St) (m : Y.J → E) :
    Y.sent st (O.cut m) = Y.sent st m := by
  funext ε γ
  unfold PscPar.sent
  rw [W_cut hO, G_cut hO,
    honQ_congr (W_cut hO st m) (inc_cut hO st m) (sum_congr (G_cut hO st m) (Gb_cut hO st m))]

end Own

/-- Nothing is withheld (`IOR.Honest.withheld`, Ior/Honest.lean). -/
theorem free_hon (Ex : ExtSpec) {Wt : Type} (msg : Wt → Y.J → E) (w : Wt) (x : E × Y.St) :
    (Y.hon Ex msg).withheld w x = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun ρ =>
    (IOR.Honest.not_mem_withheld_seq (Y.honC Ex msg) (Y.honE Ex msg) w x ρ).2
      ⟨fun h => h.elim (fun h => h) fun h => h, fun _ h => h.elim (fun h => h) fun h => h⟩

/-- The plain parts of `Y.core` (round 0 and the rounds of the variables), in closed form. -/
theorem plains_honC (Ex : ExtSpec) {Wt : Type} (msg : Wt → Y.J → E) (w : Wt)
    (x : E × Y.St) (ρ : Rho (Y.core Ex).shape) :
    (((Y.honC Ex msg).strat w x ()).run ρ).1.plains =
      Y.packC Ex x.2
        (hMu (Y.vars x.2) (Y.W x.2 (msg w)), Y.honQ x.2 (msg w) ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2))) := by
  obtain ⟨r1, r2, -, -⟩ := psc_run E Y Ex Wt msg w x ρ
  refine Prod.ext r1 ?_
  have h := pPl_pQ Y.fmt (Y.dat x.2) (((Y.honC Ex msg).strat w x ()).run ρ).1.plains.2
  rw [← h]
  exact congrArg (pPl Y.fmt (Y.dat x.2)) r2

/-- A run of the whole block, in closed form. -/
theorem run_hon (Ex : ExtSpec) {Wt : Type} (msg : Wt → Y.J → E) (w : Wt) (x : E × Y.St)
    (c : (Y.hon Ex msg).Coin) (ρ : Rho (Y.psc Ex).shape) :
    (((Y.hon Ex msg).strat w x c).run ρ).1.plains =
      Y.pack Ex x.2 (Y.sent x.2 (msg w) (Y.zEps Ex ρ) (Y.zPt Ex ρ)) ∧
    (((Y.hon Ex msg).strat w x c).run ρ).2 =
      (Y.honOut (Y.honMid x.2 (msg w) (Y.zEps Ex ρ) (Y.zPt Ex ρ)) (msg w), w) := by
  have r4 :=
    (psc_run E Y Ex Wt msg w x (Rho.fst (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) ρ)).2.2.2
  have hp := plains_honC Ex msg w x (Rho.fst (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) ρ)
  have hs : ((Y.hon Ex msg).strat w x c).run ρ = _ :=
    IOR.Honest.run_seq (Y.honC Ex msg) (Y.honE Ex msg) w x c ρ
  have hc : c.1 = () := rfl
  rw [hs, hc, r4]
  refine ⟨(Tr.plains_app _ _).trans ?_, rfl⟩
  rw [hp]
  rfl

end PscPar

section Main
variable (E : Type) [Field E] [Fintype E]

open Classical in
theorem psc_mm : Spec.psc_mm E := by
  intro Y Ex Wt msg O hV hD hO
  refine
    { noOrc := PscPar.noOrc_psc Ex
      free := PscPar.free_hon Ex msg
      run := fun w x c ρ => ?_
      stable := fun x m M h => ?_
      law := fun m x ρ h => ?_ }
  · show _ = Y.pack Ex x.2 (Y.sent x.2 (O.cut (msg w)) (Y.zEps Ex ρ) (Y.zPt Ex ρ))
    rw [PscPar.sent_cut hO]
    exact (PscPar.run_hon Ex msg w x c ρ).1
  · show hSumAll (Y.vars x.2) (Y.sum x.2 (O.put M m)) + Y.inc x.2 (O.put M m) = x.1
    rw [PscPar.sumAll_put hO, PscPar.inc_put hO]
    exact h
  · obtain ⟨τ, st⟩ := x
    have h' : hSumAll (Y.vars st) (Y.sum st m) + Y.inc st m = τ := h
    let γ : HPt (Y.vars st) := Y.hp st (Y.zPt Ex ρ)
    let u : (O.Cx → E) → RIdx (Y.vars st) → E := fun c =>
      hTr (Y.vars st) (Y.inc st m) 0 γ + hTrOf (Y.vars st) (Y.sum st (Function.extend O.cAt c m)) γ
    let v : (O.Cx → E) → Y.A → E := fun c a => Y.G st (Function.extend O.cAt c m) a γ
    let e : O.Mk ≃ PMask (Y.vars st) O.Cx :=
      Equiv.prodCongr (Equiv.arrowCongr (pIx Y.fmt (Y.dat st)).symm (Equiv.refl E)) (Equiv.refl _)
    have hu : ∀ c, HCons (Y.vars st) τ (u c) γ := fun c =>
      PscPar.rest_cons hV hD st _ _ τ γ (by rw [PscPar.sumAll_ext hO]; exact h')
    have hv : (unif (O.Cx → E)).map v = unif (Y.A → E) :=
      hO.val st m (Rho.fst (s := Y.shapeC) (t := [pRoundV E Y.A]) ρ).2
    have key := psc_mask_law E (Y.vars st) (hV st) O.Cx Y.A γ (Y.zEps Ex ρ) τ u v hu hv
    have hs : (fun M : O.Mk => Y.sent st (O.put M m) (Y.zEps Ex ρ) (Y.zPt Ex ρ)) =
        pscMsg (Y.vars st) γ (Y.zEps Ex ρ) u v ∘ e := by
      funext M
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show hMu (Y.vars st) (Y.W st (O.put M m)) = _
        rw [PscPar.W_put hO]
        rfl
      · funext i
        show Y.honQ st (O.put M m) (Y.zEps Ex ρ) γ i = _
        unfold PscPar.honQ
        rw [PscPar.W_put hO, PscPar.inc_put hO,
          PscPar.sum_congr (PscPar.G_put hO st M m) (PscPar.Gb_put hO st M m)]
        rfl
      · show (fun a => Y.G st (O.put M m) a γ) = _
        rw [PscPar.G_put hO]
        rfl
    show (unif O.Mk).map
        (Y.pack Ex st ∘ fun M : O.Mk => Y.sent st (O.put M m) (Y.zEps Ex ρ) (Y.zPt Ex ρ)) =
      (pscSim (Y.vars st) Y.A γ (Y.zEps Ex ρ) τ).map (Y.pack Ex st)
    rw [← PMF.map_comp, hs, ← PMF.map_comp, map_unif_equiv e, key]

open Classical in
theorem psc_core_mm : Spec.psc_core_mm E := by
  intro Y Ex Wt msg Rd hV hD hO
  have off : ∀ (M : PIdx Y.fmt → E) (m : Y.J → E) j,
      (∀ i, j ≠ Y.wAt i) → Function.extend Y.wAt M m j = m j :=
    fun M m j h => Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact h i rfl)
  have hW : ∀ st (M : PIdx Y.fmt → E) (m : Y.J → E),
      Y.W st (Function.extend Y.wAt M m) = fun i => M (pIx Y.fmt (Y.dat st) i) :=
    fun st M m => funext fun i => hO.inj.extend_apply _ _ _
  have hI : ∀ st (M : PIdx Y.fmt → E) (m : Y.J → E),
      Y.inc st (Function.extend Y.wAt M m) = Y.inc st m :=
    fun st M m => PscPar.inc_congr fun j hj => off M m j fun i e => hj (e ▸ hO.wS st i)
  have hS : ∀ st (M : PIdx Y.fmt → E) (m : Y.J → E),
      Y.sum st (Function.extend Y.wAt M m) = Y.sum st m :=
    fun st M m => PscPar.sum_congr (hO.wG st _ _ (off M m)) (hO.wGb st _ _ (off M m))
  refine
    { noOrc := PscPar.noOrc_core Ex
      free := fun w x => Set.eq_empty_iff_forall_notMem.2 fun ρ h => h.elim (fun h => h) fun h => h
      run := fun w x c ρ => ?_
      stable := fun x m M h => ?_
      law := fun m x ρ h => ?_ }
  · have cr : ∀ j, Rd j → (if Rd j then msg w j else 0) = msg w j := fun j h => if_pos h
    have c1 : Y.W x.2 (fun j => if Rd j then msg w j else 0) = Y.W x.2 (msg w) :=
      funext fun i => cr _ (hO.own _)
    have c2 : Y.inc x.2 (fun j => if Rd j then msg w j else 0) = Y.inc x.2 (msg w) :=
      PscPar.inc_congr fun j hj => cr j (by by_contra h; exact hj (hO.rdS x.2 j h))
    have c3 : Y.sum x.2 (fun j => if Rd j then msg w j else 0) = Y.sum x.2 (msg w) :=
      PscPar.sum_congr (hO.rdG x.2 _ _ cr) (hO.rdGb x.2 _ _ cr)
    show _ = Y.packC Ex x.2
        (hMu (Y.vars x.2) (Y.W x.2 fun j => if Rd j then msg w j else 0),
          Y.honQ x.2 (fun j => if Rd j then msg w j else 0) ρ.1 (Y.hp x.2 (pG Y.fmt ρ.2)))
    rw [c1, PscPar.honQ_congr c1 c2 c3]
    exact PscPar.plains_honC Ex msg w x ρ
  · show hSumAll (Y.vars x.2) (Y.sum x.2 (Function.extend Y.wAt M m)) +
        Y.inc x.2 (Function.extend Y.wAt M m) = x.1
    rw [hS, hI]
    exact h
  · obtain ⟨τ, st⟩ := x
    have h' : hSumAll (Y.vars st) (Y.sum st m) + Y.inc st m = τ := h
    let γ : HPt (Y.vars st) := Y.hp st (pG Y.fmt ρ.2)
    let e : (PIdx Y.fmt → E) ≃ (HIdx (Y.vars st) → E) :=
      Equiv.arrowCongr (pIx Y.fmt (Y.dat st)).symm (Equiv.refl E)
    have key := psc_tr_law E (Y.vars st) (hV st) γ ρ.1 τ _ (PscPar.rest_cons hV hD st m _ τ γ h')
    have hs : (fun M : PIdx Y.fmt → E =>
          (hMu (Y.vars st) (Y.W st (Function.extend Y.wAt M m)),
            Y.honQ st (Function.extend Y.wAt M m) ρ.1 γ)) =
        (fun W =>
            (hMu (Y.vars st) W,
              hTr (Y.vars st) 0 W γ +
                ρ.1 • (hTr (Y.vars st) (Y.inc st m) 0 γ + hTrOf (Y.vars st) (Y.sum st m) γ))) ∘
          e := by
      funext M
      refine Prod.ext ?_ ?_
      · show hMu (Y.vars st) (Y.W st (Function.extend Y.wAt M m)) = _
        rw [hW]
        rfl
      · funext i
        show Y.honQ st (Function.extend Y.wAt M m) ρ.1 γ i = _
        unfold PscPar.honQ
        rw [hW, hI, hS]
        rfl
    show (unif (PIdx Y.fmt → E)).map
        (Y.packC Ex st ∘
          fun M : PIdx Y.fmt → E =>
            (hMu (Y.vars st) (Y.W st (Function.extend Y.wAt M m)),
              Y.honQ st (Function.extend Y.wAt M m) ρ.1 γ)) = _
    rw [← PMF.map_comp, hs, ← PMF.map_comp, map_unif_equiv e, key]
    rfl

theorem psc_hands : Spec.psc_hands E := by
  intro Y Ex Wt msg O hO w x c ρ
  have h1 : Y.honMid x.2 (O.cut (msg w)) = Y.honMid x.2 (msg w) := by
    funext ε γ
    unfold PscPar.honMid
    rw [PscPar.whole_congr (PscPar.W_cut hO x.2 (msg w)) (PscPar.inc_cut hO x.2 (msg w))
        (PscPar.sum_congr (PscPar.G_cut hO x.2 (msg w)) (PscPar.Gb_cut hO x.2 (msg w)))]
  have h2 : ∀ z, Y.honOut z (O.cut (msg w)) = Y.honOut z (msg w) := fun z => by
    unfold PscPar.honOut
    rw [PscPar.G_cut hO]
  rw [h1, h2]
  exact (PscPar.run_hon Ex msg w x c ρ).2

theorem psc_mm_keep : Spec.psc_mm_keep E := fun Y Ex F Cr Wt msg O hV hD hO =>
  mm_keep _ _ _ _ _ _ _ _ _ Cr F (psc_mm E Y Ex Wt msg O hV hD hO)

omit [Field E] [Fintype E] in
theorem psc_own_card : Spec.psc_own_card E := by
  intro l
  induction l with
  | nil => show Fintype.card Unit = _; simp
  | cons f l ih =>
      show Fintype.card (Fin f.n ⊕ PIdx l) = _
      rw [Fintype.card_sum, ih, Fintype.card_fin, List.map_cons, List.sum_cons]
      omega

omit [Fintype E] in
theorem psc_own_card_all : Spec.psc_own_card_all E := fun Y O => by
  rw [Fintype.card_sum, psc_own_card]

theorem psc_no_coins : Spec.psc_no_coins E := fun _ _ _ _ =>
  inferInstanceAs (Subsingleton (Unit × Unit))

/-- The challenge of the dummy variable is not 0. -/
theorem hLast_ne :
    ∀ (l : List (PFmt E)) (d : PDats l) (D : ℕ) (ρ : Rho (pRounds (l ++ [pDummy E D]))),
      hLast l d (pDummy E D) (pDummyD E D)
          (pH (l ++ [pDummy E D]) (PDats.snoc l d (pDummy E D) (pDummyD E D))
            (pG (l ++ [pDummy E D]) ρ)) ≠ 0
  | [], _, _, ρ => ρ.1.2
  | _ :: l, d, D, ρ => hLast_ne l d.2 D ρ.2

open Classical in
theorem psc_our_own_of (hS : Spec.psc_our_sum E) : Spec.psc_our_own E := by
  intro T Rd h
  have offW : ∀ (m m' : T.J → E), (∀ j, (∀ i, j ≠ T.wAt i) → m j = m' j) →
      ∀ j, (∀ i, j ≠ Sum.elim T.wAt T.cAt i) → m j = m' j :=
    fun m m' hm j hj => hm j fun i => hj (.inl i)
  have cinj : Function.Injective T.cAt := fun a b e =>
    Sum.inr_injective
      (h.inj (show Sum.elim T.wAt T.cAt (.inr a) = Sum.elim T.wAt T.cAt (.inr b) from e))
  have key : ∀ st m,
      hSumAll (T.par.vars st) (T.par.sum st m) = hSumAll (T.vars st) (T.sum st m) := by
    intro st m
    have h0 := (hS T (hSumAll (T.par.vars st) (T.par.sum st m) + T.par.inc st m, st) m).1 rfl
    exact (add_right_cancel h0).symm
  refine
    { inj := h.inj
      own := h.own
      rdG := fun st m m' hm => ?_
      rdGb := fun st m m' hm => ?_
      rdS := h.rdS
      wG := fun st m m' hm => ?_
      wGb := fun st m m' hm => ?_
      sS := h.oS
      sum := fun st m m' hm => ?_
      val := fun st m ρ => ?_ }
  · funext a X
    show T.F st m a _ + m (T.cAt a) * _ = T.F st m' a _ + m' (T.cAt a) * _
    rw [h.rdF st m m' hm, hm (T.cAt a) (h.own (.inr a))]
  · funext b X
    show T.Fb st m b _ = T.Fb st m' b _
    rw [h.rdFb st m m' hm]
  · funext a X
    show T.F st m a _ + m (T.cAt a) * _ = T.F st m' a _ + m' (T.cAt a) * _
    rw [h.oF st m m' (offW m m' hm),
      hm (T.cAt a) fun i e =>
        Sum.inr_ne_inl
          (h.inj (show Sum.elim T.wAt T.cAt (.inr a) = Sum.elim T.wAt T.cAt (.inl i) from e))]
  · funext b X
    show T.Fb st m b _ = T.Fb st m' b _
    rw [h.oFb st m m' (offW m m' hm)]
  · rw [key, key]
    have e : T.sum st m = T.sum st m' := by
      funext X
      unfold PscOur.sum
      rw [h.oF st m m' hm, h.oFb st m m' hm]
    rw [e]
  · have hβ := hLast_ne E T.fmt (T.dat st) T.DY ρ
    have e : (fun (c : T.A → E) a =>
          T.par.G st (Function.extend T.cAt c m) a (T.par.hp st (pG T.par.fmt ρ))) =
        fun c a =>
          T.F st m a (T.ini st (T.par.hp st (pG T.par.fmt ρ))) +
              T.lst st (T.par.hp st (pG T.par.fmt ρ)) * c a := by
      funext c a
      show T.F st (Function.extend T.cAt c m) a _ + Function.extend T.cAt c m (T.cAt a) * _ = _
      rw [h.oF st _ m (fun j hj =>
            Function.extend_apply' _ _ _ (by rintro ⟨a', rfl⟩; exact hj (.inr a') rfl)),
        cinj.extend_apply, mul_comm]
    show (unif (T.A → E)).map (fun (c : T.A → E) a =>
        T.par.G st (Function.extend T.cAt c m) a (T.par.hp st (pG T.par.fmt ρ))) = unif (T.A → E)
    rw [e]
    exact psc_val_own E T.A _ _ hβ

end Main
end Cb
