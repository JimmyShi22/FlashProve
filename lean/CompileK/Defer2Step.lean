-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Step.lean: the bound for a step of the challenger (`step_bound2`), for the proof of
the lemma on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean).

Main names:
  `step_bound2`: let p have `Valid2`, and let the program c have `Step.Alw` at p, with `DSt.Ok2` on
    the way and Post at its end. If a number H bounds the expectation of a pay-off Kf plus the
    potential `potP` at every value and state with `Valid2` and Post (hK), then H bounds the
    expectation of `cost c` plus `potP` at p. The exact form is its statement.

`cost` (Rom/DeferProof_tail.lean) is the expected number of hits during a step in mode I, plus the
expectation of Kf at its end. The analogue of `step_bound` in that file: the same induction on the
program, with the counts by class, the invariant `Valid2`, the hit bounds `hitQ2`, `hitM2`
(CompileK/Defer2Valid.lean), and with the hypothesis along the program (`Step.Alw`) in the place of
the one on final states. Nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs, in the random-oracle model, on Lean's three axioms.
-/
import CompileK.Defer2Valid

set_option autoImplicit false

open scoped ENNReal
open Prob
namespace Rom
namespace DeferTail2
open DeferTail

variable {S : OSpec} {sp : Split S} {K : Type} [DecidableEq K] {cl : PtCls S K} {J : K → Bool}
  {ℓ : K → ℕ} {ks : Finset K}

theorem countK_bump_right {qs : List (Pt S)} (k : Pt S) {a : K → ℕ} {b : S.ι → ℕ}
    (h : ∀ κ, qCountK cl qs κ ≤ a κ + b (cl.orc κ)) :
    ∀ κ, qCountK cl (k :: qs) κ ≤ a κ + Function.update b k.1 (b k.1 + 1) (cl.orc κ) := by
  intro κ
  rw [qCountK_cons]
  by_cases ho : κ = cl.of k
  · subst ho
    rw [Function.update_self, cl.orc_of, Function.update_self]
    have := h (cl.of k)
    rw [cl.orc_of] at this
    omega
  · rw [Function.update_of_ne ho]
    refine (h κ).trans (Nat.add_le_add_left ?_ _)
    by_cases h2 : cl.orc κ = k.1
    · rw [h2, Function.update_self]; exact Nat.le_succ _
    · rw [Function.update_of_ne h2]

theorem countK_bump_left {qs : List (Pt S)} (k : Pt S) {a : K → ℕ} {b : S.ι → ℕ}
    (h : ∀ κ, qCountK cl qs κ ≤ a κ + b (cl.orc κ)) :
    ∀ κ,
      qCountK cl (k :: qs) κ ≤ Function.update a (cl.of k) (a (cl.of k) + 1) κ + b (cl.orc κ) := by
  intro κ
  rw [qCountK_cons]
  by_cases ho : κ = cl.of k
  · subst ho
    rw [Function.update_self, Function.update_self]
    have := h (cl.of k)
    omega
  · rw [Function.update_of_ne ho, Function.update_of_ne ho]
    exact h κ

theorem step_bound2 {α : Type} (u : K → ℕ) (H : ℝ≥0∞)
    (Kf : α × DSt S → ℝ≥0∞) (Post : α × DSt S → Prop)
    (hK : ∀ (a : α) (p : PSt S sp), Valid2 cl J ℓ ks u p →
      (∀ w, Agree p.slots w → Post (a, p.inst w)) →
      expect (law p.slots) (fun w => Kf (a, p.inst w)) + potP cl ℓ ks p ≤ H)
    (c : Step S sp α) :
    ∀ p : PSt S sp, Valid2 cl J ℓ ks u p →
      (∀ w, Agree p.slots w → c.Alw cl J (DSt.Ok2 cl J ℓ ks) (p.inst w) Post) →
      expect (law p.slots) (fun w => cost c (p.inst w) Kf) + potP cl ℓ ks p ≤ H := by
  induction c with
  | pure a =>
    intro p hv hs
    simp only [cost]
    exact hK a p hv fun w hw => hs w hw
  | sample n k ih =>
    intro p hv hs
    simp only [cost]
    rw [expect_comm]
    exact expect_add_const_le _ _ _ _ fun r _ => ih r p hv fun w hw => hs w hw r
  | plain o q k ih =>
    intro p hv hs
    simp only [cost]
    have hcomm : expect (law p.slots) (fun w => expect (lazyAnswer (p.inst w).table o q) fun y =>
          cost (k y.1) (postPlain (p.inst w) o y.2) Kf)
        = expect (lazyAnswer p.table o q) fun y => expect (law p.slots) fun w =>
          cost (k y.1)
              ((p.log ⟨o, q⟩ y.2 (Function.update p.nPlain o (p.nPlain o + 1))).inst w) Kf :=
      expect_comm (law p.slots) (lazyAnswer p.table o q) fun w y =>
        cost (k y.1) (postPlain (p.inst w) o y.2) Kf
    rw [expect_add, hcomm, add_comm (expect (law p.slots) _) _, add_assoc]
    refine expect_add_const_le _ _ _ _ fun y hy => ?_
    refine le_trans (add_le_add le_rfl
      (le_trans (add_le_add (hitQ2 hv ⟨o, q⟩) le_rfl)
        (potP_log_le hv ⟨o, q⟩ y.2 (Function.update p.nPlain o (p.nPlain o + 1)))))
      (ih y.1 (p.log ⟨o, q⟩ y.2 (Function.update p.nPlain o (p.nPlain o + 1))) ?_ ?_)
    · exact valid2_log hv ⟨o, q⟩ y.2 _ (fun k' hk' => lazy_support hy k' hk')
        (fun u₀ h0 => ⟨u₀, count_bump_right ⟨o, q⟩ h0⟩) (countK_bump_right ⟨o, q⟩ hv.count)
    · exact fun w hw => hs w hw y hy
  | fresh L k ih =>
    intro p hv hs
    simp only [cost]
    have key : expect (law p.slots) (fun w =>
          expect (PMF.uniformOfFintype (Fin L → Bool)) fun u' =>
            cost (k (p.inst w).vals.length) (postFresh (p.inst w) (List.ofFn u')) Kf) =
        expect (law (p.snoc L).slots) fun w' =>
          cost (k p.slots.length) ((p.snoc L).inst w') Kf := by
      rw [show (p.snoc L).slots = p.slots ++ [Slot.hid L] from rfl, E_snoc]
      refine expect_congr_support _ fun w hw => ?_
      have hw' := (mem_support_law _ _).1 hw
      rw [E_hid]
      refine expect_congr _ fun u' => ?_
      rw [show (p.inst w).vals.length = p.slots.length from hw'.length, inst_fresh hv.wfP hw' L]
    rw [key]
    refine ih _ (p.snoc L) (valid2_snoc hv L) fun w' hw' => ?_
    obtain ⟨w, v, rfl, hw, hv'⟩ := agree_snoc_fwd hw'
    obtain ⟨u', rfl⟩ := ok_hid hv'
    have h := hs w hw u'
    rwa [show (p.inst w).vals.length = p.slots.length from hw.length, inst_fresh hv.wfP hw L] at h
  | marked o t us pt inj k ih =>
    intro p hv hs
    have hwf := hv.wfP
    obtain ⟨w₀, hw₀⟩ := exists_agree p.slots
    obtain ⟨hfit, hmark, _⟩ := hs w₀ hw₀
    have hbad : ∀ w, Agree p.slots w → markedBad (p.inst w) o t us = false := by
      intro w hw
      have h := ((hs w hw).2.2 (Classical.arbitrary _)).1.1
      have h' : (false || markedBad (p.inst w) o t us) = false := h
      simpa using h'
    obtain ⟨ht, hus, hno, hsh, hind⟩ := markedBad_false (hbad w₀ hw₀)
    have ht₀ : t < w₀.length := ht
    have ht' : t < p.slots.length := hw₀.length ▸ ht₀
    have hus₀ : ∀ x ∈ us, x < w₀.length := fun x hx => hus x hx
    have hus' : ∀ x ∈ us, x < p.slots.length := fun x hx => hw₀.length ▸ hus₀ x hx
    obtain ⟨L, hL⟩ := hwf.hid ht' hsh
    have hind' : ∀ x ∈ p.evs, x.o = o → t ≠ x.charged ∧ t ∉ x.others := fun x hx hxo =>
      ⟨(hind (x.inst w₀) (List.mem_map_of_mem hx) hxo).1.symm,
        (hind (x.inst w₀) (List.mem_map_of_mem hx) hxo).2⟩
    -- the class
    set κ : K := cl.of ⟨o, pt [] []⟩ with hκdef
    have hκ : ∀ v vs, cl.of ⟨o, pt v vs⟩ = κ := fun v vs => hfit.1 _ _ _ _
    -- what Ok2 says of the new evaluation
    have hnew := ((hs w₀ hw₀).2.2 (Classical.arbitrary _)).1.2
      ⟨o, pt ((p.inst w₀).val t) (us.map (p.inst w₀).val), Classical.arbitrary _,
        t, us, w₀.length, false⟩
      (List.mem_append_right _ (List.mem_singleton.2 rfl))
    have hval : ∀ x, x < w₀.length →
        ∀ Lx, p.slots[x]? = some (Slot.hid Lx) →
          ((postMarked sp (p.inst w₀) o t us (pt ((p.inst w₀).val t) (us.map (p.inst w₀).val))
                (Classical.arbitrary _) (p.inst w₀).table).val x).length = Lx := by
      intro x hx Lx hLx
      show (gv (w₀ ++ [_]) x).length = Lx
      rw [gv_append_left hx]
      exact hw₀.ok hLx
    simp only [hκ] at hnew
    obtain ⟨hmem, hone, htwo⟩ := hnew
    have hEv : ∀ vis,
        EvOK cl J ℓ ks p.slots p.shown
          (⟨o, t, us, pt, inj, vis, p.slots.length, false⟩ : SEv S sp) := by
      intro vis
      have hc : clsOf cl (⟨o, t, us, pt, inj, vis, p.slots.length, false⟩ : SEv S sp) = κ := hκ _ _
      refine ⟨fun w => (hκ _ _).trans hc.symm, hc ▸ hmem, fun hJ L' hL' => ?_, fun hJ => ?_⟩
      · rw [hc] at hJ ⊢
        have := hone hJ
        rwa [hval t ht₀ L' hL'] at this
      · rw [hc] at hJ ⊢
        obtain ⟨b, hb, hbs, _⟩ := hmark hJ
        obtain ⟨b', hb', hlen, _⟩ := htwo hJ
        have hbb : b' = b := by
          have : [b'] = [b] := hb'.symm.trans hb
          simpa using this
        subst hbb
        refine ⟨b', hb, hfit.2 hJ, fun _ => hbs, fun L₁ L₂ a1 a2 => ?_⟩
        rwa [hval t ht₀ L₁ a1,
          hval b' (hus₀ b' (by rw [hb]; exact List.mem_singleton.2 rfl)) L₂ a2] at hlen
    -- the hit
    have hhit : expect (law p.slots)
          (fun w => hitM (p.inst w).table (p.inst w).evs ⟨o, pt (gv w t) (us.map (gv w))⟩) ≤
        ((qCountK cl p.qs κ + aCountK cl p.evs κ : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ κ) := by
      cases hJ : J κ with
      | false =>
        refine hitM2 hv t us pt κ (fun w => hκ _ _) [t] (fun tg htg => ?_) fun e he heo x hx => ?_
        · have h1 := hone hJ
          rw [hval t ht₀ L hL] at h1
          exact (point_prob t us pt inj hno hL tg (htg t (List.mem_singleton.2 rfl))).trans
            (inv_pow_le h1)
        · obtain rfl := List.mem_singleton.1 hx
          exact hind' e he heo
      | true =>
        obtain ⟨b, hb, hbs, hbi⟩ := hmark hJ
        obtain ⟨b', hb', hlen, _⟩ := htwo hJ
        have hbb : b' = b := by
          have : [b'] = [b] := hb'.symm.trans hb
          simpa using this
        subst hbb
        have hbm : b' ∈ us := by rw [hb]; exact List.mem_singleton.2 rfl
        obtain ⟨L', hL'⟩ := hwf.hid (hus' b' hbm) hbs
        rw [hval t ht₀ L hL, hval b' (hus₀ b' hbm) L' hL'] at hlen
        have hne : t ≠ b' := fun h => hno (h ▸ hbm)
        refine hitM2 hv t us pt κ (fun w => hκ _ _) [t, b']
          (fun tg htg => ?_) fun e he heo x hx => ?_
        · have hp :=
            point_prob2 t b' pt (hfit.2 hJ) hne hL hL' tg (htg t (by simp)) (htg b' (by simp))
          rw [hb]
          exact hp.trans (inv_pow_le hlen)
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hind' e he heo
          · obtain rfl := List.mem_singleton.1 hx
            exact hbi (e.inst w₀) (List.mem_map_of_mem he) heo
    simp only [cost]
    rw [expect_add]
    obtain ⟨μ, hμ⟩ := E_split sp o
    have key : expect (law p.slots) (fun w => expect (PMF.uniformOfFintype (S.Rng o)) fun r =>
          cost (k (sp.split o r).1 (p.inst w).vals.length)
            (postMarked sp (p.inst w) o t us
              (pt ((p.inst w).val t) (us.map (p.inst w).val)) r (p.inst w).table) Kf)
        = expect μ fun vis => expect (law (p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).slots) fun w' =>
          cost (k vis p.slots.length)
              ((p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).inst w') Kf := by
      calc _ = expect (law p.slots) fun w => expect (PMF.uniformOfFintype (S.Rng o)) fun r =>
              (fun z : sp.Vis o × (Fin (sp.tl o) → Bool) =>
                    cost (k z.1 p.slots.length)
                      ((p.mark ⟨o, t, us, pt, inj, z.1, p.slots.length, false⟩).inst
                        (w ++ [List.ofFn z.2])) Kf)
                  (sp.split o r) := by
            refine expect_congr_support _ fun w hw => expect_congr _ fun r => ?_
            have hw' := (mem_support_law _ _).1 hw
            rw [show (p.inst w).vals.length = p.slots.length from hw'.length,
              inst_mark hwf hw' o t us pt inj r (hbad w hw')]
        _ = expect (law p.slots) fun w => expect μ fun vis =>
              expect (PMF.uniformOfFintype (Fin (sp.tl o) → Bool)) fun u' =>
                  cost (k vis p.slots.length)
                      ((p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).inst
                        (w ++ [List.ofFn u'])) Kf :=
            expect_congr _ fun w =>
              hμ fun z =>
                cost (k z.1 p.slots.length)
                  ((p.mark ⟨o, t, us, pt, inj, z.1, p.slots.length, false⟩).inst
                    (w ++ [List.ofFn z.2])) Kf
        _ = expect μ fun vis => expect (law p.slots) fun w =>
              expect (PMF.uniformOfFintype (Fin (sp.tl o) → Bool)) fun u' =>
                  cost (k vis p.slots.length)
                      ((p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).inst
                        (w ++ [List.ofFn u'])) Kf :=
            expect_comm _ _ _
        _ = _ := by
            refine expect_congr _ fun vis => ?_
            rw [show (p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).slots
              = p.slots ++ [Slot.hid (sp.tl o)] from rfl, E_snoc]
            exact expect_congr _ fun w => (E_hid (sp.tl o) fun v => cost (k vis p.slots.length)
              ((p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩).inst (w ++ [v])) Kf).symm
    rw [key, add_comm (expect (law p.slots) _) _, add_assoc]
    refine expect_add_const_le _ _ _ _ fun vis _ => ?_
    have hpot : ((qCountK cl p.qs κ + aCountK cl p.evs κ : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ κ) +
          potP cl ℓ ks p ≤
        potP cl ℓ ks (p.mark ⟨o, t, us, pt, inj, vis, p.slots.length, false⟩) := by
      show _ ≤ potK ℓ ks
          (aCountK cl (p.evs ++ [(⟨o, t, us, pt, inj, vis, p.slots.length, false⟩ : SEv S sp)]))
          (qCountK cl p.qs)
      rw [aCountK_snoc,
        show clsOf cl (⟨o, t, us, pt, inj, vis, p.slots.length, false⟩ : SEv S sp) = κ from hκ _ _]
      exact potK_bump_a ℓ ks _ _ hmem
    refine le_trans (add_le_add le_rfl (le_trans (add_le_add hhit le_rfl) hpot)) (ih vis _ _ ?_ ?_)
    · exact valid2_mark hv _ ht' hus' rfl hno hsh (hEv vis)
    · intro w' hw'
      obtain ⟨w, v, rfl, hw, hv'⟩ := agree_snoc_fwd hw'
      obtain ⟨u', rfl⟩ := ok_hid hv'
      have hr : sp.split o ((sp.split o).symm (vis, u')) = (vis, u') := Equiv.apply_symm_apply _ _
      have h := ((hs w hw).2.2 ((sp.split o).symm (vis, u'))).2
      rwa [show (p.inst w).vals.length = p.slots.length from hw.length,
        inst_mark hwf hw o t us pt inj _ (hbad w hw), hr] at h
  | reveal ts k ih =>
    intro p hv hs
    have hwf := hv.wfP
    simp only [cost]
    have hviol : ∀ w, Agree p.slots w → (postReveal true (p.inst w) ts).viol = false := fun w hw =>
      (hs w hw).1.1
    obtain ⟨w₀, hw₀⟩ := exists_agree p.slots
    have hr : RevOK p ts := revOK_of_viol hw₀ (hviol w₀ hw₀)
    rw [E_fixLaw _ ts p.slots]
    refine expect_add_const_le _ _ _ _ fun ss' hss' => ?_
    have hf := fixLaw_support ts p.slots ss' hss'
    have hmap : ∀ w,
        Agree ss' w → ts.map (p.inst w).val = ts.map (gv (ss'.map Slot.val0)) := fun w hw =>
      List.map_congr_left fun t ht => gv_eq_val0 hwf hf hr hw (List.mem_append_right _ ht)
    have key : expect (law ss')
          (fun w => cost (k (ts.map (p.inst w).val)) (postReveal true (p.inst w) ts) Kf) =
        expect (law (p.reveal ts ss').slots) fun w =>
          cost (k (ts.map (gv (ss'.map Slot.val0)))) ((p.reveal ts ss').inst w) Kf := by
      refine expect_congr_support _ fun w hw => ?_
      have hw' := (mem_support_law _ _).1 hw
      rw [inst_reveal hwf hf hr hw' (hviol w (hf.agree hw')), hmap w hw']
    have hpot : potP cl ℓ ks p = potP cl ℓ ks (p.reveal ts ss') := by
      show potK ℓ ks (aCountK cl p.evs) _ =
        potK ℓ ks (aCountK cl (p.evs.map (srel (p.shown ++ ts)))) _
      rw [aCountK_srel]
      rfl
    rw [key, hpot]
    refine ih _ (p.reveal ts ss') (valid2_reveal hv hf hr ?_) fun w hw => ?_
    · intro x hx hJ hrel b hb
      obtain ⟨w₁, hw₁⟩ := exists_agree ss'
      have hG := (hs w₁ (hf.agree hw₁)).1
      rw [inst_reveal hwf hf hr hw₁ (hviol w₁ (hf.agree hw₁))] at hG
      have hx' :=
        hG.2 ((srel (p.shown ++ ts) x).inst w₁) (List.mem_map_of_mem (List.mem_map_of_mem hx))
      have hc : cl.of
            ⟨((srel (p.shown ++ ts) x).inst w₁).o, ((srel (p.shown ++ ts) x).inst w₁).pt⟩ =
          clsOf cl x := by
        show cl.of ((srel (p.shown ++ ts) x).key w₁) = _
        rw [srel_key]
        exact (hv.ev x hx).cst w₁
      rw [hc] at hx'
      obtain ⟨b', hb', _, hns⟩ := hx'.2.2 hJ
      have ho : ((srel (p.shown ++ ts) x).inst w₁).others = x.others :=
        (srel_toks (p.shown ++ ts) x).2.2.1
      rw [ho] at hb'
      rw [hb'] at hb
      obtain rfl := List.mem_singleton.1 hb
      exact hns hrel
    · have h := (hs w (hf.agree hw)).2
      rwa [inst_reveal hwf hf hr hw (hviol w (hf.agree hw)), hmap w hw] at h

end DeferTail2
end Rom
