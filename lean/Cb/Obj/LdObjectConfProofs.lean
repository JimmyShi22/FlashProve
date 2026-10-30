-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectConfProofs.lean: the proofs of the statements of Cb/Obj/LdObjectConf.lean. No axiom
beyond Lean's three; no hypothesis beyond those in the statements' own text.

An honest word is the table of the codewords of the rows' full messages; below the distance it has
one list member (erasure correction's uniqueness), so it decodes and has no collision. Under
`Cf.OK L`, the record binds: `Cb.ldFc_binds`. Under the hypotheses of its statement, the record
hides: the code's own hiding, row by row (Code/Facts.lean), and Hiop/RecRows.lean (the statement:
`Spec.ldCf_hides`, Cb/Obj/LdObjectConf.lean).
-/
import Cb.Obj.LdObjectConf
import Cb.Ld.LdFoldEqCodeProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

theorem downF_algebraMap (F E : Type) [Field F] [Field E] [Algebra F E] (x : F) :
    downF F E (algebraMap F E x) = x :=
  (Code.exists_form_algebraMap F E).choose_spec x

namespace LdCf
variable {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E)

theorem dnM_upM (m : Cf.Msg) : Cf.dnM (Cf.upM m) = m := funext fun n => downF_algebraMap F E (m n)

/-- the table of an honest word: the codewords over E of the rows' full messages -/
theorem tab_enc (m : Cf.Msg) (ρ : Cf.Rnd) :
    Cf.tab (Cf.enc m ρ) = fun r => Cf.X.G.mulVec (Code.liftWord E (Cf.full m ρ r)) := by
  funext r
  show _ = (Cf.C₀.G.map (algebraMap F E)).mulVec (Code.liftWord E (Cf.full m ρ r))
  rw [Code.mulVec_map_liftWord]
  rfl

/-- its message part -/
theorem view_full (m : Cf.Msg) (ρ : Cf.Rnd) :
    Cf.X.view (fun r => Code.liftWord E (Cf.full m ρ r)) = Cf.upM m := by
  funext n
  show algebraMap F E (Cf.C₀.fm (Cf.mrow m n.1) (ρ n.1) (Fin.castLE Cf.hp (Cf.plE n.2))) =
    algebraMap F E (m n)
  have h := Cf.C₀.fm_msg (Cf.mrow m n.1) (ρ n.1) (Cf.plE n.2) (lt_of_lt_of_le (Cf.plE n.2).2 Cf.hp)
  have e : (Fin.castLE Cf.hp (Cf.plE n.2)) =
      ⟨(Cf.plE n.2 : ℕ), lt_of_lt_of_le (Cf.plE n.2).2 Cf.hp⟩ := rfl
  rw [e, h]
  show algebraMap F E (m (n.1, Cf.plE.symm (Cf.plE n.2))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem tab_eq_lift (y : Fin Cf.C₀.n → Cf.Sg) : Cf.tab y = fun a => Code.liftWord E (Cf.tabF y a) :=
  rfl

/-- below the distance a table of codewords has one list member -/
theorem list_of_codewords (hd : HasDist Cf.C₀.G Cf.C₀.d) (he : Cf.eM < Cf.C₀.d)
    {M M' : Cf.Row → Fin Cf.C₀.k → E}
    (h : DecodesTo Cf.X.G Cf.eM (fun r => Cf.X.G.mulVec (M r)) M') : M' = M := by
  have hdE : HasDist Cf.X.G Cf.C₀.d := HasDist.map (E := E) hd
  have h1 := (decodesTo_iff_agr E _ _ _ Cf.X.G Cf.eM _ M').mp h
  refine agreesOn_unique E _ _ _ Cf.X.G Cf.C₀.d hdE (agr Cf.X.G (fun r => Cf.X.G.mulVec (M r)) M')
    (by omega) (fun r => Cf.X.G.mulVec (M r)) M' M ?_ (fun _ _ _ => rfl)
  exact (agreesOn_iff_subset E _ _ _ Cf.X.G _ _ M').mpr (Finset.Subset.refl _)

end LdCf

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype E] in
theorem ldCf_dcd_enc : Spec.ldCf_dcd_enc F E := by
  intro Cf hd he m r s
  show (Cf.X.dec (Cf.tab (Cf.enc m r)) (s, Cf.X.ZR.val s (Cf.upM m))).map Cf.dnM = some m
  have h : Cf.X.dec (fun a => Cf.X.G.mulVec (Code.liftWord E (Cf.full m r a)))
        (s, Cf.X.ZR.val s (Cf.X.view fun a => Code.liftWord E (Cf.full m r a))) =
      some (Cf.X.view fun a => Code.liftWord E (Cf.full m r a)) :=
    ldFe_honest Cf.X Cf.C₀.d (fun a => Code.liftWord E (Cf.full m r a)) s
      (HasDist.map (E := E) hd) he
  rw [Cf.view_full m r] at h
  rw [Cf.tab_enc m r]
  exact (congrArg (Option.map Cf.dnM) h).trans (congrArg some (Cf.dnM_upM m))

omit [Fintype E] in
theorem ldCf_free_enc : Spec.ldCf_free_enc F E := by
  intro Cf hd he m r s
  show ¬ Cf.X.Coll (Cf.tab (Cf.enc m r)) s
  rw [Cf.tab_enc m r]
  rintro ⟨u, u', ⟨M, hM, rfl⟩, ⟨M', hM', rfl⟩, hne, -⟩
  rw [Cf.list_of_codewords hd he hM, Cf.list_of_codewords hd he hM'] at hne
  exact hne rfl

omit [Fintype E] in
theorem ldCf_held_hold : Spec.ldCf_held_hold F E := fun _ h i _ => h i

omit [Fintype E] in
theorem ldCf_rcd : Spec.ldCf_rcd F E := fun Cf L h y =>
  (ldFc_binds F E Cf.C₀ Cf.hp Cf.J₀ Cf.Pd Cf.plE Cf.v Cf.Z Cf.eM Cf.rank L (Cf.tabF y)
    h.core.dist h.rad h.evades (h.list _)).1

theorem ldCf_strong : Spec.ldCf_strong F E := by
  intro Cf b hC hb S hS m m'
  have hP := core_props F E Cf.C₀ hC
  have h1 := hP.hides_table (R := Cf.Row) S (hS.trans hb) (Cf.mrow m)
  have h2 := hP.hides_table (R := Cf.Row) S (hS.trans hb) (Cf.mrow m')
  exact h1.trans h2.symm

theorem ldCf_rows : Spec.ldCf_rows F E := by
  intro Cf hB
  refine ⟨fun s i η k => ?_, fun s m => hB s _⟩
  funext t
  refine (ood_val_rows_same E Cf.J Cf.Row Cf.Z s (Cf.upM (Cf.hold i η)) k t).trans ?_
  refine congrFun (congrArg (Cf.Z.val s) (funext fun j => ?_)) t
  cases j <;> rfl

theorem ldCf_hides : Spec.ldCf_hides F E := fun Cf b hC hb hB =>
  rec_hides_of_rows Cf.conf Cf.rows b (ldCf_rows F E Cf hB) (ldCf_strong F E Cf b hC hb)

theorem ldCf_props : Spec.ldCf_props F E := fun Cf L b h hB hb =>
  { sub := h.sub
    admits := h.admits
    dcd_enc := ldCf_dcd_enc F E Cf h.core.dist h.rad
    free_enc := ldCf_free_enc F E Cf h.core.dist h.rad
    held_hold := ldCf_held_hold F E Cf h.held
    rcd := ldCf_rcd F E Cf L h
    hides := ldCf_hides F E Cf b h.core hb hB }

omit [Fintype F] in
theorem ldCf_padBij_pad : Spec.ldCf_padBij_pad F E := by
  intro μ J₀ P B _ _ _ _ _ _ plc w b hw hb ρ a
  obtain ⟨z, β⟩ := ρ
  have hval : ∀ c : P → F, (Sample.pad E μ J₀ P B plc w b).val (z, β) (withPad a c) =
      fun _ => Alg.mle (placed plc a) z + b β * padVal (F := F) w c := by
    intro c
    funext u
    cases u
    exact ood_val_pad E μ J₀ P B plc w b z β (withPad a c)
  constructor
  · intro c c' h
    have h1 := congrFun ((hval c).symm.trans (h.trans (hval c'))) ()
    exact hw.1 (mul_left_cancel₀ (hb β) (add_left_cancel h1))
  · intro y
    obtain ⟨c, hc⟩ := hw.2 ((b β)⁻¹ * (y () - Alg.mle (placed plc a) z))
    refine ⟨c, ?_⟩
    show (Sample.pad E μ J₀ P B plc w b).val (z, β) (withPad a c) = y
    rw [hval c, hc]
    funext u
    cases u
    field_simp [hb β]
    ring

omit [Fintype E] in
theorem ldCf_dcd_iff : Spec.ldCf_dcd_iff F E := by
  intro Cf hd he y rec m
  show (Cf.X.dec (Cf.tab y) rec).map Cf.dnM = some m ↔ _
  constructor
  · intro h
    obtain ⟨U, hU, hm⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨M, hM, hv, -⟩ := Cf.X.dec_cand hU
    obtain ⟨M₀, -, rfl⟩ := ldFc_overF F E Cf.C₀ Cf.eM hd he _ (Cf.tabF y) M hM
    have hup : U = Cf.upM (fun n => M₀ n.1 (Fin.castLE Cf.hp (Cf.plE n.2))) := hv.symm
    rw [hU, hup]
    rw [hup, Cf.dnM_upM] at hm
    rw [hm]
  · intro h
    rw [h, Option.map_some, Cf.dnM_upM]

omit [Fintype E] in
theorem ldCf_held_same : Spec.ldCf_held_same F E := fun _ _ h _ _ hU =>
  h.reads _ _ fun r l => congrArg (downF F E) (hU r l)

omit [Fintype E] in
theorem ldCf_D : Spec.ldCf_D F E := by
  classical
  intro Cf y rec i
  show (if Cf.X.Coll (Cf.tab y) rec.1 then none
        else ((Cf.X.dec (Cf.tab y) rec).map Cf.dnM).bind Cf.held) = some i ↔
    _
  by_cases hc : Cf.X.Coll (Cf.tab y) rec.1
  · rw [if_pos hc]
    exact ⟨fun h => (by cases h), fun h => absurd hc h.1⟩
  · rw [if_neg hc]
    constructor
    · intro h
      obtain ⟨m, hm, hi⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨U, hU, rfl⟩ := Option.map_eq_some_iff.mp hm
      exact ⟨hc, U, hU, hi⟩
    · rintro ⟨-, U, hU, hi⟩
      rw [hU]
      exact hi

end
end Cb
