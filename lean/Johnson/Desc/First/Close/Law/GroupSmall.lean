-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/GroupSmall.lean: THE PROVED BLOCK's CONDITION FOR THE CLOSING OF A LINK
(KIND K10) HOLDS AT THE REAL GROUP OF THE SMALL SIZE. Definitions, statements and proofs. NO TEXT OF
THE DESCRIPTION STANDS BENEATH THIS FILE: public numbers, the library's typed objects, the kernel.

The twin of GroupFull.lean (beside this file; made of it by a program that turned the names and the
numbers, then compiled) at the small size, as Johnson/G/SwitchKeptLit.lean writes it: the messages
with a main row of one of the 6 written lists (`linksSmallLit`), at the stage of one of the three
groups in front (`frontSmall`) with 218 drawn positions, at the written radius (`radSmall`), whole
members kept. The sums in front (`pre`), `maskOf` and `sum_get` are GroupFull.lean's.
  `placeSmall k` (at 9, 7 and 8 row variables it is entry 11, 12 and 13 of `foldSmall`),
    `frontSmall_place`, `groupSmall`, `placeSmall_good`, `placeSmall_paid`, `small_stage`,
    `small_radius_eq`, `small_inJ`, `small_counts`, `small_radius`, `small_len`,
    `small_fits`, `small_fix`, `small_good`, `small_good_pre`,
    `linksSmall_fit9`, `front9`.
  `k10_condition_small`: `BatFoldOKAt` at the caller of `groupSmall lo hlo gs hgs oM oZ kp`, at the
    written place's own two counts, from two premises: the coefficients evade zero; the group's data
    are in order.
  `groupSmall9`, `groupSmall9_good`, `k10_condition_small_at`: WITH NO PREMISE: at each of the 6
    lists, at the first group in front (9 row variables), nothing kept, every member's rows behind
    those of the messages in front of it, the coefficients the powers of one element along any
    numbering.
Limits. Those of GroupFull.lean, read at the small size: `k10_condition_small_at` IS A MEMBER, NOT
THE DESCRIPTION's OWN PLACE. This file rests, through FoldPriced.lean, on the files under
ThirdParty/ (lean/LIMITS.md, L15). Nothing on soundness of the protocol.

-/
import Johnson.G.SwitchKeptLit
import Johnson.Top.H.GroupFix
import Johnson.Top.H.CallerKept
import Johnson.Bridge.FoldAtWritten
import Johnson.Desc.First.Close.Law.GroupFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb Iop IOR
open VerifiableInference.OnPublicFiles


/-- The written place of a link's group as it is closed, at the small size, with k row variables. -/
def placeSmall (k : ℕ) : Johnson.Bridge.FoldedPlace :=
  ⟨⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, k, 218⟩, 76267,
    ⟨516, 13054610892900820049, 13054610892900820050, 18124568022926293377⟩,
    ⟨3, 4672366867200143431, 4672366867200143432, 5649607370⟩⟩

/-- At 9, 7 and 8 row variables it stands in the written table. -/
theorem placeSmall_mem : placeSmall 9 ∈ Johnson.Bridge.foldSmall ∧
    placeSmall 7 ∈ Johnson.Bridge.foldSmall ∧ placeSmall 8 ∈ Johnson.Bridge.foldSmall := by
  have h9 : Johnson.Bridge.foldSmall[11]'(by decide) = placeSmall 9 := rfl
  have h7 : Johnson.Bridge.foldSmall[12]'(by decide) = placeSmall 7 := rfl
  have h8 : Johnson.Bridge.foldSmall[13]'(by decide) = placeSmall 8 := rfl
  exact ⟨h9 ▸ List.getElem_mem _, h7 ▸ List.getElem_mem _, h8 ▸ List.getElem_mem _⟩

/-- Each of the three groups in front has 9, 7 or 8 row variables, and its stage, at 218 drawn
positions, is that place's. -/
theorem frontSmall_place : ∀ g ∈ frontSmall, (g.k = 9 ∨ g.k = 7 ∨ g.k = 8) ∧
    (placeSmall g.k).s = stageOf g 218 := by
  intro g hg
  simp only [frontSmall, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨Or.inr (Or.inr rfl), rfl⟩

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]

/-- The group of a link as it is closed, at the small size: whole members kept. -/
noncomputable abbrev groupSmall : RowsK (sigOf codesSmall2 lo) :=
  (rowsAtSmall lo hlo gs hgs 218 oM oZ).keep kp

include hgs in
theorem placeSmall_in : placeSmall gs.k ∈ Johnson.Bridge.foldFull ++ Johnson.Bridge.foldSmall := by
  rcases (frontSmall_place gs hgs).1 with h | h | h <;> rw [h]
  · exact List.mem_append_right _ placeSmall_mem.1
  · exact List.mem_append_right _ placeSmall_mem.2.1
  · exact List.mem_append_right _ placeSmall_mem.2.2

include hgs in
theorem placeSmall_good : (placeSmall gs.k).good = true :=
  List.all_eq_true.1 Johnson.Bridge.fold_good _ (placeSmall_in gs hgs)

include hgs in
theorem placeSmall_paid : (placeSmall gs.k).Paid :=
  Johnson.Bridge.foldedPlacesPaid _ (placeSmall_in gs hgs)

theorem small_stage : (placeSmall gs.k).s = (groupSmall lo hlo gs hgs oM oZ kp).s :=
  (frontSmall_place gs hgs).2

theorem small_radius_eq : (placeSmall gs.k).e = (groupSmall lo hlo gs hgs oM oZ kp).e := rfl

/-- hj. -/
theorem small_inJ : InJ (groupSmall lo hlo gs hgs oM oZ kp).s (groupSmall lo hlo gs hgs oM oZ kp).e
    :=
  place_inJ _ _ (placeSmall_good gs hgs) (small_stage lo hlo gs hgs oM oZ kp)
    (small_radius_eq lo hlo gs hgs oM oZ kp)

/-- hc, at the place's own counts. -/
theorem small_counts : CountsAt (groupSmall lo hlo gs hgs oM oZ kp).s
    (groupSmall lo hlo gs hgs oM oZ kp).e (placeSmall gs.k).bC (placeSmall gs.k).bZ :=
  place_counts _ _ (placeSmall_good gs hgs) (small_stage lo hlo gs hgs oM oZ kp)
    (small_radius_eq lo hlo gs hgs oM oZ kp)

/-- he. -/
theorem small_radius : (groupSmall lo hlo gs hgs oM oZ kp).G.e <
    (groupSmall lo hlo gs hgs oM oZ kp).s.d :=
  place_radius _ _ (placeSmall_good gs hgs) (small_stage lo hlo gs hgs oM oZ kp)
    (small_radius_eq lo hlo gs hgs oM oZ kp)

include hlo hgs in
theorem small_len (i : Fin lo.length) : aOf codesSmall2 (lo.get i).1 ≤ (stageOf gs 218).C.a := by
  show aOf codesSmall2 (lo.get i).1 ≤ (stageOf gs 0).C.a
  rw [(tablesSmall_ok gs hgs).1]
  exact (links_fit_small lo hlo (lo.get i) (List.get_mem lo i)).le

/-- hFi. -/
theorem small_fits : (groupSmall lo hlo gs hgs oM oZ kp).G.Fits :=
  rowsPort_fits codesSmall2 lo (memMain lo) (stageOf gs 218) radSmall oM oZ _ _
    (fun i _ => small_len lo hlo gs hgs i)
    (fun i _ => by
      show radSmall ≤ 2 ^ ((stageOf gs 0).C.a - _) * _ + (2 ^ ((stageOf gs 0).C.a - _) - 1)
      rw [(tablesSmall_ok gs hgs).1]
      exact (links_fit_small lo hlo (lo.get i) (List.get_mem lo i)).near)

/-- hv. -/
theorem small_fix (a) : ((groupSmall lo hlo gs hgs oM oZ kp).view a).Fix
    (groupSmall lo hlo gs hgs oM oZ kp).G.e :=
  membPort_fix codesSmall2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 218) (oM a.1) (oZ a.1)
    (hMSmall lo hlo gs hgs 218 a.1 a.2) (hZSmall lo hlo gs hgs 218 a.1 a.2)
    (small_len lo hlo gs hgs a.1) _

/-- hg, from four conditions on where the rows stand. -/
theorem small_good
    (fitM : ∀ r, ¬ kp r.1 → (rowsAtSmall lo hlo gs hgs 218 oM oZ).atM r <
      2 ^ ((stageOf gs 218).h + (stageOf gs 218).g))
    (injM : ∀ r r', ¬ kp r.1 → ¬ kp r'.1 → (rowsAtSmall lo hlo gs hgs 218 oM oZ).atM r =
      (rowsAtSmall lo hlo gs hgs 218 oM oZ).atM r' → r = r')
    (fitZ : ∀ r, (rowsAtSmall lo hlo gs hgs 218 oM oZ).atZ r < 2 ^ (stageOf gs 218).h)
    (injZ : Function.Injective (rowsAtSmall lo hlo gs hgs 218 oM oZ).atZ) :
    (groupSmall lo hlo gs hgs oM oZ kp).Good :=
  Rows.keep_good _ kp
    { sized := by
        have h := (Johnson.Bridge.FoldedPlace.stageJ (placeSmall_good gs hgs)).sized
        rw [(frontSmall_place gs hgs).2] at h
        exact h
      view := fun a => membPort_laws codesSmall2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 218)
        (oM a.1) (oZ a.1) (hMSmall lo hlo gs hgs 218 a.1 a.2) (hZSmall lo hlo gs hgs 218 a.1 a.2)
        (small_len lo hlo gs hgs a.1)
      fitM := fitM
      injM := injM
      fitZ := fitZ
      injZ := injZ
      one := by
        show 1 ≤ (stageOf gs 218).h + (stageOf gs 218).g
        rw [← (frontSmall_place gs hgs).2]
        show 1 ≤ 0 + gs.k
        rcases (frontSmall_place gs hgs).1 with h | h | h <;> omega }

end

/-! ## The four conditions, met: every member's rows behind those of the members in front -/

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall)

/-- **hg AT A VALUE**: nothing kept; every member's rows stand behind those of the messages in
front of it; from two comparisons of numbers. -/
theorem small_good_pre (hM : ∑ i, (lo.get i).1.mainRows ≤ 2 ^ gs.k)
    (hZ : ∑ i, maskOf lo i ≤ 1) :
    (groupSmall lo hlo gs hgs (pre fun i => (lo.get i).1.mainRows)
      (pre (maskOf lo)) fun _ => False).Good := by
  have e : (stageOf gs 218).h + (stageOf gs 218).g = gs.k := by
    rw [← (frontSmall_place gs hgs).2]
    show 0 + gs.k = gs.k
    omega
  have e0 : (stageOf gs 218).h = 0 := by
    rw [← (frontSmall_place gs hgs).2]
    rfl
  refine small_good lo hlo gs hgs _ _ _ (fun r _ => ?_) (fun r r' _ _ h => ?_) (fun r => ?_) ?_
  · rw [e]
    have h1 := pre_top (fun i => (lo.get i).1.mainRows) r.1.1
    have h2 : r.2.val < (lo.get r.1.1).1.mainRows := r.2.isLt
    show pre (fun i => (lo.get i).1.mainRows) r.1.1 + r.2.val < 2 ^ gs.k
    omega
  · exact apart_inj (A := {i // memMain lo i}) (fun a => (lo.get a.1).1.mainRows)
      (fun a => pre (fun i => (lo.get i).1.mainRows) a.1)
      (fun a b hab => pre_apart _ a.1 b.1 fun k => hab (Subtype.ext k)) h
  · rw [e0]
    have h1 := pre_top (maskOf lo) r.1.1
    have h2 : r.2.val < (lo.get r.1.1).1.maskRows := r.2.isLt
    rw [← maskOf_mem lo r.1] at h2
    show pre (maskOf lo) r.1.1 + r.2.val < 2 ^ 0
    omega
  · exact apart_inj (A := {i // memMain lo i}) (fun a => (lo.get a.1).1.maskRows)
      (fun a => pre (maskOf lo) a.1)
      (fun a b hab => by
        have h := pre_apart (maskOf lo) a.1 b.1 fun k => hab (Subtype.ext k)
        rw [maskOf_mem lo a, maskOf_mem lo b] at h
        exact h)

end

set_option maxRecDepth 1000000 in
/-- The two comparisons hold of every written list at 9 row variables. -/
theorem linksSmall_fit9 : ∀ lo ∈ linksSmallLit,
    (lo.map fun x => x.1.mainRows).sum ≤ 2 ^ 9 ∧
      (lo.map fun x => if x.1.mainRows ≠ 0 then x.1.maskRows else 0).sum ≤ 1 := by
  decide +kernel

theorem front9 : grpSmall 9 8 false ∈ frontSmall := List.mem_cons_self

/-! ## The proved block's condition -/

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit) (gs : GroupSize)
  (hgs : gs ∈ frontSmall) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]
  (keep : (sigOf codesSmall2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) (groupSmall lo hlo gs hgs oM oZ kp).G.C.J)
  (Z : Evader GE ((groupSmall lo hlo gs hgs oM oZ kp).G.Row B))
  (fx : Fin (((groupSmall lo hlo gs hgs oM oZ kp).Sh.fold Sb sl Z).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 lo).sub
    ((groupSmall lo hlo gs hgs oM oZ kp).sizeB keep Sb sl Z).kp).Msg × Wp))
  (w₀ : (sigOf codesSmall2 lo).Wit × Wp)
  (w₁ : LdBrW (groupSmall lo hlo gs hgs oM oZ kp).G
    ((groupSmall lo hlo gs hgs oM oZ kp).sizeB keep Sb sl Z).kp Wp)

/-- **THE PROVED BLOCK's CONDITION AT THE REAL GROUP**: from two things: the batching's coefficients
evade zero, and the group's data are in order. -/
theorem k10_condition_small (hZ : Z.OK) (hGood : (groupSmall lo hlo gs hgs oM oZ kp).Good) :
    BatFoldOKAt ((groupSmall lo hlo gs hgs oM oZ kp).foldCaller keep Sb sl Z fx A₀
      (placeSmall gs.k).bC (placeSmall gs.k).bZ w₀ w₁) :=
  RowsK.foldCaller_ok _ keep Sb sl Z fx A₀ _ _ w₀ w₁ hZ (small_fits lo hlo gs hgs oM oZ kp) hGood
    (small_inJ lo hlo gs hgs oM oZ kp) (small_counts lo hlo gs hgs oM oZ kp)

end

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksSmallLit)

/-- The group at the value of `small_good_pre`: the first group in front, nothing kept, every
    member's
rows behind those of the messages in front of it. -/
noncomputable abbrev groupSmall9 : RowsK (sigOf codesSmall2 lo) :=
  groupSmall lo hlo (grpSmall 9 8 false) front9 (pre fun i => (lo.get i).1.mainRows)
    (pre (maskOf lo)) fun _ => False

theorem groupSmall9_good : (groupSmall9 lo hlo).Good :=
  small_good_pre lo hlo _ front9
    (by rw [sum_get lo fun x => x.1.mainRows]; exact (linksSmall_fit9 lo hlo).1)
    (by
      have h := (linksSmall_fit9 lo hlo).2
      rw [← sum_get lo fun x => if x.1.mainRows ≠ 0 then x.1.maskRows else 0] at h
      exact h)

variable (keep : (sigOf codesSmall2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) (groupSmall9 lo hlo).G.C.J) (n : ℕ)
  (num : (groupSmall9 lo hlo).G.Row B ≃ Fin n)
  (fx : Fin (((groupSmall9 lo hlo).Sh.fold Sb sl (Cb.Pv.Bat.powersZ (E := GE) n num)).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesSmall2 lo).sub
    ((groupSmall9 lo hlo).sizeB keep Sb sl (Cb.Pv.Bat.powersZ (E := GE) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesSmall2 lo).Wit × Wp)
  (w₁ : LdBrW (groupSmall9 lo hlo).G
    ((groupSmall9 lo hlo).sizeB keep Sb sl (Cb.Pv.Bat.powersZ (E := GE) n num)).kp Wp)

/-- **THE PROVED BLOCK's CONDITION, WITH NO PREMISE**: at each of the written lists, at that group,
    at
the powers of one element along any numbering of the rows as the batching's coefficients. -/
theorem k10_condition_small_at :
    BatFoldOKAt ((groupSmall9 lo hlo).foldCaller keep Sb sl (Cb.Pv.Bat.powersZ (E := GE) n num) fx
        A₀
      (placeSmall 9).bC (placeSmall 9).bZ w₀ w₁) :=
  k10_condition_small lo hlo _ front9 _ _ _ keep Sb sl _ fx A₀ w₀ w₁
    (Cb.Pv.Bat.powersZ_ok n num num.injective) (groupSmall9_good lo hlo)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.small_good_pre
#print axioms VerifiableInference.Desc.First.Close.linksSmall_fit9
#print axioms VerifiableInference.Desc.First.Close.k10_condition_small
#print axioms VerifiableInference.Desc.First.Close.k10_condition_small_at
