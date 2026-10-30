-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/GroupFull.lean: THE PROVED BLOCK's CONDITION FOR THE CLOSING OF A LINK
(KIND K10) HOLDS AT THE REAL GROUP OF THE FULL SIZE. Definitions, statements and proofs. NO TEXT OF
THE DESCRIPTION STANDS BENEATH THIS FILE: public numbers, the library's typed objects, the kernel.

The proved block of the batching and the fold (Johnson/Top/H/BatFold.lean) is knowledge sound at a
caller under `BatFoldOKAt`: the coefficients evade zero; the lists at the joint radius are bounded;
the joint radius implies each member's own; the laws of the group's shape; the fold's conditions.
Here the caller is that of a group at the full size as Johnson/G/SwitchKeptLit.lean writes it: the
messages with a main row of one of the 26 written lists (`linksFullLit`), at the stage of one of the
three groups in front (`frontFull`) with 219 drawn positions, at the written radius (`radFull`),
whole members kept. The recipe for `full_len`, `full_fits` and `full_good` is that of a rough
check in a file of this project that is not in this library (K10Cond.lean);
the counts are taken from the written table of Johnson/Bridge/FoldAtWritten.lean.
  `placeFull k`, `placeFull_mem`, `frontFull_place`, `groupFull`, `placeFull_good`,
    `placeFull_paid`, `full_stage`, `full_radius_eq`, `full_inJ`, `full_counts`, `full_radius`,
    `full_len`, `full_fits`, `full_fix`, `full_good`, `pre` and its three lemmas, `maskOf`,
    `full_good_pre`, `linksFull_fit8`, `front8`, `sum_get`: out of
    AtFull.lean (beside this file), to the sign.
  `k10_condition_full`: `BatFoldOKAt` at the caller of `groupFull lo hlo gs hgs oM oZ kp`, at the
    written place's own two counts, at EVERY list, group in front, oM, oZ, kp, kept messages, typed
    rows, coefficients and joint, from two premises: the coefficients evade zero; the group's data
    are in order.
  `groupFull8`, `groupFull8_good`, `k10_condition_full_at`: WITH NO PREMISE: at each of the 26
    lists, at the first group in front (8 row variables), nothing kept, every member's rows behind
    those of the messages in front of it, the coefficients the powers of one element along any
    numbering.
Limits. `k10_condition_full_at` IS A MEMBER, NOT THE DESCRIPTION's OWN PLACE: that the protocol
closes a list at that group, with nothing kept and the rows laid so, is NOT said (two of the three
groups differ from it; lists with 150 or 153 main rows do not fit a group of 7 row variables unless
members are kept). At the description's own layout the group's data's being in order is a premise
(`k10_condition_full`). That the written lists, groups and radius are those of a file's plan is not
shown. No block's decision calls a test on these numbers. This file rests, through FoldPriced.lean,
on the files under ThirdParty/ (lean/LIMITS.md, L15). Nothing on soundness of the protocol.

-/
import Johnson.G.SwitchKeptLit
import Johnson.Top.H.GroupFix
import Johnson.Top.H.CallerKept
import Johnson.Bridge.FoldAtWritten
import Johnson.Desc.First.Close.Law.PlacePays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb Iop IOR
open VerifiableInference.OnPublicFiles


/-- The written place of a link's group as it is closed, at the full size, with k row variables. -/
def placeFull (k : ℕ) : Johnson.Bridge.FoldedPlace :=
  ⟨⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 0, k, 219⟩, 2433820,
    ⟨258, 13044156798776087384, 13044156798776087385, 18256289497540868099⟩,
    ⟨3, 4672644678352822300, 4672644678352822301, 180755102387⟩⟩

/-- At 8 and at 7 row variables it stands in the written table. -/
theorem placeFull_mem : placeFull 8 ∈ Johnson.Bridge.foldFull ∧
    placeFull 7 ∈ Johnson.Bridge.foldFull := by
  have h8 : Johnson.Bridge.foldFull[18]'(by decide) = placeFull 8 := rfl
  have h7 : Johnson.Bridge.foldFull[19]'(by decide) = placeFull 7 := rfl
  exact ⟨h8 ▸ List.getElem_mem _, h7 ▸ List.getElem_mem _⟩

/-- Each of the three groups in front has 8 or 7 row variables, and its stage, at 219 drawn
positions, is that place's. -/
theorem frontFull_place : ∀ g ∈ frontFull, (g.k = 8 ∨ g.k = 7) ∧
    (placeFull g.k).s = stageOf g 219 := by
  intro g hg
  simp only [frontFull, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨Or.inr rfl, rfl⟩
  · exact ⟨Or.inl rfl, rfl⟩

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]

/-- The group of a link as it is closed, at the full size: whole members kept. -/
noncomputable abbrev groupFull : RowsK (sigOf codesFull2 lo) :=
  (rowsAtFull lo hlo gs hgs 219 oM oZ).keep kp

include hgs in
theorem placeFull_in : placeFull gs.k ∈ Johnson.Bridge.foldFull ++ Johnson.Bridge.foldSmall := by
  rcases (frontFull_place gs hgs).1 with h | h <;> rw [h]
  · exact List.mem_append_left _ placeFull_mem.1
  · exact List.mem_append_left _ placeFull_mem.2

include hgs in
theorem placeFull_good : (placeFull gs.k).good = true :=
  List.all_eq_true.1 Johnson.Bridge.fold_good _ (placeFull_in gs hgs)

include hgs in
theorem placeFull_paid : (placeFull gs.k).Paid :=
  Johnson.Bridge.foldedPlacesPaid _ (placeFull_in gs hgs)

theorem full_stage : (placeFull gs.k).s = (groupFull lo hlo gs hgs oM oZ kp).s :=
  (frontFull_place gs hgs).2

theorem full_radius_eq : (placeFull gs.k).e = (groupFull lo hlo gs hgs oM oZ kp).e := rfl

/-- hj. -/
theorem full_inJ : InJ (groupFull lo hlo gs hgs oM oZ kp).s (groupFull lo hlo gs hgs oM oZ kp).e :=
  place_inJ _ _ (placeFull_good gs hgs) (full_stage lo hlo gs hgs oM oZ kp)
    (full_radius_eq lo hlo gs hgs oM oZ kp)

/-- hc, at the place's own counts. -/
theorem full_counts : CountsAt (groupFull lo hlo gs hgs oM oZ kp).s
    (groupFull lo hlo gs hgs oM oZ kp).e (placeFull gs.k).bC (placeFull gs.k).bZ :=
  place_counts _ _ (placeFull_good gs hgs) (full_stage lo hlo gs hgs oM oZ kp)
    (full_radius_eq lo hlo gs hgs oM oZ kp)

/-- he. -/
theorem full_radius : (groupFull lo hlo gs hgs oM oZ kp).G.e <
    (groupFull lo hlo gs hgs oM oZ kp).s.d :=
  place_radius _ _ (placeFull_good gs hgs) (full_stage lo hlo gs hgs oM oZ kp)
    (full_radius_eq lo hlo gs hgs oM oZ kp)

include hlo hgs in
theorem full_len (i : Fin lo.length) : aOf codesFull2 (lo.get i).1 ≤ (stageOf gs 219).C.a := by
  show aOf codesFull2 (lo.get i).1 ≤ (stageOf gs 0).C.a
  rw [(tablesFull_ok gs hgs).1]
  exact (links_fit lo hlo (lo.get i) (List.get_mem lo i)).le

/-- hFi. -/
theorem full_fits : (groupFull lo hlo gs hgs oM oZ kp).G.Fits :=
  rowsPort_fits codesFull2 lo (memMain lo) (stageOf gs 219) radFull oM oZ _ _
    (fun i _ => full_len lo hlo gs hgs i)
    (fun i _ => by
      show radFull ≤ 2 ^ ((stageOf gs 0).C.a - _) * _ + (2 ^ ((stageOf gs 0).C.a - _) - 1)
      rw [(tablesFull_ok gs hgs).1]
      exact (links_fit lo hlo (lo.get i) (List.get_mem lo i)).near)

/-- hv. -/
theorem full_fix (a) : ((groupFull lo hlo gs hgs oM oZ kp).view a).Fix
    (groupFull lo hlo gs hgs oM oZ kp).G.e :=
  membPort_fix codesFull2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 219) (oM a.1) (oZ a.1)
    (hMFull lo hlo gs hgs 219 a.1 a.2) (hZFull lo hlo gs hgs 219 a.1 a.2)
    (full_len lo hlo gs hgs a.1) _

/-- hg, from four conditions on where the rows stand. -/
theorem full_good
    (fitM : ∀ r, ¬ kp r.1 → (rowsAtFull lo hlo gs hgs 219 oM oZ).atM r <
      2 ^ ((stageOf gs 219).h + (stageOf gs 219).g))
    (injM : ∀ r r', ¬ kp r.1 → ¬ kp r'.1 → (rowsAtFull lo hlo gs hgs 219 oM oZ).atM r =
      (rowsAtFull lo hlo gs hgs 219 oM oZ).atM r' → r = r')
    (fitZ : ∀ r, (rowsAtFull lo hlo gs hgs 219 oM oZ).atZ r < 2 ^ (stageOf gs 219).h)
    (injZ : Function.Injective (rowsAtFull lo hlo gs hgs 219 oM oZ).atZ) :
    (groupFull lo hlo gs hgs oM oZ kp).Good :=
  Rows.keep_good _ kp
    { sized := by
        have h := (Johnson.Bridge.FoldedPlace.stageJ (placeFull_good gs hgs)).sized
        rw [(frontFull_place gs hgs).2] at h
        exact h
      view := fun a => membPort_laws codesFull2 (lo.get a.1).1 (lo.get a.1).2 (stageOf gs 219)
        (oM a.1) (oZ a.1) (hMFull lo hlo gs hgs 219 a.1 a.2) (hZFull lo hlo gs hgs 219 a.1 a.2)
        (full_len lo hlo gs hgs a.1)
      fitM := fitM
      injM := injM
      fitZ := fitZ
      injZ := injZ
      one := by
        show 1 ≤ (stageOf gs 219).h + (stageOf gs 219).g
        rw [← (frontFull_place gs hgs).2]
        show 1 ≤ 0 + gs.k
        rcases (frontFull_place gs hgs).1 with h | h <;> omega }

end

/-! ## The four conditions, met: every member's rows behind those of the members in front -/

/-- The sum of f over the numbers in front of i. -/
def pre {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : ℕ := ∑ j ∈ Finset.univ.filter (· < i), f j

theorem pre_step {n : ℕ} (f : Fin n → ℕ) {i j : Fin n} (h : i < j) : pre f i + f i ≤ pre f j := by
  unfold pre
  have hs : insert i (Finset.univ.filter (· < i)) ⊆ Finset.univ.filter (· < j) := by
    intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.1 hk).2 h⟩
  have hi : i ∉ Finset.univ.filter (· < i) := fun hk => lt_irrefl _ (Finset.mem_filter.1 hk).2
  calc ∑ k ∈ Finset.univ.filter (· < i), f k + f i
      = ∑ k ∈ insert i (Finset.univ.filter (· < i)), f k := by
        rw [Finset.sum_insert hi, add_comm]
    _ ≤ ∑ k ∈ Finset.univ.filter (· < j), f k := Finset.sum_le_sum_of_subset hs

theorem pre_top {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : pre f i + f i ≤ ∑ j, f j := by
  unfold pre
  have hi : i ∉ Finset.univ.filter (· < i) := fun hk => lt_irrefl _ (Finset.mem_filter.1 hk).2
  calc ∑ k ∈ Finset.univ.filter (· < i), f k + f i
      = ∑ k ∈ insert i (Finset.univ.filter (· < i)), f k := by
        rw [Finset.sum_insert hi, add_comm]
    _ ≤ ∑ k, f k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem pre_apart {n : ℕ} (f : Fin n → ℕ) (i j : Fin n) (h : i ≠ j) :
    pre f i + f i ≤ pre f j ∨ pre f j + f j ≤ pre f i := by
  rcases lt_or_gt_of_ne h with h | h
  · exact Or.inl (pre_step f h)
  · exact Or.inr (pre_step f h)

/-- The mask rows of a message that has a main row; 0 for another. -/
def maskOf (lo : List (OracleShape × ℕ)) (i : Fin lo.length) : ℕ :=
  if (lo.get i).1.mainRows ≠ 0 then (lo.get i).1.maskRows else 0

theorem maskOf_mem (lo : List (OracleShape × ℕ)) (a : {i // memMain lo i}) :
    maskOf lo a.1 = (lo.get a.1).1.maskRows := if_pos a.2

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull)

/-- **hg AT A VALUE**: nothing kept; every member's rows stand behind those of the messages in
front of it; from two comparisons of numbers. -/
theorem full_good_pre (hM : ∑ i, (lo.get i).1.mainRows ≤ 2 ^ gs.k)
    (hZ : ∑ i, maskOf lo i ≤ 1) :
    (groupFull lo hlo gs hgs (pre fun i => (lo.get i).1.mainRows)
      (pre (maskOf lo)) fun _ => False).Good := by
  have e : (stageOf gs 219).h + (stageOf gs 219).g = gs.k := by
    rw [← (frontFull_place gs hgs).2]
    show 0 + gs.k = gs.k
    omega
  have e0 : (stageOf gs 219).h = 0 := by
    rw [← (frontFull_place gs hgs).2]
    rfl
  refine full_good lo hlo gs hgs _ _ _ (fun r _ => ?_) (fun r r' _ _ h => ?_) (fun r => ?_) ?_
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
/-- The two comparisons hold of every written list at 8 row variables. -/
theorem linksFull_fit8 : ∀ lo ∈ linksFullLit,
    (lo.map fun x => x.1.mainRows).sum ≤ 2 ^ 8 ∧
      (lo.map fun x => if x.1.mainRows ≠ 0 then x.1.maskRows else 0).sum ≤ 1 := by
  decide +kernel

theorem front8 : grpFull 8 16 false ∈ frontFull := List.mem_cons_self

theorem sum_get {α : Type} (l : List α) (f : α → ℕ) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  simp [Fin.sum_univ_fun_getElem]

/-! ## The proved block's condition -/

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit) (gs : GroupSize)
  (hgs : gs ∈ frontFull) (oM oZ : Fin lo.length → ℕ)
  (kp : {i // memMain lo i} → Prop) [DecidablePred kp]
  (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) (groupFull lo hlo gs hgs oM oZ kp).G.C.J)
  (Z : Evader GE ((groupFull lo hlo gs hgs oM oZ kp).G.Row B))
  (fx : Fin (((groupFull lo hlo gs hgs oM oZ kp).Sh.fold Sb sl Z).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub
    ((groupFull lo hlo gs hgs oM oZ kp).sizeB keep Sb sl Z).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupFull lo hlo gs hgs oM oZ kp).G
    ((groupFull lo hlo gs hgs oM oZ kp).sizeB keep Sb sl Z).kp Wp)

/-- **THE PROVED BLOCK's CONDITION AT THE REAL GROUP**: from two things: the batching's coefficients
evade zero, and the group's data are in order. -/
theorem k10_condition_full (hZ : Z.OK) (hGood : (groupFull lo hlo gs hgs oM oZ kp).Good) :
    BatFoldOKAt ((groupFull lo hlo gs hgs oM oZ kp).foldCaller keep Sb sl Z fx A₀
      (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) :=
  RowsK.foldCaller_ok _ keep Sb sl Z fx A₀ _ _ w₀ w₁ hZ (full_fits lo hlo gs hgs oM oZ kp) hGood
    (full_inJ lo hlo gs hgs oM oZ kp) (full_counts lo hlo gs hgs oM oZ kp)

end

section
variable (lo : List (OracleShape × ℕ)) (hlo : lo ∈ linksFullLit)

/-- The group at the value of `full_good_pre`: the first group in front, nothing kept, every
    member's
rows behind those of the messages in front of it. -/
noncomputable abbrev groupFull8 : RowsK (sigOf codesFull2 lo) :=
  groupFull lo hlo (grpFull 8 16 false) front8 (pre fun i => (lo.get i).1.mainRows)
    (pre (maskOf lo)) fun _ => False

theorem groupFull8_good : (groupFull8 lo hlo).Good :=
  full_good_pre lo hlo _ front8
    (by rw [sum_get lo fun x => x.1.mainRows]; exact (linksFull_fit8 lo hlo).1)
    (by
      have h := (linksFull_fit8 lo hlo).2
      rw [← sum_get lo fun x => if x.1.mainRows ≠ 0 then x.1.maskRows else 0] at h
      exact h)

variable (keep : (sigOf codesFull2 lo).O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) (groupFull8 lo hlo).G.C.J) (n : ℕ)
  (num : (groupFull8 lo hlo).G.Row B ≃ Fin n)
  (fx : Fin (((groupFull8 lo hlo).Sh.fold Sb sl (Cb.Pv.Bat.powersZ (E := GE) n num)).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf codesFull2 lo).sub
    ((groupFull8 lo hlo).sizeB keep Sb sl (Cb.Pv.Bat.powersZ (E := GE) n num)).kp).Msg × Wp))
  (w₀ : (sigOf codesFull2 lo).Wit × Wp)
  (w₁ : LdBrW (groupFull8 lo hlo).G
    ((groupFull8 lo hlo).sizeB keep Sb sl (Cb.Pv.Bat.powersZ (E := GE) n num)).kp Wp)

/-- **THE PROVED BLOCK's CONDITION, WITH NO PREMISE**: at each of the written lists, at that group,
    at
the powers of one element along any numbering of the rows as the batching's coefficients. -/
theorem k10_condition_full_at :
    BatFoldOKAt ((groupFull8 lo hlo).foldCaller keep Sb sl (Cb.Pv.Bat.powersZ (E := GE) n num) fx A₀
      (placeFull 8).bC (placeFull 8).bZ w₀ w₁) :=
  k10_condition_full lo hlo _ front8 _ _ _ keep Sb sl _ fx A₀ w₀ w₁
    (Cb.Pv.Bat.powersZ_ok n num num.injective) (groupFull8_good lo hlo)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.full_good_pre
#print axioms VerifiableInference.Desc.First.Close.linksFull_fit8
#print axioms VerifiableInference.Desc.First.Close.k10_condition_full
#print axioms VerifiableInference.Desc.First.Close.k10_condition_full_at
