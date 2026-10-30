-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/Groups.lean: CONDITIONAL (`back_hit` alone). THE CLAIMS OF
THE LAYERS' OWN ROUNDS (sub-protocol K4) THAT NAME THE SLOT OF A SHOWN VALUE WITH THE COEFFICIENT 1,
GROUP BY GROUP.

What is here. A LAW ON THE VERIFIER's TEXT: the honest prover is not in it, and no drawn element.
Wherever a maker of K4's claims (OnBytes/Desc/First/K4/Claims.lean, whose docstrings number the
groups) returns a list, that list holds the member named. Each proof unfolds the maker, as
Johnson/Road/K4/Slots/Groups.lean does, and points at one member (the carries' by the library's
`carries_eq`, Johnson/Road/K4/Reads/NormRowEnts.lean). That the rest of that member names no slot is
that file's and Johnson/Road/K4/Slots/Readers.lean's lemmas, used with the set "all slots but j".
Coefficients are read in the library's field. Statements and proofs.

  `norms_hit`: group 2: MEMBERSHIP ALONE: the squares' layer's own claim, and the form "the left
      end value's slot less the right one's". That form's coefficients (1 and -1) are reckoned in
      Law/Live/Whole.lean, where the two slots differ.
  `rows_hit_end`: group 4: for each of the four end values of each norm's row products a member
      with the coefficient 1 on its slot.
  `rows_hit_carry`: group 5: the like for the nine sums of each norm.
  `terms_hit`: group 7: the like for the end values of the second token sumcheck.
  `ends_hit`, `gated_hit`: groups 8 and 9: the like for the two end values of each gated layer;
      and the two layers' own claims are members.
  `back_hit`: groups 14 and 15: the like for the batched sumcheck's end values A0 and B0; and
      its own claim and the merge's are members.
  `cf_slot_sub`, `cf_slot_add`, `mapM_hit`: the kit.

Kin. Johnson/Road/K4/Slots/Groups.lean goes through the same makers for another end: which slots a
list names. OnBytes/Desc/First/K4/RowsLaws.lean has the membership that `rows_hit_end` and
`rows_hit_carry` show anew (`rowsForms_mem`), and `mapM_hit` by place (`mapM_get`,
`mapM_range_get`); the converse is `mem_of_mapM` (Johnson/Road/K4/W/ByMake.lean). `mapM_hit` ITSELF
STANDS IN THE LIBRARY FIVE TIMES THAT ITS WRITERS KNOW OF, THE SAME SENTENCE UP TO THE BOUND LETTERS
AND THE FUNCTION's BRACKETS: `mapM_mem` (OnBytes/Maker/TablesLaws.lean;
OnBytes/Tie/Pv/Lookup/Ends/FoReadsLayer.lean; OnBytes/TypedOracleCompiler/Run/ViewERead3.lean) and `mem_mapM`
(Johnson/Desc/K14/Law/Joint.lean; OnBytes/TypedOracleCompiler/Slice/EntryOpened.lean); none of these five files lies
beneath this one. `cf_slot_sub` (the slot j less a form that does not name j has the coefficient 1
on j) stands beside `sBit_sc` (Honest/K3/Good/Live/Forms.lean), which asks only that the form's
coefficient on j is 0, `slot_sub_live` (Johnson/Desc/K5/Honest/Law/LiveForms.lean) and `live_var`
(Honest/K6/GoodLaw/Coef.lean); Law/Live/Coef.lean's head names the other kits of such rules.

Not shown here. That a maker returns. Nothing on the slots that sumchecks' own claims name
(Law/Live/PscLive.lean). `back_hit` takes as hypotheses that the two forms which the batched
sumcheck's end leaves name no slot. Nothing on entries. Nothing on what a form is worth.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Coef
import Johnson.Road.K4.Slots.FrontBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Heard Own Ten sumForms)
open OnBytes.Desc.First
open OnBytes.Desc.First.K4 (normsForms rowsForms termsForms endsForms gatedForms)
open OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_scale sl_rowR sl_shA sl_longA
  sl_sumForms digitsAt_sl sl_ofDigits_c sl_ofDigits_four all_mapM_mem mapM_length)
open OnBytes.Desc.First.K4.Reads (carries_eq)

section kit
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem cf_slot_sub {x : Aff} {j : ℕ} (h : SlotsIn (fun i => i ≠ j) x) :
    cf ρ (Aff.slot j - x) j = 1 := by
  rw [cf_sub, cf_slot_self, cf_of_slotsIn ρ h, sub_zero]

theorem cf_slot_add {x : Aff} {j : ℕ} (h : SlotsIn (fun i => i ≠ j) x) :
    cf ρ (Aff.slot j + x) j = 1 := by
  rw [cf_add, cf_slot_self, cf_of_slotsIn ρ h, add_zero]

end kit

/-- What a function returns at a member stands in the list of its returns. -/
theorem mapM_hit {α β : Type} {g : α → Option β} : ∀ (xs : List α) (ys : List β),
    xs.mapM g = some ys → ∀ a ∈ xs, ∃ b ∈ ys, g a = some b
  | [], _, _, _, ha => by cases ha
  | x :: xs, ys, h, a, ha => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨c, hc, e⟩ := mapM_hit xs bs hbs a ha
      exact ⟨c, List.mem_cons_of_mem _ hc, e⟩

variable {v : Layer.Env} {H : Heard} {l : List Aff}

/-- **Group 2.** The layer's own claim is a member; and the claim "left = right". -/
theorem norms_hit {P : Layer.Pub} (h : normsForms P v H = some l) :
    H.wpl.row ∈ l ∧ (Aff.slot H.wpl.sL - Aff.slot H.wpl.sR) ∈ l := by
  unfold normsForms at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩

/-- **Group 4.** The four end values of each norm's row products. -/
theorem rows_hit_end (h : rowsForms v H = some l) {i k : ℕ} (hi : i < v.y.NI) (hk : k < 4) :
    ∃ f ∈ l, cf Reading.gl f (H.tV.sEnd + 4 * i + k) = 1 := by
  unfold rowsForms at h
  obtain ⟨ends, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Ds, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  obtain ⟨c, hc, e⟩ := mapM_hit _ ends h1 i (List.mem_range.2 hi)
  obtain ⟨D, hD, rfl⟩ := Option.map_eq_some_iff.mp e
  have h4 := sl_ofDigits_four (S := fun a => a ≠ H.tV.sEnd + 4 * i + k)
    (fun j => digitsAt_sl hD j)
  have key : ∃ x ∈ [(P6.Row.ofDigits D).a, (P6.Row.ofDigits D).b, (P6.Row.ofDigits D).Rlo,
      (P6.Row.ofDigits D).Rhi], (Aff.slot (H.tV.sEnd + 4 * i + k) - x) ∈
      ([(P6.Row.ofDigits D).a, (P6.Row.ofDigits D).b, (P6.Row.ofDigits D).Rlo,
        (P6.Row.ofDigits D).Rhi].zipIdx.map fun x => Aff.slot (H.tV.sEnd + 4 * i + x.2) - x.1) := by
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, List.mem_cons_self⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
        List.mem_cons_of_mem _ List.mem_cons_self⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)), List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  obtain ⟨x, hx, hm⟩ := key
  refine ⟨_, ?_, cf_slot_sub Reading.gl (h4 x hx)⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatten.2 ⟨_, hc, hm⟩))

/-- **Group 5.** The nine sums of each norm. -/
theorem rows_hit_carry (h : rowsForms v H = some l) {i s : ℕ} (hi : i < v.y.NI) (hs : s < 9) :
    ∃ f ∈ l, cf Reading.gl f (H.sW + 9 * i + s) = 1 := by
  unfold rowsForms at h
  obtain ⟨ends, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Ds, hDs, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  have hlen : Ds.length = v.y.NI := by rw [mapM_length _ _ hDs, List.length_range]
  have hi' : i < Ds.length := hlen ▸ hi
  have hD : ∀ j, SlotsIn (fun a => a ≠ H.sW + 9 * i + s) (Ds[i] j) :=
    all_mapM_mem (Pr := fun D : ℕ → Aff => ∀ j, SlotsIn (fun a => a ≠ H.sW + 9 * i + s) (D j))
      _ Ds (fun _ _ _ hb => digitsAt_sl hb) hDs _ (List.getElem_mem hi')
  have hz : (Ds[i], i) ∈ Ds.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi')
  refine ⟨Aff.slot (H.sW + 9 * i + s) + (P6.Row.ofDigits Ds[i]).c s - Ds[i] s -
    Aff.scale ((P6.Row.ofDigits Ds[i]).c (s + 1)) (ofNat 256), ?_, ?_⟩
  · refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.2
      ⟨_, List.mem_map.2 ⟨(Ds[i], i), hz, rfl⟩, ?_⟩))
    rw [carries_eq]
    exact List.mem_map.2 ⟨s, List.mem_range.2 hs, rfl⟩
  · rw [cf_sub, cf_sub, cf_slot_add Reading.gl (sl_ofDigits_c hD s),
      cf_of_slotsIn Reading.gl (hD s),
      cf_of_slotsIn Reading.gl (slotsIn_scale _ (sl_ofDigits_c hD (s + 1)))]
    ring

/-- **Group 7.** The end values of the second token sumcheck. -/
theorem terms_hit (h : termsForms v H = some l) {tT : Tsc} (hT : H.tT = some tT) {x : ℕ}
    (hx : x < v.y.NN * v.y.Lam + v.y.LamM + v.y.LamM * v.y.h.NE) :
    ∃ f ∈ l, cf Reading.gl f (tT.sEnd + x) = 1 := by
  unfold termsForms at h
  obtain ⟨tT', hT', h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : tT = tT' := Option.some.inj (hT.symm.trans hT')
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  by_cases h1 : x < v.y.NN * v.y.Lam
  · obtain ⟨f, hf, e⟩ := mapM_hit _ a ha x (List.mem_range.2 h1)
    obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp e
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _ hf),
      cf_slot_sub Reading.gl (sl_rowR hz)⟩
  · by_cases h2 : x < v.y.NN * v.y.Lam + v.y.LamM
    · obtain ⟨f, hf, e⟩ := mapM_hit _ b hb (x - v.y.NN * v.y.Lam) (List.mem_range.2 (by omega))
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp e
      have ex : tT.sEnd + x = tT.sEnd + v.y.NN * v.y.Lam + (x - v.y.NN * v.y.Lam) := by omega
      rw [ex]
      exact ⟨_, List.mem_append_left _ (List.mem_append_right _ hf),
        cf_slot_sub Reading.gl (sl_shA hz)⟩
    · obtain ⟨f, hf, e⟩ := mapM_hit _ c hc (x - (v.y.NN * v.y.Lam + v.y.LamM))
        (List.mem_range.2 (by omega))
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp e
      have ex : tT.sEnd + x =
          tT.sEnd + v.y.NN * v.y.Lam + v.y.LamM + (x - (v.y.NN * v.y.Lam + v.y.LamM)) := by omega
      rw [ex]
      exact ⟨_, List.mem_append_right _ hf, cf_slot_sub Reading.gl (sl_shA hz)⟩

/-- The two claims on a product layer's end values. -/
theorem ends_hit {o : Level} {e : Array E} {t rows blocks stride : ℕ} {lamOf : ℕ → ℕ} {first : ℕ}
    (h : endsForms v o e t rows blocks stride lamOf first = some l) :
    (∃ f ∈ l, cf Reading.gl f o.sL = 1) ∧ ∃ f ∈ l, cf Reading.gl f o.sR = 1 := by
  unfold endsForms at h
  obtain ⟨ts, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tu, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aS, hS, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aU, hU, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  have key : ∀ {S : ℕ → Prop} {X : Ten} {a : Aff}, sumForms (rows * blocks) (fun x =>
      (v.longA t X (lamOf (x / blocks)) (first + x % blocks)).map fun a =>
        (a, e.getD (x / blocks * stride + x % blocks) zeroE)) = some a → SlotsIn S a :=
    fun hs => sl_sumForms (fun x p hp => by
      obtain ⟨a', ha, e1⟩ := Option.map_eq_some_iff.mp hp
      subst e1
      exact sl_longA ha) hs
  exact ⟨⟨_, List.mem_cons_self, cf_slot_add Reading.gl (key hS)⟩,
    ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, cf_slot_add Reading.gl (key hU)⟩⟩

/-- **Groups 8 and 9.** The two layers' own claims are members; their four end values. -/
theorem gated_hit {P : Layer.Pub} {hd : Level} {hd2 : Option Level}
    (h : gatedForms P v hd hd2 = some l) :
    ∃ o, hd2 = some o ∧ hd.row ∈ l ∧ o.row ∈ l ∧ (∃ f ∈ l, cf Reading.gl f hd.sL = 1) ∧
      (∃ f ∈ l, cf Reading.gl f hd.sR = 1) ∧ (∃ f ∈ l, cf Reading.gl f o.sL = 1) ∧
      ∃ f ∈ l, cf Reading.gl f o.sR = 1 := by
  unfold gatedForms at h
  obtain ⟨e, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨o, ho, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e2, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t2, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  obtain ⟨⟨f1, m1, c1⟩, ⟨f2, m2, c2⟩⟩ := ends_hit ha
  obtain ⟨⟨f3, m3, c3⟩, ⟨f4, m4, c4⟩⟩ := ends_hit hb
  have inA : ∀ f ∈ a, f ∈ hd.row :: a ++ o.row :: b := fun f hf =>
    List.mem_append_left _ (List.mem_cons_of_mem _ hf)
  have inB : ∀ f ∈ b, f ∈ hd.row :: a ++ o.row :: b := fun f hf =>
    List.mem_append_right _ (List.mem_cons_of_mem _ hf)
  exact ⟨o, ho, List.mem_append_left _ List.mem_cons_self,
    List.mem_append_right _ List.mem_cons_self, ⟨f1, inA _ m1, c1⟩, ⟨f2, inA _ m2, c2⟩,
    ⟨f3, inB _ m3, c3⟩, ⟨f4, inB _ m4, c4⟩⟩

/-- **Groups 14 and 15.** The two end values A0 and B0 of the batched sumcheck; and that its own
claim and the merge's are members. hA, hB: the two forms that the sumcheck's end leaves name no slot
(the library's `stack_fin`). -/
theorem back_hit (o : Own) (rowM : Aff) (hA : ∀ S : ℕ → Prop, SlotsIn S o.K.fin.Alin)
    (hB : ∀ S : ℕ → Prop, SlotsIn S o.K.fin.Blin) :
    o.K.rowS ∈ OnBytes.Desc.First.K4.back o rowM ∧ rowM ∈ OnBytes.Desc.First.K4.back o rowM ∧
      (∃ f ∈ OnBytes.Desc.First.K4.back o rowM, cf Reading.gl f o.K.sA0 = 1) ∧
      ∃ f ∈ OnBytes.Desc.First.K4.back o rowM, cf Reading.gl f o.K.sB0 = 1 := by
  unfold OnBytes.Desc.First.K4.back
  exact ⟨List.mem_cons_self,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, cf_slot_sub Reading.gl (hA _)⟩,
    ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      cf_slot_sub Reading.gl (hB _)⟩⟩

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.cf_slot_sub
#print axioms ProofFile.Honest.K4.Live.cf_slot_add
#print axioms ProofFile.Honest.K4.Live.mapM_hit
#print axioms ProofFile.Honest.K4.Live.norms_hit
#print axioms ProofFile.Honest.K4.Live.rows_hit_end
#print axioms ProofFile.Honest.K4.Live.rows_hit_carry
#print axioms ProofFile.Honest.K4.Live.terms_hit
#print axioms ProofFile.Honest.K4.Live.ends_hit
#print axioms ProofFile.Honest.K4.Live.gated_hit
#print axioms ProofFile.Honest.K4.Live.back_hit
