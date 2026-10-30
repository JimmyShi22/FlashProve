-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveForms.lean: slots that the written lists of an attention segment's
claims name with a coefficient that does not read 0, list by list. ONE DIRECTION: each slot that a
statement lists is so named; that no other slot is, is not said. Statements with their proofs ON THE
VERIFIER'S OWN DATA: no prover is in this file. rho: any reading in a field
(OnBytes/Model/HideLaws.lean).

The lists are Fo.claim3T .. Fo.claim8T (OnBytes/Tie/Pv/Lookup/Ends/FoAttLists1.lean,
FoAttLists2.lean) at any plain structure H of what was heard. That the runs "first" and "second"
gather just these lists is first_any and second_any (Johnson/Desc/First/Att/Claims/Any.lean).

Main names:
  Quiet           a form names no slot with a coefficient that reads other than 0
  slotCo_foldl_quiet, quiet_weightedF .. quiet_readGroupT, slotCo_lessF
                  the written readers of tables are quiet
  slot_sub_live   "slot less a quiet form" has the coefficient 1 on its slot
  planes_live     a plane claim's members: the slots s0 + x, x below np
  unit_live, unit_row   a softmax-table unit's list: its plane values, the maximum's slot, its end
                  values as far as its pieces go; its row is a member
  live5, row5     the division's list: ZC, RH, RHP, the index's bits, the two high parts, the end
                  values; the row
  live6, row6m, row6d   the value product's: CL0, CL1, ACC; both sumchecks' end values; the rows
  live7, row7f, row7d   the maxima; the FIRST end values of the score at the index; the key's end
                  values; the two rows
  live8, row8     the end values of "the index's cells are bits"; the row

live6 is CONDITIONAL on: the slots of ACC and ZC lie in front of CL0's. unit_list, unit_row and
unit_live are CONDITIONAL on: the unit's tables and its plane claim are there (h1, h2); where one is
missing the unit's list is empty. All else is unconditional. By a reading of the lists, which no
statement here says: not named by any of these lists but inside a row: a unit's seventh scalar, the
second of the five, and the SECOND end values of the score at the index.
Limits. Nothing on the rows' own coefficients (Johnson/Desc/K5/Honest/Law/Live.lean). Nothing on the
key forms, which no list holds. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Live

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading Aff)
open OnBytes.Attention (PW PlaneClaim Score ScoreTables Sc3 sc3A sc3B)
open OnBytes.Model (TenAt)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## 1 Forms that name no slot -/

/-- The form's coefficient on every slot reads 0. -/
def Quiet (f : Aff) : Prop := ∀ j, slotCo ρ f j = 0

/-- Adding multiples of quiet forms turns no coefficient. -/
theorem slotCo_foldl_quiet {α : Type} (fv : α → Aff) (c : α → E) (hq : ∀ a, Quiet ρ (fv a))
    (j : ℕ) : ∀ (l : List α) (s : Aff),
      slotCo ρ (l.foldl (fun s a => Aff.addMul s (fv a) (c a)) s) j = slotCo ρ s j
  | [], _ => rfl
  | a :: l, s => by
    rw [List.foldl_cons, slotCo_foldl_quiet fv c hq j l, slotCo_addMul, hq a j, mul_zero, add_zero]

theorem quiet_weightedF (n : ℕ) (w : Array E) (fv : ℕ → Aff) (hq : ∀ k, Quiet ρ (fv k)) :
    Quiet ρ (Fo.weightedF n w fv) := fun j => by
  unfold Fo.weightedF
  rw [slotCo_foldl_quiet ρ fv (fun i => w.getD i zeroE) hq j, slotCo_ofConst]

theorem quiet_u3Form (a b c : ℕ) : Quiet ρ (Fo.u3Form a b c) := fun j => slotCo_ent ρ _ _ _ j

/-- "start less the pieces' quiet forms" has start's coefficients. -/
theorem slotCo_lessF (start : Aff) (pw : Array PW) (fv : PW → Aff) (hq : ∀ w, Quiet ρ (fv w))
    (j : ℕ) : slotCo ρ (Fo.lessF start pw fv) j = slotCo ρ start j := by
  unfold Fo.lessF
  exact slotCo_foldl_quiet ρ fv (fun w => mulE OnBytes.Attention.minusOne w.wp) hq j _ _

variable (H : OnBytes.Attention.Heard) (Kc : ℕ)

theorem quiet_planeF (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    Quiet ρ (Fo.planeF H Kc t x lam a z isD) :=
  quiet_weightedF ρ _ _ _ fun _ => quiet_u3Form ρ _ _ _

theorem quiet_shVF (t off nl J lam j : ℕ) : Quiet ρ (Fo.shVF H Kc t off nl J lam j) :=
  quiet_weightedF ρ _ _ _ fun _ => quiet_u3Form ρ _ _ _

theorem quiet_overGF (zg : Array E) (fv : ℕ → Aff) (hq : ∀ g, Quiet ρ (fv g)) :
    Quiet ρ (Fo.overGF H zg fv) := quiet_weightedF ρ _ _ _ hq

theorem quiet_readDenominatorF (t : ℕ) (zg : Array E) (lam a : ℕ) :
    Quiet ρ (Fo.readDenominatorF H Kc t zg lam a) :=
  quiet_overGF ρ H _ _ fun _ => quiet_shVF ρ H Kc _ _ _ _ _ _

theorem quiet_readMaximumF (t : ℕ) (zg : Array E) (lam a : ℕ) :
    Quiet ρ (Fo.readMaximumF H Kc t zg lam a) :=
  quiet_overGF ρ H _ _ fun _ => quiet_shVF ρ H Kc _ _ _ _ _ _

theorem quiet_readIndexBitF (t : ℕ) (zg : Array E) (lam a b : ℕ) :
    Quiet ρ (Fo.readIndexBitF H Kc t zg lam a b) :=
  quiet_overGF ρ H _ _ fun _ => quiet_shVF ρ H Kc _ _ _ _ _ _

theorem quiet_xlT (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) :
    Quiet ρ (Fo.xlT H Kc t X lam hd zc) := fun j => by
  unfold Fo.xlT Fo.xlF
  split
  · split
    · exact quiet_weightedF ρ _ _ _ (fun _ => quiet_weightedF ρ _ _ _ fun _ =>
        quiet_u3Form ρ _ _ _) j
    · exact slotCo_empty ρ j
  · exact slotCo_empty ρ j

theorem quiet_readHeadT (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    Quiet ρ (Fo.readHeadT H Kc t X zg zc lam a) :=
  quiet_overGF ρ H _ _ fun _ => quiet_xlT ρ H Kc _ _ _ _ _

theorem quiet_readGroupT (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    Quiet ρ (Fo.readGroupT H Kc t X zg zc lam) :=
  quiet_overGF ρ H _ _ fun _ => quiet_xlT ρ H Kc _ _ _ _ _

/-- **"Slot less a quiet form" has the coefficient 1 on its slot.** -/
theorem slot_sub_live (s : ℕ) (q : Aff) (hq : Quiet ρ q) : slotCo ρ (Aff.slot s - q) s ≠ 0 := by
  rw [slotCo_sub, slotCo_slot, if_pos rfl, hq, sub_zero]
  exact one_ne_zero

theorem lessF_live (s : ℕ) (pw : Array PW) (fv : PW → Aff) (hq : ∀ w, Quiet ρ (fv w)) :
    slotCo ρ (Fo.lessF (Aff.slot s) pw fv) s ≠ 0 := by
  rw [slotCo_lessF ρ _ _ _ hq, slotCo_slot, if_pos rfl]
  exact one_ne_zero

/-- A number below 2 n is 2 b or 2 b + 1 with b below n. -/
theorem SD.pair_cases {e n : ℕ} (h : e < 2 * n) : ∃ b < n, e = 2 * b ∨ e = 2 * b + 1 :=
  ⟨e / 2, by omega, by omega⟩

/-! ## 2 Plane claims and the softmax-table units -/

/-- **A plane claim's members.** -/
theorem planes_live (pc : PlaneClaim) {x : ℕ} (hx : x < pc.np) :
    ∃ f ∈ Fo.linPlanesT H Kc pc, slotCo ρ f (pc.s0 + x) ≠ 0 :=
  ⟨_, List.mem_flatMap.2 ⟨x, List.mem_range.2 hx, List.mem_singleton.2 rfl⟩,
    lessF_live ρ _ _ _ fun _ => quiet_planeF ρ H Kc _ _ _ _ _ _⟩

section Unit
variable {n : ℕ} {k : Score} {tb : ScoreTables} {pc : PlaneClaim}
  (h1 : H.t.score[n]? = some tb) (h2 : H.planes[k.claim]? = some pc)
include h1 h2

theorem unit_list : Fo.unitKFDT H Kc n k = Fo.linPlanesT H Kc pc ++
    ([Fo.lessF (Aff.slot (k.s0 + 5)) k.pw fun w => Fo.readMaximumF H Kc tb.tM k.zg w.lam w.a] ++
      ([k.sc.rowU] ++ k.pw.toList.zipIdx.flatMap fun x =>
        Fo.endValuesT H Kc k tb (k.sc.r.extract (k.sc.r.size - H.S.cf.ldh) k.sc.r.size)
          x.2 x.1)) := by
  unfold Fo.unitKFDT
  rw [h1, h2]

/-- The unit's row is a member of its list. -/
theorem unit_row : k.sc.rowU ∈ Fo.unitKFDT H Kc n k := by
  rw [unit_list H Kc h1 h2]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_singleton.2 rfl)))

/-- **A softmax-table unit's list**: its plane claim's slots, the maximum's, and its end values as
far as its pieces go. -/
theorem unit_live {j : ℕ} (hj : (∃ x < pc.np, j = pc.s0 + x) ∨ j = k.s0 + 5 ∨
    ∃ e < 2 * k.pw.size, j = k.sc.sEnd + e) :
    ∃ f ∈ Fo.unitKFDT H Kc n k, slotCo ρ f j ≠ 0 := by
  rw [unit_list H Kc h1 h2]
  rcases hj with ⟨x, hx, rfl⟩ | rfl | ⟨e, he, rfl⟩
  · obtain ⟨f, hf, hl⟩ := planes_live ρ H Kc pc hx
    exact ⟨f, List.mem_append_left _ hf, hl⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.2 rfl)),
      lessF_live ρ _ _ _ fun _ => quiet_readMaximumF ρ H Kc _ _ _ _⟩
  · obtain ⟨b, hb, hc⟩ := SD.pair_cases he
    have hm : (k.pw[b], b) ∈ k.pw.toList.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simp [hb]
    rcases hc with rfl | rfl
    · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨_, hm, List.mem_append_left _ (List.mem_singleton.2 rfl)⟩))),
        slot_sub_live ρ _ _ (quiet_readHeadT ρ H Kc _ _ _ _ _ _)⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨_, hm, List.mem_append_right _ (List.mem_singleton.2 rfl)⟩))),
        slot_sub_live ρ _ _ (quiet_readGroupT ρ H Kc _ _ _ _ _)⟩

end Unit

/-! ## 3 The division -/

theorem row5 : H.d.scE.rowU ∈ Fo.claim5T H Kc :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_singleton.2 rfl)))))))

/-- **The division's list.** -/
theorem live5 {j : ℕ} (hj : j = H.d.s5 + 2 ∨ j = H.d.s5 + 3 ∨ j = H.d.s5 + 4 ∨
    (∃ k < H.S.cf.lt, j = H.d.sIB + k) ∨ j = H.d.s5h ∨ j = H.d.s5h + 1 ∨
    ∃ e < 2 * H.S.NP, j = H.d.scE.sEnd + e) :
    ∃ f ∈ Fo.claim5T H Kc, slotCo ρ f j ≠ 0 := by
  rcases hj with rfl | rfl | rfl | ⟨k, hk, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_singleton.2 rfl),
      lessF_live ρ _ _ _ fun _ => quiet_readDenominatorF ρ H Kc _ _ _ _⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.2 rfl)),
      lessF_live ρ _ _ _ fun _ => quiet_readHeadT ρ H Kc _ _ _ _ _ _⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_singleton.2 rfl))), lessF_live ρ _ _ _ fun _ => quiet_readHeadT ρ H Kc _ _ _ _ _ _⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk,
        List.mem_singleton.2 rfl⟩)))),
      lessF_live ρ _ _ _ fun _ => quiet_readIndexBitF ρ H Kc _ _ _ _ _⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.2 rfl))))),
      lessF_live ρ _ _ _ fun _ => quiet_readHeadT ρ H Kc _ _ _ _ _ _⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_singleton.2 rfl)))))),
      lessF_live ρ _ _ _ fun _ => quiet_readHeadT ρ H Kc _ _ _ _ _ _⟩
  · obtain ⟨b, hb, hc⟩ := SD.pair_cases he
    have mem : ∀ f ∈ Fo.endValuesET H Kc b (H.d.pwW.getD b default), f ∈ Fo.claim5T H Kc :=
      fun f hf => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_right _ (List.mem_append_left _
            (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, hf⟩))))))))
    rcases hc with rfl | rfl
    · exact ⟨_, mem _ (List.mem_append_left _ (List.mem_singleton.2 rfl)),
        slot_sub_live ρ _ _ (quiet_readDenominatorF ρ H Kc _ _ _ _)⟩
    · exact ⟨_, mem _ (List.mem_append_right _ (List.mem_singleton.2 rfl)),
        slot_sub_live ρ _ _ (quiet_readHeadT ρ H Kc _ _ _ _ _ _)⟩

/-! ## 4 The value product -/

theorem product_row (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool) (tV : ℕ) :
    sc.rowU ∈ Fo.valueProductT H Kc sc tS pt isD tV :=
  List.mem_append_left _ (List.mem_singleton.2 rfl)

/-- A value product's end values. -/
theorem product_live (sc : Sc3) (tS : ℕ) (pt : Array E) (isD : Bool) (tV : ℕ) {e : ℕ}
    (he : e < 2 * H.S.NP) :
    ∃ f ∈ Fo.valueProductT H Kc sc tS pt isD tV, slotCo ρ f (sc.sEnd + e) ≠ 0 := by
  obtain ⟨b, hb, hc⟩ := SD.pair_cases he
  rcases hc with rfl | rfl
  · refine ⟨_, List.mem_append_right _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb,
      List.mem_append_left _ (List.mem_singleton.2 rfl)⟩), slot_sub_live ρ _ _ fun j => ?_⟩
    rw [slotCo_add, slotCo_add, slotCo_scale, slotCo_ofConst, quiet_planeF ρ H Kc,
      quiet_planeF ρ H Kc]
    ring
  · refine ⟨_, List.mem_append_right _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb,
      List.mem_append_right _ (List.mem_singleton.2 rfl)⟩), slot_sub_live ρ _ _ fun j => ?_⟩
    rw [slotCo_add, slotCo_ofConst, quiet_readGroupT ρ H Kc, add_zero]

theorem row6m : H.d.vpm.rowU ∈ Fo.claim6T H Kc :=
  List.mem_append_right _ (List.mem_append_left _ (product_row H Kc _ _ _ _ _))

theorem row6d : H.d.vpd.rowU ∈ Fo.claim6T H Kc :=
  List.mem_append_right _ (List.mem_append_right _ (product_row H Kc _ _ _ _ _))

/-- **The value product's list**, CONDITIONAL on: the slots of ACC and ZC, the first and the third
of the five scalars, lie in front of the two value products' scalars. -/
theorem live6 (ho : H.d.s5 + 2 < H.d.sCl) {j : ℕ} (hj : j = H.d.sCl ∨ j = H.d.sCl + 1 ∨
    j = H.d.s5 ∨ (∃ e < 2 * H.S.NP, j = H.d.vpm.sEnd + e) ∨
    ∃ e < 2 * H.S.NP, j = H.d.vpd.sEnd + e) :
    ∃ f ∈ Fo.claim6T H Kc, slotCo ρ f j ≠ 0 := by
  have co : ∀ j, slotCo ρ (Aff.slot H.d.sCl + Aff.slot (H.d.sCl + 1) - Aff.slot H.d.sACC -
      Aff.scale (Aff.slot H.d.sZC) H.d.gam) j =
      (if H.d.sCl = j then 1 else 0) + (if H.d.sCl + 1 = j then 1 else 0) -
        (if H.d.s5 = j then 1 else 0) - ρ.val H.d.gam * (if H.d.s5 + 2 = j then 1 else 0) :=
    fun j => by
      rw [slotCo_sub, slotCo_sub, slotCo_add, slotCo_scale, slotCo_slot, slotCo_slot, slotCo_slot,
        slotCo_slot]
      rfl
  rcases hj with rfl | rfl | rfl | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · refine ⟨_, List.mem_append_left _ (List.mem_singleton.2 rfl), ?_⟩
    rw [co, if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · refine ⟨_, List.mem_append_left _ (List.mem_singleton.2 rfl), ?_⟩
    rw [co, if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega)]
    simp
  · refine ⟨_, List.mem_append_left _ (List.mem_singleton.2 rfl), ?_⟩
    rw [co, if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega)]
    simp
  · obtain ⟨f, hf, hl⟩ := product_live ρ H Kc H.d.vpm H.t.tVM H.t.ptM false H.t.qVM he
    exact ⟨f, List.mem_append_right _ (List.mem_append_left _ hf), hl⟩
  · obtain ⟨f, hf, hl⟩ := product_live ρ H Kc H.d.vpd H.t.tVD H.t.ptD true H.t.qVD he
    exact ⟨f, List.mem_append_right _ (List.mem_append_right _ hf), hl⟩

/-! ## 5 The maximum and its index -/

theorem row7f : H.x.scF.rowU ∈ Fo.claim7T H Kc :=
  List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.2 rfl))

theorem row7d : H.x.scd.rowU ∈ Fo.claim7T H Kc :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_singleton.2 rfl))))

/-- **The list on the maximum and its index**: the maxima, the first end values of the score at the
index, and the end values of the key at the index. -/
theorem live7 {j : ℕ} (hj : (∃ b < H.S.NP, j = H.x.sM6 + b) ∨
    (∃ b < H.S.NP, j = H.x.scF.sEnd + 2 * b) ∨ (∃ lam < H.S.Lam, j = H.x.scd.sEnd + lam) ∨
    ∃ b < H.S.NP, ∃ k < H.S.cf.lt, j = H.x.scd.sEnd + (H.S.Lam + b * H.S.cf.lt + k)) :
    ∃ f ∈ Fo.claim7T H Kc, slotCo ρ f j ≠ 0 := by
  rcases hj with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨lam, hl, rfl⟩ | ⟨b, hb, k, hk, rfl⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb,
      List.mem_singleton.2 rfl⟩), slot_sub_live ρ _ _ (quiet_readMaximumF ρ H Kc _ _ _ _)⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, List.mem_singleton.2 rfl⟩))),
      slot_sub_live ρ _ _ (quiet_readHeadT ρ H Kc _ _ _ _ _ _)⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨lam,
        List.mem_range.2 hl, List.mem_singleton.2 rfl⟩))))),
      slot_sub_live ρ _ _ (quiet_readGroupT ρ H Kc _ _ _ _ _)⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨b,
        List.mem_range.2 hb, List.mem_flatMap.2 ⟨k, List.mem_range.2 hk,
          List.mem_singleton.2 rfl⟩⟩))))),
      slot_sub_live ρ _ _ (quiet_readIndexBitF ρ H Kc _ _ _ _ _)⟩

theorem row8 : H.x.scH.rowU ∈ Fo.claim8T H Kc :=
  List.mem_append_left _ (List.mem_singleton.2 rfl)

/-- **The list "the index's cells are bits"**: both end values of a pair stand in the form "the
second less the first plus 1". -/
theorem live8 {e : ℕ} (he : e < 2 * H.S.NP) :
    ∃ f ∈ Fo.claim8T H Kc, slotCo ρ f (H.x.scH.sEnd + e) ≠ 0 := by
  obtain ⟨b, hb, hc⟩ := SD.pair_cases he
  refine ⟨sc3B H.x.scH b - sc3A H.x.scH b + Aff.ofConst oneE, List.mem_append_right _
    (List.mem_flatMap.2 ⟨b, List.mem_range.2 hb, List.mem_append_left _
      (List.mem_singleton.2 rfl)⟩), ?_⟩
  rw [slotCo_add, slotCo_sub, slotCo_ofConst]
  unfold sc3A sc3B
  rw [slotCo_slot, slotCo_slot]
  rcases hc with rfl | rfl
  · rw [if_neg (by omega), if_pos rfl]
    simp
  · rw [if_pos rfl, if_neg (by omega)]
    simp

end H2K5.Honest

#print axioms H2K5.Honest.slotCo_foldl_quiet
#print axioms H2K5.Honest.quiet_weightedF
#print axioms H2K5.Honest.quiet_u3Form
#print axioms H2K5.Honest.slotCo_lessF
#print axioms H2K5.Honest.quiet_planeF
#print axioms H2K5.Honest.quiet_shVF
#print axioms H2K5.Honest.quiet_overGF
#print axioms H2K5.Honest.quiet_readDenominatorF
#print axioms H2K5.Honest.quiet_readMaximumF
#print axioms H2K5.Honest.quiet_readIndexBitF
#print axioms H2K5.Honest.quiet_xlT
#print axioms H2K5.Honest.quiet_readHeadT
#print axioms H2K5.Honest.quiet_readGroupT
#print axioms H2K5.Honest.slot_sub_live
#print axioms H2K5.Honest.lessF_live
#print axioms H2K5.Honest.SD.pair_cases
#print axioms H2K5.Honest.planes_live
#print axioms H2K5.Honest.unit_list
#print axioms H2K5.Honest.unit_row
#print axioms H2K5.Honest.unit_live
#print axioms H2K5.Honest.row5
#print axioms H2K5.Honest.live5
#print axioms H2K5.Honest.product_row
#print axioms H2K5.Honest.product_live
#print axioms H2K5.Honest.row6m
#print axioms H2K5.Honest.row6d
#print axioms H2K5.Honest.live6
#print axioms H2K5.Honest.row7f
#print axioms H2K5.Honest.row7d
#print axioms H2K5.Honest.live7
#print axioms H2K5.Honest.row8
#print axioms H2K5.Honest.live8
