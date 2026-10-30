-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/LookHeard.lean: the honest side of the kind "lookup" (K3): AT
ANY NUMBER OF PARTS OF KEYS: CONDITIONAL ON `StageStep` AND ON `LeavesStep`
(Honest/K3/Law/Statements.lean): THE VERIFIER'S HEARING RETURNS ON A COURSE'S ROUNDS, and what it
heard is the run's. General in the face. Theorems.

  `callP_tie0` … `callP_bits`   the calls, as the verifier's text writes them
  `sum_stepR`     a sumcheck's stage, with the challenges that its structure keeps
  `front_walkP`, `tie_walkP`, `parts_walk`, `join_walkP`, `tree_walk`, `trees_walk`, `tab_walkP`
                  the hearing's pieces, one after the other, along the course's rounds
  `lookHeard_of_stepsP`   on `Cut` besides: the hearing returns; `HeardIs`; the invariant behind the
                  last stage; the leaves' own slots free; the rows heard are `RowsGood`; the leaves'
                  late row's worth; `PointsAgree`
  `lookHeardP`    **the same from `Fit`, the invariant in front and the course's rounds**
  `lookHeard`     **the statement `LookHeard`, at its own name**

Limits. CONDITIONAL ON `StageStep` AND `LeavesStep`, which are shown elsewhere from the laws of the
masked sumcheck's honest part. NO MEMBER IS TYPED HERE. Nothing on values but inside `RowsGood` and
the late row's clause, which are conditional on the stages' sums. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Walk
import Johnson.Desc.ProofFile.Honest.K3.Parts.Forward
import Johnson.Desc.ProofFile.Honest.K3.Law.CutOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE oneE addE subE mulE isZeroE)
open OnBytes.Model (Reading Aff Fork eqTab orderDefault)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV noVar
  leafVars bitsCall)
open VerifiableInference.Desc.First.ProdV
  (layBack levelVars stepDown LevelOut level Carried levelEnds
  elementsAlone)
open ProofFile.Honest.K3.Forward
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (zb0_of_fit zb1_of_fit)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

variable {W : Type}

theorem parts_pos {f : LFace} (h : f.ok = true) : 1 ≤ f.parts.length := by
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
  have h5 := h.1.1.1.1.2
  cases hq : f.parts with
  | nil => simp [hq] at h5
  | cons a l => simp

theorem take_sum_succ {l : List Nat} {i v : Nat} (h : l[i]? = some v) :
    (l.take (i + 1)).sum = (l.take i).sum + v := by
  rw [List.take_add_one, h]
  simp

section Walk
variable (SS : StageStep) (LS : LeavesStep) {R : Course W} {x : List Fmt.RoundView} (hF : Fit R)
  (C : Cut R x)

/-! ## The calls, as the verifier's text writes them -/

include hF in
theorem callP_tie0 (h2 : 2 ≤ R.f.planes) : R.call (.tie 0) = noVar 3 3 :=
  call_eqP R hF (mem_at (atP_tie R.f (j := 0) (by omega))) (k := noVar 3 3) rfl

include hF in
theorem callP_tieS {j : Nat} (hj : j + 1 < R.f.planes - 1) : R.call (.tie (j + 1)) = noVar 3 2 :=
  call_eqP R hF (mem_at (atP_tie R.f hj)) (k := noVar 3 2) rfl

include hF in
theorem callP_split {i : Nat} (hi : i < R.f.parts.length - 1) : R.call (.split i) = noVar 2 2 :=
  call_eqP R hF (mem_at (atP_split R.f hi)) (k := noVar 2 2) rfl

include hF in
theorem callP_key {i l v : Nat} (hi : R.f.parts[i]? = some v) (hl : l < v) : R.call (.key i l) =
    ⟨0, levelVars l (R.pts.keyPt i l) (R.f.orders i l), some levelEnds⟩ :=
  call_eqP R hF (mem_at (atP_key R.f hi hl).1) (k := levelCall l) rfl

include hF in
theorem callP_tab {l : Nat} (hl : l < R.f.d) : R.call (.tab l) =
    ⟨0, levelVars (R.f.mu + l) (R.pts.tabPt l) (orderDefault (R.f.mu + l)), some levelEnds⟩ :=
  call_eqP R hF (mem_at (atP_tab R.f hl).1) (k := levelCall (R.f.mu + l)) rfl

include hF in
theorem callP_leaves : R.call .leaves =
    { lead := 0, vs := leafVars R.f (R.pts.tabPt R.f.d), ends := none } :=
  call_eqP R hF (mem_at (atP_leaves R.f))
    (k := { lead := 0, vs := leafVars R.f #[], ends := none }) rfl

include hF in
theorem callP_bits : R.call .bits = bitsCall R.pts.zeroPt.toList :=
  call_eqP R hF (mem_at (atP_bits R.f))
    (k := bitsCall (List.replicate (R.f.mu + R.f.d) zeroE)) rfl

/-! ## A sumcheck's stage, with its structure's challenges -/

include SS hF C in
theorem sum_stepR {n : Nat} {s : Stage} {F : Fork} (hn : (stages R.f)[n]? = some s)
    (ht : 0 < s.tail R.f) (I : Inv R n F) :
    ∃ xs h row G, x.drop (off R.f n) = xs ++ x.drop (off R.f (n + 1)) ∧
      xs.length = s.rounds R.f ∧ elementsAlone xs = true ∧
      MaskedSum.whole (R.form s) (R.call s) (fun _ v => endTerm R.factor s v) F xs =
        some (h, row, G) ∧ h.r = R.r s ∧
      isZeroE (h.r.getLastD zeroE) = false ∧ h.sEnd = R.endSlot s ∧ Inv R (n + 1) G ∧ Later F G ∧
      (Sums R s (rd (R.claimed s)) (rd (endTerm R.factor s (R.shown s))) →
        ∀ (H : Fork) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE), Later G H →
          MasksAre R mask → row.value Reading.gl (H.worldOf Reading.gl mask entry) = 0) := by
  obtain ⟨seen, e⟩ := C.stage s (mem_at hn)
  obtain ⟨a, b, c⟩ := split_at C hn
  obtain ⟨h, row, G, w, r, y, z, I', last⟩ := SS W R n s F seen _ hF hn ht I e
  exact ⟨_, h, row, G, a, b, c, w, r, y, z, I', MaskedSum.whole_keeps w, last⟩

/-! ## The shift and alpha -/

include hF C in
theorem front_walkP {F : Fork} (I : Inv R 0 F) :
    (if R.f.shifted then drawV else pure zeroE : Hr E) F x =
        some (R.pts.theta, F, x.drop (off R.f (oAlpha R.f))) ∧
      drawV F (x.drop (off R.f (oAlpha R.f))) =
        some (R.pts.alpha, F, x.drop (off R.f (iTie R.f 0))) ∧ Inv R (iTie R.f 0) F := by
  have ht : R.pts.theta = (if R.f.shifted then
      elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base .shift) else zeroE) := rfl
  have I1 : (if R.f.shifted then drawV else pure zeroE : Hr E) F x =
      some (R.pts.theta, F, x.drop (off R.f (oAlpha R.f))) ∧ Inv R (oAlpha R.f) F := by
    rw [ht]
    by_cases hs : R.f.shifted = true
    · obtain ⟨r, a, q, I'⟩ := quiet_step C (atP_shift R.f hs) rfl I
      have h1 : oAlpha R.f = 1 := by simp [oAlpha, hs]
      simp only [if_pos hs, h1]
      rw [elem_at hF C (atP_shift R.f hs) a]
      have h0 : off R.f 0 = 0 := rfl
      rw [h0, List.drop_zero] at a
      refine ⟨?_, I'⟩
      conv_lhs => rw [a]
      exact drawV_ret q F _
    · have h1 : oAlpha R.f = 0 := by simp [oAlpha, hs]
      have h0 : off R.f 0 = 0 := rfl
      simp only [if_neg hs, h1, h0, List.drop_zero]
      exact ⟨rfl, I⟩
  obtain ⟨e5, I5⟩ := I1
  obtain ⟨r, a, q, I'⟩ := quiet_step C (atP_alpha R.f) rfl I5
  refine ⟨e5, ?_, I'⟩
  have ha : R.pts.alpha = e1 r := elem_at hF C (atP_alpha R.f) a
  rw [ha, a]
  exact drawV_ret q F _

/-! ## The tie -/

include SS hF C in
theorem tie_walkP {F : Fork} (I : Inv R (iTie R.f 0) F) :
    ∃ rows sG G, tieV R.f.planes R.factor F (x.drop (off R.f (iTie R.f 0))) =
        some ((rows, R.endSlot (.tie 0), sG), G, x.drop (off R.f (jSplit R.f 0))) ∧
      rows.size = R.f.planes - 1 ∧ (∀ i, i < R.f.planes → sG.getD i 0 = R.planeSlot i) ∧
      Inv R (jSplit R.f 0) G ∧ RowsGood R rows G ∧ Later F G := by
  have h2 : 2 ≤ R.f.planes := two_le_planes_of_ok R.f hF.ok
  obtain ⟨xs, h0, row0, G0, a, b, al, w, y, z, I1, lt0, zr0⟩ :=
    sum_step SS hF C (atP_tie R.f (j := 0) (by omega)) (show 0 < 3 by omega) I
  rw [callP_tie0 hF h2] at w
  rw [rounds_tie] at b
  have s1 := sumV_ret (k := noVar 3 3) w b al y (x.drop (off R.f (iTie R.f 0 + 1)))
  rw [← a] at s1
  let P : Nat → (Array Aff × Nat × Array Nat) → Fork → List Fmt.RoundView → Prop := fun j s F' rs =>
    Inv R (iTie R.f (j + 1)) F' ∧ rs = x.drop (off R.f (iTie R.f (j + 1))) ∧ s.2.1 = cur R j ∧
      s.1.size = j + 1 ∧ s.2.2.size = j + 1 ∧ (∀ i, i ≤ j → s.2.2.getD i 0 = R.planeSlot i) ∧
      RowsGood R s.1 F' ∧ Later F F'
  have hP0 : P 0 (#[row0], h0.sEnd + 1, #[h0.sEnd + 2]) G0 (x.drop (off R.f (iTie R.f 0 + 1))) := by
    refine ⟨I1, rfl, by show h0.sEnd + 1 = _; rw [z]; rfl, rfl, rfl, ?_,
      (rowsGood_empty R G0).push (mem_at (atP_tie R.f (j := 0) (by omega)))
        (show 0 < 3 by omega) zr0,
      lt0⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    show h0.sEnd + 2 = _
    rw [z]
    simp [Course.planeSlot]
  obtain ⟨s, G, rs', e2, I', hrs, hc, q1, q2, q3, gd, lt⟩ :=
    foldlM_ret (f := fun s (_ : Nat) => tieStep s) P (List.range (R.f.planes - 2)) 0 _ G0 _
      (by
        intro j hj s F rs hPj
        rw [List.length_range] at hj
        rw [Nat.zero_add] at hPj ⊢
        obtain ⟨I, hrs, hc, q1, q2, q3, gd, lt⟩ := hPj
        obtain ⟨xs, h, row, G, a, b, al, w, y, z, I', lt', zr⟩ :=
          sum_step SS hF C (atP_tie R.f (j := j + 1) (by omega)) (show 0 < 2 by omega) I
        rw [callP_tieS hF (by omega), form_tie, ← hc] at w
        rw [rounds_tie] at b
        have sv := sumV_ret (k := noVar 3 2) w b al y (x.drop (off R.f (iTie R.f (j + 1) + 1)))
        rw [← a, ← hrs] at sv
        refine ⟨(s.1.push row, h.sEnd, s.2.2.push (h.sEnd + 1)), G, _,
          (bind_ret sv).trans rfl, I', rfl, z, by simp [q1], by simp [q2], ?_,
          (gd.later lt').push (mem_at (atP_tie R.f (j := j + 1) (by omega)))
            (show 0 < 2 by omega) zr, lt.trans lt'⟩
        intro i hi
        show (s.2.2.push (h.sEnd + 1)).getD i 0 = _
        rw [getD_push, q2]
        by_cases hij : i = j + 1
        · subst hij
          rw [if_pos rfl, z]
          have h3 : j + 1 + 1 < R.f.planes := by omega
          simp [Course.planeSlot, h3]
        · rw [if_neg hij]
          exact q3 i (by omega)) hP0
  rw [Nat.zero_add, List.length_range] at I' hrs hc q1 q2 q3
  have hi : iTie R.f (R.f.planes - 2 + 1) = jSplit R.f 0 := by
    unfold iTie jSplit
    omega
  rw [hi] at I' hrs
  have tv := tieV_ret (w := R.f.planes) (a := R.factor) s1 e2
  rw [hrs, z] at tv
  refine ⟨_, _, G, tv, by rw [q1]; omega, ?_, I', gd, lt⟩
  intro i hi
  rw [getD_push, q2]
  by_cases hij : i = R.f.planes - 2 + 1
  · rw [if_pos hij, hc]
    have h3 : ¬ (i + 1 < R.f.planes) := by omega
    have h4 : i ≠ 0 := by omega
    by_cases h5 : R.f.planes = 2
    · have h6 : R.f.planes - 2 = 0 := by omega
      rw [h6]
      simp [Course.planeSlot, h4, h5, cur]
    · obtain ⟨n, hn⟩ : ∃ n, R.f.planes - 2 = n + 1 := ⟨R.f.planes - 3, by omega⟩
      rw [hn]
      simp [Course.planeSlot, h3, h4, h5, cur, hn]
  · rw [if_neg hij]
    exact q3 i (by omega)

/-! ## The parts' step -/

/-- The form that is left behind the last step of the parts' step is the last part's root. -/
theorem form_split_last (R : Course W) (h1 : 1 ≤ R.f.parts.length) :
    R.form (.split (R.f.parts.length - 1)) = R.root (R.f.parts.length - 1) := by
  have h3 : ¬ (R.f.parts.length - 1 + 1 < R.f.parts.length) := by omega
  by_cases h : R.f.parts.length ≤ 1
  · have e : R.f.parts.length - 1 = 0 := by omega
    rw [e]
    show Aff.slot (R.endSlot (.tie 0)) = R.root 0
    have h3' : ¬ (0 + 1 < R.f.parts.length) := by omega
    simp [Course.root, h3', h]
  · obtain ⟨n, hn⟩ : ∃ n, R.f.parts.length - 1 = n + 1 := ⟨R.f.parts.length - 2, by omega⟩
    have e2 : R.f.parts.length - 2 = n := by omega
    unfold Course.root
    rw [if_neg h3, if_neg h, e2, hn]
    rfl

include SS hF C in
theorem parts_walk : ∀ (n j : Nat) (rows : Array Aff) (F : Fork),
    j + n = R.f.parts.length - 1 → Inv R (jSplit R.f j) F → RowsGood R rows F →
    ∃ rows' roots G, partsV n rows (R.form (.split j)) F (x.drop (off R.f (jSplit R.f j))) =
        some ((rows', roots), G, x.drop (off R.f (jJoin R.f))) ∧
      rows'.size = rows.size + n ∧ roots = (List.range (n + 1)).map (fun t => R.root (j + t)) ∧
      Inv R (jJoin R.f) G ∧ RowsGood R rows' G ∧ Later F G
  | 0, j, rows, F, hj, I, g => by
    have e : j = R.f.parts.length - 1 := by omega
    subst e
    refine ⟨rows, _, F, partsV_zero_ret _ _ _ _, rfl, ?_, I, g, Later.refl F⟩
    rw [form_split_last R (parts_pos hF.ok)]
    rfl
  | n + 1, j, rows, F, hj, I, g => by
    have hlt : j < R.f.parts.length - 1 := by omega
    obtain ⟨xs, h, row, G, a, b, al, w, y, z, I', lt', zr⟩ :=
      sum_step SS hF C (atP_split R.f hlt) (show 0 < 2 by omega) I
    rw [callP_split hF hlt] at w
    have b' : xs.length = 3 := b
    have sv := sumV_ret (k := noVar 2 2) w b' al y (x.drop (off R.f (jSplit R.f j + 1)))
    rw [← a] at sv
    have hix : jSplit R.f j + 1 = jSplit R.f (j + 1) := rfl
    rw [hix] at sv I'
    obtain ⟨rows', roots, G', e, s1, s2, I'', g', lt''⟩ :=
      parts_walk n (j + 1) (rows.push row) G (by omega) I'
        ((g.later lt').push (mem_at (atP_split R.f hlt)) (show 0 < 2 by omega) zr)
    have hform : R.form (.split (j + 1)) = Aff.slot (h.sEnd + 1) := by
      rw [z]
      rfl
    rw [hform] at e
    refine ⟨rows', _, G', partsV_succ_ret sv e, by rw [s1]; simp; omega, ?_, I'', g',
      lt'.trans lt''⟩
    show Aff.slot h.sEnd :: roots = _
    have hr : R.root (j + 0) = Aff.slot (R.endSlot (.split j)) := by
      have : j + 1 < R.f.parts.length := by omega
      simp [Course.root, this]
    have hR : (List.range (n + 1 + 1)).map (fun t => R.root (j + t)) =
        R.root (j + 0) :: (List.range (n + 1)).map fun t => R.root (j + 1 + t) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t _
      show R.root (j + (t + 1)) = R.root (j + 1 + t)
      rw [show j + (t + 1) = j + 1 + t by omega]
    rw [s2, z, hR, hr]

/-! ## JOIN -/

include hF C in
theorem join_walkP {F : Fork} (I : Inv R (jJoin R.f) F) :
    ∃ jo, drawsV R.f.mu F (x.drop (off R.f (jJoin R.f))) =
        some (jo, F, x.drop (off R.f (jKey R.f 0 0))) ∧ jo.reverse = R.pts.rhoT ∧
      Inv R (jKey R.f 0 0) F := by
  obtain ⟨r, a, q, I'⟩ := quiet_step C (atP_join R.f) rfl I
  have hix : jJoin R.f + 1 = jKey R.f 0 0 := by simp [jKey]
  rw [hix] at a I'
  refine ⟨_, by rw [a]; exact drawsV_ret q F _, ?_, I'⟩
  show _ = (drawsAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base .join) R.f.mu).toArray.reverse
  rw [draws_at hF C (k := R.f.mu) (atP_join R.f) a q.elems]

/-! ## The key trees -/

include SS hF C in
/-- One part's key tree. -/
theorem tree_walk {i v : Nat} (hi : R.f.parts[i]? = some v) (rows0 : Array Aff) {F : Fork}
    (I : Inv R (jKey R.f i 0) F) (g0 : RowsGood R rows0 F) :
    ∃ c G, vRun 0 v (R.f.orders i) { rows := rows0, point := #[], form := R.root i } F
        (x.drop (off R.f (jKey R.f i 0))) = some (c, G, x.drop (off R.f (jKey R.f (i + 1) 0))) ∧
      c.point = R.pts.keyPt i v ∧ c.form = R.form (.key i v) ∧ c.rows.size = rows0.size + v ∧
      Inv R (jKey R.f (i + 1) 0) G ∧ RowsGood R c.rows G ∧ Later F G := by
  have hix : ∀ l, jKey R.f i 0 + 2 * l = jKey R.f i l := fun l => by unfold jKey; omega
  have hsg : ∀ l, l < v → (stages R.f)[jKey R.f i 0 + 2 * l]? = some (Stage.key i l) :=
    fun l hl => by rw [hix]; exact (atP_key R.f hi hl).1
  have hln : ∀ l, l < v → (stages R.f)[jKey R.f i 0 + 2 * l + 1]? = some (Stage.keyLine i l) :=
    fun l hl => by rw [hix]; exact (atP_key R.f hi hl).2
  have hro : ∀ l, l < v → (Stage.key i l).rounds R.f = 0 + l + 3 :=
    fun l _ => by rw [rounds_key]; omega
  have := run_walk SS hF C 0 (R.f.orders i) (fun l => .key i l) (fun l => .keyLine i l)
    (jKey R.f i 0) (fun l => R.pts.keyPt i l) (fun l => R.form (.key i l)) v hsg hln
    (fun l hl => by rw [Nat.zero_add]; exact callP_key hF hi hl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (hpt_of hF C 0 (R.f.orders i) (fun l => .key i l) (fun l => .keyLine i l) (jKey R.f i 0)
      (fun l => R.pts.keyPt i l) v hsg hln hro (fun _ _ => rfl)
      (fun l _ => by simp only [Nat.zero_add]; rfl))
    (fun _ _ => show 0 < 2 by omega) hro
    (fun _ _ => rfl) (fun _ _ => rfl) rows0 F I g0 v (Nat.le_refl _)
  have hnext : jKey R.f i 0 + 2 * v = jKey R.f (i + 1) 0 := by
    unfold jKey
    rw [take_sum_succ hi]
    omega
  rw [hnext] at this
  exact this

include SS hF C in
/-- The parts' key trees, from part number i on. -/
theorem trees_walk : ∀ (xs : List Nat) (i : Nat), R.f.parts.drop i = xs → ∀ (rows : Array Aff)
    (F : Fork), Inv R (jKey R.f i 0) F → RowsGood R rows F →
    ∃ rows' keys G, keysV R.f (xs.zipIdx i) ((List.range xs.length).map fun t => R.root (i + t))
        rows F (x.drop (off R.f (jKey R.f i 0))) =
        some ((rows', keys), G, x.drop (off R.f (jTab R.f 0))) ∧
      rows'.size = rows.size + xs.sum ∧
      keys = (xs.zipIdx i).map (fun y => (R.pts.keyPt y.2 y.1, R.form (.key y.2 y.1))) ∧
      Inv R (jTab R.f 0) G ∧ RowsGood R rows' G ∧ Later F G
  | [], i, hd, rows, F, I, g => by
    have hi : R.f.parts.length ≤ i := List.drop_eq_nil_iff.1 hd
    have e : jKey R.f i 0 = jTab R.f 0 := by
      unfold jKey jTab
      rw [List.take_of_length_le hi]
    rw [e] at I ⊢
    exact ⟨rows, [], F, keysV_nil_ret _ _ _ _ _, rfl, rfl, I, g, Later.refl F⟩
  | v :: xs, i, hd, rows, F, I, g => by
    obtain ⟨d1, _, d3⟩ := drop_cons hd
    obtain ⟨c, G, e, pc, fc, rc, I', g', lt⟩ := tree_walk SS hF C d3 rows I g
    obtain ⟨rows', keys, G', e', s1, s2, I'', g'', lt'⟩ :=
      trees_walk xs (i + 1) d1.symm c.rows G I' g'
    have hroots : (List.range (v :: xs).length).map (fun t => R.root (i + t)) =
        R.root i :: (List.range xs.length).map fun t => R.root (i + 1 + t) := by
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t _
      show R.root (i + (t + 1)) = R.root (i + 1 + t)
      rw [show i + (t + 1) = i + 1 + t by omega]
    rw [hroots, List.zipIdx_cons]
    refine ⟨rows', _, G', keysV_cons_ret (x := (v, i)) e e', ?_, ?_, I'', g'', lt.trans lt'⟩
    · rw [s1, rc, List.sum_cons]
      omega
    · show (c.point, c.form) :: keys = _
      rw [pc, fc, s2]
      rfl

/-! ## The table side -/

include SS hF C in
theorem tab_walkP (rows0 : Array Aff) {F : Fork} (I : Inv R (jTab R.f 0) F)
    (g0 : RowsGood R rows0 F) :
    ∃ c G, vRun R.f.mu R.f.d orderDefault
        { rows := rows0, point := R.pts.rhoT, form := R.join } F
        (x.drop (off R.f (jTab R.f 0))) = some (c, G, x.drop (off R.f (jTab R.f R.f.d))) ∧
      c.point = R.pts.tabPt R.f.d ∧ c.form = R.tabForm R.f.d ∧
      c.rows.size = rows0.size + R.f.d ∧ Inv R (jTab R.f R.f.d) G ∧ RowsGood R c.rows G ∧
      Later F G := by
  have hix : ∀ l, jTab R.f 0 + 2 * l = jTab R.f l := fun l => by unfold jTab; omega
  have hsg : ∀ l, l < R.f.d → (stages R.f)[jTab R.f 0 + 2 * l]? = some (Stage.tab l) :=
    fun l hl => by rw [hix]; exact (atP_tab R.f hl).1
  have hln : ∀ l, l < R.f.d → (stages R.f)[jTab R.f 0 + 2 * l + 1]? = some (Stage.tabLine l) :=
    fun l hl => by rw [hix]; exact (atP_tab R.f hl).2
  have := run_walk SS hF C R.f.mu orderDefault (fun l => .tab l) (fun l => .tabLine l)
    (jTab R.f 0) (fun l => R.pts.tabPt l) (fun l => R.tabForm l) R.f.d hsg hln
    (fun l hl => callP_tab hF hl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (hpt_of hF C R.f.mu orderDefault (fun l => .tab l) (fun l => .tabLine l) (jTab R.f 0)
      (fun l => R.pts.tabPt l) R.f.d hsg hln (fun l _ => rounds_tab R.f l) (fun _ _ => rfl)
      (fun _ _ => rfl))
    (fun _ _ => show 0 < 2 by omega)
    (fun l _ => rounds_tab R.f l)
    (fun _ _ => rfl) (fun _ _ => rfl) rows0 F I g0 R.f.d (Nat.le_refl _)
  rw [hix] at this
  exact this

end Walk

/-! ## The assembly -/

/-- **CONDITIONAL ON `StageStep`, ON `LeavesStep` AND ON `Cut` (no member is typed here); GENERAL IN
THE FACE: the verifier's hearing returns on the course's rounds**, from a ledger at which the
invariant holds in front of the first stage; what it heard is the run's; the invariant holds behind
the last stage; the leaves' own slots are free there; the rows heard are `RowsGood`; the leaves'
row, made later, is worth what `LeavesStep` says; the points that it kept are the run's. -/
theorem lookHeard_of_stepsP (SS : StageStep) (LS : LeavesStep) (R : Course W) (F : Fork)
    (x : List Fmt.RoundView) (hF : Fit R) (I0 : Inv R 0 F) (C : Cut R x) :
    ∃ g G, hearV R.f F x = some (g, G) ∧ HeardIs R g ∧ Inv R (stages R.f).length G ∧
      (∀ j, R.first + firstSlot R.f .leaves ≤ j →
        j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j) ∧
      RowsGood R g.rows G ∧
      (∀ cf : GE, Sums R .leaves (rd (R.claimed .leaves)) cf →
        ∀ (F' G' H : Fork) (y : Aff) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
          Sized F' → Later G F' → MaskedSum.row g.leaves oneE {} F' = some (y, G') →
          Later G' H → MasksAre R mask →
          y.value Reading.gl (H.worldOf Reading.gl mask entry) = rd g.leaves.eps * (1 - cf)) ∧
      PointsAgree R.f g R.a.base (R.t.heard ++ R.ds) := by
  have h2 := two_le_planes_of_ok R.f hF.ok
  have h1 := parts_pos hF.ok
  obtain ⟨e5, e6, I6⟩ := front_walkP hF C (inv_owed3 I0)
  obtain ⟨rows, sG, F7, e7, hrows, hsG, I7, g7, _⟩ := tie_walkP SS hF C I6
  obtain ⟨rows2, roots, F8, e8, hrows2, hroots, I8, g8, _⟩ :=
    parts_walk SS hF C (R.f.parts.length - 1) 0 rows F7 (by omega) I7 g7
  obtain ⟨jo, e9, hjo, I9⟩ := join_walkP hF C I8
  obtain ⟨rows3, keys, F10, e10, hrows3, hkeys, I10, g10, _⟩ :=
    trees_walk SS hF C R.f.parts 0 (List.drop_zero) rows2 F8 I9 g8
  obtain ⟨table, F12, e12, ptb, ftb, rtb, I12, g12, _⟩ := tab_walkP SS hF C rows3 I10 g10
  -- the leaves
  obtain ⟨xs, lv, F14, a14, b14, al14, w14, r14, f14, I14, free14, lt14, last14⟩ :=
    leaves_step LS hF C (atP_leaves R.f) I12
  rw [callP_leaves hF] at w14
  rw [rounds_leaves] at b14
  have e14 := openV_ret w14 (by rw [b14]; simp [leafVars]) al14
    (x.drop (off R.f (jTab R.f R.f.d + 1)))
  rw [← a14, ← ptb] at e14
  have hfl : R.form .leaves = table.form := ftb.symm
  rw [hfl] at e14
  -- ZERO
  obtain ⟨rz, az, qz, I15⟩ := quiet_step C (atP_zero R.f) rfl I14
  have e15 := drawsV_ret qz F14 (x.drop (off R.f (jTab R.f R.f.d + 1 + 1)))
  rw [← az] at e15
  have hz : ((rz.drawn.elems.map E.ofTriple).toArray).reverse = R.pts.zeroPt := by
    show _ = (drawsAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base .zero)
      (R.f.mu + R.f.d)).toArray.reverse
    rw [draws_at hF C (k := R.f.mu + R.f.d) (atP_zero R.f) az qz.elems]
  -- the bits
  obtain ⟨xb, hb, rowb, F16, ab, bb, alb, wb, rb, yb, zb, I16, lt16, zr16⟩ :=
    sum_stepR SS hF C (atP_bits R.f) (show 0 < 1 by omega) I15
  have wa := MaskedSum.whole_writesAbove I15.sized wb
  rw [callP_bits hF, ← hz] at wb
  have qe : rz.drawn.elems.length = R.f.mu + R.f.d := qz.elems
  have e16 := sumV_ret wb (by
    rw [bb, rounds_bits]
    simp [VerifiableInference.Desc.K3.roundsOf, bitsCall, qe]) alb yb
    (x.drop (off R.f (jTab R.f R.f.d + 2 + 1)))
  rw [← ab] at e16
  have hlen : jTab R.f R.f.d + 2 + 1 = (stages R.f).length := (stagesP_len R.f).symm
  have hend : x.drop (off R.f (jTab R.f R.f.d + 2 + 1)) = [] := by
    rw [hlen, off_len, ← C.len]
    exact List.drop_length
  rw [hend] at e16
  have hf0 : R.form (.split 0) = Aff.slot (R.endSlot (.tie 0)) := rfl
  rw [hf0] at e8
  have hrl : (List.range R.f.parts.length).map (fun t => R.root (0 + t)) = roots := by
    rw [hroots, show R.f.parts.length - 1 + 1 = R.f.parts.length by omega]
  rw [hrl] at e10
  rw [← join_eq R sG hsG, ← hjo] at e12
  have hsz : table.point.size = R.f.mu + R.f.d := by
    rw [ptb]
    exact tabPt_size R.f R.a.base (R.t.heard ++ R.ds) R.f.d
  have hslots : F16.next = F.next + R.f.slots := by
    have n0 : slotsIn R.f 0 = 0 := rfl
    have n1 : slotsIn R.f (stages R.f).length = R.f.slots := by
      unfold slotsIn
      rw [List.take_length, slots_stages R.f h2]
    rw [I16.next, I0.next, hlen, n0, n1]
    omega
  have hlins : (table.rows.push rowb).size = R.f.lins := by
    simp only [Array.size_push, rtb, hrows3, hrows2, hrows, VerifiableInference.Desc.K3.Face.lins]
  have hkl : keys.length = R.f.parts.length := by
    rw [hkeys]
    simp
  have hm := messagesV_introP R.f e5 e6 e7 e8 e9 e10 hkl e12 hsz e14 e15 e16 hslots hlins
  obtain ⟨_, _, _, _, _, hrec, _⟩ := MaskedSum.hear_spec w14
  refine ⟨_, F16, hearV_intro R.f hF.ok hm, ⟨rfl, zb, hlins, ?_, ?_, f14, r14⟩, ?_, ?_,
    ((g12.later lt14).later lt16).push (mem_at (atP_bits R.f)) (show 0 < 1 by omega) zr16,
    fun cf hcf F' G' H y mask entry hS hl hr hl' hm' =>
      last14 cf hcf F' G' H y mask entry hS (lt16.trans hl) hr hl' hm',
    ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩⟩
  · show keys.map (·.2) = _
    rw [hkeys, List.map_map]
    rfl
  · show lv.start = _
    rw [hrec]
  · rw [← hlen]
    exact I16
  · intro j j1 j2 hf
    obtain ⟨s1, s2⟩ := slotsIn_at (atP_leaves R.f)
    have hn : j < F14.next := by
      rw [I14.next, s2]
      rw [s1] at j2
      unfold Stage.slots
      omega
    exact free14 j (by rw [f14]; exact j1) (by rw [f14]; exact j2) ((wa.2 j hn).1 hf)
  · show keys.map (·.1) = _
    rw [hkeys, List.map_map]
    rfl
  · show lv.r.toArray = _
    rw [r14]
    exact (zb0_of_fit R hF).symm
  · show (hb.r.take (R.f.mu + R.f.d)).toArray = _
    rw [rb]
    exact (zb1_of_fit R hF).symm
  · show lv.vars = _
    rw [hrec]
    rfl

/-- **CONDITIONAL ON `StageStep` AND ON `LeavesStep` (no member is typed here); GENERAL IN THE FACE:
the same, from `Fit`, the invariant in front of the first stage, and the course's rounds.** -/
theorem lookHeardP (SS : StageStep) (LS : LeavesStep) (R : Course W) (F : Fork) (x : List Fmt.RoundView)
    (hF : Fit R) (I0 : Inv R 0 F) (h : R.rounds = some x) :
    ∃ g G, hearV R.f F x = some (g, G) ∧ HeardIs R g ∧ Inv R (stages R.f).length G ∧
      (∀ j, R.first + firstSlot R.f .leaves ≤ j →
        j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j) ∧
      RowsGood R g.rows G ∧
      (∀ cf : GE, Sums R .leaves (rd (R.claimed .leaves)) cf →
        ∀ (F' G' H : Fork) (y : Aff) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
          Sized F' → Later G F' → MaskedSum.row g.leaves oneE {} F' = some (y, G') →
          Later G' H → MasksAre R mask →
          y.value Reading.gl (H.worldOf Reading.gl mask entry) = rd g.leaves.eps * (1 - cf)) ∧
      PointsAgree R.f g R.a.base (R.t.heard ++ R.ds) :=
  lookHeard_of_stepsP SS LS R F x hF I0 (cut_of_rounds R x hF h)

/-- **CONDITIONAL ON `StageStep` AND ON `LeavesStep` (no member is typed here): the statement
`LookHeard` (Honest/K3/Law/Statements.lean), at its own name: at every face.** -/
theorem lookHeard (SS : StageStep) (LS : LeavesStep) : LookHeard := fun _ R F x hF I0 h =>
  let ⟨g, G, a, b, c, d, _⟩ := lookHeardP SS LS R F x hF I0 h
  ⟨g, G, a, b, c, d⟩

#print axioms ProofFile.Honest.K3.Parts.parts_pos
#print axioms ProofFile.Honest.K3.Parts.take_sum_succ
#print axioms ProofFile.Honest.K3.Parts.callP_tie0
#print axioms ProofFile.Honest.K3.Parts.callP_tieS
#print axioms ProofFile.Honest.K3.Parts.callP_split
#print axioms ProofFile.Honest.K3.Parts.callP_key
#print axioms ProofFile.Honest.K3.Parts.callP_tab
#print axioms ProofFile.Honest.K3.Parts.callP_leaves
#print axioms ProofFile.Honest.K3.Parts.callP_bits
#print axioms ProofFile.Honest.K3.Parts.sum_stepR
#print axioms ProofFile.Honest.K3.Parts.front_walkP
#print axioms ProofFile.Honest.K3.Parts.tie_walkP
#print axioms ProofFile.Honest.K3.Parts.form_split_last
#print axioms ProofFile.Honest.K3.Parts.parts_walk
#print axioms ProofFile.Honest.K3.Parts.join_walkP
#print axioms ProofFile.Honest.K3.Parts.tree_walk
#print axioms ProofFile.Honest.K3.Parts.trees_walk
#print axioms ProofFile.Honest.K3.Parts.tab_walkP
#print axioms ProofFile.Honest.K3.Parts.lookHeard_of_stepsP
#print axioms ProofFile.Honest.K3.Parts.lookHeardP
#print axioms ProofFile.Honest.K3.Parts.lookHeard

end ProofFile.Honest.K3.Parts
