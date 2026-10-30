-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/StageFacts.lean: the honest side of the kind "lookup" (K3).
What the proofs of the steps at a stage (Honest/K3/Law/StageStep.lean) need of a stage's call, of
its challenges and of the slots that its claimed form names. Theorems, with two definitions.

Terms. Honest/K3/GLOSSARY.md ("course", "form", "slot", "stage").

What is shown, by the file's sections.
  1. `wp_map_d`, `shapeOk_congr`, `ownSlots_congr`, `entries_drawE`: what of a call does not depend
     on its points.
  2. `shapeOk_stage`, `call_own`, `call_ends`: a stage's call in the run: its tests; its counts.
  3. `drawsFit_drop`, `drawsFit_take`, `fit_stage`, `drawsOk_stage`, `beta_ne`: a stage's
     challenges.
  4. `SlotsIn`, `form_slots`: the slots that a stage's claimed form names are end slots in front of
     it. `SlotsIn` has, but for the form's letter, the text of the library's
     `Kinds.Head.Law.SlotsAt` (Johnson/Desc/Kinds/Law/PlanesFormsInT.lean); the tie:
     `slotsIn_eq_slotsAt` (Honest/K3/Law/TiesSealedForms.lean [not in this library]). This folder
     has two more of the notion: `Names` (Honest/K3/Parts/NamesMarks.lean), `In`
     (Honest/K3/Parts/NamesOwn.lean).

Hypotheses that remain.
  `hF`, `hs`: `Fit R`; the stage is one of the row's. `hok`, `h`: the face passes the verifier's
    tests. `h`, `hl`, `he`: the stage's call is k; its lead is 0; it has end values.
  `hv`, `he`, `h`: (in section 1) two calls have the same degrees and end values.
  In section 4: `ha`, `hb`, `h`: `SlotsIn` of the forms that go in; Q at the slot. `h`, `hT`, `hS`,
    `hP`: `EndsIn` at the stage, at the tie's steps, at the parts' steps, at every stage in front.
    `hp`: Q at every plane's slot. `ht`, `h2`: the stage has two end values; two planes at least.
  `h` besides: in `map_one`: g is 1 everywhere; in `drawFit_parts`: the frame's test on one round
    accepts; in `ofTriple_ne`: the three words are not all 0. Seven theorems have hypotheses without
    a name: `shapeOk_shape`, `lead_zero`, `drawsFit_drop`, `drawsFit_take`, `drawsFit_counts`,
    `join_slots_fold`, `tab_slots`.

Imported. Honest/Law/Cut.lean.

Users. This file is imported by Honest/K3/FastLaw/Lift.lean, Honest/K3/Law/SpecNumbered.lean and
Honest/K3/Law/StageStep.lean.

Limits. Lemmas about definitions of the honest side.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Steps
import Johnson.Desc.ProofFile.Honest.K3.RowAt
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE isZeroE)
open OnBytes.Model (Reading Aff Fork eqTab)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call shapeOk ownSlots)
open VerifiableInference.Desc.K3 (entriesV)
open ProofFile.Honest.SumLaw (drawsOk varsOf ownOf)

variable {W : Type}

/-! ## 1 What of a call does not depend on its points -/

theorem wp_map_d : ∀ (vs : List Var) (zs : List E), (withPoints vs zs).map Var.d = vs.map Var.d
  | [], _ => rfl
  | .plain _ :: vs, zs => by simp [withPoints, wp_map_d vs zs]
  | .point _ _ :: vs, _ :: zs => by simp [withPoints, wp_map_d vs zs, Var.d]
  | .point _ _ :: vs, [] => by simp [withPoints, wp_map_d vs []]

theorem shapeOk_congr {k k' : Call} (hv : k.vs.map Var.d = k'.vs.map Var.d)
    (he : k.ends = k'.ends) :
    shapeOk k = shapeOk k' := by
  have h1 : ∀ vs : List Var, (vs.all fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) =
      ((vs.map Var.d).all fun d => decide (2 ≤ d) && decide (d ≤ 65)) := by
    intro vs
    rw [List.all_map]
    rfl
  have h2 : ∀ vs : List Var, vs.isEmpty = (vs.map Var.d).isEmpty := by
    intro vs
    cases vs <;> rfl
  unfold shapeOk
  rw [h1 k.vs, h1 k'.vs, h2 k.vs, h2 k'.vs, hv, he]

theorem all_map_d {k k' : Call} (hv : k.vs.map Var.d = k'.vs.map Var.d) (he : k.ends = k'.ends) :
    k.all.map Var.d = k'.all.map Var.d := by
  unfold Call.all
  rw [he]
  cases k'.ends <;> simp [hv]

theorem ownSlots_congr {vs vs' : List Var} (h : vs.map Var.d = vs'.map Var.d) :
    ownSlots vs = ownSlots vs' := by
  have e : ∀ l : List Var, (l.map fun v => v.d - 1) = (l.map Var.d).map (· - 1) := by
    intro l
    rw [List.map_map]
    rfl
  rw [ownSlots_eq, ownSlots_eq, e, e, h]

theorem map_one {α : Type} (g : α → Nat) (h : ∀ a, g a = 1) :
    ∀ l : List α, l.map g = List.replicate l.length 1
  | [] => rfl
  | a :: l => by rw [List.map_cons, h a, map_one g h l]; rfl

theorem entries_drawE (k : Call) :
    (MaskedSum.entries k).map (·.drawE) =
      1 :: (List.replicate k.vs.length 1 ++
        (match k.ends with
         | none => []
         | some _ => [1, 0])) := by
  unfold MaskedSum.entries
  cases k.ends <;> simp [MaskedSum.entry] <;> exact map_one _ (fun _ => rfl) _

/-! ## 2 A stage's call in the run -/

theorem one_le_mu_of_ok (f : LFace) (h : f.ok = true) : 1 ≤ f.mu := by
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1

theorem call_vs_d (R : Course W) (s : Stage) :
    (R.call s).vs.map Var.d = (shapeAt R.a s).vs.map Var.d := wp_map_d _ _

theorem call_ends (R : Course W) (s : Stage) : (R.call s).ends = (shapeAt R.a s).ends := rfl

theorem shapeAt_of {a : At} {s : Stage} {k : Call} (h : s.call a.face = some k) : shapeAt a s = k :=
    by
  unfold shapeAt
  rw [h]
  rfl

/-- The tests on the plan hold of every stage's shape. -/
theorem shapeOk_shape {f : LFace} (hok : f.ok = true) :
    ∀ (s : Stage) (k : Call), s.call f = some k → shapeOk k = true
  | .tie 0, k, h => by obtain rfl := Option.some.inj h; rfl
  | .tie (_ + 1), k, h => by obtain rfl := Option.some.inj h; rfl
  | .split _, k, h => by obtain rfl := Option.some.inj h; rfl
  | .key _ m, k, h => by
    obtain rfl := Option.some.inj h
    rw [levelCall_eq]
    simp [shapeOk, Var.d, VerifiableInference.Desc.First.ProdV.levelEnds]
  | .tab l, k, h => by
    obtain rfl := Option.some.inj h
    rw [levelCall_eq]
    simp [shapeOk, Var.d, VerifiableInference.Desc.First.ProdV.levelEnds]
  | .leaves, k, h => by
    obtain rfl := Option.some.inj h
    have := one_le_mu_of_ok f hok
    simp only [shapeOk, VerifiableInference.Desc.K3.leafVars, List.all_map, Bool.and_eq_true,
      List.all_eq_true, List.mem_range, Function.comp, Var.d, decide_eq_true_eq,
      Bool.not_eq_true', List.isEmpty_map]
    refine ⟨fun j _ => by split <;> omega, ?_⟩
    cases hn : f.mu + f.d with
    | zero => omega
    | succ n => simp [List.range_succ]
  | .bits, k, h => by
    obtain rfl := Option.some.inj h
    simp [shapeOk, VerifiableInference.Desc.K3.bitsCall, Var.d]

theorem shapeOk_stage (R : Course W) (hok : R.f.ok = true) {s : Stage} {k : Call}
    (h : s.call R.f = some k) : shapeOk (R.call s) = true := by
  rw [shapeOk_congr (call_vs_d R s) (call_ends R s), shapeAt_of h]
  exact shapeOk_shape hok s k h

/-- The sumcheck's own slots, counted at the call in the run, are the stage's. -/
theorem call_own (R : Course W) {s : Stage} {k : Call} (h : s.call R.f = some k) (hl : k.lead = 0) :
    ownSlots (R.call s).all = s.own R.f := by
  rw [ownSlots_congr (all_map_d (call_vs_d R s) (call_ends R s)), shapeAt_of h]
  simp [Stage.own, h, ownRun, hl]

theorem lead_zero {f : LFace} : ∀ (s : Stage) (k : Call), s.call f = some k → k.lead = 0
  | .tie 0, k, h => by obtain rfl := Option.some.inj h; rfl
  | .tie (_ + 1), k, h => by obtain rfl := Option.some.inj h; rfl
  | .split _, k, h => by obtain rfl := Option.some.inj h; rfl
  | .key _ _, k, h => by obtain rfl := Option.some.inj h; rfl
  | .tab _, k, h => by obtain rfl := Option.some.inj h; rfl
  | .leaves, k, h => by obtain rfl := Option.some.inj h; rfl
  | .bits, k, h => by obtain rfl := Option.some.inj h; rfl

/-! ## 3 A stage's challenges -/

theorem drawsFit_drop : ∀ (L : List Fmt.DeclaredRound) (ds : List Fmt.Drawn) (a : Nat),
    drawsFit L ds = true → drawsFit (L.drop a) (ds.drop a) = true
  | _, _, 0, h => by simpa using h
  | [], [], _ + 1, _ => by simp [drawsFit]
  | [], _ :: _, _ + 1, h => by simp [drawsFit] at h
  | _ :: _, [], _ + 1, h => by simp [drawsFit] at h
  | _ :: L, _ :: ds, a + 1, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    simpa using drawsFit_drop L ds a h.2

theorem drawsFit_take : ∀ (L : List Fmt.DeclaredRound) (ds : List Fmt.Drawn) (a : Nat),
    drawsFit L ds = true → drawsFit (L.take a) (ds.take a) = true
  | _, _, 0, _ => by simp [drawsFit]
  | [], [], _ + 1, _ => by simp [drawsFit]
  | [], _ :: _, _ + 1, h => by simp [drawsFit] at h
  | _ :: _, [], _ + 1, h => by simp [drawsFit] at h
  | _ :: L, _ :: ds, a + 1, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    simp only [List.take_succ_cons, drawsFit, Bool.and_eq_true]
    exact ⟨h.1, drawsFit_take L ds a h.2⟩

theorem drawFit_parts {d : Fmt.DeclaredRound} {R : Fmt.Drawn} (h : drawFit d R = true) :
    R.elems.length = d.entry.drawE ∧ R.poss.length = d.entry.poss ∧
      R.trits.length = d.entry.trits ∧ VerifiableInference.Desc.drawsMarkedNonzeroHaveNonzeroWords d ⟨[], R⟩ = true := by
  simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.2⟩

theorem drawsFit_counts : ∀ (es : List Fmt.Entry) (ds : List Fmt.Drawn),
    drawsFit (es.map declOf) ds = true → ds.map (·.elems.length) = es.map (·.drawE)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | e :: es, d :: ds, h => by
    simp only [List.map_cons, drawsFit, Bool.and_eq_true] at h
    simp only [List.map_cons]
    rw [(drawFit_parts h.1).1, drawsFit_counts es ds h.2]
    rfl

/-- A stage's own challenges pass the frame's test at the stage's own entries. -/
theorem fit_stage {R : Course W} (hF : Fit R) {s : Stage} (hs : s ∈ stages R.f) :
    drawsFit ((Stage.entries R.f s).map declOf) (R.draws s) = true := by
  have h := drawsFit_take _ _ (s.rounds R.f) (drawsFit_drop _ _ (firstRound R.f s) hF.draws)
  rw [← List.map_drop, ← List.map_take,
    entries_at R.f (two_le_planes_of_ok R.f hF.ok) s hs] at h
  exact h

/-- They are as many, each with as many elements, as the call in the run states. -/
theorem drawsOk_stage {R : Course W} (hF : Fit R) {s : Stage} (hs : s ∈ stages R.f) {k : Call}
    (h : s.call R.f = some k) : drawsOk (R.call s) (R.draws s) = true := by
  have h1 := drawsFit_counts _ _ (fit_stage hF hs)
  have h2 : Stage.entries R.f s = MaskedSum.entries k := by
    unfold Stage.entries
    rw [h]
  have h3 : (R.call s).vs.length = k.vs.length := by
    have := congrArg List.length (call_vs_d R s)
    rw [shapeAt_of h] at this
    simpa using this
  have h4 : (R.call s).ends = k.ends := by rw [call_ends, shapeAt_of h]
  unfold drawsOk
  rw [h1, h2, entries_drawE, entries_drawE, h3, h4]
  exact beq_self_eq_true _

/-- Behind as many entries as there are variables and one more, the last of the variables'
challenges is the entry that follows. -/
theorem last_of_take (y v : E) : ∀ (P : List E) (z : E),
    ((P ++ [y, v]).take (P.length + 1)).getLastD z = y
  | [], _ => rfl
  | a :: P, _ => by
    simp only [List.cons_append, List.length_cons, List.take_succ_cons, List.getLastD_cons]
    exact last_of_take y v P a

theorem ofTriple_ne {x : UInt64 × UInt64 × UInt64} (h : x ≠ (0, 0, 0)) :
    isZeroE (E.ofTriple x) = false := by
  cases hz : isZeroE (E.ofTriple x) with
  | false => rfl
  | true =>
    exfalso
    have e := congrArg E.triple (OnBytes.Model.isZeroE_eq hz)
    rw [OnBytes.E.triple_ofTriple] at e
    exact h e

/-- **Y's challenge is not 0**, at a stage with end values. -/
theorem beta_ne {R : Course W} (hF : Fit R) {s : Stage} (hs : s ∈ stages R.f) {k : Call} {e : Ends}
    (h : s.call R.f = some k) (he : k.ends = some e) :
    isZeroE ((R.r s).getLastD zeroE) = false := by
  have h0 := fit_stage hF hs
  have h2 : Stage.entries R.f s =
      ([MaskedSum.entry "PSC epsilon" (k.lead + 1) 1 0] ++
        (k.vs.map fun v => MaskedSum.entry "PSC round" (v.d - 1) 1 0)) ++
      [MaskedSum.entry "PSC Y" e.dY 1 1, MaskedSum.entry "PSC values" e.n 0 0] := by
    unfold Stage.entries MaskedSum.entries
    rw [h]
    simp only [he]
  rw [h2, List.map_append, drawsFit_append, Bool.and_eq_true] at h0
  obtain ⟨hA, hB⟩ := h0
  have hn : (([MaskedSum.entry "PSC epsilon" (k.lead + 1) 1 0] ++
      (k.vs.map fun v => MaskedSum.entry "PSC round" (v.d - 1) 1 0)).map declOf).length =
      k.vs.length + 1 := by
    simp
  rw [hn] at hA hB
  have hlen : ((R.draws s).take (k.vs.length + 1)).length = k.vs.length + 1 := by
    have := congrArg List.length (drawsFit_counts _ _ hA)
    simp only [List.length_map, List.length_append, List.length_cons, List.length_nil] at this
    omega
  rcases hd : (R.draws s).drop (k.vs.length + 1) with _ | ⟨dY, _ | ⟨dV, _ | ⟨_, _⟩⟩⟩
  · rw [hd] at hB; simp [drawsFit] at hB
  · rw [hd] at hB; simp [drawsFit] at hB
  · rw [hd] at hB
    simp only [List.map_cons, List.map_nil, drawsFit, Bool.and_eq_true] at hB
    obtain ⟨c1, _, _, c4⟩ := drawFit_parts hB.1
    have hall : (R.call s).all.length = k.vs.length + 1 := by
      have := congrArg List.length (all_map_d (call_vs_d R s) (call_ends R s))
      rw [shapeAt_of h] at this
      simp only [List.length_map] at this
      rw [this]
      unfold Call.all
      rw [he]
      simp
    have hsplit : R.draws s = (R.draws s).take (k.vs.length + 1) ++ [dY, dV] := by
      rw [← hd, List.take_append_drop]
    rcases hP : drawnE ((R.draws s).take (k.vs.length + 1)) with _ | ⟨p, P⟩
    · have := congrArg List.length hP
      simp only [drawnE, List.length_map, hlen, List.length_nil] at this
      omega
    · have hPl : P.length = k.vs.length := by
        have := congrArg List.length hP
        simp only [drawnE, List.length_map, hlen, List.length_cons] at this
        omega
      have hr : R.r s = (P ++ [(dY.elems.head?.map E.ofTriple).getD zeroE,
          (dV.elems.head?.map E.ofTriple).getD zeroE]).take (P.length + 1) := by
        unfold Course.r varsOf ownOf
        rw [hall, hsplit]
        have : drawnE ((R.draws s).take (k.vs.length + 1) ++ [dY, dV]) =
            drawnE ((R.draws s).take (k.vs.length + 1)) ++
              [(dY.elems.head?.map E.ofTriple).getD zeroE,
                (dV.elems.head?.map E.ofTriple).getD zeroE] := by
          simp [drawnE]
        rw [this, hP, hPl]
        rfl
      rw [hr, last_of_take]
      rcases hel : dY.elems with _ | ⟨x, _ | ⟨_, _⟩⟩
      · rw [hel] at c1; simp [declOf, MaskedSum.entry] at c1
      · simp only [List.head?_cons, Option.map_some, Option.getD_some]
        apply ofTriple_ne
        intro h0
        have hk : Fmt.kindOf "PSC Y" = some .elems := by decide
        unfold VerifiableInference.Desc.drawsMarkedNonzeroHaveNonzeroWords at c4
        simp only [declOf, MaskedSum.entry, hk, Option.any_some, hel] at c4
        subst h0
        simp [Fmt.dsElems] at c4
      · rw [hel] at c1; simp [declOf, MaskedSum.entry] at c1
  · rw [hd] at hB; simp [drawsFit] at hB

/-! ## 4 The slots that a form names -/

/-- Every slot that the form names has the property. -/
def SlotsIn (Q : Nat → Prop) (a : Aff) : Prop := ∀ x ∈ a.slots.toList, Q x.1

theorem slotsIn_const (Q : Nat → Prop) (v : E) : SlotsIn Q (Aff.ofConst v) := by
  intro x hx
  simp [Aff.ofConst] at hx

theorem slotsIn_empty (Q : Nat → Prop) : SlotsIn Q ({} : Aff) := by
  intro x hx
  simp at hx

theorem slotsIn_slot {Q : Nat → Prop} {j : Nat} (h : Q j) : SlotsIn Q (Aff.slot j) := by
  intro x hx
  have e : x = (j, oneE) := by simpa [Aff.slot] using hx
  rw [e]
  exact h

theorem slotsIn_addMul {Q : Nat → Prop} {a b : Aff} (ha : SlotsIn Q a) (hb : SlotsIn Q b) (k : E) :
    SlotsIn Q (Aff.addMul a b k) := by
  intro x hx
  simp only [Aff.addMul, OnBytes.Model.foldl_push_toList, List.mem_append, List.mem_map] at hx
  rcases hx with h | ⟨y, hy, rfl⟩
  · exact ha x h
  · exact hb y hy

theorem slotsIn_scale {Q : Nat → Prop} {a : Aff} (ha : SlotsIn Q a) (k : E) :
    SlotsIn Q (Aff.scale a k) := slotsIn_addMul (slotsIn_empty Q) ha k

theorem slotsIn_add {Q : Nat → Prop} {a b : Aff} (ha : SlotsIn Q a) (hb : SlotsIn Q b) :
    SlotsIn Q (a + b) := slotsIn_addMul ha hb oneE

section
variable (R : Course W) (Q : Nat → Prop)

/-- All end slots of a stage have the property. -/
def EndsIn (s : Stage) : Prop := ∀ j, j < s.tail R.f → Q (R.endSlot s + j)

theorem line_slots (s : Stage) (xi : E) (ht : s.tail R.f = 2) (h : EndsIn R Q s) :
    SlotsIn Q (R.line s xi) :=
  slotsIn_add (slotsIn_scale (slotsIn_slot (h 0 (by omega))) _)
    (slotsIn_scale (slotsIn_slot (h 1 (by omega))) _)

theorem plane_slot (h2 : 2 ≤ R.f.planes) (hT : ∀ k, k < R.f.planes - 1 → EndsIn R Q (.tie k))
    (j : Nat) : Q (R.planeSlot j) := by
  unfold Course.planeSlot
  by_cases h0 : j = 0
  · rw [if_pos h0]
    exact hT 0 (by omega) 2 (show 2 < 3 by omega)
  · rw [if_neg h0]
    by_cases h1 : j + 1 < R.f.planes
    · rw [if_pos h1]
      obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      exact hT (q + 1) (by omega) 1 (show 1 < 2 by omega)
    · rw [if_neg h1]
      by_cases h3 : R.f.planes = 2
      · rw [if_pos h3]
        exact hT 0 (by omega) 1 (show 1 < 3 by omega)
      · rw [if_neg h3]
        obtain ⟨q, hq⟩ : ∃ q, R.f.planes - 2 = q + 1 := ⟨R.f.planes - 3, by omega⟩
        rw [hq]
        exact hT (q + 1) (by omega) 0 (show 0 < 2 by omega)

theorem join_slots_fold (hp : ∀ j, Q (R.planeSlot j)) : ∀ (l : List Nat) (c : Aff), SlotsIn Q c →
    SlotsIn Q (l.foldl (fun (c : Aff) j =>
      if j < R.f.planes then
        Aff.addMul c (Aff.slot (R.planeSlot j)) ((eqTab R.pts.rhoT).getD j zeroE)
      else c + Aff.ofConst ((eqTab R.pts.rhoT).getD j zeroE)) c)
  | [], _, hc => hc
  | j :: l, c, hc => by
    simp only [List.foldl_cons]
    apply join_slots_fold hp l
    by_cases hj : j < R.f.planes
    · rw [if_pos hj]
      exact slotsIn_addMul hc (slotsIn_slot (hp j)) _
    · rw [if_neg hj]
      exact slotsIn_add hc (slotsIn_const Q _)

theorem tab_slots (h2 : 2 ≤ R.f.planes) (hT : ∀ k, k < R.f.planes - 1 → EndsIn R Q (.tie k)) :
    ∀ l, (∀ l', l' < l → EndsIn R Q (.tab l')) → SlotsIn Q (R.tabForm l)
  | 0, _ => join_slots_fold R Q (plane_slot R Q h2 hT) _ _ (slotsIn_const Q _)
  | l + 1, h => line_slots R Q (.tab l) _ rfl (h l (Nat.lt_succ_self l))

theorem root_slots (hT : EndsIn R Q (.tie 0))
    (hS : ∀ k, k < R.f.parts.length - 1 → EndsIn R Q (.split k)) (i : Nat) :
    SlotsIn Q (R.root i) := by
  unfold Course.root
  by_cases h0 : i + 1 < R.f.parts.length
  · rw [if_pos h0]
    exact slotsIn_slot (hS i (by omega) 0 (show 0 < 2 by omega))
  · rw [if_neg h0]
    by_cases h1 : R.f.parts.length ≤ 1
    · rw [if_pos h1]
      exact slotsIn_slot (hT 0 (show 0 < 3 by omega))
    · rw [if_neg h1]
      exact slotsIn_slot (hS _ (by omega) 1 (show 1 < 2 by omega))

/-- **The slots that a stage's claimed form names are end slots of stages in front of it.** -/
theorem form_slots (hok : R.f.ok = true) (s : Stage) (hs : s ∈ stages R.f)
    (hP : ∀ s', s' ∈ stages R.f → Fore s' s → EndsIn R Q s') : SlotsIn Q (R.form s) := by
  have h2 : 2 ≤ R.f.planes := two_le_planes_of_ok R.f hok
  match s, hs, hP with
  | .shift, _, _ => exact slotsIn_const Q _
  | .alpha, _, _ => exact slotsIn_const Q _
  | .join, _, _ => exact slotsIn_const Q _
  | .keyLine _ _, _, _ => exact slotsIn_const Q _
  | .tabLine _, _, _ => exact slotsIn_const Q _
  | .zero, _, _ => exact slotsIn_const Q _
  | .bits, _, _ => exact slotsIn_const Q _
  | .tie 0, _, _ => exact slotsIn_const Q _
  | .tie 1, _, hP =>
    exact slotsIn_slot (hP (.tie 0) (mem_tie (by omega)) (fore_mid rfl (show 0 < 1 by omega)) 1
      (show 1 < 3 by omega))
  | .tie (n + 2), hs, hP =>
    have hn := tie_lt hs
    exact slotsIn_slot (hP (.tie (n + 1)) (mem_tie (by omega))
      (fore_mid rfl (show n + 1 < n + 2 by omega)) 0 (show 0 < 2 by omega))
  | .split 0, _, hP =>
    exact slotsIn_slot (hP (.tie 0) (mem_tie (by omega)) (fore_grp (show 2 < 3 by omega)) 0
      (show 0 < 3 by omega))
  | .split (i + 1), hs, hP =>
    have hn := split_lt hs
    exact slotsIn_slot (hP (.split i) (mem_split (by omega))
      (fore_mid rfl (show i < i + 1 by omega)) 1 (show 1 < 2 by omega))
  | .key i 0, _, hP =>
    exact root_slots R Q (hP _ (mem_tie (by omega)) (fore_grp (show 2 < 5 by omega)))
      (fun k hk => hP _ (mem_split hk) (fore_grp (show 3 < 5 by omega))) i
  | .key i (m + 1), hs, hP =>
    have hm : Stage.key i m ∈ stages R.f := by
      obtain ⟨x, hx, hi, hlt⟩ := mem_key hs
      rw [hi]
      exact mem_keyOf hx (by omega)
    exact line_slots R Q (.key i m) _ rfl
      (hP _ hm (fore_last rfl rfl (show 2 * m < 2 * (m + 1) by omega)))
  | .tab l, hs, hP =>
    have hl := mem_tab hs
    exact tab_slots R Q h2 (fun k hk => hP _ (mem_tie hk) (fore_grp (show 2 < 6 by omega))) l
      (fun l' hl' => hP _ (mem_tabOf (by omega)) (fore_mid rfl hl'))
  | .leaves, _, hP =>
    exact tab_slots R Q h2 (fun k hk => hP _ (mem_tie hk) (fore_grp (show 2 < 7 by omega))) R.f.d
      (fun l' hl' => hP _ (mem_tabOf hl') (fore_grp (show 6 < 7 by omega)))

end

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.wp_map_d
#print axioms ProofFile.Honest.K3.Law.shapeOk_congr
#print axioms ProofFile.Honest.K3.Law.all_map_d
#print axioms ProofFile.Honest.K3.Law.ownSlots_congr
#print axioms ProofFile.Honest.K3.Law.map_one
#print axioms ProofFile.Honest.K3.Law.entries_drawE
#print axioms ProofFile.Honest.K3.Law.one_le_mu_of_ok
#print axioms ProofFile.Honest.K3.Law.call_vs_d
#print axioms ProofFile.Honest.K3.Law.call_ends
#print axioms ProofFile.Honest.K3.Law.shapeAt_of
#print axioms ProofFile.Honest.K3.Law.shapeOk_shape
#print axioms ProofFile.Honest.K3.Law.shapeOk_stage
#print axioms ProofFile.Honest.K3.Law.call_own
#print axioms ProofFile.Honest.K3.Law.lead_zero
#print axioms ProofFile.Honest.K3.Law.drawsFit_drop
#print axioms ProofFile.Honest.K3.Law.drawsFit_take
#print axioms ProofFile.Honest.K3.Law.drawFit_parts
#print axioms ProofFile.Honest.K3.Law.drawsFit_counts
#print axioms ProofFile.Honest.K3.Law.fit_stage
#print axioms ProofFile.Honest.K3.Law.drawsOk_stage
#print axioms ProofFile.Honest.K3.Law.last_of_take
#print axioms ProofFile.Honest.K3.Law.ofTriple_ne
#print axioms ProofFile.Honest.K3.Law.beta_ne
#print axioms ProofFile.Honest.K3.Law.slotsIn_const
#print axioms ProofFile.Honest.K3.Law.slotsIn_empty
#print axioms ProofFile.Honest.K3.Law.slotsIn_slot
#print axioms ProofFile.Honest.K3.Law.slotsIn_addMul
#print axioms ProofFile.Honest.K3.Law.slotsIn_scale
#print axioms ProofFile.Honest.K3.Law.slotsIn_add
#print axioms ProofFile.Honest.K3.Law.line_slots
#print axioms ProofFile.Honest.K3.Law.plane_slot
#print axioms ProofFile.Honest.K3.Law.join_slots_fold
#print axioms ProofFile.Honest.K3.Law.tab_slots
#print axioms ProofFile.Honest.K3.Law.root_slots
#print axioms ProofFile.Honest.K3.Law.form_slots
