-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Gives.lean: the statement `GoodGives`
(Honest/K3/GoodDrawsLaw.lean), proved at its own name: where the test on a run's spots accepts, each
slot in that run's window is named, with a coefficient that is not 0, by a form of that run. At any
face with a level on the table side. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there spot, sample, good samples, window (a run's), stage, form
and slot. In this file: f is the lookup's face, lo the ledger's next slot in front of the lookup, rs
the rounds. A slot is live in a list of forms if some form names it with a coefficient that is not 0
(`liveIn`, Honest/K3/GoodDraws.lean). A stage's own slots are those of its sumcheck; its end slots
are those of its end values.

What is shown.
  `slotsIn_mono`, `end_lt`: a stage's end slots stand in front of every later stage's slots.
  `key_mem`, `tab_mem`: which levels of key trees, and of the table side, stand in the row.
  `spot_fine`, `eps_ne`, `var_ne`, `xi_ne`: what a run's test gives, spot by spot.
  `front_live`: a slot that a start form names is named by that sumcheck's row.
  `own_live`, `ends_live`: a stage's own slots; its end values' slots.
  `goodGives`: the statement.
Helpers: `sc_slot_self`, `line_live`, `part_pos`, `planes_le`, `part_at`, `vars_mem`, `runOf_key`,
`run_keyLine`, `runOf_tab`, `run_tabLine`, `planeSlot_inj`, `plane_live`, `z_live`, `ends_tie`,
`ends_split`, `ends_key`, `ends_tab`, `ok_of_fit` (the statement of `fit_ok`,
Honest/K3/FastLaw/Lift.lean, once more).

Hypotheses that remain. `goodGives` has none beside those inside `GoodGives`: the face has a level
on the table side (1 ≤ f.d); the rounds' samples are such as the rounds can sample (`canDraw`,
GoodDrawsLaw.lean); the hearing `hearV` returns on these rounds, from any ledger; `planesV` returns
behind it; `goodRun f r` accepts the samples. The theorems on the way take what they need of these
by name: `hg` (a run's test accepts), `H` and `S` (what the hearing leaves, whole or at one
sumcheck: `HeardOut`, Honest/K3/Good/Walk.lean; `SumOut`, Honest/K3/Good/Step.lean), `hpl` (the
leads of the claims on the planes), `hokf` (the face passes the verifier's tests), `hd` (1 ≤ f.d),
and, under `hs`, `hp`, `hr`, `hi`, `hj`, `hl`, `hm`, `hv` and their like, that a stage, a spot, a
part or a number is in range. Some of their hypotheses are neither of these nor ranges: `he`, `hC`
of `front_live` (a challenge's value is not 0; the start form's coefficient is not 0), `h0`, `h1` of
`line_live` (xi is neither 0 nor 1), `h` of `vars_mem` (what the list of spots is), `h` of
`planeSlot_inj`.

How the proof goes. Over `heard_out` (Honest/K3/Good/Walk.lean), which says what the hearing leaves,
stage by stage.

Users. Honest/K3/Good/MarkEvents.lean, Honest/K3/Good/Live/Pure.lean and
Honest/K3/Good/Live/Windows.lean import this file.

Limits. As the statement's own (the head of GoodDrawsLaw.lean): the claims on the planes are those
of `planesV`, of which the forms are the claims' leads; the caller's claim is read as the key side's
last form alone. That these are the forms of the claims that a seated sub-protocol states is not
shown here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE subE mulE okE isZeroE)
open OnBytes.Model (Fork Aff Reading)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (rowAff)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV planesV)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (atP_tie atP_split atP_join atP_key atP_tab atP_leaves atP_bits jSplit
    jJoin jKey jTab)

variable {f : LFace} {lo : Nat} {rs : List Fmt.RoundView}

/-! ## Order -/

theorem slotsIn_mono (f : LFace) {n n' : Nat} (h : n ≤ n') : slotsIn f n ≤ slotsIn f n' := by
  unfold slotsIn
  rw [List.map_take, List.map_take]
  have e : ((stages f).map (Stage.slots f)).take n =
      (((stages f).map (Stage.slots f)).take n').take n := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [e]
  exact sumTake_le _ n

/-- A stage's end slots stand in front of every later stage's slots. -/
theorem end_lt {n n' : Nat} {s s' : Stage} (hs : (stages f)[n]? = some s)
    (hs' : (stages f)[n']? = some s') (h : n < n') {i : Nat} (hi : i < s.tail f) :
    endOf f lo s + i < lo + firstSlot f s' := by
  obtain ⟨a1, a2⟩ := slotsIn_at hs
  obtain ⟨b1, _⟩ := slotsIn_at hs'
  have m := slotsIn_mono f (n := n + 1) (n' := n') h
  unfold endOf
  rw [a1, b1]
  rw [a2] at m
  unfold Stage.slots at m
  omega

/-! ## Which levels of key trees stand in the row -/

theorem key_mem {i m : Nat} (hs : Stage.key i m ∈ stages f) : ∃ v, f.parts[i]? = some v ∧ m < v :=
    by
  have h : ∃ x ∈ f.parts.zipIdx,
      Stage.key i m ∈ (List.range x.1).flatMap fun m => [Stage.key x.2 m, Stage.keyLine x.2 m] := by
    unfold stages at hs
    simp only [List.mem_append] at hs
    rcases hs with hs | h
    · rcases hs with hs | h
      · rcases hs with hs | h
        · exfalso
          by_cases hc : f.shifted = true <;> simp [hc] at hs
        · exact List.mem_flatMap.1 h
      · exfalso
        simp at h
    · exfalso
      simp at h
  obtain ⟨x, hx, h⟩ := h
  obtain ⟨m', hm', h'⟩ := List.mem_flatMap.1 h
  simp only [List.mem_cons, Stage.key.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h'
  obtain ⟨rfl, rfl⟩ := h'
  exact ⟨x.1, List.mem_zipIdx_iff_getElem?.1 hx, List.mem_range.1 hm'⟩

theorem tab_mem {l : Nat} (hs : Stage.tab l ∈ stages f) : l < f.d := by
  unfold stages at hs
  by_cases hc : f.shifted = true <;> simp [hc] at hs <;> exact hs

/-! ## What a run's test gives -/

theorem spot_fine {r : Run} {ds : List Fmt.Drawn} (hg : goodRun f r ds = true) {s : Stage}
    (hs : s ∈ stages f) {p : Spot} (hp : p ∈ spotsAt f s) (hr : p.run f = r) : p.fine f ds = true :=
    by
  unfold goodRun at hg
  refine List.all_eq_true.1 hg p (List.mem_filter.2 ⟨?_, by simp [hr]⟩)
  exact List.mem_flatMap.2 ⟨s, hs, hp⟩

theorem eps_ne {r : Run} (hg : goodRun f r (rs.map (·.drawn)) = true) {s : Stage}
    (hs : s ∈ stages f)
    (hp : (⟨s, 0, 0, false⟩ : Spot) ∈ spotsAt f s) (hr : (⟨s, 0, 0, false⟩ : Spot).run f = r) :
    vl (one rs (firstRound f s)) ≠ 0 := by
  have h := (ne_of_fine (spot_fine hg hs hp hr)).1
  rw [value_one] at h
  exact h

theorem var_ne {r : Run} (hg : goodRun f r (rs.map (·.drawn)) = true) {s : Stage}
    (hs : s ∈ stages f)
    {l : Nat} (hp : (⟨s, 1 + l, 0, false⟩ : Spot) ∈ spotsAt f s)
    (hr : (⟨s, 1 + l, 0, false⟩ : Spot).run f = r) : vl (one rs (firstRound f s + 1 + l)) ≠ 0 := by
  have h := (ne_of_fine (spot_fine hg hs hp hr)).1
  rw [value_one, ← Nat.add_assoc] at h
  exact h

theorem xi_ne {r : Run} (hg : goodRun f r (rs.map (·.drawn)) = true) {s : Stage} (hs : s ∈ stages f)
    (hp : (⟨s, 0, 0, true⟩ : Spot) ∈ spotsAt f s) (hr : (⟨s, 0, 0, true⟩ : Spot).run f = r) :
    vl (one rs (firstRound f s)) ≠ 0 ∧ vl (one rs (firstRound f s)) ≠ 1 := by
  have h := ne_of_fine (spot_fine hg hs hp hr)
  rw [value_one] at h
  exact ⟨h.1, h.2 rfl⟩

/-- A slot that a sumcheck's start form names is named by that sumcheck's row, where its eps is not
0. -/
theorem front_live {s : Stage} {C y : Aff} {sE j : Nat} (S : SumOut f lo rs s C y sE)
    (hj : j < lo + firstSlot f s) (he : vl (one rs (firstRound f s)) ≠ 0) (hC : sc C j ≠ 0) :
    sc y j ≠ 0 := by
  rw [S.front j hj]
  exact neg_ne_zero.2 (mul_ne_zero he hC)

theorem sc_slot_self (j : Nat) : sc (Aff.slot j) j ≠ 0 := by
  rw [sc_slot, if_pos rfl]
  exact one_ne_zero

/-- The two slots of the form behind a level, where xi is neither 0 nor 1. -/
theorem line_live (sE : Nat) {xi : E} (h0 : vl xi ≠ 0) (h1 : vl xi ≠ 1) {i : Nat} (hi : i < 2) :
    sc (lineForm sE xi) (sE + i) ≠ 0 := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · rw [Nat.add_zero, sc_line_first]
    exact sub_ne_zero.2 (Ne.symm h1)
  · rw [sc_line_second]
    exact h0

theorem part_pos (hokf : f.ok = true) {i v : Nat} (hv : f.parts[i]? = some v) : 1 ≤ v := by
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq] at hokf
  have h := hokf.1.1.1.2
  have := List.all_eq_true.1 h v (List.mem_of_getElem? hv)
  simpa using this

theorem planes_le (hokf : f.ok = true) : f.planes ≤ 2 ^ f.mu := by
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq] at hokf
  exact hokf.1.1.1.1.1.2

theorem part_at {i : Nat} (h : i < f.parts.length) : ∃ v, f.parts[i]? = some v :=
  ⟨f.parts[i], List.getElem?_eq_getElem h⟩

/-! ## A stage's own slots -/

theorem vars_mem {s : Stage} {pre : List Spot}
    (h : spotsAt f s = pre ++ (List.range (((s.call f).map (·.vs.length)).getD 0)).map
      fun l => (⟨s, 1 + l, 0, false⟩ : Spot)) {l : Nat}
    (hl : l < ((s.call f).map (·.vs.length)).getD 0) : (⟨s, 1 + l, 0, false⟩ : Spot) ∈ spotsAt f s
    := by
  rw [h]
  exact List.mem_append_right _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)

/-- **A stage's own slots are named by its row**, where the test on its run's spots accepts. -/
theorem own_live {g : HeardV} {pl : List PlaneClaim} {c : Aff} (H : HeardOut f lo rs g)
    (hpl : pl.map (·.lead) = [rowAff g.leaves oneE {}, Aff.slot g.sBit, c]) {s : Stage}
    (hs : s ∈ stages f) (hg : goodRun f (runOf f s false) (rs.map (·.drawn)) = true) {i : Nat}
    (hi : i < s.own f) : ∃ a ∈ formsOf g pl (runOf f s false), sc a (lo + firstSlot f s + i) ≠ 0 :=
    by
  cases s with
  | shift => exact absurd hi (Nat.not_lt_zero i)
  | alpha => exact absurd hi (Nat.not_lt_zero i)
  | join => exact absurd hi (Nat.not_lt_zero i)
  | keyLine a b => exact absurd hi (Nat.not_lt_zero i)
  | tabLine a => exact absurd hi (Nat.not_lt_zero i)
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | tie t =>
    obtain ⟨y, hy, S⟩ := H.tie t (tie_lt hs)
    refine ⟨y, hy, S.own (fun l hl => ?_) i hi⟩
    cases t <;> exact absurd hl (Nat.not_lt_zero l)
  | split a =>
    obtain ⟨y, hy, S⟩ := H.split a (split_lt hs)
    exact ⟨y, hy, S.own (fun l hl => absurd hl (Nat.not_lt_zero l)) i hi⟩
  | key a m =>
    obtain ⟨v, hv, hm⟩ := key_mem hs
    obtain ⟨y, hy, S⟩ := H.key a v m hv hm
    exact ⟨y, hy, S.own (fun l hl => var_ne hg hs (vars_mem (pre := [⟨.key a m, 0, 0, false⟩]) rfl
      hl)
      rfl) i hi⟩
  | tab l =>
    obtain ⟨sG, _, T, _⟩ := H.tab
    obtain ⟨y, hy, S⟩ := T l (tab_mem hs)
    exact ⟨y, hy, S.own (fun k hk => var_ne hg hs (vars_mem (pre := [⟨.tab l, 0, 0, false⟩]) rfl hk)
      rfl) i hi⟩
  | leaves =>
    obtain ⟨sG, _, _, L⟩ := H.tab
    refine ⟨rowAff g.leaves oneE {}, ?_, (L oneE).own (fun k hk =>
      var_ne hg hs (vars_mem (pre := [⟨.leaves, 0, 0, false⟩]) rfl hk) rfl) i hi⟩
    show _ ∈ pl.map (·.lead)
    rw [hpl]
    simp
  | bits =>
    obtain ⟨y, hy, S⟩ := H.bits
    exact ⟨y, hy, S.own (fun k hk => var_ne hg hs (vars_mem (pre := []) rfl hk) rfl) i hi⟩

/-! ## A stage's end values' slots -/

theorem runOf_key {i m v : Nat} (hv : f.parts[i]? = some v) :
    runOf f (.key i m) true = if m + 1 = v then Run.join else Run.objects := by
  have e : f.parts.getD i 0 = v := by rw [List.getD_eq_getElem?_getD, hv]; rfl
  show (if m + 1 == f.parts.getD i 0 then Run.join else Run.objects) = _
  rw [e]
  by_cases h : m + 1 = v <;> simp [h]

theorem run_keyLine {i m v : Nat} (hv : f.parts[i]? = some v) :
    (⟨.keyLine i m, 0, 0, true⟩ : Spot).run f = if m + 1 = v then Run.join else Run.objects := by
  have e : f.parts.getD i 0 = v := by rw [List.getD_eq_getElem?_getD, hv]; rfl
  show (if m + 1 == f.parts.getD i 0 then Run.join else Run.objects) = _
  rw [e]
  by_cases h : m + 1 = v <;> simp [h]

theorem runOf_tab (l : Nat) :
    runOf f (.tab l) true = if l + 1 = f.d then Run.planes else Run.objects := by
  show (if l + 1 == f.d then Run.planes else Run.objects) = _
  by_cases h : l + 1 = f.d <;> simp [h]

theorem run_tabLine (l : Nat) :
    (⟨.tabLine l, 0, 0, true⟩ : Spot).run f = if l + 1 = f.d then Run.planes else Run.objects := by
  show (if l + 1 == f.d then Run.planes else Run.objects) = _
  by_cases h : l + 1 = f.d <;> simp [h]

theorem planeSlot_inj {j j0 : Nat} (hj : j < f.planes) (h0 : j0 < f.planes)
    (h : planeSlot f lo j = planeSlot f lo j0) : j = j0 := by
  unfold planeSlot curOf at h
  split at h <;> split at h <;> omega

/-- **The slot of a real plane's root is named by the row of the table side's first level.** -/
theorem plane_live {g : HeardV} (hokf : f.ok = true) (hd : 1 ≤ f.d) (H : HeardOut f lo rs g)
    (hg : goodRun f .objects (rs.map (·.drawn)) = true) {j0 : Nat} (h0 : j0 < f.planes)
    (hlt : planeSlot f lo j0 < lo + firstSlot f (.tab 0)) :
    ∃ a ∈ g.rows.toList, sc a (planeSlot f lo j0) ≠ 0 := by
  obtain ⟨sG, hsG, T, _⟩ := H.tab
  obtain ⟨y, hy, S⟩ := T 0 hd
  have hs : Stage.tab 0 ∈ stages f := mem_at (atP_tab f hd).1
  refine ⟨y, hy, front_live S hlt (eps_ne hg hs (by simp [spotsAt]) rfl) ?_⟩
  show sc (ProofFile.Honest.K3.Forward.joinForm f sG (rhoOf f rs)) _ ≠ 0
  rw [← hsG j0 h0, sc_join f sG _ h0 (planes_le hokf)
    (fun j hj e => planeSlot_inj (lo := lo) hj h0 (by rw [← hsG j hj, ← hsG j0 h0]; exact e))]
  unfold rhoOf
  refine weight_ne _ ?_ ?_
  · have : (many rs (firstRound f .join)).toArray.size = f.mu := by simpa using H.rho
    rw [this]
    exact Nat.lt_of_lt_of_le h0 (planes_le hokf)
  · intro z hz
    have hz' : z ∈ many rs (firstRound f .join) := by simpa using hz
    obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.1 hz'
    have hk' : k < f.mu := by rw [← H.rho]; exact hk
    have hp : (⟨.join, 0, k, true⟩ : Spot) ∈ spotsAt f .join :=
      List.mem_map.2 ⟨k, List.mem_range.2 hk', rfl⟩
    have a := ne_of_fine (spot_fine hg (mem_at (atP_join f)) hp rfl)
    rw [value_many] at a
    have ev : (many rs (firstRound f .join + 0)).getD k zeroE = z := by
      rw [Nat.add_zero, List.getD_eq_getElem _ _ hk]
      exact e
    rw [ev] at a
    exact ⟨a.1, a.2 rfl⟩

/-- The slot of the key side's whole product is named by the row of the sumcheck that starts from
it. -/
theorem z_live {g : HeardV} (hokf : f.ok = true) (H : HeardOut f lo rs g)
    (hg : goodRun f .objects (rs.map (·.drawn)) = true) (h2 : 2 ≤ f.planes)
    (hL : 1 ≤ f.parts.length) :
    ∃ a ∈ g.rows.toList, sc a (e0 f lo) ≠ 0 := by
  have ht : (stages f)[iTie f 0]? = some (Stage.tie 0) := atP_tie f (by omega)
  have hb : ∀ {n' : Nat} {s' : Stage}, (stages f)[n']? = some s' → iTie f 0 < n' →
      e0 f lo < lo + firstSlot f s' := by
    intro n' s' hs' hn
    have := end_lt (lo := lo) ht hs' hn (i := 0) (by rw [tail_tie0]; omega)
    simpa [e0] using this
  by_cases h1 : f.parts.length = 1
  · obtain ⟨v, hv⟩ := part_at (f := f) (i := 0) (by omega)
    obtain ⟨y, hy, S⟩ := H.key 0 v 0 hv (part_pos hokf hv)
    have hk := (atP_key f hv (part_pos hokf hv)).1
    refine ⟨y, hy, front_live S (hb hk (by unfold iTie jKey jJoin jSplit; omega))
      (eps_ne hg (mem_at hk) (by simp [spotsAt]) rfl) ?_⟩
    have e : keyStart f lo rs 0 0 = Aff.slot (e0 f lo) := by
      show rootOf f lo 0 = _
      unfold rootOf
      rw [if_neg (by omega), h1]
      rfl
    rw [e]
    exact sc_slot_self _
  · have hi : 0 < f.parts.length - 1 := by omega
    obtain ⟨y, hy, S⟩ := H.split 0 hi
    have hk := atP_split f hi
    exact ⟨y, hy, front_live S (hb hk (by unfold iTie jSplit; omega))
      (eps_ne hg (mem_at hk) (by simp [spotsAt]) rfl) (sc_slot_self _)⟩

/-- The end values' slots of a step of the tie. -/
theorem ends_tie {g : HeardV} (hokf : f.ok = true) (hd : 1 ≤ f.d) (H : HeardOut f lo rs g)
    (hg : goodRun f .objects (rs.map (·.drawn)) = true) {t : Nat} (ht : t < f.planes - 1) {i : Nat}
    (hi : i < (Stage.tie t).tail f) : ∃ a ∈ g.rows.toList, sc a (endOf f lo (.tie t) + i) ≠ 0 := by
  have h2 : 2 ≤ f.planes := two_le_planes_of_ok f hokf
  have hL : 1 ≤ f.parts.length := by
    cases hp : f.parts with
    | nil =>
      simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq] at hokf
      have := hokf.1.1.1.1.2
      simp [hp] at this
    | cons a l => simp
  have hat := atP_tie f ht
  have hbT : endOf f lo (.tie t) + i < lo + firstSlot f (.tab 0) :=
    end_lt hat (atP_tab f hd).1 (by unfold iTie jTab jJoin jSplit; omega) hi
  -- a slot of the chain: named by the next step's row
  have chain : ∀ k, k + 1 < f.planes - 1 → curOf f lo k = endOf f lo (.tie t) + i → t ≤ k →
      ∃ a ∈ g.rows.toList, sc a (endOf f lo (.tie t) + i) ≠ 0 := by
    intro k hk e htk
    obtain ⟨y, hy, S⟩ := H.tie (k + 1) hk
    have hk' := atP_tie f hk
    refine ⟨y, hy, front_live S (end_lt hat hk' (by unfold iTie; omega) hi)
      (eps_ne hg (mem_at hk') (by simp [spotsAt]) rfl) ?_⟩
    rw [← e]
    exact sc_slot_self _
  have plane : ∀ j0, j0 < f.planes → planeSlot f lo j0 = endOf f lo (.tie t) + i →
      ∃ a ∈ g.rows.toList, sc a (endOf f lo (.tie t) + i) ≠ 0 := by
    intro j0 h0 e
    rw [← e]
    exact plane_live hokf hd H hg h0 (by rw [e]; exact hbT)
  cases t with
  | zero =>
    have hi' : i < 3 := by rw [tail_tie0] at hi; exact hi
    have he : endOf f lo (.tie 0) = e0 f lo := rfl
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    · rw [he, Nat.add_zero]
      exact z_live hokf H hg h2 hL
    · by_cases hp : f.planes = 2
      · refine plane 1 (by omega) ?_
        unfold planeSlot curOf
        split <;> omega
      · refine chain 0 (by omega) ?_ (Nat.le_refl 0)
        unfold curOf
        omega
    · refine plane 0 (by omega) ?_
      unfold planeSlot curOf
      split <;> omega
  | succ t =>
    have hi' : i < 2 := by rw [tail_tieS] at hi; exact hi
    have he : endOf f lo (.tie (t + 1)) = e0 f lo + 6 * t + 7 := endOf_tie ht
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · by_cases hp : t + 2 < f.planes - 1
      · refine chain (t + 1) hp ?_ (Nat.le_refl _)
        unfold curOf
        omega
      · refine plane (f.planes - 1) (by omega) ?_
        unfold planeSlot curOf
        split <;> omega
    · refine plane (t + 1) (by omega) ?_
      unfold planeSlot curOf
      split <;> omega

/-- The end values' slots of one of the parts' steps. -/
theorem ends_split {g : HeardV} (hokf : f.ok = true) (H : HeardOut f lo rs g)
    (hg : goodRun f .objects (rs.map (·.drawn)) = true) {a : Nat} (ha : a < f.parts.length - 1)
    {i : Nat} (hi : i < (Stage.split a).tail f) :
    ∃ y ∈ g.rows.toList, sc y (endOf f lo (.split a) + i) ≠ 0 := by
  have hat := atP_split f ha
  have hi' : i < 2 := hi
  -- the root of a part: named by the row of its key tree's first level
  have root : ∀ b, a ≤ b → b < f.parts.length →
      rootOf f lo b = Aff.slot (endOf f lo (.split a) + i) →
      ∃ y ∈ g.rows.toList, sc y (endOf f lo (.split a) + i) ≠ 0 := by
    intro b hab hb e
    obtain ⟨v, hv⟩ := part_at hb
    obtain ⟨y, hy, S⟩ := H.key b v 0 hv (part_pos hokf hv)
    have hk := (atP_key f hv (part_pos hokf hv)).1
    refine ⟨y, hy, front_live S (end_lt hat hk (by unfold jKey jJoin jSplit; omega) hi)
      (eps_ne hg (mem_at hk) (by simp [spotsAt]) rfl) ?_⟩
    show sc (rootOf f lo b) _ ≠ 0
    rw [e]
    exact sc_slot_self _
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · refine root a (Nat.le_refl a) (by omega) ?_
    unfold rootOf
    rw [if_pos (by omega), Nat.add_zero]
  · by_cases hn : a + 1 < f.parts.length - 1
    · obtain ⟨y, hy, S⟩ := H.split (a + 1) hn
      have hk := atP_split f hn
      exact ⟨y, hy, front_live S (end_lt hat hk (by unfold jSplit; omega) hi)
        (eps_ne hg (mem_at hk) (by simp [spotsAt]) rfl) (sc_slot_self _)⟩
    · refine root (a + 1) (by omega) (by omega) ?_
      unfold rootOf
      have e : f.parts.length - 1 = a + 1 := by omega
      rw [if_neg (by omega), e]
      rfl

/-- The end values' slots of a level of a key tree. -/
theorem ends_key {g : HeardV} {pl : List PlaneClaim} (H : HeardOut f lo rs g) {a m v : Nat}
    (hv : f.parts[a]? = some v) (hm : m < v)
    (hg : goodRun f (runOf f (.key a m) true) (rs.map (·.drawn)) = true) {i : Nat} (hi' : i < 2) :
    ∃ y ∈ formsOf g pl (runOf f (.key a m) true), sc y (endOf f lo (.key a m) + i) ≠ 0 := by
  obtain ⟨hat, hline⟩ := atP_key f hv hm
  have hi : i < (Stage.key a m).tail f := hi'
  rw [runOf_key hv] at hg ⊢
  by_cases hl : m + 1 = v
  · rw [if_pos hl] at hg ⊢
    obtain ⟨y, hy, e⟩ := H.keys a v hv
    obtain ⟨x0, x1⟩ := xi_ne hg (mem_at hline) (by simp [spotsAt])
      (by rw [run_keyLine hv, if_pos hl])
    refine ⟨y.2, List.mem_map.2 ⟨y, hy, rfl⟩, ?_⟩
    rw [e, ← hl]
    exact line_live _ x0 x1 hi'
  · rw [if_neg hl] at hg ⊢
    have hm' : m + 1 < v := by omega
    obtain ⟨y, hy, S⟩ := H.key a v (m + 1) hv hm'
    have hk := (atP_key f hv hm').1
    obtain ⟨x0, x1⟩ := xi_ne hg (mem_at hline) (by simp [spotsAt])
      (by rw [run_keyLine hv, if_neg hl])
    exact ⟨y, hy, front_live S (end_lt hat hk (by unfold jKey; omega) hi)
      (eps_ne hg (mem_at hk) (by simp [spotsAt]) rfl) (line_live _ x0 x1 hi')⟩

/-- The end values' slots of a level of the table side. -/
theorem ends_tab {g : HeardV} {pl : List PlaneClaim} {c : Aff} (H : HeardOut f lo rs g)
    (hpl : pl.map (·.lead) = [rowAff g.leaves oneE {}, Aff.slot g.sBit, c]) {l : Nat} (hl : l < f.d)
    (hg : goodRun f (runOf f (.tab l) true) (rs.map (·.drawn)) = true) {i : Nat} (hi' : i < 2) :
    ∃ y ∈ formsOf g pl (runOf f (.tab l) true), sc y (endOf f lo (.tab l) + i) ≠ 0 := by
  obtain ⟨hat, hline⟩ := atP_tab f hl
  have hi : i < (Stage.tab l).tail f := hi'
  obtain ⟨sG, _, T, L⟩ := H.tab
  rw [runOf_tab] at hg ⊢
  by_cases hd' : l + 1 = f.d
  · rw [if_pos hd'] at hg ⊢
    obtain ⟨x0, x1⟩ := xi_ne hg (mem_at hline) (by simp [spotsAt])
      (by rw [run_tabLine, if_pos hd'])
    have hk := atP_leaves f
    refine ⟨rowAff g.leaves oneE {}, ?_, front_live (L oneE)
      (end_lt hat hk (by unfold jTab; omega) hi)
      (eps_ne hg (mem_at hk) (by simp [spotsAt]) rfl) ?_⟩
    · show _ ∈ pl.map (·.lead)
      rw [hpl]
      simp
    · rw [← hd']
      exact line_live _ x0 x1 hi'
  · rw [if_neg hd'] at hg ⊢
    have hl' : l + 1 < f.d := by omega
    obtain ⟨y, hy, S⟩ := T (l + 1) hl'
    have hk := (atP_tab f hl').1
    obtain ⟨x0, x1⟩ := xi_ne hg (mem_at hline) (by simp [spotsAt])
      (by rw [run_tabLine, if_neg hd'])
    exact ⟨y, hy, front_live S (end_lt hat hk (by unfold jTab; omega) hi)
      (eps_ne hg (mem_at hk) (by simp [spotsAt]) rfl) (line_live _ x0 x1 hi')⟩

/-- **A stage's end values' slots are named by a form of their run**, where the test on that run's
spots accepts. -/
theorem ends_live {g : HeardV} {pl : List PlaneClaim} {c : Aff} (hokf : f.ok = true) (hd : 1 ≤ f.d)
    (H : HeardOut f lo rs g)
    (hpl : pl.map (·.lead) = [rowAff g.leaves oneE {}, Aff.slot g.sBit, c]) {s : Stage}
    (hs : s ∈ stages f) (hg : goodRun f (runOf f s true) (rs.map (·.drawn)) = true) {i : Nat}
    (hi : i < s.tail f) : ∃ a ∈ formsOf g pl (runOf f s true), sc a (endOf f lo s + i) ≠ 0 := by
  cases s with
  | shift => exact absurd hi (Nat.not_lt_zero i)
  | alpha => exact absurd hi (Nat.not_lt_zero i)
  | join => exact absurd hi (Nat.not_lt_zero i)
  | keyLine a b => exact absurd hi (Nat.not_lt_zero i)
  | tabLine a => exact absurd hi (Nat.not_lt_zero i)
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | leaves => exact absurd hi (Nat.not_lt_zero i)
  | bits =>
    have hi' : i < 1 := hi
    obtain rfl : i = 0 := by omega
    refine ⟨Aff.slot g.sBit, ?_, ?_⟩
    · show _ ∈ pl.map (·.lead)
      rw [hpl]
      simp
    · rw [H.sBit, Nat.add_zero]
      exact sc_slot_self _
  | tie t => exact ends_tie hokf hd H hg (tie_lt hs) hi
  | split a => exact ends_split hokf H hg (split_lt hs) hi
  | key a m =>
    obtain ⟨v, hv, hm⟩ := key_mem hs
    exact ends_key H hv hm hg hi
  | tab l => exact ends_tab H hpl (tab_mem hs) hg hi

/-! ## The statement -/

/-- Challenges that the rounds can sample have their elements' words below the prime. -/
theorem ok_of_fit : ∀ (L : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit L ds = true →
    ∀ d ∈ ds, ∀ x ∈ d.elems, okE (E.ofTriple x) = true
  | [], [], _, d, hd, _, _ => by simp at hd
  | [], _ :: _, h, _, _, _, _ => by simp [drawsFit] at h
  | _ :: _, [], h, _, _, _, _ => by simp [drawsFit] at h
  | c :: L, R :: Rs, h, d, hd, x, hx => by
    simp only [drawsFit, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hd with rfl | hd'
    · have h1 := h.1
      simp only [drawFit, Bool.and_eq_true] at h1
      have h2 := List.all_eq_true.1 h1.1.2 x hx
      exact h2
    · exact ok_of_fit L Rs h.2 d hd' x hx

/-- **The statement `GoodGives` (Honest/K3/GoodDrawsLaw.lean), at its own name.** No hypothesis
beside its own. -/
theorem goodGives : GoodGives := by
  intro f F G G' rs g pl hd hc hh hp r hg j hj
  obtain ⟨hokf, hm⟩ := hearV_messages hh
  have hok : Ok rs := fun r0 hr0 x hx =>
    ok_of_fit _ _ hc r0.drawn (List.mem_map.2 ⟨r0, hr0, rfl⟩) x hx
  have H := heard_out hokf hok hm
  have hpl : ∃ c, pl.map (·.lead) = [rowAff g.leaves oneE {}, Aff.slot g.sBit, c] := by
    unfold planesV at hp
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hp
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1', _⟩ := e
    have hy' : MaskedSum.row g.leaves oneE {} G = some (y.1, y.2) := hy
    rw [← e1', ← MaskedSum.row_spec hy']
    exact ⟨_, rfl⟩
  obtain ⟨c, hpl⟩ := hpl
  rw [live_iff]
  unfold windowOf at hj
  obtain ⟨s, hs, hj⟩ := List.mem_flatMap.1 hj
  rcases List.mem_append.1 hj with h1 | h1
  · split at h1
    · rename_i hr
      obtain rfl : runOf f s false = r := by simpa using hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
      rw [← Nat.add_assoc]
      exact own_live H hpl hs hg (List.mem_range.1 hi)
    · simp at h1
  · split at h1
    · rename_i hr
      obtain rfl : runOf f s true = r := by simpa using hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
      have e : F.next + (firstSlot f s + s.own f + i) = endOf f F.next s + i := by
        unfold endOf
        omega
      rw [e]
      exact ends_live hokf hd H hpl hs hg (List.mem_range.1 hi)
    · simp at h1

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.slotsIn_mono
#print axioms ProofFile.Honest.K3.Good.end_lt
#print axioms ProofFile.Honest.K3.Good.key_mem
#print axioms ProofFile.Honest.K3.Good.tab_mem
#print axioms ProofFile.Honest.K3.Good.spot_fine
#print axioms ProofFile.Honest.K3.Good.eps_ne
#print axioms ProofFile.Honest.K3.Good.var_ne
#print axioms ProofFile.Honest.K3.Good.xi_ne
#print axioms ProofFile.Honest.K3.Good.front_live
#print axioms ProofFile.Honest.K3.Good.sc_slot_self
#print axioms ProofFile.Honest.K3.Good.line_live
#print axioms ProofFile.Honest.K3.Good.part_pos
#print axioms ProofFile.Honest.K3.Good.planes_le
#print axioms ProofFile.Honest.K3.Good.part_at
#print axioms ProofFile.Honest.K3.Good.vars_mem
#print axioms ProofFile.Honest.K3.Good.own_live
#print axioms ProofFile.Honest.K3.Good.runOf_key
#print axioms ProofFile.Honest.K3.Good.run_keyLine
#print axioms ProofFile.Honest.K3.Good.runOf_tab
#print axioms ProofFile.Honest.K3.Good.run_tabLine
#print axioms ProofFile.Honest.K3.Good.planeSlot_inj
#print axioms ProofFile.Honest.K3.Good.plane_live
#print axioms ProofFile.Honest.K3.Good.z_live
#print axioms ProofFile.Honest.K3.Good.ends_tie
#print axioms ProofFile.Honest.K3.Good.ends_split
#print axioms ProofFile.Honest.K3.Good.ends_key
#print axioms ProofFile.Honest.K3.Good.ends_tab
#print axioms ProofFile.Honest.K3.Good.ends_live
#print axioms ProofFile.Honest.K3.Good.ok_of_fit
#print axioms ProofFile.Honest.K3.Good.goodGives
