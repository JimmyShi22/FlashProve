-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TokAsksOf.lean: CONDITIONAL.

Not shown here. That the plan's lists of points are what readsOf returns (h): a hypothesis;
K4Ground.reads (Johnson/Road/K4/W/Ground.lean) is it, at the verifier's layout. No example is
known. No property is claimed.

THE FAMILIES OF THE VERIFIER's LIST ARE OF THE SORTS THAT TokAsk NAMES, where the lists of points
are readsOf's. TokReads.lean asks (TokAsks) that no long family stands at the point "rt" and no
short one at "Y". By readsOf's text (OnBytes/Model/LayerLayout.lean) a long family's point is one
of "Z", "Z_V", "Y", "Z_a", "Z_b", and a short one's is one of "zt", "P_V", "r_tV", "rt"; tableAsks
(OnBytes/Model/LayerForms.lean) adds, in the first group, one long family at "Z_E".

  TokNames       no long list holds "rt", no short list holds "Y".
  tokAsk_long, tokAsk_short   the families of one matrix.
  tokAsks_of_names   TokAsks from TokNames.
  mem_ite, mem_long, mem_short   the members of readsOf's two sorts of list.
  tokNames_of_readsOf   TokNames of what readsOf returns.
  tokAsks_of_readsOf    TokAsks where the plan's lists are readsOf's.
-/
import Johnson.Road.K4.C.TokReads
import Johnson.Road.FormsKeysWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Reads TableAsk tableAsks readsOf)
open OnBytes.Desc.First.K4.Honest (K4Pub)

/-- No long list of points holds "rt", no short one holds "Y". This defines a hypothesis; the
definition claims nothing. -/
structure TokNames (rd : Reads) : Prop where
  af : ∀ n ∈ rd.rdAF, n ≠ "rt"
  qa : ∀ n ∈ rd.rdQA, n ≠ "rt"
  xi : ∀ n ∈ rd.rdXI, n ≠ "rt"
  xo : ∀ n ∈ rd.rdXO, n ≠ "rt"
  ad : ∀ n ∈ rd.rdAD, n ≠ "Y"
  ar : ∀ n ∈ rd.rdAR, n ≠ "Y"
  qs : ∀ n ∈ rd.rdQS, n ≠ "Y"

/-- The long families of one matrix. -/
theorem tokAsk_long {y : Lay} {mn : String} {M0 parts : ℕ} {pts : List String} {a : TableAsk}
    (ha : a ∈ Fo.famAsks y mn M0 parts pts true) (h : ∀ n ∈ pts, n ≠ "rt") : TokAsk a := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
  by_cases c : n = "Y"
  · exact Or.inr (Or.inr (Or.inl ⟨c, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h n hn, c⟩))

/-- The short families of one matrix. -/
theorem tokAsk_short {y : Lay} {mn : String} {M0 parts : ℕ} {pts : List String} {a : TableAsk}
    (ha : a ∈ Fo.famAsks y mn M0 parts pts false) (h : ∀ n ∈ pts, n ≠ "Y") : TokAsk a := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
  by_cases c : n = "rt"
  · exact Or.inr (Or.inl ⟨c, rfl⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨c, h n hn⟩))

/-- **TokAsks from TokNames.** -/
theorem tokAsks_of_names {Q : K4Pub} (N : TokNames Q.P.rd) : TokAsks Q := by
  intro a ha
  rw [Fo.tableAsks_eq] at ha
  rcases List.mem_append.mp ha with hb | hb
  · unfold Fo.preAsks at hb
    simp only [List.mem_append] at hb
    rcases hb with ((((((hb | hb) | hb) | hb) | hb) | hb) | hb) | hb
    · exact tokAsk_long hb N.af
    · exact tokAsk_long hb N.qa
    · exact tokAsk_long hb N.xi
    · split at hb
      · refine tokAsk_long hb fun n hn => ?_
        rw [List.mem_singleton.mp hn]
        decide
      · exact absurd hb List.not_mem_nil
    · exact tokAsk_long hb N.xo
    · exact tokAsk_short hb N.ad
    · exact tokAsk_short hb N.ar
    · split at hb
      · exact tokAsk_short hb N.qs
      · exact absurd hb List.not_mem_nil
  · left
    intro hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact absurd hn.1 (by simp [Fo.planeAsk])
    · exact absurd hn.2.1 (by simp [Fo.planeAsk])
    · exact absurd hn.2.2 (by simp [Fo.planeAsk])

/-- A member of a list that is there or not. -/
theorem mem_ite {c : Prop} [Decidable c] {l : List String} {n : String}
    (h : n ∈ (if c then l else [])) : n ∈ l := by
  split at h
  · exact h
  · exact absurd h List.not_mem_nil

/-- A member of a long list, as readsOf makes it, is not "rt". -/
theorem mem_long {c1 c2 c3 c4 c5 : Prop} [Decidable c1] [Decidable c2] [Decidable c3]
    [Decidable c4] [Decidable c5] {n : String}
    (h : n ∈ (if c1 then ["Z"] else []) ++ (if c2 then ["Z_V"] else []) ++
      (if c3 then ["Y"] else []) ++
      (if c4 then ["Z_a"] ++ (if c5 then ["Z_b"] else []) else [])) : n ≠ "rt" := by
  simp only [List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · rw [List.mem_singleton.mp (mem_ite h)]
    decide
  · rw [List.mem_singleton.mp (mem_ite h)]
    decide
  · rw [List.mem_singleton.mp (mem_ite h)]
    decide
  · rcases List.mem_append.mp (mem_ite h) with h | h
    · rw [List.mem_singleton.mp h]
      decide
    · rw [List.mem_singleton.mp (mem_ite h)]
      decide

/-- A member of a short list, as readsOf makes it, is not "Y". -/
theorem mem_short {c1 c2 c3 : Prop} [Decidable c1] [Decidable c2] [Decidable c3] {n : String}
    (h : n ∈ (if c1 then ["zt"] else []) ++ (if c2 then ["P_V", "r_tV"] else []) ++
      (if c3 then ["rt"] else [])) : n ≠ "Y" := by
  simp only [List.mem_append] at h
  rcases h with (h | h) | h
  · rw [List.mem_singleton.mp (mem_ite h)]
    decide
  · have h' := mem_ite h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl <;> decide
  · rw [List.mem_singleton.mp (mem_ite h)]
    decide

/-- **TokNames of what readsOf returns.** -/
theorem tokNames_of_readsOf {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) : TokNames rd := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  exact ⟨fun _ hn => mem_long hn, fun _ hn => mem_long hn, fun _ hn => mem_long hn,
    fun _ hn => mem_long hn, fun _ hn => mem_short hn, fun _ hn => mem_short hn,
    fun _ hn => mem_short hn⟩

/-- **TokAsks where the plan's lists of points are readsOf's.** -/
theorem tokAsks_of_readsOf {Q : K4Pub} (h : readsOf Q.P.y = .ok Q.P.rd) : TokAsks Q :=
  tokAsks_of_names (tokNames_of_readsOf h)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.tokAsk_long
#print axioms OnBytes.Road.K4.C.tokAsk_short
#print axioms OnBytes.Road.K4.C.tokAsks_of_names
#print axioms OnBytes.Road.K4.C.mem_ite
#print axioms OnBytes.Road.K4.C.mem_long
#print axioms OnBytes.Road.K4.C.mem_short
#print axioms OnBytes.Road.K4.C.tokNames_of_readsOf
#print axioms OnBytes.Road.K4.C.tokAsks_of_readsOf
