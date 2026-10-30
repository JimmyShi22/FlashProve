-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/EndsThere.lean: CONDITIONAL. Statements with their proofs.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: THE VALUES THAT THE
SECOND TOKEN SUMCHECK SHOWS ARE MADE (`endsOn`, Johnson/Desc/K4/Honest/Sides.lean), on reads that
hold the weights of the tables at the point rt, and they are as many as the verifier counts
(`nEndT`).
How. The honest side values the verifier's own claims on these values (`termsForms`,
OnBytes/Desc/First/K4/Claims.lean). Each is a slot less a form of one of three readers at rt. Every
entry that such a form names lies in a table at rt (`inTest_terms`: EntsAt.lean's walk, carried on
to the reciprocal of a norm's row after Below.lean's `below_rowR` and `below_terms`); a form that
names only entries whose weights the reads hold is valued (`valued_of_inTest`, StackDataOf.lean).

Not shown here. `PtAt` is a hypothesis (PtsHave.lean pays it at the honest reads). That `termsForms`
returns (TermsFormsOf.lean). The count is shown for a model with routed experts (hp3). A RETURN AND
A NUMBER: nothing on what a value is worth. Nothing on soundness, on completeness or on any other
property. No property is claimed.

  `inTest_rowCells`, `inTest_rowR`, `inTest_terms`   the walk
  `terms_len`   the claims are as many as the verifier counts
  `endsOn_there`   **the values are made, and how many**
-/
import Johnson.Road.K4.C.StackDataOf
import Johnson.Road.K4.C.PanelsOf
import Johnson.Road.K4.Reads.TermsEnts
import Johnson.Road.K4.Reads.NormsEnts
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model.Layer (Env Heard nEndT aff0)
open OnBytes.Desc.First.K4 (termsForms)
open OnBytes.Desc.First.K4.Reads (EntsIn entsIn_ofConst entsIn_slot entsIn_add entsIn_sub
  entsIn_scale entsIn_addMul entsIn_foldl entsIn_ledDig all_mapM)
open OnBytes.Desc.First.K4.Slots (Gives)
open OnBytes.Desc.First.K4.Honest (Sides valAff? endsOn)

variable {v : Env} {T : ℕ → Prop} {S : String → Prop}

/-- The cells of a norm's row at the point rt. -/
theorem inTest_rowCells (H : PtAt v T S) (hrt : S "rt") {i n : ℕ} {cells : Array Aff}
    (h : v.rowCells "rt" i n = some cells) (j : ℕ) : InTest v T (cells.getD j aff0) := by
  unfold Env.rowCells at h
  obtain ⟨t, ht, h⟩ := bind_some h
  obtain ⟨tr, -, h⟩ := bind_some h
  have hs : StartAt v T t := H "ar" (by simp) "rt" t hrt ht
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : j < ys.length
  · have e : ys.toArray.getD j aff0 = ys[j] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := InTest v T) (fun _ _ hb => inTest_U3at hs _ _ hb) _ ys hys _
      (List.getElem_mem hj)
  · have e : ys.toArray.getD j aff0 = aff0 := by simp [Array.getD, hj]
    rw [e]
    exact entsIn_ofConst _

/-- **The reciprocal of a norm's row at the point rt.** After `below_rowR` (Below.lean). -/
theorem inTest_rowR (H : PtAt v T S) (hrt : S "rt") (i : ℕ) :
    Gives (v.rowR "rt" i) (InTest v T) := by
  intro f h
  unfold Env.rowR at h
  split at h
  · obtain ⟨r, hr, e⟩ := map_some h
    subst e
    unfold Env.row5At at hr
    obtain ⟨cells, hc, hr⟩ := bind_some hr
    obtain rfl : row5 (fun j => cells.getD j aff0) = r := Option.some.inj hr
    have hD : ∀ j, InTest v T ((Array.ofFn (n := 99) fun j : Fin 99 =>
        (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE)) := by
      intro j
      by_cases hj : j < 99
      · have e : (Array.ofFn (n := 99) fun j : Fin 99 =>
            (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE) =
            LedK.add (cells.getD j aff0) (LedK.c (ofNat 128)) := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_add (inTest_rowCells H hrt hc j) (entsIn_ofConst _)
      · have e : (Array.ofFn (n := 99) fun j : Fin 99 =>
            (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE) =
            LedK.c zeroE := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_ofConst _
    exact entsIn_add (entsIn_ledDig hD 80 3) (entsIn_scale _ (entsIn_ledDig hD 83 3))
  · obtain ⟨r, hr, e⟩ := map_some h
    subst e
    unfold Env.rowAt at hr
    obtain ⟨cells, hc, hr⟩ := bind_some hr
    have hr' := Option.some.inj hr
    subst hr'
    have hD : ∀ j, InTest v T ((cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0) := by
      intro j
      by_cases hj : j < cells.size
      · have e : (cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0 =
            cells.getD j aff0 + Aff.ofConst (ofNat 128) := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_add (inTest_rowCells H hrt hc j) (entsIn_ofConst _)
      · have e : (cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0 = aff0 := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_ofConst _
    have dg : ∀ a n, InTest v T
        (Env.digits (cells.map fun a => a + Aff.ofConst (ofNat 128)) a n) := fun a n =>
      entsIn_foldl _ (fun _ _ hf => entsIn_addMul _ hf (hD _)) _ _ (entsIn_ofConst _)
    exact entsIn_add (dg 57 3) (entsIn_scale _ (dg 60 3))

/-- **Every claim on the second token sumcheck's end values.** After `below_terms` (Below.lean). -/
theorem inTest_terms (H : PtAt v T S) (hrt : S "rt") {Hd : Heard} {l : List Aff}
    (h : termsForms v Hd = some l) : ∀ a ∈ l, InTest v T a := by
  unfold termsForms at h
  obtain ⟨tT, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : a ++ b ++ c = l := Option.some.inj h
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · rcases List.mem_append.mp hf with hf | hf
    · refine all_mapM (Pr := InTest v T) (fun i y hy => ?_) _ a a1 f hf
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
      exact entsIn_sub (entsIn_slot _) (inTest_rowR H hrt _ _ hx)
    · refine all_mapM (Pr := InTest v T) (fun i y hy => ?_) _ b a2 f hf
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
      exact entsIn_sub (entsIn_slot _) (at_shA H _ hrt _ _ _ hx)
  · refine all_mapM (Pr := InTest v T) (fun i y hy => ?_) _ c a3 f hf
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
    exact entsIn_sub (entsIn_slot _) (at_shA H _ hrt _ _ _ hx)

/-- The claims are as many as the verifier counts, with routed experts. -/
theorem terms_len (hp3 : v.y.h.p3 = true) {Hd : Heard} {l : List Aff}
    (h : termsForms v Hd = some l) : l.length = nEndT v.y := by
  unfold termsForms at h
  obtain ⟨tT, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : a ++ b ++ c = l := Option.some.inj h
  have e1 := optMapM_len _ _ a1
  have e2 := optMapM_len _ _ a2
  have e3 := optMapM_len _ _ a3
  rw [List.length_range] at e1 e2 e3
  unfold nEndT
  rw [if_pos hp3, List.length_append, List.length_append, e1, e2, e3, Nat.mul_add, Nat.mul_one,
    Nat.add_assoc]

/-- CONDITIONAL on every hypothesis named. **THE VALUES THAT THE SECOND TOKEN SUMCHECK SHOWS ARE
MADE, AND THEY ARE AS MANY AS THE VERIFIER COUNTS.** -/
theorem endsOn_there {Sd : Sides} {R : OnBytes.Desc.First.K4.Honest.Reads} {Hd : Heard}
    (hE : termsForms Sd.v Hd = some Sd.ends) (hp3 : Sd.v.y.h.p3 = true)
    (H : PtAt Sd.v (fun e => R.has e = true) S) (hrt : S "rt") :
    ∃ sh, endsOn Sd R = some sh ∧ sh.size = nEndT Sd.v.y := by
  obtain ⟨sh, hsh⟩ := amapM_there
    (g := fun a => (valAff? Sd.v R (fun _ => zeroE) a).map negE) Sd.ends.toArray (fun a ha => by
      rw [Option.isSome_map]
      exact valued_of_inTest (inTest_terms H hrt hE a (by simpa using ha)) _)
  refine ⟨sh, hsh, ?_⟩
  rw [optAmapM_size hsh, List.size_toArray, terms_len hp3 hE]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.inTest_rowCells
#print axioms OnBytes.Road.K4.C.inTest_rowR
#print axioms OnBytes.Road.K4.C.inTest_terms
#print axioms OnBytes.Road.K4.C.terms_len
#print axioms OnBytes.Road.K4.C.endsOn_there
