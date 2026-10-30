-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReadersThere.lean: kind K5: THE FORMS THAT K5's TWO READERS HAND TO THE LOOKUP's
RUN "planes" (readersOfK, Att/Guest.lean: a bit's plane; the pin), AT THE RECORD BEHIND THE HEARING's
LAY, NAME ONLY WHAT IS THERE: the public test affInT (Batch/FormsIn.lean;
imported, not turned), with no late slot; each names no slot at all.

Main names:
  `at_there`: a form that `u3at` returns names no slot that fails Ps (it names none) and an entry of
    the tables' part alone.
  `readers_forms`: what readersOfK's two readers hand out, at the seat's reading (i, K): such forms.
  `k5_readers_there`: **each passes affInT own none [] at the part behind the lay, and each of its
    entries names row 0 of an array with one own row.**
Premises: the hearing's return at a sized ledger · the seat's reading returns · U3There
(Att/K05FormsMade.lean).
Limits. THIS IS K5's SHARE OF "planes" ALONE: the run is the lookup's (planesRun, Look/K3Runs.lean): how
its three forms are made of these, of the lookup's own slots and of the leaves' late slots is not
spoken of. free := none and late := [] are closed here, not paid. EMPTY AT: a place or column at
which a reader answers nothing.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05JoinThere
import Johnson.Desc.First.Att.Guest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.K9 (affInT)
open K5Law (SlotsIn Cov LenIn)

/-- A form that u3at returns. -/
theorem at_there {Ps : ℕ → Prop} {i : Runs.In} {K nW : ℕ} (hL : LenIn i nW) {t n : ℕ} {f : Aff}
    (h : (Runs.gather K (Runs.u3at i t n)).map (·.1) = some f) :
    SlotsIn Ps f ∧ Cov i.iU3 K nW f := by
  unfold Runs.gather at h
  simp only [Option.map_map, Option.map_eq_some_iff] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨(K5Law.sv_u3at (Ps := Ps) t n #[] y hy (by simp)).1,
    (K5Law.cv_u3at hL t n #[] y hy (by simp)).1⟩

section
variable {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : Heard}
  {G : Fork} {c : ParC} {i : Runs.In} {K : ℕ}

/-- What the two readers hand out. -/
theorem readers_forms {Ps : ℕ → Prop} {t : First.S} {nW : ℕ} (hin : inOf (seatCO c) c t = some (i, K))
    (hL : LenIn i nW) {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)}
    (hr : readersOfK (seatCO c) c t = some r) :
    (∀ e col f, r.1 e col = some f → SlotsIn Ps f ∧ Cov i.iU3 K nW f) ∧
      ∀ col f, r.2 col = some f → SlotsIn Ps f ∧ Cov i.iU3 K nW f := by
  unfold readersOfK at hr
  rw [hin] at hr
  obtain rfl := Option.some.inj hr
  exact ⟨fun e col f hf => at_there hL hf, fun col f hf => at_there hL hf⟩

/-- **K5's readers' forms, behind the lay, name only what is there.** -/
theorem k5_readers_there (own : List (ℕ × ℕ)) (hh : hear x (a.F, rs, 0) = some (h, G, [], 0))
    (hz : Sized a.F) (hin : inOf (seatCO c) c (behind s a h G) = some (i, K))
    (U : U3There own s a c) (o : Option ℕ) {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)}
    (hr : readersOfK (seatCO c) c (behind s a h G) = some r) {f : Aff}
    (hf : (∃ e col, r.1 e col = some f) ∨ ∃ col, r.2 col = some f) :
    affInT own none [] (partAt s a G o) f = true ∧
      ∀ e ∈ f.ents.toList, e.row = 0 ∧ ∃ T, G.trees[e.tree]? = some T ∧ T.R = 1 := by
  obtain ⟨eg, eu, hK, g0, l, lk, _, hl, hp, ht⟩ := inOf_behind hin
  obtain ⟨zG, bl⟩ := hear_below hh hz
  rw [← eg] at ht
  obtain ⟨r1, r2⟩ := readers_forms (Ps := PscRun.Filled G) hin (K5Law.len_in ht) hr
  have hb : SlotsIn (PscRun.Filled G) f ∧ Cov i.iU3 K c.nW f := by
    rcases hf with ⟨e, col, hf⟩ | ⟨col, hf⟩
    · exact r1 e col f hf
    · exact r2 col f hf
  exact form_there own zG U bl.trees hK o hb.1 (eu ▸ hb.2)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.at_there
#print axioms VerifiableInference.Desc.First.Att.P.readers_forms
#print axioms VerifiableInference.Desc.First.Att.P.k5_readers_there
