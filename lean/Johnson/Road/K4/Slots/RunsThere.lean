-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Slots/RunsThere.lean: BEHIND EACH OF K4's TWO RUNS OF CLAIMS, EVERY SLOT THAT A FORM
OF THE RUN NAMES IS FILLED IN THE LEDGER THAT THE RUN HANDS ON: the run itself lays its windows.
Statements and proofs: HearFills.lean's `hs_front`, `hs_back` with the runs' laws
(`formsFrontWith_some`, `formsBack_some`, OnBytes/Desc/First/K4/ClaimsLaws.lean) and `run_fills`
(Fills.lean).

  `front_there`: where `hear` returned (o, G, u) from a ledger with arrays of the right sizes, and
    `formsFrontWith rows P g o Gr` returns (fs, F₁) from a ledger Gr of the right sizes that keeps
    what G has filled: every form of fs is `SlotsIn (Filled F₁)`, UNDER k3, hBit, hLv AT Gr (the
    three premises on the lookup's record).
  `back_there`: the like for `formsBack o Gr`: NO FURTHER PREMISE.
  `slots_all`: `SlotsIn (Filled F) f` as the Bool `f.slots.all fun x => F.gotF.getD x.1 false`: the
    first half of the test `thereAt` of the statement on K4 (Johnson/Desc/Plain/K04Plain.lean, which
    is not imported here).

Limits. THE SECOND HALF OF `thereAt` (every entry that a form names is one that the arrays have) IS
NOT TREATED. k3, hBit, hLv are premises. One direction, from returns. Nothing on what lies under a
slot. Nothing on soundness.
-/
import Johnson.Road.K4.Slots.HearFills

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Sized Filled)

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G Gr F₁ : Fork}
  {t0 u : Tape} {fs : Array Aff}

/-- **UNDER k3, hBit, hLv: behind the run "front" every slot that its forms name is filled.** -/
theorem front_there (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hG : ∀ j, Filled G j → Filled Gr j) (sG : Sized Gr) {rows : Bool}
    (hr : formsFrontWith rows P g o Gr = some (fs, F₁))
    (k3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, SlotsIn (Filled Gr) f)
    (hBit : Filled Gr o.H.fo.sBit) (hLv : SlotsIn (Filled Gr) o.H.fo.leaves.start) :
    ∀ f ∈ fs.toList, SlotsIn (Filled F₁) f := by
  obtain ⟨sh, pp, l, F1, F2, _, a2, a3, rfl, r1, r2, rfl⟩ := formsFrontWith_some hr
  obtain ⟨s1, k1, f1⟩ := run_fills sG r1
  obtain ⟨_, k2, f2⟩ := run_fills s1 r2
  have fin : ∀ j, Filled F2 j →
      Filled ((if rows then F2.paid o.H.fo.owedObjects else F2).paid o.H.fo.owedPlanes) j := by
    intro j hj
    cases rows <;> exact hj
  rw [List.toList_toArray]
  intro f hf x hx
  refine fin _ ?_
  rcases hs_front hF h hG k3 hBit hLv sh a2 a3 f hf x hx with ⟨w, hw, h1, h2⟩ | hU
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have e := f1 (x.1 - o.H.tV.p.first) (by simp only [Array.size_replicate]; omega)
      rw [Nat.add_sub_cancel' h1] at e
      exact k2 _ e
    · have e := f2 (x.1 - o.H.fo.leaves.first) (by simp only [Array.size_replicate]; omega)
      rwa [Nat.add_sub_cancel' h1] at e
  · exact k2 _ (k1 _ hU)

/-- **Behind the run "back" every slot that its forms name is filled.** -/
theorem back_there (hF : Sized F) (h : hear engFl P hp g fo F t0 = some (o, G, u))
    (hG : ∀ j, Filled G j → Filled Gr j) (sG : Sized Gr)
    (hr : formsBack o Gr = some (fs, F₁)) : ∀ f ∈ fs.toList, SlotsIn (Filled F₁) f := by
  obtain ⟨F1, rfl, r1, rfl⟩ := formsBack_some hr
  obtain ⟨_, k1, f1⟩ := run_fills sG r1
  rw [List.toList_toArray]
  intro f hf x hx
  show Filled F1 x.1
  rcases hs_back hF h hG f hf x hx with ⟨h1, h2⟩ | hU
  · have e := f1 (x.1 - o.wo.toWsMerged.p.first) (by simp only [Array.size_replicate]; omega)
    rwa [Nat.add_sub_cancel' h1] at e
  · exact k1 _ hU

/-- The same as the Bool that the statement's test reads. -/
theorem slots_all {F : Fork} {f : Aff} (h : SlotsIn (Filled F) f) :
    (f.slots.all fun x => F.gotF.getD x.1 false) = true := by
  rw [Array.all_eq_true']
  intro x hx
  exact h x (Array.mem_toList_iff.mpr hx)

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.front_there
#print axioms OnBytes.Desc.First.K4.Slots.back_there
#print axioms OnBytes.Desc.First.K4.Slots.slots_all
