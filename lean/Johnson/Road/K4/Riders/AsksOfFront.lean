-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/AsksOfFront.lean: THE PREMISES OF K4's TWO LAWS ON WHAT ITS ROW MAKES, AS FAR
AS THEY SPEAK OF THE VERIFIER's STATE IN FRONT OF K4's SUB-PROTOCOL, OUT OF TESTS WITH CODE ON THAT
STATE AND ONE TEST ON THE PUBLIC PARAMETERS: `KeptAsks`, whole (Total/AtKept.lean: the totality
law's premises) and the line names of `InTAsks` (InT/Statement.lean). Statements and proofs: each
test unfolded into the law's own words.

  `named_of`: `namedB F f` gives the lookups' `Named F f` · `ready_of`: `readyB` gives `Ready` ·
    `winFree_of`: `winFreeB` gives `WinFree`.
  **`padNames_of_left`**: where `lookLeftB s` (Johnson/Desc/First/FillBare.lean: the name
    "K4.lookLeft") accepts, at a feed-forward segment whose two readers of what the lookup returned
    agree: the lookups' structure `PadNames fo a.F`: the line names of `InTAsks`.
  **`keptAsks_of_front`**: `KeptAtS p s s'` · FOUR TESTS ON THE VERIFIER's STATE IN FRONT (ledgerB ·
    freeAboveB ns · lookLeftB · the two readers agree: lookLayB's clause) · hsh (what was heard has
    the layout's own shape: the item left m's sentence says it) · ONE TEST ON THE PUBLIC PARAMETERS
    (`frontB` at the sub-protocol's own letters) ⟹ there is a member o₀ with `KeptAsks p s s' p.P
    o₀`.

Limits. The tests are premises: the table's promise in front of K4's sub-protocol holds the first
two (ledger m, freeAbove m) and lookLayB (look m); "K4.lookLeft" is asked of the table's files,
laid in no issue of the composed filling, and has not run. frontB has not run. K04_law, the law of
K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Desc.First.FillBare
import Johnson.Road.K4.Total.AtKept
import Johnson.Road.K4.Total.PlanMember
import Johnson.Road.K4.Riders.ObjectsAtMeans
import Johnson.Top.H.Keep.PadNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Slots (SlotsIn)
open OnBytes.Desc.First.K4.Total (KeptAsks Ready WinFree frontB member_at_block)
open VerifiableInference.Desc.First (S LayOwn ledgerB freeAboveB)
open VerifiableInference.Desc.First.FillBare (namedB readyB winFreeB lookLeftB parts_of
ents_of_named)

/-- The test on a form gives the lookups' "named". -/
theorem named_of {F : Fork} {f : Aff} (h : namedB F f = true) : _root_.Fo.Tp.Named F f := by
  refine ⟨fun Q y hy => ?_, fun x hx => ?_⟩
  · rw [ents_of_named h] at hy
    exact nomatch hy
  · unfold namedB at h
    have e := List.all_eq_true.1 (Eq.mp (Bool.and_eq_true _ _) h).2 x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at e
    exact ⟨e.1, e.2⟩

theorem ready_of {p : Psc} (h : readyB p = true) : Ready p := by
  unfold readyB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem winFree_of {p : Psc} {F : Fork} (h : winFreeB p F = true) : WinFree p F := by
  intro i hi
  unfold winFreeB at h
  have e := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at e
  refine ⟨e.1, fun hf => ?_⟩
  unfold Filled at hf
  rw [e.2] at hf
  exact nomatch hf

/-- **The lookups' structure on what the kept forms name, out of the test.** -/
theorem padNames_of_left {s : S} (h : lookLeftB s = true) {a : LayOwn} (ha : s.here = .lay a)
    (hag : a.fo = a.lookHeard) {fo : Forest.Heard} (hfo : a.fo = some fo) :
    _root_.Fo.Tp.PadNames fo a.F := by
  obtain ⟨h1, h2, h3, h4, _⟩ := parts_of h ha (hag ▸ hfo)
  exact ⟨fun f hf => named_of (h1 f hf), named_of h2, named_of h3, named_of h4⟩

/-- **The totality law's premises at the verifier's state, out of tests in front and one test on the
plan.**
-/
theorem keptAsks_of_front {p : Par} {s s' : S} (K : KeptAtS p s s') (hled : ledgerB s = true)
    {ns : ℕ} (hfa : freeAboveB ns s = true) (hleft : lookLeftB s = true)
    (hag : ∀ a, s.here = .lay a → a.fo = a.lookHeard)
    (hsh : ∀ a fo, s.here = .lay a → a.fo = some fo → fo.shape = p.P.y.fo)
    (hB : frontB (!p.k3Runs) p.P p.hp p.g p.P.y.fo = true) : ∃ o₀, KeptAsks p s s' p.P o₀ := by
  obtain ⟨a, fo, o, G, ha, hfo, _, _, hown, _, _, _, _, _, _, t, u, hh⟩ := K
  obtain ⟨o₀, hS, hm⟩ := member_at_block hh (hsh a fo ha hfo) hB
  have inj : ∀ b, s.here = .lay b → b = a := fun b hb => by
    have e := hb.symm.trans ha
    cases e
    rfl
  refine ⟨o₀, ⟨fun b hb => ?_, fun b hb => ?_, fun b fo' hb hfo' => ?_, fun o' ho' => ?_, rfl, rfl,
    hm⟩⟩
  · exact sized_of_ledgerB hb hled
  · exact free_of_freeAboveB hb (sized_of_ledgerB hb hled) hfa
  · obtain ⟨_, _, _, _, h5, h6, h7⟩ := parts_of hleft hb ((hag b hb) ▸ hfo')
    exact ⟨ready_of h5, h6, winFree_of h7⟩
  · obtain rfl : o' = o := Option.some.inj (ho'.symm.trans hown)
    exact hS

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.padNames_of_left
#print axioms OnBytes.Road.K4.Riders.keptAsks_of_front
