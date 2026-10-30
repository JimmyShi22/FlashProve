-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/AtKept.lean: THE LAW AT THE CARRIED RECORD: UNDER `KeptAsks` (seven premises,
the member among them): BEHIND A YES OF K4's BLOCK AT THE FIRST CHAIN's STATE (`blockAtS p`) BOTH
RUNS THAT THE BLOCK STATES, "front" AND "back", RETURN AT THE RECORD THAT THE YES LEAVES. Said of
`KeptAtS p s s'` (Johnson/Road/K4/KeptAtS.lean: what a yes of that block leaves; `kept_atS` gives it
at a yes). One statement with its proof: calls of `runs_return_behind` (RunsReturnLaw.lean) and of
`frontAtS_returns`, `backAtS_returns` (AtSeat.lean).

WHO SPENDS IT: whoever promises, behind K4's yes, a test on the record that asks the block's own
runs (the table of joints' public item formsInT m 3 "own": its reader is the run itself, called at
the border's record, each run by itself).

  `KeptAsks`: what is asked beside `KeptAtS`, in the record's own words: IN FRONT OF THE YES the
    link's ledger has arrays of the right sizes and is free from its next free number on; the
    lookup's leaves' sumcheck has its four marks, and its window lies below that number, there and
    free · the member: a record o₀ and a public record P₀ of p.P's layout and reads at which the
    listing `front` returns, and what K4 heard has o₀'s skeleton.
  **`runs_at_kept`**: the statement on top: with the lists: "front" gives `frontOf p o G`'s list,
    "back" `formsBack o G`'s, o what the record holds as heard, G its ledger; and the record that
    each run leaves holds that listing's ledger. SAID OF `blockAtS p`, whose runs give forms: the
    block at the one type of a claim (`blockAtC p`, Johnson/Desc/First/K4/AtC.lean), which a link's
    seat holds, states the same runs with each form carried over (`atClaims_run`, AtCLaws.lean):
    that step is the caller's.

Limits. `KeptAsks` IS A PREMISE: its first half is the table's items ledger · freeAbove and the
lookup's law's (three of the four marks and the window's place are in the library; "a variable" and
"there and free" have nobody by name); its second is the member (by a run, no theorem:
RunsReturnLaw.lean's Limits) with `hear_skel` for the skeleton (at one plan, from lookups of one
shape: that the shapes are one has nobody by name). AT THE RECORD RIGHT BEHIND THE YES: at a later
border's record the ledger has moved on: the law's premise `Fit` is owed there. The return is needed
for that public item's test, not enough: what each form names must be there too. K04_law, the law of
K4's block itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Total.RunsReturnLaw
import Johnson.Road.K4.Total.AtSeat
import Johnson.Road.K4.KeptAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Road.K4 (KeptAtS)
open VerifiableInference.Desc.First (S LayOwn)

/-- **What is asked beside `KeptAtS`.** -/
structure KeptAsks (p : Par) (s s' : S) (P₀ : Pub) (o₀ : Own) : Prop where
  sized : ∀ a, s.here = .lay a → Sized a.F
  free : ∀ a, s.here = .lay a → ∀ j, a.F.next ≤ j → ¬ Filled a.F j
  leaves : ∀ a fo, s.here = .lay a → a.fo = some fo → Ready fo.leaves ∧
    fo.leaves.first + fo.leaves.walk.1.length ≤ a.F.next ∧ WinFree fo.leaves a.F
  skel : ∀ o, s'.own? = some o → Skel o o₀
  y₀ : P₀.y = p.P.y
  rd₀ : P₀.rd = p.P.rd
  member : ∃ a b, (front (!p.k3Runs) P₀ p.g o₀ a b).isSome = true

/-- The block's listing in front is the one listing at the flag's other value. -/
theorem frontOf_eq (p : Par) (o : Own) (F : Fork) :
    frontOf p o F = formsFrontWith (!p.k3Runs) p.P p.g o F := by
  unfold frontOf formsFrontNoRows formsFront
  cases p.k3Runs <;> rfl

/-- **UNDER `KeptAsks` (the member among its fields): behind a yes of K4's block both of its runs
return
at the record that the yes leaves.** -/
theorem runs_at_kept {p : Par} {s s' : S} {P₀ : Pub} {o₀ : Own} (K : KeptAtS p s s')
    (A : KeptAsks p s s' P₀ o₀) :
    ∃ (o : Own) (G : Fork) (ff fb : Array Aff) (G₁ G₂ : Fork) (runF runB : ℕ → S → _) (sf sb : S),
      s'.own? = some o ∧ s'.fork? = some G ∧ frontOf p o G = some (ff, G₁) ∧
      formsBack o G = some (fb, G₂) ∧
      (blockAtS p).claims.lookup "front" = some runF ∧ (∀ n, runF n s' = .ok (ff.toList, sf)) ∧
      sf.fork? = some G₁ ∧
      (blockAtS p).claims.lookup "back" = some runB ∧ (∀ n, runB n s' = .ok (fb.toList, sb)) ∧
      sb.fork? = some G₂ := by
  obtain ⟨a, fo, o, G, ha, hfo, h3, _, h5, _, _, _, hR, _, _, t, u, hh⟩ := K
  obtain ⟨a', ha', _⟩ := hR.here a ha
  have eF : a'.F = G := by
    have : s'.fork? = some a'.F := by simp [S.fork?, ha']
    exact Option.some.inj (this.symm.trans h3)
  have eo : a'.own = some o := by
    have : s'.own? = a'.own := by simp [S.own?, ha']
    rw [← this]
    exact h5
  obtain ⟨l1, l2, l3⟩ := A.leaves a fo ha hfo
  obtain ⟨⟨ff, G₁, hf, _⟩, fb, G₂, hb⟩ := runs_return_behind (rows := !p.k3Runs) (Pr := p.P)
    (P₀ := P₀) (o₀ := o₀) hh rfl rfl
    ⟨A.sized a ha, l1, l2, A.skel o h5, A.y₀, A.rd₀, A.member⟩ (A.free a ha) l3
  have hf' : frontOf p o a'.F = some (ff, G₁) := by rw [frontOf_eq, eF]; exact hf
  have hb' : formsBack o a'.F = some (fb, G₂) := by rw [eF]; exact hb
  obtain ⟨runF, sf, r1, r2, ⟨_, r3⟩⟩ := frontAtS_returns ha' eo hf'
  obtain ⟨runB, sb, q1, q2, ⟨_, q3⟩⟩ := backAtS_returns (p := p) ha' eo hb'
  exact ⟨o, G, ff, fb, G₁, G₂, runF, runB, sf, sb, h5, h3, by rw [← eF]; exact hf',
    by rw [← eF]; exact hb', r1, r2, by rw [r3]; rfl, q1, q2, by rw [q3]; rfl⟩

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.runs_at_kept
