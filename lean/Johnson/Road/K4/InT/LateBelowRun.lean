-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/InT/LateBelowRun.lean: EVERY SLOT THAT ONE OF K4's TWO RUNS OF CLAIMS "front" |
"back" FILLS LATE LIES BELOW THE LEDGER's NEXT: Johnson/Road/K4/Slots/LateBelow.lean's two
statements AT THE RUN ITSELF (a run of `blockAtC p`) AND THE STATES, in the letters of `RunSame` and
of `k4_runSame_below` (Johnson/Road/K4/InT/RunsSameK4.lean). A statement with its proof: calls.

  **`k4_late_below`**: name = "front" ∨ name = "back" · (blockAtC p).claims.lookup name = some runC
    · runC n s = .ok (cl, t) · s.fork? = some F · t.fork? = some G · Sized F · the three windows of
    what K4's hearing returned end at or below F.next ⟹ ∀ x ∈ K9.lateOf F G, x.1 < F.next.

Limits. That the windows end at or below the ledger's next is a premise (two of the three at a
reached state: Johnson/Road/K4/InT/WinsReached.lean). AT K4's OWN RUNS: the driver's guard round
them is Johnson/Road/K4/InT/SeatTie.lean's. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Slots.LateBelow
import Johnson.Desc.First.K4.RunsAtC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.InT

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par blockAtC frontAtC backAtC frontOf Wrote)
open OnBytes.Desc.First.K4.Slots (late_below_front late_below_back)
open VerifiableInference.Desc (K9.lateOf Claim)
open VerifiableInference.Desc.First (S LayOwn)

/-- What "wrote" says of the two ledgers. -/
theorem wrote_forks {s t : S} {a : LayOwn} {G₁ F G : Fork} (hw : Wrote s a G₁ t)
    (hF : s.fork? = some F) (hG : t.fork? = some G) : F = a.F ∧ G = G₁ := by
  have e1 : s.fork? = some a.F := by simp [S.fork?, hw.1]
  have e2 : t.fork? = some G₁ := by rw [hw.2]; rfl
  exact ⟨Option.some.inj (hF.symm.trans e1), Option.some.inj (hG.symm.trans e2)⟩

/-- **The late slots of K4's two runs lie below the ledger's next.** -/
theorem k4_late_below {p : Par} {name : String} (hn : name = "front" ∨ name = "back")
    {runC : ℕ → S → Except String (List Claim × S)}
    (hC : (blockAtC p).claims.lookup name = some runC) {n : ℕ} {s t : S} {cl : List Claim}
    {F G : Fork} (hr : runC n s = .ok (cl, t)) (hF : s.fork? = some F) (hG : t.fork? = some G)
    (hS : PscRun.Sized F)
    (W : ∀ (a : LayOwn) (o : Own), s.here = .lay a → a.own = some o →
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ F.next ∧
      o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ F.next ∧
      o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ F.next) :
    ∀ x ∈ K9.lateOf F G, x.1 < F.next := by
  rcases hn with rfl | rfl
  · obtain ⟨a, o, fs, G₁, ho, hf, _, hw⟩ := frontAtC hC hr
    obtain ⟨rfl, rfl⟩ := wrote_forks hw hF hG
    obtain ⟨w1, w2, _⟩ := W a o hw.1 ho
    unfold frontOf at hf
    by_cases hk : p.k3Runs = true
    · rw [if_pos hk] at hf
      exact late_below_front hS hf w1 w2
    · rw [if_neg hk] at hf
      exact late_below_front hS hf w1 w2
  · obtain ⟨a, o, fs, G₁, ho, hf, _, hw⟩ := backAtC hC hr
    obtain ⟨rfl, rfl⟩ := wrote_forks hw hF hG
    obtain ⟨_, _, w3⟩ := W a o hw.1 ho
    exact late_below_back hS hf w3

end OnBytes.Road.K4.InT

#print axioms OnBytes.Road.K4.InT.wrote_forks
#print axioms OnBytes.Road.K4.InT.k4_late_below
