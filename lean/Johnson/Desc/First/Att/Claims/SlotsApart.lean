-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SlotsApart.lean: kind K5: Claims/SlotsCovered.lean's and
Claims/SlotsBehind.lean's laws A RUN AT A TIME: of "first" from the return of "first" alone, of "second"
from the return of "second" alone. slots_covered_K05' and slots_behind_K05 take both returns at once: at
a record where one run returns and the other does not they cannot be called.

Main names: first_slots_K05 · second_slots_K05 (general in Ps) · first_behind_K05 · second_behind_K05
(at "filled in the ledger behind the hearing").
The proofs are the halves of slots_covered_K05's, over its own lemmas sv_claim3 … sv_claim8.
IS IT EMPTY HERE? As Claims/SlotsCovered.lean and Claims/SlotsBehind.lean say of theirs.
Limits. As theirs. NEITHER RECORD OF PREMISES IS SHOWN OF ANYTHING HERE.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.SlotsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)

variable {K : ℕ} {Ps : ℕ → Prop} {i : P.Runs.In}

/-- **"first", from its own return.** -/
theorem first_slots_K05 {l₁ : List Aff} {j : JoinsP} (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) : ∀ f ∈ l₁, SlotsIn Ps f := by
  unfold P.Runs.firstRun P.Runs.gather at h1
  simp only [Option.map_eq_some_iff] at h1
  obtain ⟨_, ⟨y1, hy1, rfl⟩, e1⟩ := h1
  have c1 := (CV.bind (C := SlotsIn Ps) (sv_claim3 hP _) fun j3 _ => CV.bind (sv_claim4 hP hR j3)
    fun j4 _ => sv_claim5 hP hR j4) #[] y1 hy1 (by simp)
  have a1 : l₁ = y1.2.toList := (Prod.mk.inj e1).1.symm
  exact fun f h => c1.2 f (a1 ▸ h)

/-- **"second", from its own return.** -/
theorem second_slots_K05 {l₂ : List Aff} (hP : PtsSlots Ps i.g i.p) (hR : RowsSlots Ps i.p)
    (h2 : P.Runs.secondRun i K = some l₂) : ∀ f ∈ l₂, SlotsIn Ps f := by
  unfold P.Runs.secondRun P.Runs.gather at h2
  simp only [Option.map_eq_some_iff] at h2
  obtain ⟨_, ⟨y2, hy2, rfl⟩, e2⟩ := h2
  have c2 := (CV.bind (C := SlotsIn Ps) (sv_claim6 hP hR) fun _ _ => CV.bind (sv_claim7 hP hR)
    fun _ _ => sv_claim8 hP hR) #[] y2 hy2 (by simp)
  have a2 : l₂ = y2.2.toList := e2.symm
  exact fun f h => c2.2 f (a2 ▸ h)

end K5Law

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open K5Law (SlotsIn)

variable {x : Params.AttentionRounds} {F G F' : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ} {h : Heard}
  {i : Runs.In} {zk : Array (Array E)} {l : Left} {K : ℕ} {l₁ l₂ : List Aff} {j : Runs.JoinsP}

theorem first_behind_K05 (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : GeoFits i.g x)
    (h1 : Runs.firstRun i K = some (l₁, j)) : ∀ f ∈ l₁, SlotsIn (PscRun.Filled G) f := by
  obtain ⟨L, _, _, _, hs, _, _⟩ := hear_said hh hz
  exact K5Law.first_slots_K05 (pts_slots hs hp gf) (rows_slots li hs (K5Law.points_are hp)) h1

theorem second_behind_K05 (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : GeoFits i.g x)
    (h2 : Runs.secondRun i K = some l₂) : ∀ f ∈ l₂, SlotsIn (PscRun.Filled G) f := by
  obtain ⟨L, _, _, _, hs, _, _⟩ := hear_said hh hz
  exact K5Law.second_slots_K05 (pts_slots hs hp gf) (rows_slots li hs (K5Law.points_are hp)) h2

end VerifiableInference.Desc.First.Att.P

#print axioms K5Law.first_slots_K05
#print axioms K5Law.second_slots_K05
#print axioms VerifiableInference.Desc.First.Att.P.first_behind_K05
#print axioms VerifiableInference.Desc.First.Att.P.second_behind_K05
