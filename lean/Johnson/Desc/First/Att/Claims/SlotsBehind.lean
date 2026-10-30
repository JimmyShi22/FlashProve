-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/SlotsBehind.lean: kind K5: ONE SENTENCE AS ONE THEOREM: every slot that a
form gathered by the run "first" or "second" names bears the mark "filled" in the ledger G that the
kind's hearing returns; so does every slot that a key form names; so does every slot that the one
form of the lookup's "join" names, IF g.cEnd's do. Calls of lemmas that lie; no new argument.

The calls: hear_said (Att/K5SaidAll.lean: where the hearing returns from a sized ledger, what was
heard is Said of G) · pts_slots (Att/K05PtsSlots.lean) · rows_slots (Att/K05RowsSlots.lean) ·
slots_covered_K05' (Claims/SlotsCovered.lean) · keys_slots_K05, join_slots_K05
(Claims/SlotsCoveredKeys.lean), all at Ps := PscRun.Filled G (OnBytes/Tie/Pv/Psc/PscFork.lean:
G.gotF.getD j false = true).

IS IT EMPTY HERE?
  · Empty where the hearing, pointsOf or a run does not return, where the ledger in front is not sized,
    where l is not what LeftIs says, where GeoFits fails. THAT ALL THESE HOLD TOGETHER AT ONE RECORD IS
    SHOWN NOWHERE HERE: no member at a real hearing, none at a toy.
  · One h, one G, one zk, one l, one i go through all premises: the letters meet by Lean's own check.
  · The ledger at which LeftIs speaks (F') is free, as in rows_slots.

Main names: slots_behind_K05 · keys_behind_K05 · join_behind_K05.
Limits. "Filled in G" is the mark alone: nothing on j < G.ns, on the sizes of vp and mf, on a late slot,
  on a slot masked elsewhere, on the mask row's seat. Nothing on entries. THAT g.cEnd NAMES FILLED
  SLOTS IS A PREMISE (Fo.FilledA G g.cEnd). The lookup's run "planes" is not spoken of. No tie from
  a reader of forms in other files to these runs' lists.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5SaidAll
import Johnson.Desc.First.Att.K05PtsSlots
import Johnson.Desc.First.Att.Claims.SlotsCoveredKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.K.Kc
open VerifiableInference.Desc.First
open K5Law (SlotsIn SlotsJ)

variable {x : Params.AttentionRounds} {F G F' : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ} {h : Heard}
  {i : Runs.In} {zk : Array (Array E)} {l : Left} {K : ℕ} {l₁ l₂ : List Aff} {j : Runs.JoinsP}

/-- **Every slot that a form of "first" or "second" names is filled behind the hearing.** -/
theorem slots_behind_K05 (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : GeoFits i.g x)
    (h1 : Runs.firstRun i K = some (l₁, j)) (h2 : Runs.secondRun i K = some l₂) :
    ∀ f ∈ l₁ ++ l₂, SlotsIn (PscRun.Filled G) f := by
  obtain ⟨L, _, _, _, hs, _, _⟩ := hear_said hh hz
  exact K5Law.slots_covered_K05' (pts_slots hs hp gf) (rows_slots li hs (K5Law.points_are hp)) h1 h2

/-- **So is every slot that a key form names.** -/
theorem keys_behind_K05 (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : GeoFits i.g x)
    (h1 : Runs.firstRun i K = some (l₁, j)) : SlotsJ (PscRun.Filled G) j := by
  obtain ⟨L, _, _, _, hs, _, _⟩ := hear_said hh hz
  exact K5Law.keys_slots_K05 (pts_slots hs hp gf) (rows_slots li hs (K5Law.points_are hp)) h1

/-- **So is every slot that join's one form names, if g.cEnd's are.** -/
theorem join_behind_K05 {k3 : Runs.PadIn} {kf : Array Aff} {g : Forest.Heard} {F₀ : Fork} {t : Tape}
    {y : Aff × Fork × Tape} (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : GeoFits i.g x)
    (h1 : Runs.firstRun i K = some (l₁, j)) (hk : Runs.keysRun i k3 j = some kf)
    (hc : Fo.FilledA G g.cEnd) (hj : Look.joinF g kf F₀ t = some y) : SlotsIn (PscRun.Filled G) y.1 := by
  obtain ⟨L, _, _, _, hs, _, _⟩ := hear_said hh hz
  exact K5Law.join_slots_K05 (pts_slots hs hp gf) (rows_slots li hs (K5Law.points_are hp)) h1 hk
    (K5Law.slotsIn_mono (fun _ hq => hq.2) (K5Law.filledA_iff.1 hc)) hj

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.slots_behind_K05
#print axioms VerifiableInference.Desc.First.Att.P.keys_behind_K05
#print axioms VerifiableInference.Desc.First.Att.P.join_behind_K05
