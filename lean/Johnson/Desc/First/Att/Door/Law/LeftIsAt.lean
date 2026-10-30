-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/LeftIsAt.lean: KIND K5: K5AtMg's FIELD leftIs (Johnson/Desc/First/Att/K05AtMg.lean: what the item "left" says in front of the kind's block is what the lookup on the calls leaves) AT THE LOOKUPS' OWN FILLING OF THAT ITEM's Prop HALF (k3LeftItemAt, Johnson/Desc/First/Look/K3LeftItem.lean; mgAll (Johnson/Desc/Sound/MgAll.lean) pays "pubP (.left m) a = k3LeftItemAt X m a.2" by rfl: its mgAll_pubP with the lookups' fill_pubP_left). THE LAW's TWO LETTERS x0 | gOf ARE CHOSEN AS FUNCTIONS OF THE VERIFIER's STATE ALONE (leftOut_chosen_room, Johnson/Desc/First/Att/K05LeftChosen.lean): SO THEY ARE NO LETTERS OF THE TOP: "THERE ARE x0 AND gOf WITH …". Mathlib beneath.
-- FROM: PlanIs · "attention is covered" · what the public parameters hand for the lookup on the calls: guard_theorems' first clause (the calls' parameters fix x.fs as their shape) · the tiling (k5Plan_of_public's kin: planIs_tiles · planIs_next0 · place_calls): the room asked (the calls' scalars and the kind's slots) fits the plan's number of slots.
import Johnson.Desc.First.Look.K3Fill
import Johnson.Desc.First.Att.K05LeftChosen
import Johnson.Desc.First.Att.K05PlanOfPublic
import Johnson.Desc.First.Att.GuardPlan

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Look (lookAt placeAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.OnPublicFiles (K3LeftAt k3LeftItemAt k3LeftItem LeftQ)

/-- **What the lookups' item says at an attention link, in the law's letters.** -/
theorem leftAt_of_item {W : Verify.Public} (hP : PlanIs W) (h4 : W.p4 = true) {g : ℕ} {a : Attention.Plan} (ha : W.A[g]? = some a)
    {x : Look.Place} (hx : lookAt W (2 * g + 1) false = some x) {s : First.S} (h : k3LeftItemAt W (2 * g + 1) s) :
    K3LeftAt (fun s : First.S => s.fork?) (fun s : First.S => s.lookHeard?) x.fs x.lm x.F.next (LeftQ x.ns) s := by
  obtain ⟨p, hp, ⟨hS, e, L⟩, _⟩ := h
  unfold placeAt at hp
  rw [hx] at hp
  obtain rfl := Option.some.inj hp
  have e' := (guard_theorems hP h4 ha hx (Params.settingOf W.P.frame)).1
  obtain rfl : x.fs = hS := Option.some.inj (e'.symm.trans e)
  exact L

/-- **leftIs, with x0 and gOf chosen.** J₀, ι: the law's places. -/
theorem leftIs_at {J₀ Cl : Type} [DecidableEq J₀] (claim : Aff → Cl) {W : Verify.Public} (hP : PlanIs W) (h4 : W.p4 = true) {g : ℕ}
    {a : Attention.Plan} (ha : W.A[g]? = some a) {x : Look.Place} (hx : lookAt W (2 * g + 1) false = some x)
    (ι : Fo.Pl → Option J₀) :
    ∃ (x0 : First.S → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option J₀)) (gOf : First.S → Forest.Heard),
      ∀ s, k3LeftItemAt W (2 * g + 1) s →
        K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next ι
          (fun F => Room F a.ns x.F.next (Forest.elems x.fs + (slotsOf (script a.own) + 0))) (x0 s) (gOf s) s := by
  have ht := planIs_tiles hP ha
  have hz := planIs_next0 hP ha
  obtain ⟨c1, c2, _, c4⟩ := place_calls h4 ha hx
  obtain ⟨x0, gOf, H⟩ := leftOut_chosen_room (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next a.ns
    (Forest.elems x.fs + (slotsOf (script a.own) + 0)) ι () (by rw [c1, hz, c4]; omega)
  refine ⟨x0, gOf, fun s h => H s ?_⟩
  have L := leftAt_of_item hP h4 ha hx h
  rw [c2] at L
  exact L

#print axioms leftAt_of_item
#print axioms leftIs_at

end H2K5.Door
