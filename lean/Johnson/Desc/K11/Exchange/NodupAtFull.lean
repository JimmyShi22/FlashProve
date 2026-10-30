-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/NodupAtFull.lean: the proofs of `PlacesNodup` and `NodupAtFull`
(Johnson/Desc/K11/Exchange/NodupAtFullStatement.lean), to the letter. Lemmas; none of the library's
goals.

How. A list each of whose members it counts once has no member twice; a front piece of such a list
is such a list; and a list whose image under a function is such a list is one too. Under the
hypothesis the file's description passes the tests on the plan, of which the test on places is one,
and its first chain is cF (`IM.Open.desc`, Johnson/IMR/SeatOpen.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.NodupAtFullStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Exchange
open VerifiableInference.Desc (FileDescription placesOf)

/-- **The places of the first chain's flat list are pairwise different.** -/
theorem placesNodup : PlacesNodup := by
  intro Xi F h
  unfold FileDescription.placesOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  have hn : (F.places.map fun p => (p.2.1.chain, p.2.1.link, p.2.1.piece)).Nodup :=
    List.nodup_iff_count_eq_one.2 h.2
  unfold FileDescription.places at hn
  rw [List.map_append, List.map_append] at hn
  have h1 := hn.of_append_left.of_append_left
  have e : (placesOf F.first.blocksInOrder).map (fun p => (p.2.1.chain, p.2.1.link, p.2.1.piece)) =
      (F.first.blocksInOrder.map (·.place)).map fun p => (p.chain, p.link, p.piece) := by
    unfold placesOf
    rw [List.map_map, List.map_map]
    rfl
  rw [e] at h1
  exact h1.of_map _

/-- **The same under the one hypothesis.** -/
theorem nodupAtFull : NodupAtFull := by
  intro Z D r Zp Np cF x h
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := h.laid.planOk
  rw [O.desc] at hp
  unfold FileDescription.planOk FileDescription.planOkCore at hp
  simp only [Bool.and_eq_true] at hp
  exact placesNodup _ _ hp.1.1.1.1.1.2

end Johnson.Desc.First.ForkMerge.Exchange

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.placesNodup
#print axioms Johnson.Desc.First.ForkMerge.Exchange.nodupAtFull
