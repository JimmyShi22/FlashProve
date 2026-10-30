-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/RngAtHead.lean: the smallness test (K8), public data alone: under
the library's head, the round named "RNG" of segment l is the round in front of which the first
chain's flat list stands at the kind's own number, 14 l + 6 (at l = 24: 343), and that member has
one round. These are two public premises of `zz_under_thread`
(Johnson/Desc/ProofFile/Honest/K8/ZzUnderThread.lean) and of what is stated over it.

The road is that of Johnson/Desc/ProofFile/Honest/K5/Law/BaseAt.lean. Each side is held against a
written list of the library, and the two written lists are held against each other by Lean's kernel.
  The rounds by name: `roundNumbers` reads the declared rounds' entries alone
  (`roundNumbers_entries`, Johnson/Desc/ProofFile/Honest/K2/Law/PlacesWritten.lean); under the head
  these are the written entries `P5T.esFull.1` (`entries_of_plans`).
  The rounds in front of a border: the sum of the rows' numbers of rounds (`roundsTo_cut`); under
  the head the flat list's rows are the written rows `cutFirstFull` (`pins_at_head`).

  `rngAllB`, `rng_closed`, `rng_bite`, `rng_bite_back`   the test on the two written lists: there
                  are 25 rounds "RNG", and number l stands behind just the rounds of the rows in
                  front of the kind's number; one border on or back the test says no
  `oneAllB`, `one_closed`, `one_bite`   the written row at the kind's number has one round; asked
                  for two the test says no
  `rng_at_head`, `hrng_at_head`   under the head: the first fact, plainly and in the form in which
                  `zz_under_thread` asks it
  `next_at_head`  under the head: one round lies between the kind's number and the next

Limits. The full size and the written lists alone. The head is a hypothesis: where it cannot be met
the three last statements say nothing. The closed facts speak of written lists: that any public
files give these lists is the head's matter. Five lines are one evaluation each by Lean's kernel
(`decide +kernel`), with two options raised at each.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.BaseAt
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K8.ZzData

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.PlanWritten (cutOf cutFirstFull pubBy_entries)
open H2K5.Row (asBy entries_of_plans)
open ProofFile.Honest.K2 (roundNumbers)
open ProofFile.Honest.K2.Law (entryNumbers roundNumbers_entries)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 Closed facts on the written lists -/

/-- The test: the written entries have 25 rounds "RNG", and number l of them stands behind just the
rounds of the first 14 l + (4, at l = 24: 5) + s written rows. -/
def rngAllB (s : Nat) : Bool :=
  decide ((entryNumbers P5T.esFull.1 "RNG").length = 25) &&
    (List.range 25).all fun l =>
      decide ((entryNumbers P5T.esFull.1 "RNG")[l]? =
        some (((cutFirstFull.take (14 * l + (if l = 24 then 5 else 4) + s)).map (·.2.2.1)).sum))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The two written lists, at the 25 draws.** A closed fact, by the kernel. -/
theorem rng_closed : rngAllB 2 = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can say no: one border on. -/
theorem rng_bite : rngAllB 3 = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can say no: one border back. -/
theorem rng_bite_back : rngAllB 1 = false := by decide +kernel

/-- The test: the written row number 14 l + (4, at l = 24: 5) + 2 has `want` rounds. -/
def oneAllB (want : Nat) : Bool :=
  (List.range 25).all fun l =>
    decide ((cutFirstFull[14 * l + (if l = 24 then 5 else 4) + 2]?).map (·.2.2.1) = some want)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The written row at each of the kind's 25 numbers has one round.** A closed fact, by the
kernel. -/
theorem one_closed : oneAllB 1 = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can say no. -/
theorem one_bite : oneAllB 2 = false := by decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Segment l's round "RNG" is the round in front of which the flat list stands at the kind's
number.** Under the head; l is below 25. -/
theorem rng_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) :
    (roundNumbers Zp.D.1 "RNG")[l]? =
      some (roundsTo cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2)) := by
  obtain ⟨hm, hc⟩ := H2K5.Door.pins_at_head h.toAtMg
  have W := H2K12.written354_of_pins h.scope h.laid.pub hm h.laid.laidPOf
  have hZ := asBy h.laid.pub
  have he := entries_of_plans hZ ((pubBy_entries hZ).1.symm.trans W.entries)
  have hb := rng_closed
  unfold rngAllB at hb
  rw [Bool.and_eq_true] at hb
  rw [roundNumbers_entries, he, K5.roundsTo_cut, hc]
  exact of_decide_eq_true (List.all_eq_true.1 hb.2 l (List.mem_range.2 hl))

/-- The same, at the public data of the digits' filling, whatever the ground and the lists of
matrices are. -/
theorem hrng_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : Ground)
    (mats : Nat → List (Nat × String × Nat)) {l : Nat} (hl : l < 25) :
    (zzPubOf G Zp.D.1 mats).rng[l]? =
      some (roundsTo cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2)) :=
  rng_at_head h hl

/-- **One round lies between the kind's number and the next.** Under the head; l is below 25. -/
theorem next_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) :
    roundsTo cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2 + 1) =
      roundsTo cF.blocksInOrder (14 * l + (if l = 24 then 5 else 4) + 2) + 1 := by
  obtain ⟨-, hc⟩ := H2K5.Door.pins_at_head h.toAtMg
  have e := of_decide_eq_true (List.all_eq_true.1 one_closed l (List.mem_range.2 hl))
  obtain ⟨row, hrow, h1⟩ := Option.map_eq_some_iff.1 e
  rw [K5.roundsTo_cut, K5.roundsTo_cut, hc, List.take_add_one, hrow, List.map_append,
    List.sum_append]
  show _ + ([row].map (·.2.2.1)).sum = _
  rw [List.map_singleton, List.sum_singleton, h1]

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.rngAllB
#print axioms ProofFile.Honest.K8.rng_closed
#print axioms ProofFile.Honest.K8.rng_bite
#print axioms ProofFile.Honest.K8.rng_bite_back
#print axioms ProofFile.Honest.K8.oneAllB
#print axioms ProofFile.Honest.K8.one_closed
#print axioms ProofFile.Honest.K8.one_bite
#print axioms ProofFile.Honest.K8.rng_at_head
#print axioms ProofFile.Honest.K8.hrng_at_head
#print axioms ProofFile.Honest.K8.next_at_head
