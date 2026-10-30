-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverStops.lean: THE STOPS OF A CHAIN's HALVES AS MARKS OF THE
CANONICAL COVER. `runC` (Honest/Walk.lean) can go on at a list of challenges at which a part stops,
and the thread's laws say nothing there (Honest/Law/CoverThread.lean, Limits; not in the sealed
library). So whoever pays a debt (`LocalDebts`, Honest/Law/CoverHeld.lean) by the thread wants «no
part in front has stopped» in hand. A stop is a test on challenges, at what a part sees of the
input: so it can be laid as a mark (Honest/Law/Marks.lean), one a member; its number is then counted
at that member's gate. `stopQ`: a filling of the letter Q: no part of the members in front stops. It
holds at the chain's start, and goes on past a member whose marks are silent (`stopQ_zero`,
`stopQ_step`).

WHAT THIS IS. Definitions, and lemmas on the frame's own `chainStopAt` (Honest/Rule.lean). No
measure is in this file. None of the library's goals.

loc₀: of the challenges in front of the chain, those that its stops are handed: a letter. In the
first and the shared chain: none. In the second chain the stops are handed the first chain's, with
the sealing round's fixed one.

  `stopMarks`, `stop_silent`, `stopQ`, `stopQ_zero`, `stopQ_step`

Limits. sh: the marks' stated shares: a letter: nothing holds it against the parts' own stated
shares. THE STOPS ARE THEN COUNTED TWICE where the withheld set's measure is added beside the falls'
number: once there, once as marks here. `stopMarks` LAYS A MARK AT EVERY MEMBER, ALSO AT ONE WITHOUT
A ROUND: at such a member the mark's gate has no message to measure over, and holds it by 0 or by 1
alone (Honest/Law/CoverChain.lean, Limits): harmless where no half stands there, or its parts' stops
say nothing at no challenge of their own. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverSplit
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y : Type}

section
variable (v : Option V) (hs : List (Placed V W Y)) (skip : Nat)
  (loc₀ : List Fmt.Drawn → List Fmt.Drawn) (sh : Place → Odds)

/-- **One mark a member: a part of the half at its place stops.** fr: all challenges in front, those
in front of the chain first. -/
def stopMarks (bs : List (Block S Cl)) : List Mark :=
  bs.map fun b => ⟨b.place, fun fr own =>
    (chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip) own).map fun _ => "a part stops",
    sh b.place⟩

/-- Where the marks at a member's place are silent, no part of its half stops. ms: further marks. -/
theorem stop_silent (bs : List (Block S Cl)) (ms : List Mark) {b : Block S Cl} (hb : b ∈ bs)
    (fr own : List Fmt.Drawn)
    (h : (markOf (stopMarks v hs skip loc₀ sh bs ++ ms) b.place fr own).isSome = false) :
    chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip) own = none := by
  unfold markOf at h
  cases hc : chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip) own with
  | none => rfl
  | some y =>
    exfalso
    have hm : (⟨b.place, fun fr own =>
        (chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip) own).map
          fun _ => "a part stops", sh b.place⟩ : Mark) ∈
        (stopMarks v hs skip loc₀ sh bs ++ ms).filter fun m => m.place == b.place := by
      refine List.mem_filter.2 ⟨List.mem_append_left _ (List.mem_map.2 ⟨b, hb, rfl⟩), ?_⟩
      exact beq_self_eq_true _
    have hs' := (findSome_isSome (fun m : Mark => m.test fr own) _).2 ⟨_, hm, by
      show ((chainStopAt v [b] hs (loc₀ (fr.take skip) ++ fr.drop skip) own).map
        fun _ => "a part stops").isSome = true
      rw [hc]
      rfl⟩
    rw [hs'] at h
    cases h

/-- **A filling of the letter Q**: no part of the members in front stops. -/
def stopQ (bs : List (Block S Cl)) (j : Nat) (fr : List Fmt.Drawn) : Prop :=
  chainStopAt v (bs.take j) hs (loc₀ (fr.take skip)) (fr.drop skip) = none

theorem stopQ_zero (bs : List (Block S Cl)) (fr : List Fmt.Drawn) :
    stopQ v hs skip loc₀ bs 0 fr := rfl

/-- **It goes on past a member whose marks are silent.** -/
theorem stopQ_step (bs : List (Block S Cl)) (ms : List Mark) {j : Nat} {b : Block S Cl}
    (hj : bs[j]? = some b) (fr own : List Fmt.Drawn) (hsk : skip ≤ fr.length)
    (hn : (fr.drop skip).length = ((bs.take j).flatMap (·.rounds)).length)
    (hq : stopQ v hs skip loc₀ bs j fr)
    (hm : (markOf (stopMarks v hs skip loc₀ sh bs ++ ms) b.place fr own).isSome = false) :
    stopQ v hs skip loc₀ bs (j + 1) (fr ++ own) := by
  have hb : b ∈ bs := List.mem_of_getElem? hj
  have h1 := stop_silent v hs skip loc₀ sh bs ms hb fr own hm
  unfold stopQ at hq ⊢
  have e1 : bs.take (j + 1) = bs.take j ++ [b] := by
    rw [List.take_add_one, hj]
    rfl
  have d1 : (fr ++ own).drop skip = fr.drop skip ++ own := List.drop_append_of_le_length hsk
  have d2 : (fr ++ own).take skip = fr.take skip := List.take_append_of_le_length hsk
  rw [e1, d1, d2, chainStopAt_append, ← hn, List.take_left' rfl, List.drop_left' rfl, hq, h1]
  rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.stop_silent
#print axioms ProofFile.Honest.stopQ_zero
#print axioms ProofFile.Honest.stopQ_step
