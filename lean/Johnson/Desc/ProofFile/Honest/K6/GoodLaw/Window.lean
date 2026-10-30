-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Window.lean: TWO SMALL LAWS UNDER THE INVARIANT `K6GoodAt`
(Honest/K6/GoodLaw/Runs.lean) OF THE SUB-PROTOCOL "THE OUTPUT HEAD's OWN ROUNDS" (K6), ON WHICH
SLOTS OF THE LEDGER STAND WHERE IN ITS WINDOW [b, e). CONDITIONAL on the invariant at the state.
Lemmas with their proofs. None of the library's goals. Whose: part 4's.

  `sV_of_good`      **the slot of the value that the merge takes (`Heard.sV`,
                    OnBytes/Model/HeadHeard.lean) is the window's last: sV + 1 = e**, at every state
                    with the invariant, whatever the head's own part holds as heard
  `sV_at_window`    the same in numbers, at e := b + `headWindow` p: sV = b + 40 + 8 lt + 4 lPd
  `join_keys_in`    **no key vector that the run "join" takes names a slot outside the window**: so
                    none below b, where the form in which the lookup's key side ended has its slots
  `slot_inj`        a tool: two equal forms "the hidden value under a slot" name one slot

What it is not. FACTS ON THE VERIFIER's STATE AND ON NUMBERS OF SLOTS: no value of a witness, no
measure, no chance. That the invariant holds at any state of a run is not shown here (behind a yes
of the block's step, under the two tests on its draws and its other premises (`K6On`, `Canonical`,
the lookup's side's debt on the form in which its key side ended): `k6_border_good`,
Honest/K6/GoodLaw/Runs.lean). b and e are letters: which written numbers they are is not said here.
`sV_of_good` says nothing on who names that slot: by reading, no claim of this sub-protocol's runs
does. The proof of `join_keys_in` goes as that of `join_unnamed` (Honest/K6/GoodLaw/Runs.lean) goes,
without its last widening: both ends of the library's `keys_slotsIn` are kept. Called:
`weightSlot_filled` (Johnson/Desc/Kinds/Law/WeightAtSame.lean), `hear_parts` (Law/Cut.lean),
`sumcheck_ends` (Law/HeardEnds.lean), `own_callOf`, `takes_sumcheck` (Law/Takes.lean),
`lettersAt_ok`, `reads_bare` (Law/RunsStill.lean), `keys_slotsIn` (Law/KeysHave.lean), `reads_wide`,
`getD_has` (Honest/K6/GoodLaw/Runs.lean). Over files that have not yet landed in the library:
Honest/K6/GoodLaw/Runs.lean and what it imports.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Runs
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.Desc.Kinds.Law.HeardEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace ProofFile.Honest.K6.GoodLaw
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (Given seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (SlotsIn)

/-- Two forms "the hidden value under a slot" that are equal name one slot. -/
theorem slot_inj {a b : Nat} (h : Aff.slot a = Aff.slot b) : a = b := by
  have e := congrArg (fun f : Aff => (f.slots.getD 0 (0, zeroE)).1) h
  simpa [Aff.slot] using e

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Head.Par)

/-- **THE SLOT OF THE VALUE THAT THE MERGE TAKES IS THE WINDOW's LAST**: at a state with the
invariant, whatever the head's own part holds as heard: `Heard.sV` (OnBytes/Model/HeadHeard.lean) is
e - 1. -/
theorem sV_of_good {b e : Nat} {s : S} (k : K6GoodAt h iU3 p b e s) :
    ∀ (o : VerifiableInference.Desc.First.HeadOwn) (x : OnBytes.Model.Head.Heard),
      s.here = .head o → o.x = some x → x.sV + 1 = e := by
  intro o x ho hx
  obtain ⟨⟨g, H, F0, G, rs, hg, hH, hW, hh, _, rfl, rfl, _, _⟩, _⟩ := k
  letI := g
  obtain ⟨x', hx', hv, _⟩ := Head.Law.weightSlot_filled h iU3 ho hH
  obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hx)
  obtain ⟨Fa, Fb, l1, _, _, wFb, _, hsL, _⟩ := Head.Law.Came.hear_parts hW hh
  obtain ⟨c8, R8, T8, _, _, _, _, _, _, _, _, E8⟩ :=
    Head.Law.sumcheck_ends wFb hsL (fun _ => zeroE)
  have e1 := (E8 1 (by omega)).1
  rw [e1, Head.Law.own_callOf] at hv
  have hn := slot_inj hv
  have nG := (Head.Law.takes_sumcheck (⟨wFb.2.1, wFb.2.2, wFb.1⟩ : OnBytes.PscRun.Sized Fb)
    hsL).next
  show x'.tH.sEnd + 1 + 1 = G.next
  omega

/-- The same in numbers, at the two ends that `k6_border_good` has. -/
theorem sV_at_window {b : Nat} {s : S} (k : K6GoodAt h iU3 p b (b + headWindow p) s) :
    ∀ (o : VerifiableInference.Desc.First.HeadOwn) (x : OnBytes.Model.Head.Heard),
      s.here = .head o → o.x = some x → x.sV = b + 40 + 8 * headLt p + 4 * headLPd p := by
  intro o x ho hx
  have e := sV_of_good h iU3 p k o x ho hx
  unfold headWindow at e
  omega

/-- **NO KEY VECTOR THAT "join" TAKES NAMES A SLOT OUTSIDE THE WINDOW**: so none below b, where the
form in which the lookup's key side ended has its slots. -/
theorem join_keys_in {b e : Nat} {u : S} (k : K6GoodAt h iU3 p b e u) {KF : Array Aff}
    (hK : Head.callerKeys p (seatAt h iU3) u = some KF) :
    ∀ c, c < KF.size → ∀ d : Aff, SlotsIn b e (KF.getD c d) := by
  intro c hc d
  obtain ⟨⟨g, H, F0, G, rs, hg, hH, hW, hh, _, rfl, rfl, _, _⟩, _⟩ := k
  unfold Head.callerKeys at hK
  obtain ⟨v, hv, hKF⟩ := Option.map_eq_some_iff.mp hK
  obtain ⟨g', b', x'⟩ := v
  have hl : Head.lettersAt p (seatAt h iU3) u = .ok (g', b', x') := by
    cases hx : Head.lettersAt p (seatAt h iU3) u with
    | error w => rw [hx] at hv; cases hv
    | ok w =>
      rw [hx] at hv
      exact congrArg Except.ok (Option.some.inj hv)
  obtain ⟨H', x, e1, e2, e3, e4⟩ := Head.Law.lettersAt_ok h iU3 p hl
  rw [hH] at e2
  obtain rfl := Option.some.inj e2
  have hg1 : (Except.ok g : Except String Given) = .ok g' := hg.symm.trans e1
  obtain rfl := Except.ok.inj hg1
  simp only [Prod.mk.injEq, true_and] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨hN, hR⟩ := Head.Law.reads_bare h iU3 e3
  have hw := reads_wide h iU3 e3
  subst hKF
  letI := g
  letI : FinalNorm.Reads := x.1
  letI : Head.Reads := x.2
  have hks := Head.Law.keys_slotsIn hW hh hN hR hw
  refine getD_has _ (fun f hf => ?_) c hc _
  obtain ⟨cc, _, rfl⟩ := List.mem_map.1 hf
  exact hks cc.1 cc.2

#print axioms slot_inj
#print axioms sV_of_good
#print axioms sV_at_window
#print axioms join_keys_in

end ProofFile.Honest.K6.GoodLaw
