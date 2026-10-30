-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/Seat.lean: over Johnson/Desc/Ok/PlanWritten/AtDesc.lean: THE LAWS OF THE
FORMS THAT CAN BE COPIED WHOLE (defined in Johnson/Desc/Ok/PlanWritten/Test.lean), with no key left
to the caller's care. `seatPinnedProof pol F`, `seatPinnedKey pol F`: from the public parameter
file: the key off its strict scan; no planner, no hash; WHERE THE SCAN REFUSES: NO. `pinnedProofAt m
F`, `pinnedKeyAt m F`: for a maker that holds its own m. The rules in the goals' scope:
Johnson/Goal/Numbers/PlanWrittenDescScope.lean.

ROW OR TOOL. EVERY DECLARATION HERE IS A TOOL: rules for all descriptions F, all files, all m. No
description is named. F IS A FREE LETTER EVERYWHERE, bound to no file and no m: these files are not
the tie of a description to the written lists; they are what a seat needs for it.

Why. `descPinnedProof k F` takes the key as a letter k. Doors stand open to whoever lays it by hand:
a k from elsewhere than the public parameter file's scan; a scan of other bytes than those of which
the scope was asked; a "yes" in the arm where the scan refuses; a place beside, not beneath, what
the description's yes rests on. The forms here shut the first and the third by their text.

THE CONDITION ON THE SEAT, (S1) to (S5). It was set down for the test with the key of what the
planner makes; word for word, but for one remark in brackets, in (S2), on files that are not in this
library:
  (S1) The description F of the public files Z asks, BENEATH F.planOk (so that F.planOk = true → the
    conjunct = true is provable: IN F.fileOk, Block.lean:155, :545: a Bool that the maker fills, the
    one place beneath planOk that can hold a k WITHOUT TURNING Block.lean; planOkCore's own text
    cannot name k, for want of a field), the Bool match madeOfAt Z.pol Z.lay Z.KL c with | .ok m =>
    descPinnedProof (keyOf m) F₀ | .error _ => false where F₀ has F's three chains and F's
    tableDepth (F.roundsDeclaredByBlocks reads no fileOk: Block.lean:394: so no circle).
  (S2) Z.pol, Z.lay, Z.KL are THE SAME three byte arrays on which InScope was asked.
  (S3) c: any (the ∀ is free: zero32, the format's own digest through madeOf, or the run's).
  (S4) k is read off NOTHING else: no field of the key, entry or proof file, no letter of the
    instance Xi, no number handed in beside Z.
  (S5) the key file's description likewise, with descPinnedKey, AT THE SAME m.
WITH THE KEY OFF THE SCAN the Bool of (S1) is `seatPinnedProof Z.pol F₀`: where `madeOfAt Z.pol
Z.lay Z.KL c` returns the two say the same (`seat_eq_at`); where the planner refuses and the scan
returns, (S1)'s Bool says no and this one asks the test. (S2) then speaks of Z.pol alone, (S3) falls
away, (S4) is met by the text, and (S5) reads: with `seatPinnedKey`, AT THE SAME pol. WHAT THE SEAT
STILL OWES, typed nowhere: that the yes on which its description's laws rest gives a yes of the
conjunct, at the named description.

WHICH FORM FOR WHICH CASE. `seatPinnedProof Z.pol F`, wherever the public parameter file is at hand:
it calls no planner and no hash; the rule in scope is `seat_in_scope`, which names no m and no k.
`pinnedProofAt m F`, where the description is made of an m that its maker already holds, at THAT m;
the rule in scope is `at_in_scope`, whose premise names the call that returned m.

Definitions, statements and proofs.
  `keyOf_eq`: the key of m, written out: three fields of the scan that m holds. By definition.
    `scan_of_made`: where `madeOfAt pol lay KL c` returns m, the strict scan of pol returns, and it
    is the scan that m holds. By the library's `plannedAt_scan` (OnBytes/Tie/PlanAtPolicy.lean).
    `key_of_pol`: SO THE KEY HANGS ON THE PARAMETER FILE ALONE: two m made of one pol, at whatever
    layout files, scale files and digests, have one key.
  `seat_eq_at`, `seat_eq_at_key`: there `seatPinnedProof pol F` is `pinnedProofAt m F`, and the key
    file's like.
  `seat_yes`, `seat_yes_key`: where the scan returns a P with the full size's key, a yes says:
    written out, F's declared rounds are the full size's written lists, its depth is 32, and
    `F.data` returns the written data.
  TEETH. `seat_refusal`: where the scan refuses, the test says no. `seat_plant`: where the scan
    returns the full size's key A PLANT IS REFUSED: if F's declared rounds, written out, are the
    proof file's written lists with one number changed, the test says no.
  THE ARM BEARS WEIGHT. `laxSeat`: the text of `seatPinnedProof` with "yes" in the arm of the
    refusal. `laxSeat_refusal`: where the scan refuses it says yes OF EVERY F, the planted ones too.
    `lax_not_rule`: there, at an F of another depth than 32, it says yes and the rule's conclusion
    fails.
  `seat_other`: where the scan returns another key, the test says yes: outside the full size's key
    nothing is pinned.

What of OnBytes/Model/ and OnBytes/Tie/ is used. Named: `Model.polScan`, `Model.PolScan`
(OnBytes/Model/Config.lean). Called: `Tie.plannedAt_scan`. In premises, through `madeOfAt`:
`Tie.plannedAt`, the text of `Model.Verify.planned`.

Limits. NO DESCRIPTION IS NAMED: nothing is laid anywhere by this file. ONE DIRECTION: nothing here
says that a test says yes anywhere. IT PINS NOTHING OUTSIDE THE FULL SIZE's KEY. That `polScan`
calls no hash is by a search and a reading (the head of Johnson/Desc/Ok/PlanWritten/Test.lean), by
nothing proved. `pinnedProofAt` and `pinnedKeyAt` leave the question which hash the maker of m
reaches with that maker. That there is a parameter file at which the scan refuses is not shown here,
so `lax_not_rule` has a premise. The plants' premises are shown of no F. All limits of
Johnson/Desc/Ok/PlanWritten/AtDesc.lean. Nothing on soundness.


-/
import Johnson.Desc.Ok.PlanWritten.AtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number VerifiableInference.Desc
open OnBytes.Model (polScan PolScan)

variable {Xi : Type}

/-! ## The key hangs on the parameter file alone -/

/-- The key of m, written out. By definition. -/
theorem keyOf_eq (m : Made) : keyOf m = (m.p.X.P.h.L, m.p.X.P.h.d, m.p.X.P.h.V) := rfl

/-- **Where the planner returns, the strict scan of the parameter file returns, and it is the scan
that m holds.** At every digest c. -/
theorem scan_of_made {pol lay KL c : ByteArray} {m : Made} (h : madeOfAt pol lay KL c = .ok m) :
    polScan pol = .ok m.p.X.P :=
  OnBytes.Tie.plannedAt_scan (madeOfAt_planned h)

/-- **Two m made of one parameter file have one key**, whatever the other two files and the
digests. -/
theorem key_of_pol {pol lay KL c lay' KL' c' : ByteArray} {m m' : Made}
    (h : madeOfAt pol lay KL c = .ok m) (h' : madeOfAt pol lay' KL' c' = .ok m') :
    keyOf m = keyOf m' := by
  have e : m.p.X.P = m'.p.X.P := Except.ok.inj ((scan_of_made h).symm.trans (scan_of_made h'))
  unfold keyOf
  rw [e]

/-- Where the planner returns m, the form from the parameter file is the form at m. -/
theorem seat_eq_at {pol lay KL c : ByteArray} {m : Made} (F : FileDescription Xi)
    (h : madeOfAt pol lay KL c = .ok m) : seatPinnedProof pol F = pinnedProofAt m F := by
  unfold seatPinnedProof
  rw [scan_of_made h]
  rfl

/-- The like for a key file's description. -/
theorem seat_eq_at_key {pol lay KL c : ByteArray} {m : Made} (F : FileDescription Xi)
    (h : madeOfAt pol lay KL c = .ok m) : seatPinnedKey pol F = pinnedKeyAt m F := by
  unfold seatPinnedKey
  rw [scan_of_made h]
  rfl

/-! ## What a yes says -/

/-- **Where the scan returns the full size's key, a yes says**: the written lists, the depth 32, and
the written data. -/
theorem seat_yes {pol : ByteArray} {P : PolScan} {F : FileDescription Xi} (hP : polScan pol = .ok P)
    (hk : keyOfScan P = fullKey) (h : seatPinnedProof pol F = true) :
    writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32 ∧
      F.data "proof file" = .ok writtenPFull := by
  unfold seatPinnedProof at h
  rw [hP] at h
  exact ⟨(descPinned_yes hk h).1, (descPinned_yes hk h).2, data_of_pinnedProof hk h⟩

/-- The like for a key file's description. -/
theorem seat_yes_key {pol : ByteArray} {P : PolScan} {F : FileDescription Xi} (hP : polScan pol = .ok P)
    (hk : keyOfScan P = fullKey) (h : seatPinnedKey pol F = true) :
    writtenOf "key file" F.roundsDeclaredByBlocks = .ok dryKeyFull ∧ F.tableDepth = 32 ∧
      F.data "key file" = .ok writtenKFull := by
  unfold seatPinnedKey at h
  rw [hP] at h
  exact ⟨(descPinned_yes hk h).1, (descPinned_yes hk h).2, data_of_pinnedKey hk h⟩

/-! ## Teeth -/

/-- **A tooth: where the scan refuses, the test says no.** -/
theorem seat_refusal {pol : ByteArray} {e : String} (F : FileDescription Xi)
    (h : polScan pol = .error e) : seatPinnedProof pol F = false := by
  unfold seatPinnedProof
  rw [h]

/-- **A tooth: A PLANT IS REFUSED**, where the scan returns the full size's key. -/
theorem seat_plant {pol : ByteArray} {P : PolScan} {F : FileDescription Xi} (hP : polScan pol = .ok P)
    (hk : keyOfScan P = fullKey) (hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok plantedProof) :
    seatPinnedProof pol F = false := by
  unfold seatPinnedProof
  rw [hP]
  exact descPinned_plant hk hw

/-- Where the scan returns another key, the test says yes. -/
theorem seat_other {pol : ByteArray} {P : PolScan} (F : FileDescription Xi) (hP : polScan pol = .ok P)
    (hk : keyOfScan P ≠ fullKey) : seatPinnedProof pol F = true := by
  unfold seatPinnedProof
  rw [hP]
  exact descPinned_other hk

/-! ## The arm of the refusal bears weight -/

/-- The text of `seatPinnedProof` with "yes" in the arm of the refusal. FOR A TOOTH ALONE. -/
def laxSeat (pol : ByteArray) (F : FileDescription Xi) : Bool :=
  match polScan pol with
  | .ok P => descPinnedProof (keyOfScan P) F
  | .error _ => true

/-- Where the scan refuses it says yes of every F. -/
theorem laxSeat_refusal {pol : ByteArray} {e : String} (F : FileDescription Xi)
    (h : polScan pol = .error e) : laxSeat pol F = true := by
  unfold laxSeat
  rw [h]

/-- **So the rule would be false of it**: where the scan refuses, at an F of another depth than 32,
it says yes, and the rule's conclusion fails. -/
theorem lax_not_rule {pol : ByteArray} {e : String} {F : FileDescription Xi}
    (h : polScan pol = .error e) (hd : F.tableDepth ≠ 32) :
    laxSeat pol F = true ∧
      ¬ (writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32) :=
  ⟨laxSeat_refusal F h, fun x => hd x.2⟩

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.keyOf_eq
#print axioms VerifiableInference.PlanWritten.scan_of_made
#print axioms VerifiableInference.PlanWritten.key_of_pol
#print axioms VerifiableInference.PlanWritten.seat_eq_at
#print axioms VerifiableInference.PlanWritten.seat_eq_at_key
#print axioms VerifiableInference.PlanWritten.seat_yes
#print axioms VerifiableInference.PlanWritten.seat_yes_key
#print axioms VerifiableInference.PlanWritten.seat_refusal
#print axioms VerifiableInference.PlanWritten.seat_plant
#print axioms VerifiableInference.PlanWritten.seat_other
#print axioms VerifiableInference.PlanWritten.laxSeat_refusal
#print axioms VerifiableInference.PlanWritten.lax_not_rule
