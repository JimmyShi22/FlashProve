-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/CallerSlots.lean: WHICH LEDGER SLOTS THE OUTPUT HEAD's
FORMS FOR THE LOOKUP ON ITS CALLS NAME: THE READERS OF THE PLANES' MATRIX (`Head.callerReaders` at
`Head.planesAt`) HAND FORMS THAT NAME NO SLOT, AT EVERY STATE; THE CALLS' KEY VECTORS
(`Head.callerKeys`) NAME SLOTS OF THE HEAD's OWN WINDOW ALONE, AT A STATE WITH THE INVARIANT
`K6GoodAt` (Honest/K6/GoodLaw/Runs.lean). On the verifier's text alone. No definition; five
theorems.

What for. The authors of the kind "lookup" ask of the caller, slot by slot, that its key forms and
its readers' forms do not name a slot of the lookup's own stretch, or the merge's slot. The three
ends here are in the forms that they named; the carriage to their own sentences is theirs.

  `planeEntry_noSlot`, `planesAt_noSlot`   a form that `planeEntry` hands is one entry of the reads'
                         array (`Aff.ent`): its list of slots is empty
  `callerBits_noSlot`    **the readers of bits**: first component. NO PREMISE ON THE STATE
  `callerPins_noSlot`    **the reader of the pin**: second component. NO PREMISE ON THE STATE
  `callerKeys_slotsIn`   **the key vectors**: every slot that one names lies from b on and below e.
                         CONDITIONAL: the invariant at the state, with the window's two ends b, e

By. The library's `keys_slotsIn` (Johnson/Desc/Kinds/Law/KeysHave.lean), `reads_bare`
(Johnson/Desc/Kinds/Law/RunsStill.lean), `lettersAt_ok`; our `reads_wide` (Runs.lean). The last
proof follows the lines of `join_unnamed` (Runs.lean) and stops where that one widens the window.

Limits.
  * THAT THE INVARIANT STANDS AT ANY STATE is not said here: Runs.lean's head says where it holds.
  * Of the invariant's clauses the tests on the samples and the lookup's own debt are not spent.
  * b and e are letters: which written numbers they are, and that the lookup's stretch ends at or
    below b, is not said here.
  * Nothing on the entries that a form names. Nothing on any value.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Runs
import Johnson.Desc.Kinds.HeadCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6.GoodLaw
open OnBytes.Model (Aff)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (Given seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (SlotsIn)

/-- A form that `planeEntry` hands names no slot. -/
theorem planeEntry_noSlot (tab : List (String × Nat × Nat)) (iU3 cols : Nat) (x : Head.PlaneRead)
    (i : Nat) (a : Form) (h : Head.planeEntry tab iU3 cols x i = some a) : a.slots = #[] := by
  unfold Head.planeEntry at h
  obtain ⟨e, _, h2⟩ := Option.bind_eq_some_iff.mp h
  split at h2
  · obtain rfl := Option.some.inj h2
    rfl
  · cases h2

/-- So does every form that the seat of the three further reads hands. -/
theorem planesAt_noSlot (iU3 : Nat) (t : S) (at_ : Head.PlaneRead → Nat → Option Form)
    (h : Head.planesAt iU3 t = some at_) : ∀ x i a, at_ x i = some a → a.slots = #[] := by
  unfold Head.planesAt at h
  split at h
  · obtain ⟨tt, _, e1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tr, _, e2⟩ := Option.bind_eq_some_iff.mp e1
    split at e2
    · cases e2
    · obtain rfl := Option.some.inj e2
      exact fun x i a ha => planeEntry_noSlot _ _ _ x i a ha
  · cases h

/-- **THE READERS OF BITS NAME NO SLOT**, at every state. -/
theorem callerBits_noSlot (iU3 : Nat) (t : S) :
    ∀ r, Head.callerReaders (Head.planesAt iU3) t = some r →
      ∀ e col a, r.1 e col = some a → a.slots = #[] := by
  intro r hr e col a ha
  unfold Head.callerReaders at hr
  obtain ⟨at_, hat, rfl⟩ := Option.map_eq_some_iff.mp hr
  exact planesAt_noSlot iU3 t at_ hat _ col a ha

/-- **THE READER OF THE PIN NAMES NO SLOT**, at every state. -/
theorem callerPins_noSlot (iU3 : Nat) (t : S) :
    ∀ r, Head.callerReaders (Head.planesAt iU3) t = some r →
      ∀ col a, r.2 col = some a → a.slots = #[] := by
  intro r hr col a ha
  unfold Head.callerReaders at hr
  obtain ⟨at_, hat, rfl⟩ := Option.map_eq_some_iff.mp hr
  exact planesAt_noSlot iU3 t at_ hat _ col a ha

/-- CONDITIONAL: the invariant at t. **EVERY SLOT THAT A CALL's KEY VECTOR NAMES LIES IN THE HEAD's
OWN WINDOW.** -/
theorem callerKeys_slotsIn (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Head.Par) (b e : Nat)
    (t : S) (hI : K6GoodAt h iU3 p b e t) :
    ∀ KF, Head.callerKeys p (seatAt h iU3) t = some KF → ∀ a ∈ KF, SlotsIn b e a := by
  intro KF hK a ha
  obtain ⟨⟨g, H, F0, G, rs, hg, hH, hW, hh, _, rfl, rfl, _, _⟩, _⟩ := hI
  unfold Head.callerKeys at hK
  obtain ⟨v, hv, hKF⟩ := Option.map_eq_some_iff.mp hK
  obtain ⟨g', b', x'⟩ := v
  have hl : Head.lettersAt p (seatAt h iU3) t = .ok (g', b', x') := by
    cases hx : Head.lettersAt p (seatAt h iU3) t with
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
  obtain ⟨cc, _, rfl⟩ := List.mem_map.1 (List.mem_toArray.1 ha)
  exact hks cc.1 cc.2

end ProofFile.Honest.K6.GoodLaw

#print axioms ProofFile.Honest.K6.GoodLaw.planeEntry_noSlot
#print axioms ProofFile.Honest.K6.GoodLaw.planesAt_noSlot
#print axioms ProofFile.Honest.K6.GoodLaw.callerBits_noSlot
#print axioms ProofFile.Honest.K6.GoodLaw.callerPins_noSlot
#print axioms ProofFile.Honest.K6.GoodLaw.callerKeys_slotsIn
