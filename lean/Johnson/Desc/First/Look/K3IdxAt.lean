-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3IdxAt.lean: the lookup on a link's CALLS: THE LETTER idx OF THE PUBLIC
TIES AT A LINK (linkTieB, Johnson/Goal/Meaning/ReadingsOne.lean; OneNumber,
Johnson/Desc/First/Look/K3CopiesOne.lean) AS A CLOSED TERM WITH CODE, AT ANY NUMBERING num OF THE
MESSAGES: idxAt D num l n: the place, in link l's own list of messages (the kept ones, then the
link's own), of the message whose number is n. IT TAKES THE LINK: a message that one link owns and
another borrows stands at two places in the two links' lists. The like of idxP (ReadingsOne.lean),
which stands at the one numbering numP. With the lemma that the ties' third clause wants, and a test
with code for its premise. On public data alone. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs in the verifier: functions of the request's shape.
Used by K5CellsOfAt.lean, K5OneView.lean, K5TieWitness.lean (Johnson/Desc/First/Att/Door/Law/) and
  others.
LETTERS: D: what has been sent (its field shape alone is read); num; l: a link; n: a number.

Main names: `candsAt` (the messages of link l's list, each as (the link that first sent it, its
  number among that link's)) · `idxAt` · `numPartsB` (num gives two numbers to two messages of
  the list) · `idxAt_pair` (the like of msgIn_pair).

Limits. Nothing says that linkTieB says yes at idxAt. 0 where no message of the list has the number.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerAttReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- The messages of link l's list: the kept ones as they were first sent, then the link's own. -/
def candsAt (D : Sent) (l : Nat) : List (Nat × Nat) :=
  (bornAt D l).toList ++
    (List.range (((D.shape.link[l]?).map (·.messages.length)).getD 0)).map fun a => (l, a)

/-- **Where the message of number n stands in link l's own list.** -/
def idxAt (D : Sent) (num : Nat → Nat → Nat) (l n : Nat) : Nat :=
  (((candsAt D l).find? fun oa => num oa.1 oa.2 == n).bind fun oa => msgIn D l oa.1 oa.2).getD 0

/-- A test: num gives two numbers to two messages of link l's list. -/
def numPartsB (D : Sent) (num : Nat → Nat → Nat) (l : Nat) : Bool :=
  (candsAt D l).all fun p => (candsAt D l).all fun q => num p.1 p.2 != num q.1 q.2 || p == q

/-- **Under the test the tie of a message's place says: the message stands in link l's list.** -/
theorem idxAt_pair (D : Sent) (num : Nat → Nat → Nat) (l o a : Nat)
    (hB : numPartsB D num l = true) (hm : (o, a) ∈ candsAt D l)
    (h : (msgIn D l o a).isSome = true) : msgIn D l o a = some (idxAt D num l (num o a)) := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 h
  unfold idxAt
  cases hf : (candsAt D l).find? fun oa => num oa.1 oa.2 == num o a with
  | none =>
    have h0 := List.find?_eq_none.1 hf (o, a) hm
    simp at h0
  | some p =>
    have hp0 := List.find?_some hf
    have hp : (num p.1 p.2 == num o a) = true := hp0
    have hpm : p ∈ candsAt D l := List.mem_of_find?_eq_some hf
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hB p hpm) (o, a) hm
    rw [Bool.or_eq_true] at h1
    have e : p = (o, a) := by
      rcases h1 with h1 | h1
      · rw [bne_iff_ne] at h1
        exact absurd (beq_iff_eq.1 hp) h1
      · exact beq_iff_eq.1 h1
    rw [e]
    show msgIn D l o a = some ((msgIn D l o a).getD 0)
    rw [hj]
    rfl

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.idxAt_pair
