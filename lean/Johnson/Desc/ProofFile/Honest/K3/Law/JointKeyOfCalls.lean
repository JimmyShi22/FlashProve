-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Law/JointKeyOfCalls.lean: the kind "lookup" (K3): the library's
joint key vector (`jointKey`, OnBytes/Tie/Pv/Lookup/Ends/Joint.lean), at the indices below 2 ^ v,
hangs on the calls' key vectors below their own lengths alone. One theorem; no definition. Public
numbers of a shape and two families of vectors: no site, no coin, no Script, no mask.

Why. `FillsAt.keys`, `FillsAt.turn` and `TiedTo.keys` (Thread/ExchangeFillAt.lean,
Thread/ExchangeMg.lean, Thread/ExchangeTies.lean) speak of the joint vector at every index below
2 ^ s.shape.v. Whoever ties two makes of key vectors call by call, key number by key number, has an
equation at each call c below NC and each number below 2 ^ n_c. This theorem leads from the second
form to the first.

What is shown.
  `jointKey_congr`: where the library's test `FoNums.ok` accepts the shape h, and kv and kv' agree
    at every call c below h.NC at every number below 2 ^ `FoNums.nOf` h c: the two joint vectors
    agree at every index below 2 ^ h.v, at every shift θ. General in the ring.

How the proof goes. Index X stands for place X / 2 ^ rK of tree X % 2 ^ rK. Below 2 ^ v the place is
below 2 ^ dT (`Cb.ldLkpShift_split`, Cb/Ld/LdLkpShiftProofs.lean). At a tree from NT on the joint
vector reads no key. At a tree y below NT it reads its call's key number (y - first) * 2 ^ dT +
place; by three clauses of the test (`Cb.Fo.ok_parts`, OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean) the
call is below NC, y - first is below 2 ^ iota, and n is iota + dT: so that number is below 2 ^ n
(`Cb.ldLkpShift_num`).

Hypotheses that remain. hok: the library's test on the shape's numbers: public; at every site of a
public part it accepts (`FastLaw.sites_ok`, Honest/K3/FastLaw/Sites.lean; not called here). hk: the
agreement of the two families: whoever calls the theorem brings it.

Imported. The library alone: OnBytes/Tie/Pv/Lookup/Ends/Joint.lean,
OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean, Cb/Ld/LdLkpShiftProofs.lean.

Users. None in this folder. `jointKey_at` (KeysAreKvG.lean) writes the joint vector out at one place
of one tree; neither theorem calls the other.

Limits. One direction: from the calls' vectors to the joint vector. Nothing on an index from 2 ^ v
on, nor on a key number from 2 ^ n on. Nothing on which vectors a caller, a filling or a witness
has. No instance of hk at two makes of vectors is exhibited in this file.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Tie.Pv.Lookup.Ends.Joint
import OnBytes.Tie.Pv.Lookup.Forest.FoHole
import Cb.Ld.LdLkpShiftProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Ends (jointKey)

/-- **Below 2 ^ v the joint key vector hangs on the calls' key vectors below their own lengths
alone.** Conditional on the library's test on the shape's numbers and on the two families' agreement
at every call below NC, at every number below 2 ^ n of the call. -/
theorem jointKey_congr {R : Type} [CommRing R] (h : OnBytes.Model.Forest.Shape)
    (hok : FoNums.ok h = true) (kv kv' : ℕ → ℕ → R) (θ : R)
    (hk : ∀ c, c < h.NC → ∀ Y, Y < 2 ^ FoNums.nOf h c → kv c Y = kv' c Y) :
    ∀ X, X < 2 ^ h.v → jointKey h kv θ X = jointKey h kv' θ X := by
  intro X hX
  obtain ⟨_, hb, hcc, _⟩ := Cb.Fo.ok_parts hok
  have hx : X / 2 ^ h.rK < 2 ^ h.dT := (Cb.ldLkpShift_split h.dT h.rK X hX).1
  by_cases hy : X % 2 ^ h.rK < h.NT
  · obtain ⟨c1, c2, c3⟩ := hb _ hy
    have hi : (X % 2 ^ h.rK - FoNums.fst h (FoNums.co h (X % 2 ^ h.rK))) * 2 ^ h.dT +
        X / 2 ^ h.rK < 2 ^ FoNums.nOf h (FoNums.co h (X % 2 ^ h.rK)) := by
      rw [(hcc _ c1).2.2.1, Nat.mul_comm, Nat.add_comm _ (X / 2 ^ h.rK)]
      exact (Cb.ldLkpShift_num _ h.dT _ _ (by omega) hx).1
    unfold jointKey
    simp only [hy, if_true]
    exact congrArg (· + _) (hk _ c1 _ hi)
  · unfold jointKey
    simp only [hy, if_false]

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.jointKey_congr
