-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/ArrApartChains.lean: the numbering `arrOf` of the witness's messages
(Johnson/P5T/PlanSeats.lean) gives a seat of the first chain's list and a seat of a later chain's
list different numbers, where the first chain has at most 1000 sendings. Statements with their
proofs. No Mathlib is imported here.

Why it holds. Two seats that are found in the list and bear one number have one key (`arrOf_key`,
Johnson/P5T/ArrApart.lean). The key of a seat of the first chain's list begins with 0, or it is
(1, s, i) with s the number of one of that chain's sendings. The key of a seat of a later chain's
list is (1, 1000 * chain + s', i'), by the make of `chainSeats`.

  `keyOf_or`: the two forms of a key. `planSeats_send`: a seat of the first chain's list bears the
    number of one of that chain's sendings.
  `key_apart_chains`: the keys differ, at every later chain (1 ≤ chain).
  `arr_apart_first`: so the numbers differ, in any list in which both seats are found.
  `arr_apart_chains`: **the statement**, at the list of all three chains' seats (`planSeatsAll`) and
    the shared chain. `arr_apart_chains_last`: the like at the last chain.

Can the premises be met? That both seats are found in the list, each at its own tree and tenant, is
a fact on the list of rounds at the public files: not shown here. The bound of 1000 sendings is a
test on that list: not run here. Without it the statement is not meant: sending number 1000 of the
first chain would share its key's second number with the shared chain's sending number 0.
Limits. Nothing on two seats of one chain (Johnson/P5T/ArrApart.lean), nor on a seat of the shared
chain against one of the last. Nothing on soundness.
-/
import Johnson.P5T.ArrApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T

/-- A seat's key begins with 0, or it is (1, the sending's number, the place in the sending). -/
theorem keyOf_or (p : PSeat) : (keyOf p).1 = 0 ∨ keyOf p = (1, p.send, p.idx) := by
  unfold keyOf
  split
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A seat of the first chain's list bears the number of one of that chain's sendings. -/
theorem planSeats_send (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (p : PSeat)
    (h : p ∈ planSeats Z dl) : p.send < Z.made.proof.1.sends.length := by
  unfold planSeats at h
  dsimp only at h
  obtain ⟨s, hs, hp⟩ := List.mem_flatMap.1 h
  cases hl : OnBytes.layTrees Z.made.proof.1.codes s.1.sent.toArray with
  | none => rw [hl] at hp; cases hp
  | some lay =>
    rw [hl] at hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
    have a := List.mem_zipIdx hs
    show s.2 < _
    omega

/-- **A seat of the first chain's list and a seat of a later chain's list have different keys**,
where the first chain has at most 1000 sendings. -/
theorem key_apart_chains (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (chain base : Nat)
    (c : Johnson.G.ChainSends) (dl' : List Fmt.DeclaredRound) (p p' : PSeat)
    (h0 : p ∈ planSeats Z dl) (h1 : p' ∈ chainSeats chain base c dl') (hc : 1 ≤ chain)
    (hlen : Z.made.proof.1.sends.length ≤ 1000) : keyOf p ≠ keyOf p' := by
  intro hk
  obtain ⟨s', lay', i', _, _, rfl⟩ := chainSeats_mem chain base c dl' p' h1
  have hk' : keyOf p = (1, 1000 * chain + s'.2, i') := hk
  rcases keyOf_or p with e | e
  · rw [hk'] at e
    exact Nat.one_ne_zero e
  · rw [e] at hk'
    have e2 : p.send = 1000 * chain + s'.2 := congrArg (fun x : Nat × Nat × Nat => x.2.1) hk'
    have e3 := planSeats_send Z dl p h0
    omega

/-- The same on the numbers, in any list in which both seats are found. -/
theorem arr_apart_first (ps : List PSeat) (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound)
    (chain base : Nat) (c : Johnson.G.ChainSends) (dl' : List Fmt.DeclaredRound) (j t j' t' : Nat)
    (p p' : PSeat) (hp : (ps.find? fun q => q.j == j && q.t == t) = some p)
    (hp' : (ps.find? fun q => q.j == j' && q.t == t') = some p') (h0 : p ∈ planSeats Z dl)
    (h1 : p' ∈ chainSeats chain base c dl') (hc : 1 ≤ chain)
    (hlen : Z.made.proof.1.sends.length ≤ 1000) : arrOf ps j t ≠ arrOf ps j' t' :=
  fun h => key_apart_chains Z dl chain base c dl' p p' h0 h1 hc hlen
    (arrOf_key ps j t j' t' p p' hp hp' h)

/-- **A seat of the first chain's list and a seat of the shared chain's list never bear one
number.** -/
theorem arr_apart_chains (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (j t j' t' : Nat)
    (p p' : PSeat)
    (hp : ((planSeatsAll Z D).find? fun q => q.j == j && q.t == t) = some p)
    (hp' : ((planSeatsAll Z D).find? fun q => q.j == j' && q.t == t') = some p')
    (h0 : p ∈ planSeats Z D.1)
    (h1 : p' ∈ chainSeats 1 (rootsBefore D.1 D.1.length) Z.made.proof.2.1 D.2.1)
    (hlen : Z.made.proof.1.sends.length ≤ 1000) :
    arrOf (planSeatsAll Z D) j t ≠ arrOf (planSeatsAll Z D) j' t' :=
  arr_apart_first _ Z D.1 1 _ _ D.2.1 j t j' t' p p' hp hp' h0 h1 (Nat.le_refl 1) hlen

/-- The like for the last chain's list. -/
theorem arr_apart_chains_last (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (j t j' t' : Nat)
    (p p' : PSeat)
    (hp : ((planSeatsAll Z D).find? fun q => q.j == j && q.t == t) = some p)
    (hp' : ((planSeatsAll Z D).find? fun q => q.j == j' && q.t == t') = some p')
    (h0 : p ∈ planSeats Z D.1)
    (h1 : p' ∈ chainSeats 2 (rootsBefore D.1 D.1.length + rootsBefore D.2.1 D.2.1.length)
      Z.made.proof.2.2 D.2.2)
    (hlen : Z.made.proof.1.sends.length ≤ 1000) :
    arrOf (planSeatsAll Z D) j t ≠ arrOf (planSeatsAll Z D) j' t' :=
  arr_apart_first _ Z D.1 2 _ _ D.2.2 j t j' t' p p' hp hp' h0 h1 (by decide) hlen

end P5T

#print axioms P5T.keyOf_or
#print axioms P5T.planSeats_send
#print axioms P5T.key_apart_chains
#print axioms P5T.arr_apart_first
#print axioms P5T.arr_apart_chains
#print axioms P5T.arr_apart_chains_last
