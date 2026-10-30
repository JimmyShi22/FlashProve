-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/KitTwo.lean: the library's challenge kit at the release's field
(`ckP .two`, Run/PlanPull.lean) satisfies the three clauses that `due_typed` (Honest/Law/Due.lean)
asks of a kit (`kit_two`). What a challenge shows has the entry's counts, ranges and signs (the
library's own `fitsDrawn_ckP`, Johnson/Desc/K12/Law/FitWritten.lean); the words of the elements
drawn are below the prime; and a sealed digest is shown at a round of the kind "sealed" alone.

  `toU_lt`, `elems_lt`         the words
  `digest_none`, `sealed_mem`  the digest
  `kit_two`                    the three clauses

Limits.
  * Nothing is said on how the challenges are distributed.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.K12.Law.FitWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (fieldPrimeWord)
open Run (ckP FV Vals outAll toU toU3)

theorem toU_lt (x : FV .two) : toU x < fieldPrimeWord := by
  have hx : x.val < 2 ^ 64 := lt_of_lt_of_le x.isLt (by decide)
  have hp : fieldPrimeWord.toNat = Fmt.Fld.two.p := by decide
  unfold toU
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hx, hp]
  exact x.isLt

theorem elems_lt : ∀ (ds : List Fmt.Draw) (v : Vals .two ds),
    ∀ z ∈ (Fmt.collect (outAll .two ds v)).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord
  | [], _, _, h => nomatch h
  | .elem :: ds, v, z, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨toU_lt _, toU_lt _, toU_lt _⟩
    · exact elems_lt ds v.2 z h
  | .elemNZ :: ds, v, z, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨toU_lt _, toU_lt _, toU_lt _⟩
    · exact elems_lt ds v.2 z h
  | .pos _ :: ds, v, z, h => elems_lt ds v.2 z h
  | .trits _ :: ds, v, z, h => elems_lt ds v.2 z h
  | .sealed :: ds, v, z, h => elems_lt ds v.2 z h

theorem digest_none : ∀ (ds : List Fmt.Draw) (v : Vals .two ds), Fmt.Draw.sealed ∉ ds →
    (Fmt.collect (outAll .two ds v)).digest = none
  | [], _, _ => rfl
  | .elem :: ds, v, h => digest_none ds v.2 fun k => h (List.mem_cons_of_mem _ k)
  | .elemNZ :: ds, v, h => digest_none ds v.2 fun k => h (List.mem_cons_of_mem _ k)
  | .pos _ :: ds, v, h => digest_none ds v.2 fun k => h (List.mem_cons_of_mem _ k)
  | .trits _ :: ds, v, h => digest_none ds v.2 fun k => h (List.mem_cons_of_mem _ k)
  | .sealed :: _, _, h => absurd List.mem_cons_self h

theorem sealed_mem (e : Fmt.Entry) (k : Fmt.Kind) (h : Fmt.Draw.sealed ∈ Fmt.dsOf e k) :
    k = .sealed := by
  unfold Fmt.dsOf at h
  rcases List.mem_append.1 h with h | h
  · have h1 := (List.mem_replicate.1 h).2
    cases h1
  · rcases List.mem_append.1 h with h | h
    · have h1 := H2K.Fit.dsElems_isE e k _ h
      cases h1
    · rcases List.mem_cons.1 h with h | h
      · cases h
      · by_cases hk : k = .sealed
        · exact hk
        · rw [if_neg hk] at h
          cases h

/-- **The kit at the release's field satisfies the three clauses.** -/
theorem kit_two : ∀ e k (c : (ckP .two).Ch e k),
    H2K.Fit.FitsDrawn e k ((ckP .two).dr e k c) ∧
    (∀ z ∈ ((ckP .two).dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
    (((ckP .two).dr e k c).digest = none ∨ k = .sealed) := by
  intro e k c
  refine ⟨H2K.Fit.fitsDrawn_ckP e k c, elems_lt _ _, ?_⟩
  by_cases hk : k = .sealed
  · exact Or.inr hk
  · exact Or.inl (digest_none _ _ fun h => hk (sealed_mem e k h))

end ProofFile.Honest

#print axioms ProofFile.Honest.toU_lt
#print axioms ProofFile.Honest.elems_lt
#print axioms ProofFile.Honest.digest_none
#print axioms ProofFile.Honest.sealed_mem
#print axioms ProofFile.Honest.kit_two
