-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file stands over Block.lean and State.lean, and over the seats that go with
them (Stored/HeadSeatAt.lean, Stored/ReplySeatAt.lean). In the made-up record
x is laid by hand (by State.lean an
honest record in front holds none there: NOT looked at here).
Johnson/Desc/Kinds/Law/K06ToyRecord.lean: THE RECORD OF K06_law's TOY, AND WHAT HOLDS OF IT WITHOUT A ROUND: a record of the first chain, LAID BY HAND, in front of the output head's own rounds, at the
head's public numbers of the stored full-size example (Law/K07MemberAt.lean: hR; the lookup's made-up points gR).
  sK        unmarked · the head's link opened, the lookup heard (gR) · the reply 0 held (e < T: the next token's own test asks 0 there) · the request's 1026 words: 1024 tokens 0, then r = 0,
            e = 1023: EVERY POSITION BELOW 1023 IS CHECKED AND HAS A COST (costed_K; rc_K : RC = 1023; cost_K; figures_K) · the ledger: a fresh ledger of 1000 numbers.
  plan_ok · has_features · start_ok · token_lt · given_K · ledger_K · lays_K: the premises of the row at this record that read no round; the seat's two layings return.
  admits_K  Admits (Law/CellsWithCosts.lean) at the record's letters: the policy admits the cost 2^sh = 256 = theta at every costed position.

WHAT IT IS NOT. A record of no run and no fold. Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K07MemberAt
import Johnson.Desc.Kinds.Law.RowRides
import Johnson.Desc.Kinds.Law.NormSends
import Johnson.Desc.Kinds.Law.CellsWithCosts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Fork)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First (S)

namespace K06Toy

open K07Real (hR pR gR)

/-- The ledger in front: fresh, of 1000 numbers. -/
def FK : Fork := Part.MaskedSum.freshLedger 1000

/-- The request's words: 1024 tokens 0; the first covered position 0; the position behind the last 1023. -/
def reqK : Array UInt32 := ⟨List.replicate 1024 0 ++ [0, 1023]⟩

/-- The record in front of the head's own rounds. -/
def sK : S :=
  { S.blank with
    failed := none
    req := reqK
    out := { S.blank.out with reply := some (E.mk3 0 0 0) }
    here := .head { fr := S.blank.check.frame, kept := #[], ids := #[],
                    L := { check := S.blank.check }, F := FK, tl := {}, Fm := {},
                    opened := true, lookHeard := some gR,
                    x := some { VerifiableInference.Desc.First.blankHeard with g1 := gR } } }

theorem plan_ok : pR.ok = true := by decide

theorem has_features : hasFeatures pR := by
  show 0 < 5120
  omega

theorem ledger_K : (seatAt hR 0).ledger sK = FK := rfl

theorem given_K : (given pR (seatAt hR 0) sK).toOption.isSome = true := by decide

theorem token_K : Reply.token (seatAt hR 0).toSeat sK = some 0 := by decide

set_option maxRecDepth 100000 in
theorem rowR_K : sK.rowR = 0 := by decide
set_option maxRecDepth 100000 in
theorem rowE_K : sK.rowE = 1023 := by decide
set_option maxRecDepth 100000 in
theorem reqT_K : sK.reqT = 1024 := by decide

/-- Every word of the request is below the vocabulary's size. -/
theorem words_small : ∀ w ∈ reqK.toList, w.toNat < 202048 := by
  intro w hw
  have hw' : w ∈ List.replicate 1024 (0 : UInt32) ++ [0, 1023] := hw
  rcases List.mem_append.mp hw' with h | h
  · rw [List.eq_of_mem_replicate h]
    decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide

set_option maxRecDepth 100000 in
/-- Every token that the record's request names is an entry of the vocabulary. -/
theorem tok_small (t : Nat) : sK.tokv.getD t 0 < 202048 := by
  by_cases ht : t < sK.tokv.size
  · have e : sK.tokv.getD t 0 = sK.tokv[t]'ht := by simp [Array.getD, ht]
    rw [e]
    have hm : sK.tokv[t]'ht ∈ sK.tokv.toList := Array.getElem_mem_toList ht
    unfold S.tokv at hm
    rw [Array.toList_map] at hm
    obtain ⟨w, hw, e2⟩ := List.mem_map.mp hm
    have e3 : sK.tokv[t]'ht = w.toNat := e2.symm
    rw [e3]
    refine words_small w ?_
    rw [Array.toList_extract] at hw
    rw [List.extract_eq_drop_take] at hw
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  · have e : sK.tokv.getD t 0 = 0 := by simp [Array.getD, ht]
    rw [e]
    omega

theorem start_ok : pR.okStart ((seatAt hR 0).request sK) = true := by
  unfold Par.okStart Request.ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, fun t _ => tok_small t⟩
  · show sK.rowR < sK.rowE
    rw [rowR_K, rowE_K]
    omega
  · show sK.rowE ≤ 2 ^ 10
    rw [rowE_K]
    omega

theorem token_lt : ∀ y, Reply.token (seatAt hR 0).toSeat sK = some y → y < pR.sizes.V := by
  intro y hy
  rw [token_K] at hy
  obtain rfl := Option.some.inj hy
  show 0 < 202048
  omega

set_option maxRecDepth 100000 in
/-- Every token of the record's request is 0. -/
theorem tok_zero (t : Nat) : sK.tokv.getD t 0 = 0 := by
  by_cases ht : t < sK.tokv.size
  · have e : sK.tokv.getD t 0 = sK.tokv[t]'ht := by simp [Array.getD, ht]
    rw [e]
    have hm : sK.tokv[t]'ht ∈ sK.tokv.toList := Array.getElem_mem_toList ht
    unfold S.tokv at hm
    rw [Array.toList_map] at hm
    obtain ⟨w, hw, e2⟩ := List.mem_map.mp hm
    have e3 : sK.tokv[t]'ht = w.toNat := e2.symm
    rw [e3]
    rw [Array.toList_extract, List.extract_eq_drop_take, reqT_K] at hw
    have hw2 : w ∈ (List.replicate 1024 (0 : UInt32) ++ [0, 1023]).take 1024 := hw
    rw [List.take_left' (List.length_replicate ..)] at hw2
    rw [List.eq_of_mem_replicate hw2]
    rfl
  · simp [Array.getD, ht]

section Letters

/-- The record's letters, the token 0. -/
local instance : Sizes := pR.sizes
local instance : Policy := pR.policy
local instance : Request := (seatAt hR 0).request sK
local instance : Token := ⟨0⟩

theorem win_K (t : Nat) : win t = 0 := by
  unfold win
  split
  · exact tok_zero (t + 1)
  · rfl

/-- Admits at the record's letters. -/
theorem admits_K : Admits :=
  ⟨fun t _ => by
      unfold costN
      rw [win_K]
      decide,
    by decide, last_of_lt (by
      show sK.rowE < 2 ^ 10
      rw [rowE_K]
      omega)⟩

/-- Every position below 1023 has a cost. -/
theorem costed_K {t : Nat} (ht : t < 1023) : costed t = true := by
  unfold costed checked
  have h1 : (r : Nat) = 0 := rowR_K
  have h2 : (e : Nat) = 1023 := rowE_K
  have h3 : (T : Nat) = 1024 := rfl
  rw [h1, h2, h3]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The figures that the heads name, off the record's letters. -/
theorem figures_K : (sh : Nat) = 8 ∧ (theta : Nat) = 256 ∧ (C : Nat) = 256 ∧ (cap : Nat) = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The number of positions with a cost. -/
theorem rc_K : RC = 1023 := by
  unfold RC
  have h1 : (r : Nat) = 0 := rowR_K
  have h2 : (e : Nat) = 1023 := rowE_K
  have h3 : (T : Nat) = 1024 := rfl
  rw [h1, h2, h3]
  rfl

/-- The cost that the cells pay at every position: the lift alone. -/
theorem cost_K (t : Nat) : costN t = 256 := by
  unfold costN
  rw [win_K]
  rfl

end Letters

/-- The seat's two layings return at this record, whatever is laid. -/
theorem lays_K (F1 : Fork) (H : HeardAll) :
    ∃ s1 s2, (seatAt hR 0).setLedger sK F1 = .ok s1 ∧ (seatAt hR 0).setHeard s1 H = .ok s2 :=
  ⟨_, _, rfl, rfl⟩

theorem wellLaid_K : WellLaid ((seatAt hR 0).ledger sK) := by
  letI := pR.sizes
  letI := pR.policy
  letI : Request := requestOf sK
  letI : Token := ⟨0⟩
  exact (fresh_ledger 1000).1
theorem fresh_K : Fresh ((seatAt hR 0).ledger sK) 1000 := by
  letI := pR.sizes
  letI := pR.policy
  letI : Request := requestOf sK
  letI : Token := ⟨0⟩
  exact (fresh_ledger 1000).2

end K06Toy

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.K06Toy.plan_ok
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K06Toy.start_ok
#print axioms VerifiableInference.Desc.Kinds.Head.Law.K06Toy.lays_K
