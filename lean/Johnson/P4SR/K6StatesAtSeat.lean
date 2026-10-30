-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P4SR/K6StatesAtSeat.lean (a law about the seat's form and the lot's block, no part of either): THE NAMED
PREMISE K6States (Johnson/Desc/Kinds/Law/K6Silent.lean: which runs stand at the link's hearing block under the head's four
names) AT A BLOCK THAT IS THE SEATED BLOCK, ALONE, IN THE SEAT's DRESS. Theorems.

Why. The reader of the head's silent forms and the tie of the promises take K6States as a premise. At the seat the
link's fourth hearing block is the seated block b' under the mark's guard, the spot's name, the driver's address and the
driver's guard on the reply (IMR/SeatForm.lean: LaidAlone same b b' name a). That dress keeps the names of the runs
and only adds refusals.

What is said.
  lookup_of_mem     a name among a list's first components is looked up.
  seated_names      the seated block states four runs: norm, join, policy, logits.
  **k6States_of_laid**   for all W, l, ms, b', b, same, name, a, Lk, i with Head.seatedClaims W l ms = some b',
                    LaidAlone same b b' name a and Lk.hear[i]? = some b: there is iU3 with
                    W.H.tl.ix.U.getD 2 none = some iU3 and
                    K6States W.hS iU3 (parOf W.hS (workAtW W)) l 4 (K9.statesOfLink Lk) i.
How. Law/K6StatesOfHear.lean's bridge; its four premises from IMR/SeatForm.lean (claims_lookup, claim_yes)
and Law/SeatedRuns.lean (seated_claims, seated_run, seated_join).

The letters. iU3 stands under "there is", TIED BY THE EQUATION THAT MAKES IT. b' IS PINNED BY ITS OWN EQUATION
(seatedClaims W l ms = some b'): LaidAlone alone does not determine it.
What it does not give. THE THREE PREMISES AT THE DESCRIPTION's OWN CHAIN (link 24, hearing block 3):
k6_of hands them out: the joining is two lines: P4SR/K6StatesAtChain.lean (k6States_at_seat). Nothing on the way back
(a run of the kind that answers need not answer in the dress). Nothing on soundness.

-/
import Johnson.IMR.SeatForm
import Johnson.Desc.Kinds.Law.K6StatesOfHear
import Johnson.Desc.Kinds.Law.SeatedRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4
open VerifiableInference.Desc (Block Claim Link Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW seated_claims seated_run seated_join K6States
  K6Name k6States_of_hear)

/-- A name among a list's first components is looked up. -/
theorem lookup_of_mem {β : Type} : ∀ (l : List (String × β)) (n : String), n ∈ l.map (·.1) →
    ∃ r, l.lookup n = some r
  | [], _, h => by cases h
  | (a, r) :: tl, n, h => by
    by_cases e : n = a
    · subst e
      exact ⟨r, List.lookup_cons_self⟩
    · have e' : (n == a) = false := by simpa using e
      rw [List.lookup_cons, e']
      rcases List.mem_cons.1 h with h | h
      · exact absurd h e
      · exact lookup_of_mem tl n h

/-- The seated block states four runs, under these names, in this order. -/
theorem seated_names {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b' : Block S Claim} (hs : seatedClaims W l ms = some b') :
    b'.claims.map (·.1) = ["norm", "join", "policy", "logits"] := by
  obtain ⟨iU3, _, e⟩ := seated_claims hs
  rw [e]
  rfl

/-- **K6States at our seated block in the seat's dress.** -/
theorem k6States_of_laid {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b' b : Block S Claim} {same : S → S → Bool} {name : String} {a : Place} {Lk : Link S Claim}
    {i : Nat} (hs : seatedClaims W l ms = some b') (hla : IM.LaidAlone same b b' name a)
    (hb : Lk.hear[i]? = some b) :
    ∃ iU3, W.H.tl.ix.U.getD 2 none = some iU3 ∧
      K6States W.hS iU3 (parOf W.hS (workAtW W)) l 4 (VerifiableInference.Desc.K9.statesOfLink Lk) i := by
  obtain ⟨iU3, hU, _⟩ := seated_claims hs
  refine ⟨iU3, hU, k6States_of_hear W.hS iU3 _ l 4 Lk i b hb ?_ ?_ ?_⟩
  · intro n hN
    have hm : n ∈ b'.claims.map (·.1) := by
      rw [seated_names hs]
      rcases hN with rfl | rfl | rfl | rfl <;> simp
    obtain ⟨r', hr'⟩ := lookup_of_mem _ _ hm
    exact ⟨IM.guardRun same r', by rw [IM.claims_lookup hla, hr']; rfl⟩
  · intro n run hn hr
    obtain ⟨r', h', -, hy⟩ := IM.claim_yes hla hr
    have hne : n ≠ "join" := by
      rcases hn with rfl | rfl | rfl <;> decide
    obtain ⟨j, hU', hk⟩ := seated_run hs h' hne
    obtain rfl : j = iU3 := Option.some.inj (hU'.symm.trans hU)
    exact ⟨r', hk, fun k t y h => ((hy k t y).1 h).1⟩
  · intro run hr k t y h
    obtain ⟨r', h', -, hy⟩ := IM.claim_yes hla hr
    obtain ⟨j, hU', e⟩ := seated_join hs h'
    obtain rfl : j = iU3 := Option.some.inj (hU'.symm.trans hU)
    rw [← e]
    exact ((hy k t y).1 h).1

end P4

#print axioms P4.seated_names
#print axioms P4.k6States_of_laid
