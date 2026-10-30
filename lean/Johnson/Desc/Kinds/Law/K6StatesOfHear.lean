-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6StatesOfHear.lean: Law/K6Silent.lean's NAMED PREMISE K6States (which runs
stand at the link's block under the head's four names) FROM WHAT THE LINK's LAW's FILES AND THE
LOT's FILES CONCLUDE, in plain terms: a bridge. Statements and proofs.

  find_of_lookup   a list's lookup under a name, as the first pair with that name.
  k6States_of_hear at a link whose hearing block number b is blk: where blk states a run under each
                   of the four names, and every run that blk states under one of them only adds
                   refusals to the bare kind's run of that name (at "join": to the lookup's joinRun
                   at the caller's keys): K6States at statesOfLink Lk and b.

WHAT IT IS NOT. An implication: hb, hn, hown, hjoin are premises: at the seat they are meant to come
from the link's law's ties at the seat, the lot's own runs, and "the seated block states what the
lot's block states": joined by nobody yet. Nothing on the way back (K6Back). Nothing on soundness.
LETTERS. run' stands under "there is" in hown: tied by the kind's own lookup.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Silent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Block Claim Link)
open VerifiableInference.Desc.First (S)

/-- A list's lookup under a name, as the first pair with that name. -/
theorem find_of_lookup {β : Type} (l : List (String × β)) (n : String) (r : β)
    (h : l.lookup n = some r) : l.find? (fun x => x.1 == n) = some (n, r) := by
  induction l with
  | nil => cases h
  | cons a tl ih =>
    obtain ⟨a1, a2⟩ := a
    by_cases e : a1 = n
    · subst e
      rw [List.lookup_cons_self] at h
      obtain rfl : a2 = r := Option.some.inj h
      simp
    · have e' : (n == a1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun q => e q.symm
      rw [List.lookup_cons, e'] at h
      rw [List.find?_cons_of_neg (by simpa using e)]
      exact ih h

/-- **K6States, from what the link's hearing block states.** -/
theorem k6States_of_hear (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) (l piece : Nat)
    (Lk : Link S Claim) (b : Nat) (blk : Block S Claim) (hb : Lk.hear[b]? = some blk)
    (hn : ∀ name, K6Name name → ∃ run, blk.claims.lookup name = some run)
    (hown : ∀ name run, name = "norm" ∨ name = "policy" ∨ name = "logits" →
      blk.claims.lookup name = some run → ∃ run',
        (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run' ∧
          ∀ k t y, run k t = .ok y → run' k t = .ok y)
    (hjoin : ∀ run, blk.claims.lookup "join" = some run → ∀ k t y, run k t = .ok y →
      K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) k t = .ok y) :
    K6States h iU3 p l piece (K9.statesOfLink Lk) b := by
  have hs : K9.statesOfLink Lk b = blk.claims := by
    unfold K9.statesOfLink
    rw [hb]
    rfl
  refine ⟨fun name hname => ?_, ?_⟩
  · have hN : K6Name name := by
      rcases hname with q | q | q
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr (Or.inl q))
    obtain ⟨run, hr⟩ := hn name hN
    obtain ⟨run', h1, h2⟩ := hown name run hname hr
    exact ⟨run, run', by rw [hs]; exact find_of_lookup _ _ _ hr, h1, h2⟩
  · obtain ⟨run, hr⟩ := hn "join" (Or.inr (Or.inr (Or.inr rfl)))
    exact ⟨run, by rw [hs]; exact find_of_lookup _ _ _ hr, hjoin run hr⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6States_of_hear
