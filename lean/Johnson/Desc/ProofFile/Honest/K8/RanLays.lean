-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/RanLays.lean: A LAW ON THE THREAD OF THE RUNS THAT THE BATCHING
GATHERS (`Ran`, Johnson/Desc/ProofFile/Honest/K9/GatherFold.lean, another house's file): A SENTENCE
THAT ONE NAMED RUN OF THE ORDER LAYS, AND THAT EVERY RUN BEHIND IT IN THE ORDER HANDS ON, HOLDS AT
THE STATE BEHIND THE LAST RUN. That house's `ran_inv` carries a sentence that holds from the start;
this one carries a sentence that comes to hold on the way. General in the two sentences; no kind is
named. None of the library's goals.

  **`ran_lays`**   at an order pre ++ o₀ :: post: I holds in front and every named run hands it on ·
                   under I the run that the entry o₀ names lays J · under I every run that an entry
                   of post names hands J on ⊢ I and J hold behind the last run. OF THE RUNS IN FRONT
                   OF o₀ NOTHING IS ASKED ON J
Limits. From the thread alone: that the gatherer's yes gives a thread is the other house's
`gather_ran`.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K9.GatherFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.K9 (Ran claimsRunOf ran_inv)

/-- **A sentence that one run of the order lays holds behind the last.** -/
theorem ran_lays (bs : List (Block S Claim)) (I J : S → Prop) (o₀ : Nat × String)
    (post : List (Nat × String))
    (hJ : ∀ o ∈ post, ∀ run, claimsRunOf bs o = some run → ∀ n t z, I t → J t →
      run n t = .ok z → J z.2)
    (hL : ∀ run, claimsRunOf bs o₀ = some run → ∀ n t z, I t → run n t = .ok z → J z.2) :
    ∀ (pre : List (Nat × String)) (n : Nat) (t : S) (ls : List (List Claim)) (e : S),
    (∀ o ∈ pre ++ o₀ :: post, ∀ run, claimsRunOf bs o = some run → ∀ n t z, I t →
      run n t = .ok z → I z.2) →
    I t → Ran bs (pre ++ o₀ :: post) n t ls e → I e ∧ J e
  | [], _, _, [], _, _, _, h => h.elim
  | [], n, t, l :: ls, e, hI, h0, h => by
    obtain ⟨run, u, hr, hz, hrest⟩ := h
    have hu : I u := hI o₀ List.mem_cons_self run hr n t (l, u) h0 hz
    have ju : J u := hL run hr n t (l, u) h0 hz
    exact (ran_inv bs (fun x => I x ∧ J x) post (n + l.length) u ls e
      (fun o' ho' run' hr' n' t' z' hIJ hz' =>
        ⟨hI o' (List.mem_cons_of_mem _ ho') run' hr' n' t' z' hIJ.1 hz',
          hJ o' ho' run' hr' n' t' z' hIJ.1 hIJ.2 hz'⟩)
      ⟨hu, ju⟩ hrest).2
  | _ :: _, _, _, [], _, _, _, h => h.elim
  | o :: pre, n, t, l :: ls, e, hI, h0, h => by
    obtain ⟨run, u, hr, hz, hrest⟩ := h
    have hu : I u := hI o List.mem_cons_self run hr n t (l, u) h0 hz
    exact ran_lays bs I J o₀ post hJ hL pre (n + l.length) u ls e
      (fun o' ho' => hI o' (List.mem_cons_of_mem _ ho')) hu hrest

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.ran_lays
