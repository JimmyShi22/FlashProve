-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/FreeAt.lean: the kind "lookup" (K3): at the state that
the fold of the first chain reaches right behind the lookup on a link's calls, at the 24 links in
front of the head's: the ledger has its sizes and no slot from its next slot on is filled. Theorems.

Terms. Honest/K3/GLOSSARY.md ("ledger", "slot"). In this file: `Sized`, `Filled` and `FreeAbove` are
the library's (OnBytes/Tie/Pv/Psc/PscFork.lean, PscRoom.lean): `FreeAbove G` says ∀ j, G.next ≤ j →
¬ Filled G j. `LeftQ n G` (Johnson/Desc/First/Look/K3LeftItem.lean): G has its sizes and n slots,
and each slot from its next on and below n is free.

What is shown.
  `freeAbove_of_leftQ`: `LeftQ n G` gives `FreeAbove G`.
  `free_behind_calls`: the title's sentence. Its conclusion writes out the library's
    `FreeAt (fun s => s.fork?) t` (Johnson/Desc/First/Look/K3KeepsFree.lean).

Hypotheses that remain. In `free_behind_calls`: those of the library's `calls_reached`
(Johnson/Desc/First/Look/K03LeftQ.lean), word for word: the goals' scope (`hS`, `hR`); the proof
file's description returns (`O`); the description passes the library's tests on the plan (`hOk`);
`l < 24` (`hl`); the fold over the chain's first 14 l + 2 + `IM.k3Ix l false` + 1 sub-protocols
returns the state t (`h`). The fold may start from any state s₀. In `freeAbove_of_leftQ`: `h` is
`LeftQ n G`.

How the proof goes. A joining of three theorems of the library: `calls_reached` (that return is an
acceptance of the kind's own decision from a state whose ledger is `LeftQ`), `seatCalls_keeps`
(Johnson/Top/H/K3SeatFits.lean) and `decide_freeAbove` (Johnson/Desc/First/Look/K3KeepsFree.lean).

Limits. At that one state of each of the 24 links. That a later sub-protocol's hearing begins from
this ledger is not said here. Not at the head's link: there the library has this conclusion at every
state reached at border 341, in the goals' scope and at the description's return too (its `hS`,
`hR`, `O`), where the sub-protocol at 340 passes its test on the plan: `P4.free_at_341`
(Johnson/P4R/FreeAt341N.lean). Not behind the lookup on the digits. It says nothing where the fold
rejects. No instance of the hypotheses together is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K03LeftQ
import Johnson.Desc.First.Look.K3KeepsFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes.Model (Fork)
open OnBytes.PscRun (Sized Filled FreeAbove)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles (LeftQ calls_reached seatCalls_keeps decide_freeAbove)

/-- A ledger with its sizes whose slots from the next on are free has none of them filled. -/
theorem freeAbove_of_leftQ {n : ℕ} {G : Fork} (h : LeftQ n G) : FreeAbove G := by
  obtain ⟨⟨_, _, hz⟩, _, hf⟩ := h
  intro j hj hfill
  unfold Filled at hfill
  by_cases hlt : j < G.ns
  · have h1 := hf j hj hlt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)] at h1 hfill
    rw [Option.getD_some] at h1 hfill
    rw [h1] at hfill
    exact Bool.false_ne_true hfill
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at hfill
    exact Bool.false_ne_true hfill

variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Right behind the lookup on a link's calls, as it is reached, nothing is filled from the
ledger's next slot on.** Conditional on the hypotheses that the head of this file lists. No instance
of these hypotheses is exhibited in this file. -/
theorem free_behind_calls (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (l : ℕ) (hl : l < 24) {s₀ t : S} {R R' : List Fmt.RoundView}
    {C C' : List VerifiableInference.Desc.OpenedColumn}
    (h : VerifiableInference.Desc.foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + IM.k3Ix l false + 1))
      s₀ R C = .ok (t, R', C')) :
    ∃ G, t.fork? = some G ∧ Sized G ∧ FreeAbove G := by
  obtain ⟨s, G, p, piece, laid, sent, rs, gs, _, hG, hQ, _, hd⟩ :=
    calls_reached hS hR O hOk l hl h
  exact decide_freeAbove _ piece laid sent p [] (seatCalls_keeps K3Lot.ofForm) hG hQ.1
    (freeAbove_of_leftQ hQ) hd

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.freeAbove_of_leftQ
#print axioms ProofFile.Honest.K3.Good.Live.free_behind_calls
