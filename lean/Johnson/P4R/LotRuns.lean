-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P4R/LotRuns.lean (a law about the lots of Johnson/Desc/ProofFile/Lot/K6K7.lean, no part of
them): WHAT EVERY BLOCK OF THE TWO LOTS STATES, RUN BY RUN. Theorems.

Why. The link's law ties a run at an entry of a link's order to a run of SOME block b' of SOME lot of the
seat's list, known by membership and by its place alone. So what a kind's files owe is a "for all": of every
block of its lot.

What is said, for all Z, G and every b in (k6Lot Z).blocks G:
  k6_lot_block   b is the seated constant: there is ms with headBefore Z G = some ms and
                 Head.seatedClaims G.W (G.built.size - 1) ms = some b.
  k6_lot_names   it states four runs, named norm, join, policy, logits, in this order.
  k6_lot_run     a run that is looked up in b under a name other than "join" IS the run of that name of the
                 bare kind: (kind asClaim (seatAt G.W.hS iU3) l 4 (parOf G.W.hS (workAtW G.W))).claims.
  k6_lot_join    the run that is looked up under "join" IS K3.joinRun (K3.seatCalls asClaim)
                 (callerKeys (parOf G.W.hS (workAtW G.W)) (seatAt G.W.hS iU3)).
  k7_lot_none    every block of k7Lot.blocks G states no run, in front of the batching or behind it.
EQUATIONS, NOT "Under": whoever wants "Under r' run" takes it from the equation.

The letters. l := G.built.size - 1. iU3 stands under "there is", TIED BY AN EQUATION THAT MAKES IT:
G.W.H.tl.ix.U.getD 2 none = some iU3. ms likewise: headBefore Z G = some ms. No place is asked: the lot has at
most one block.

What it does not give. Nothing on what the runs claim (Johnson/Desc/Kinds/Law/: the runs' own laws). Nothing on
the guards that the driver and the seat lay over a lot's block. That the lot HAS a block (headBefore answers,
seatedClaims answers) is not said: where it has none the statements hold idly. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Lot.K6K7
import Johnson.Desc.Kinds.Law.SeatedRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P4
open ProofFile (Cl Pub Ground Lot)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW seated_claims seated_run seated_join)

variable {Z : Pub} {G : Ground} {b : Block S Cl}

/-- **Every block of K6's lot is the seated constant.** -/
theorem k6_lot_block (hb : b ∈ (k6Lot Z).blocks G) :
    ∃ ms, headBefore Z G = some ms ∧ seatedClaims G.W (G.built.size - 1) ms = some b := by
  have h : b ∈ k6Hear Z G := by
    unfold ProofFile.Lot.blocks ProofFile.asCl at hb
    rcases List.mem_append.1 hb with h | h
    · obtain ⟨x, hx, _⟩ := List.mem_map.1 h
      exact nomatch hx
    · exact h
  unfold k6Hear at h
  rw [Option.mem_toList] at h
  exact Option.bind_eq_some_iff.1 h

/-- It states four runs, under these names, in this order. -/
theorem k6_lot_names (hb : b ∈ (k6Lot Z).blocks G) :
    b.claims.map (·.1) = ["norm", "join", "policy", "logits"] := by
  obtain ⟨ms, _, h⟩ := k6_lot_block hb
  obtain ⟨iU3, _, e⟩ := seated_claims h
  rw [e]
  rfl

/-- **A run under a name other than "join" is the bare kind's run of that name.** -/
theorem k6_lot_run (hb : b ∈ (k6Lot Z).blocks G) {name : String}
    {run : Nat → S → Except String (List Claim × S)} (hr : b.claims.lookup name = some run)
    (hn : name ≠ "join") :
    ∃ iU3, G.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      (kind asClaim (seatAt G.W.hS iU3) (G.built.size - 1) 4
        (parOf G.W.hS (workAtW G.W))).claims.lookup name = some run := by
  obtain ⟨ms, _, h⟩ := k6_lot_block hb
  exact seated_run h hr hn

/-- **The run under "join".** -/
theorem k6_lot_join (hb : b ∈ (k6Lot Z).blocks G)
    {run : Nat → S → Except String (List Claim × S)} (hr : b.claims.lookup "join" = some run) :
    ∃ iU3, G.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      run = VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls asClaim)
        (callerKeys (parOf G.W.hS (workAtW G.W)) (seatAt G.W.hS iU3)) := by
  obtain ⟨ms, _, h⟩ := k6_lot_block hb
  exact seated_join h hr

/-- **K7's lot states no run.** -/
theorem k7_lot_none (hb : b ∈ k7Lot.blocks G) : b.claims = [] ∧ b.after = [] := by
  unfold ProofFile.Lot.blocks ProofFile.asCl at hb
  rcases List.mem_append.1 hb with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    obtain rfl : x = k7Core G := List.mem_singleton.1 hx
    exact ⟨rfl, rfl⟩
  · exact nomatch h

end P4

#print axioms P4.k6_lot_block
#print axioms P4.k6_lot_names
#print axioms P4.k6_lot_run
#print axioms P4.k6_lot_join
#print axioms P4.k7_lot_none
