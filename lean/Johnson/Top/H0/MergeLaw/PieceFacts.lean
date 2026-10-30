-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/PieceFacts.lean: two of the facts on the piece that the merge's laws ask of
the written rounds. Two theorems with their proofs.

Why. The merge's laws take a list of written rounds under two premises: its entries are the block's
own (`mergeEntries`), and each round has the kind of its name. The rule for a file cuts the file's
written rounds into stretches, and shows of each stretch that it goes along its block's declared
rounds (`Along (RoundIs num)`, Johnson/Desc/Sound/Stretch.lean). Here the one is carried to the
other.

What is said. `entries_of_along`: where written rounds go along declared rounds that are bare
entries, one for one: their entries are these entries, and each has the kind that its name has.
`merge_stretch`: so, at any block that has the merge's declared rounds, the stretch meets the two
premises.

Limits. That a description's piece has such a stretch, of the right length, is not said here.
Nothing on the piece's errors, its base, or the rounds behind it. Nothing on soundness.

-/
import Johnson.Desc.Sound.Stretch
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Maker
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (RoundIs Along)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind mergeEntries)

/-- Where written rounds go along declared rounds that are bare entries, one for one: their entries
are these entries, and each has the kind that its name has. -/
theorem entries_of_along {num : Fmt.TreeSource → ℕ} : ∀ (es : List Fmt.Entry) (ds : List RDT),
    ds.length = es.length →
    Along (RoundIs num) (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) ds →
    ds.map (·.entry) = es ∧ ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind
  | [], [], _, _ => ⟨rfl, fun _ h => nomatch h⟩
  | [], _ :: _, hl, _ => by cases hl
  | _ :: _, [], hl, _ => by cases hl
  | e :: es, d :: ds, hl, h => by
    have h' : RoundIs num ({ entry := e } : Fmt.DeclaredRound) d ∧
        Along (RoundIs num) (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) ds := h
    obtain ⟨k1, k2⟩ := entries_of_along es ds (Nat.succ.inj hl) h'.2
    have e1 : d.entry = e := h'.1.1
    have e2 : Fmt.kindOf e.name = some d.kind := h'.1.2.1
    refine ⟨by rw [List.map_cons, e1, k1], fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [e1]
      exact e2
    · exact k2 x hx

/-- **TWO OF THE FACTS ON THE PIECE**: where a block has the merge's declared rounds and a stretch
of written rounds goes along them, one for one: the stretch has the block's own entries, and each
round the kind of its name: the two premises of the merge's laws on the written rounds. -/
theorem merge_stretch {T Cl : Type} {num : Fmt.TreeSource → ℕ} (P : HeadMergeP) (b : Block T Cl)
    (hb : b.rounds = (headClaimMergeKind P).rounds) (ds : List RDT) (hl : ds.length = b.rounds.length)
    (h : Along (RoundIs num) b.rounds ds) :
    ds.map (·.entry) = mergeEntries P.lay.lk 1 P.work ∧
      ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind := by
  rw [hb] at hl h
  exact entries_of_along _ ds (by simpa [headClaimMergeKind] using hl) h

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_stretch
