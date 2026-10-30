-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/QuietLaw.lean: `Plays` holds at a sub-protocol without a round
(`plays_quiet`). `Plays` is the first of the six hypotheses of Honest/Thread/Pays.lean. It holds at
every sub-protocol of a `Thread`'s blocksInOrder list that declares no round and no oracle message, whether
or not a prover's side is defined at its place. A lemma on this folder's own functions and
definitions, general in the `Thread`'s parameters: no kind is named.

Why. `chainSteps` prepares one `Step` for each declared round (Honest/Law/Run.lean, `steps_decl`),
so none here; the rounds can draw nothing; `play` on no round returns the state that it was given;
nothing is read; no tree is new.

Limits.
  * It is none of the library's goals.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **`Plays` holds at a sub-protocol that declares no round and no oracle message.** -/
theorem plays_quiet {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    (hr : blk.rounds = []) (ho : blk.oracles = []) : Plays T b := by
  intro blk' hblk' k s m E ds l _ hd _ hl
  rw [hblk] at hblk'
  cases hblk'
  have hl0 : l = [] := by
    have e := steps_decl hl
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hr] at e
    exact List.map_eq_nil_iff.1 e
  have hd0 : ds = [] := by
    have e := drawsFit_length _ _ hd
    rw [hr] at e
    exact List.eq_nil_of_length_eq_zero e
  subst hl0
  subst hd0
  refine ⟨([], m), [], ?_, ?_⟩
  · unfold Thread.Moved
    refine ⟨⟨[], hl, rfl⟩, ?_⟩
    rw [hr]
    rfl
  · intro σ hσ
    have e : T.hand (b + 1) = T.hand b := by
      unfold Thread.hand
      rw [treesTo_succ hblk, ho]
      rfl
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
    rw [e] at h1
    simp [h1] at h2

end ProofFile.Honest

#print axioms ProofFile.Honest.plays_quiet
