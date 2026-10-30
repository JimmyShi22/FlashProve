-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PrunedNil.lean: **An empty forest is nothing, whole or cut**: for the verifier's walks
over pruned sets of paths (Compile/Batch/Verifier.lean: runForest, runForests, Forest.split) it
makes no difference whether a tree of which nothing is opened is flagged "pruned" or not (proved for
such a forest at the front of a list of forests; no statement here is on the verifiers).
WHAT IT IS FOR. A round without positions (for instance the round of a nonce alone:
Iop/SplitNonce.lean) needs no tree (Iop/BatchWire.lean: has0, hasJ); its flag for pruned sets is
read by Forest.split on a forest without checks.
    need_nil, upN_nil, octC_nil, bindPure      tools
    split_nil_need        such a forest asks for 0 digests, for both values of the flag;
                          split_nil_flat: it holds no check
    runForest_nil         its walk asks nothing and says "true"
    **runForests_split_nil**      runForests (Forest.split b ⟨d, r, []⟩ ++ Fs) s = runForests Fs s,
                                  for both b
What it does not say. That the forests of a round without a tree ARE empty is by reading
Compile/Batch/Verifier.lean (checksOpt at "no root"); no lemma here says it.  Nothing on the
prover's side.
-/
import Compile.Batch.Pruned

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

theorem need_nil : ∀ d, Octopus.need d [] = 0
  | 0 => rfl
  | d + 1 => (Nat.zero_add _).trans (need_nil d)
theorem upN_nil : ∀ d, Octopus.upN d [] = []
  | 0 => rfl
  | d + 1 => upN_nil d

/-- an empty forest asks for no digest and holds no check, whole or cut -/
theorem split_nil_need (b : Bool) (d : ℕ) (r : ℕ → Dig lam) :
    needF (Forest.split b (⟨d, r, []⟩ : Forest lam L)) = 0 := by
  cases b
  · rfl
  · show Octopus.need d [] + 0 = 0
    rw [need_nil]
theorem split_nil_flat (b : Bool) (d : ℕ) (r : ℕ → Dig lam) :
    flatF (Forest.split b (⟨d, r, []⟩ : Forest lam L)) = [] := by
  cases b <;> rfl


theorem bindPure {S : OSpec} {α : Type} (c : OComp S α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, ih]
  | query o q k ih => simp only [OComp.bind, ih]

theorem octC_nil :
    ∀ (d : ℕ) (s : List (Dig lam)), Octopus.octC (hashTreeNode (L := L) (K := K)) d [] [] s = pure []
  | 0, _ => rfl
  | d + 1, s => octC_nil d s

/-- the walk of an empty forest asks nothing and says "true" -/
theorem runForest_nil (d : ℕ) (r : ℕ → Dig lam) (s : List (Dig lam)) :
    runForest (K := K) (⟨d, r, []⟩ : Forest lam L) s = pure true := by
  change (Octopus.octC (hashTreeNode (L := L) (K := K)) d [] [] s >>=
      fun out => pure (((Octopus.upN d []).zip out).all fun m => decide (m.2 = r m.1))) = pure true
  rw [octC_nil, upN_nil]
  rfl

/-- so the walks over a list of forests do not see whether an empty forest stands before them whole
(flag true) or cut (flag false) -/
theorem runForests_split_nil
    (b : Bool) (d : ℕ) (r : ℕ → Dig lam) (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    runForests (K := K) (Forest.split b (⟨d, r, []⟩ : Forest lam L) ++ Fs) s =
      runForests (K := K) Fs s := by
  cases b
  · rfl
  · change (runForest (K := K) (⟨d, r, []⟩ : Forest lam L) (s.take (Octopus.need d [])) >>=
          fun a => runForests (K := K) Fs (s.drop (Octopus.need d [])) >>= fun b => pure (a && b)) =
      _
    rw [runForest_nil, need_nil]
    change ((runForests (K := K) Fs s).bind fun b => OComp.pure b) = _
    exact bindPure _

end Compile.Batch
