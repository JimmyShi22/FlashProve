-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/ToldReach.lean: WHICH COINS THE HONEST COMMITTER BEHIND THE PUBLIC READING TAKES AT A
NUMBER, AND THAT EVERY PAIR OUT OF ITS TWO ENUMERATIONS IS REACHED. Statements and proofs; general
in the told record.

Why. The argument system runs its committer at a number n (`withCoins`, Rom/WithCoins.lean). A goal
on binding lets the opener name randomness, of which n is made. How far such a goal reaches is how
many settings of coins the numbers reach.

Main names (namespace `VerifiableInference.OnPublicFiles`).
  `committerOverTypedOracles_withCoins`: `committerOverTypedOracles` (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean) at the number n is
    `committerAtFixedCoins` at entry n % (ri.n + 1) of ri and entry n / (ri.n + 1) % (sl.n + 1) of sl.
  `commitBehind_withCoins`: so `T.commitBehind` (Johnson/Top/ToldCommit.lean) at n is: the public
    reading, then `committerAtFixedCoins` at these two entries over the coding at d, the told part laid beside.
    Premise: the public reading draws nothing.
  `reach_pair`: arithmetic: n := a + (p + 1) c has n % (p + 1) = a, n / (p + 1) % (q + 1) = c and
    n < (p + 1) (q + 1), for a ≤ p and c ≤ q.
  **`commitBehind_reach`**: at the number a + (ri.n + 1) c the committer runs at (ri.e a, sl.e c):
    EVERY PAIR OF ENTRIES IS REACHED BY A NUMBER BELOW (ri.n + 1) (sl.n + 1).

Limits. Nothing is said on whether ri or sl is onto anything. The system's committer
(`Rec.tokenArgumentSystem`, Johnson/Top/FrontEnc.lean) runs the scheme's committer at the number and then asks
the hash function at the key's code: that step is not restated here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ToldCommit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- `committerOverTypedOracles` at a number. -/
theorem committerOverTypedOracles_withCoins {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type}
    {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (ri : Enum L.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : Bd) (i : I)
    (n : ℕ) :
    (committerOverTypedOracles W S ri sl b₀ i).withCoins n =
      committerAtFixedCoins W S b₀ i (ri.e ⟨n % (ri.n + 1), Nat.mod_lt _ ri.n.succ_pos⟩)
        (sl.e ⟨n / (ri.n + 1) % (sl.n + 1), Nat.mod_lt _ sl.n.succ_pos⟩) :=
  withCoins_noCoin _ _ (noCoin_committerAtFixedCoins W S _ _ _ _)

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (ri : Enum R.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : R.LeafBody)

/-- The committer behind the public reading, at a number. -/
theorem commitBehind_withCoins (noCoin : T.Pub.NoCoin) (i : R.Index) (n : ℕ) :
    (T.commitBehind ri sl b₀ i).withCoins n =
      T.Pub.bind fun d =>
        ((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ i (ri.e ⟨n % (ri.n + 1), Nat.mod_lt _ ri.n.succ_pos⟩)
          (sl.e ⟨n / (ri.n + 1) % (sl.n + 1), Nat.mod_lt _ sl.n.succ_pos⟩)).overOne (T.m d)).bind
          fun o => .pure ((T.part d, o.1), o.2) := by
  unfold LayoutsByPublicReading.commitBehind
  rw [OComp.withCoins_bind_of_noCoin _ _ _ noCoin]
  congr 1
  funext d
  rw [OComp.withCoins_bind_pure, withCoins_overOne, committerOverTypedOracles_withCoins]

/-- Arithmetic: the number of a pair. -/
theorem reach_pair (p q a c : ℕ) (ha : a < p + 1) (hc : c < q + 1) :
    (a + (p + 1) * c) % (p + 1) = a ∧ (a + (p + 1) * c) / (p + 1) % (q + 1) = c ∧
      a + (p + 1) * c < (p + 1) * (q + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · rw [Nat.add_mul_div_left _ _ (Nat.succ_pos p), Nat.div_eq_of_lt ha, Nat.zero_add,
      Nat.mod_eq_of_lt hc]
  · calc a + (p + 1) * c < (p + 1) + (p + 1) * c := Nat.add_lt_add_right ha _
      _ = (p + 1) * (c + 1) := by ring
      _ ≤ (p + 1) * (q + 1) := Nat.mul_le_mul_left _ hc

/-- **Every pair of entries is reached.** -/
theorem commitBehind_reach (noCoin : T.Pub.NoCoin) (i : R.Index) (a : Fin (ri.n + 1))
    (c : Fin (sl.n + 1)) :
    (T.commitBehind ri sl b₀ i).withCoins (a.val + (ri.n + 1) * c.val) =
      T.Pub.bind fun d =>
        ((committerAtFixedCoins R.queryLayout (T.Sd d) b₀ i (ri.e a) (sl.e c)).overOne (T.m d)).bind
          fun o => .pure ((T.part d, o.1), o.2) := by
  have h := reach_pair ri.n sl.n a.val c.val a.isLt c.isLt
  have ea : (⟨(a.val + (ri.n + 1) * c.val) % (ri.n + 1), Nat.mod_lt _ ri.n.succ_pos⟩ :
      Fin (ri.n + 1)) = a := Fin.ext h.1
  have ec : (⟨(a.val + (ri.n + 1) * c.val) / (ri.n + 1) % (sl.n + 1),
      Nat.mod_lt _ sl.n.succ_pos⟩ : Fin (sl.n + 1)) = c := Fin.ext h.2.1
  rw [commitBehind_withCoins T ri sl b₀ noCoin i, ea, ec]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.committerOverTypedOracles_withCoins
#print axioms VerifiableInference.OnPublicFiles.commitBehind_withCoins
#print axioms VerifiableInference.OnPublicFiles.reach_pair
#print axioms VerifiableInference.OnPublicFiles.commitBehind_reach
