-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ZetaErrAtInput.lean: an upper bound on the error term zetaW of the theorem on
index privacy, at an input of the compiler, where the seven error numbers need not be 0. It is the
bound boundZ that is known where they are 0, plus the explicit sum of the seven.

What this file has (namespace OnBytes.FrontRoad).
zetaWithErrors: let r be an input of the compiler that satisfies Twelve (E2E/ZetaAtInput.lean:
bounds on the salts' lengths, the tree's depth, the trees' leaves, the rounds and the request trees'
depths). Let a be any structure of the honest side's parameters, c any numbers of the coins with at
least 256 free bits in a leaf's salt, and u any structure of the numbers. Let CT, CL, CB bound the
honest side's limits on proof-of-work attempts, and let n ≤ u.s1. Then zetaW at t queries and n
requests is at most boundZ (9 + CT + CL + CB) M t n plus an explicit sum. The sum is (zT + (M + 1) ·
zL + n · zO) + (hT + (M + 1) · hL + n · hO) + (M + 2) · δ, where M + 1 is the number of copies. It
is zeta_of_twelve (E2E/LinkLaidPrivacy.lean) without that theorem's premise that the seven numbers
are 0.

  Spec.zetaWithErrors   that statement, as a proposition with a name.
  zeta_keyAndSessions   that statement at the numbers indexPrivacyNumbers s1 zT 0 0 hT 0 hO
      (E2E/PremisesAtFiles.lean). There the link's two errors, the sessions' simulation error zO and
      δ are 0, and the sum is zT + hT + n · hO.

How it fits. It rests on zetaW_split (Johnson/WholeKey/ZetaSplit.lean) and zeta_of_twelve, and
imports nothing else of this folder, so that files outside this folder can call it. By err_le_zetaW
(Johnson/WholeKey/ZetaSplit.lean) the explicit sum is also a lower bound on zetaW. So the bound here
is exact in the seven numbers: only boundZ, which bounds zetaW's other two terms, can be improved.
It is for honest sides at which some of the seven numbers are not 0, for example provers whose
aborts that may depend on the private input have positive probability.
Johnson/FrontRoad/ZetaErr.lean carries it to this folder's premise ZetaLe. A lemma on the way to
index privacy; not one of the release's goal statements.

Limits.
  It gives no number for zT, zL, zO, hT, hL, hO or δ. It is arithmetic on an explicit expression.
      Whether a given prover's aborts that may depend on the private input are rare is a premise of
      PremW (Johnson/WholeKey/Premises.lean), and is proved here of no prover.
  The sum grows with the number n of requests. Where n · hO is 1 or more the bound says nothing.
  zetaW has no term for the public part of a prover's abort set. A prover that aborts publicly at
      every list of verifier messages satisfies PremW with zO = hO = 0 wherever PremW holds at some
      parameters, and fails completeness (said here without a theorem). So a small bound here says
      nothing on whether the prover is useful.
  All limits of E2E/ZetaCaps.lean, of E2E/ZetaAtInput.lean, and of E2E/ZetaAtCaps.lean on the bound
      boundZ hold here. Among them: no bound on zetaW says that the proof-of-work searches succeed,
      and boundZ is not proved to be tight. What zetaW bounds, and under which premises, is stated
      in Johnson/WholeKey/Statement.lean.
Terms: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.
-/
import E2E.LinkLaidPrivacy
import Johnson.WholeKey.ZetaSplit

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid
open VerifiableInference.OnPublicFiles (InnerCompilerInput)

/-- Statement only; proved as zetaWithErrors below. The bound of zeta_of_twelve
(E2E/LinkLaidPrivacy.lean) without its premise that the seven error numbers are 0, with the explicit
sum of the seven added. -/
def Spec.zetaWithErrors : Prop :=
  ∀ (r : InnerCompilerInput), Twelve r → ∀ (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (c : CoinNums r.LeafBody)
    (u : NumsW) (t n CT CL CB : ℕ), (∀ i, a.capT i ≤ CT) → (∀ i, a.capL i ≤ CL) →
    (∀ i, a.capB i ≤ CB) → n ≤ u.s1 → 256 ≤ c.ℓ →
    zetaW r.queryLayout r.seedQueries r.compilerParameters a c u t n ≤
      boundZ (9 + CT + CL + CB) a.M t n +
        ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
          (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
          ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ)

/-- **The bound on zetaW at error numbers that need not be 0.** Proves Spec.zetaWithErrors. -/
theorem zetaWithErrors : Spec.zetaWithErrors := fun r h a c u t n CT CL CB hT hL hB hn hℓ => by
  rw [zetaW_split r.queryLayout r.seedQueries r.compilerParameters a c u t n]
  exact add_le_add
    (zeta_of_twelve r h a c { u with zT := 0, zL := 0, zO := 0, hT := 0, hL := 0, hO := 0, δ := 0 }
      t n CT CL CB hT hL hB ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hn hℓ) le_rfl

/-- The same at the numbers indexPrivacyNumbers s1 zT 0 0 hT 0 hO: the link's two errors, the sessions'
simulation error zO and δ are 0, and the sum is zT + hT + n · hO. -/
theorem zeta_keyAndSessions (r : InnerCompilerInput) (h : Twelve r) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (c : CoinNums r.LeafBody) (s1 : ℕ) (zT hT hO : ℝ≥0∞) (t n CT CL CB : ℕ) (cT : ∀ i, a.capT i ≤ CT)
    (cL : ∀ i, a.capL i ≤ CL) (cB : ∀ i, a.capB i ≤ CB) (hn : n ≤ s1) (hℓ : 256 ≤ c.ℓ) :
    zetaW r.queryLayout r.seedQueries r.compilerParameters a c (indexPrivacyNumbers s1 zT 0 0 hT 0 hO) t n ≤
      boundZ (9 + CT + CL + CB) a.M t n + (zT + hT + (n : ℝ≥0∞) * hO) := by
  have e := zetaWithErrors r h a c (indexPrivacyNumbers s1 zT 0 0 hT 0 hO) t n CT CL CB cT cL cB hn hℓ
  have s : (zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * 0) +
      (hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * 0 + (n : ℝ≥0∞) * hO) + ((a.M + 2 : ℕ) : ℝ≥0∞) * 0 =
      zT + hT + (n : ℝ≥0∞) * hO := by
    simp only [mul_zero, add_zero]
    ring
  exact s ▸ e

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.Spec.zetaWithErrors
#print axioms OnBytes.FrontRoad.zetaWithErrors
#print axioms OnBytes.FrontRoad.zeta_keyAndSessions
