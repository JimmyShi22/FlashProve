-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaGeneral.lean: an upper bound on the error term `OnBytes.WholeKey.zetaW`
(Johnson/WholeKey/Zeta.lean) for arbitrary parameters, when every search limit is 0.

Summary. The premises are on numbers alone. E2E/ZetaCaps.lean extends the bound to arbitrary search
limits, and E2E/ZetaAtCaps.lean applies it at the verifier's parameters.

Main results.
  `zetaW_le`: `zetaW … t n ≤ (t A + 9 A (2 (M + 2) + A)) / 2 ^ b`, if all search limits are 0 · the
    six errors of simulators and aborts and the error of the OOD seeds are 0 · there are no more
    sessions than one copy serves · a leaf's salt, a Fiat-Shamir query's salt and a digest each have
    at least b secret bits · each of nine oracle names gets at most A counted queries.
  `mW_le`: the counts at the nine names are at most `boundA M n` (E2E/ZetaArith.lean), from ten
    numbers of the wiring.

Terms: E2E/HidingTerms.lean.

Limits.
- A bound on a written expression. What that expression bounds, and under which premises, is stated
  in Johnson/WholeKey/Statement.lean and Johnson/WholeKey/Main.lean.
- An upper bound, not proved to be tight.

Definitions and helper lemmas.
  `runLeaves_eq`: the count of leaves in Johnson/WholeKey/Zeta.lean (`runLeaves`) is `lv` of
  E2E/ZetaWires.lean.
  `maxCap_zero`, `nine`, `nine_card`, `osW_of_caps`: with all search limits 0, queries with a secret
    are counted at nine oracle names.


-/
import Johnson.WholeKey.Zeta
import E2E.ZetaArith
import E2E.ZetaWires

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.ZetaAt
open OnBytes.WholeKey OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

section
variable {lam K : ℕ}

/-- The statement's count of leaves is the count of E2E/ZetaWires.lean. -/
theorem runLeaves_eq : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
    runLeaves s A W = lv s A W
  | [], _, _ => rfl
  | _ :: s, (_, A), (w, W) => by
    show _ + _ + runLeaves s A W = _ + _ + lv s A W
    rw [runLeaves_eq s A W]

/-- With all search limits 0 no search has a later try. -/
theorem maxCap_zero : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ),
    maxCap s A W (fun _ => 0) i = 0
  | [], _, _, _ => rfl
  | _ :: s, (a, A), (w, W), i => by
    show max (if roundHasTest a w = true then 0 else 0) (maxCap s A W (fun _ => 0) (i + 1)) = 0
    rw [maxCap_zero s A W (i + 1), ite_self, max_self]

end

/-- The nine oracle names that are left where no search has a later try. -/
def nine : Finset ON₂ :=
  {.leaf, .rleaf, .rnode, .g .test, .g .link, .g .onl, .fb .test, .fb .link, .fb .onl}

theorem nine_card : nine.card ≤ 9 := by decide

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (p : Params) (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) (u : NumsW)

theorem osW_of_caps (hT : a.capT = fun _ => 0) (hL : a.capL = fun _ => 0)
    (hB : a.capB = fun _ => 0) : osW W a = nine := by
  unfold osW laterNames
  rw [hT, hL, hB, maxCap_zero, maxCap_zero, maxCap_zero]
  simp only [Finset.range_zero, Finset.image_empty, Finset.union_empty]
  rfl

/-- **The error, from bounds on the counts**: all search limits 0; the six errors of simulators and
aborts and the OOD seeds' error 0; no more sessions than one copy serves; at least b secret bits in
a leaf's salt, in a Fiat-Shamir query's salt and in a digest; at most A queries with a secret at
each of the nine names. -/
theorem zetaW_le (t n A b : ℕ) (hT : a.capT = fun _ => 0) (hL : a.capL = fun _ => 0)
    (hB : a.capB = fun _ => 0)
    (hz : u.zT = 0 ∧ u.zL = 0 ∧ u.zO = 0 ∧ u.hT = 0 ∧ u.hL = 0 ∧ u.hO = 0 ∧ u.δ = 0)
    (hn : n ≤ u.s1) (hb1 : b ≤ c.ℓ) (hb2 : b ≤ p.sFS) (hb3 : b ≤ lam)
    (hm : ∀ o ∈ nine, mW W a n o ≤ A) :
    zetaW W S p a c u t n ≤
      ((t * A + 9 * (A * (2 * (a.M + 2) + A)) : ℕ) : ℝ≥0∞) / 2 ^ b := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hz
  have he : ∀ o ∈ nine, eW W S a n o ≤ 2 * (a.M + 2) := by
    intro o ho
    simp only [nine, Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.zero_le _
      | (show (if _ then 2 * (a.M + 2) else 0) ≤ _
         split
         · exact Nat.le_refl _
         · exact Nat.zero_le _)
  have hbits : ∀ o ∈ nine, b ≤ bitsW (lam := lam) p c o := by
    intro o ho
    simp only [nine, Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hb1
      | exact hb3
      | exact le_min hb2 hb3
  unfold zetaW
  rw [pOver_zero _ _ _ hn, z1, z2, z3, z4, z5, z6, z7, osW_of_caps W a hT hL hB]
  simp only [mul_zero, add_zero, zero_add]
  exact costTotal_le_of _ _ _ _ t A (2 * (a.M + 2)) b 9 hm he hbits nine_card

/-- **The counts at the nine names, from ten numbers of the wiring.** -/
theorem mW_le (n : ℕ) (hd : W.depth = 32)
    (l1 : runLeaves L.offline.shape aT (wTC W).sh ≤ 2 ^ 37)
    (l2 : runLeaves L.link.shape aL (wLC W).sh ≤ 2 ^ 25)
    (l3 : runLeaves L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ≤ 2 ^ 39)
    (r1 : L.offline.shape.length ≤ 2 ^ 20) (r2 : L.link.shape.length ≤ 2 ^ 20)
    (r3 : L.onlineBatch.loc.shape.length ≤ 2 ^ 20) (q1 : W.depthReqT ≤ 2 ^ 20) (q2 : W.depthReqL ≤ 2 ^ 20)
    (q3 : W.depthReq ≤ 2 ^ 20) : ∀ o ∈ nine, mW W a n o ≤ boundA a.M n := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    counts_le a.M n _ _ _ _ _ _ _ _ _ l1 l2 l3 r1 r2 r3 q1 q2 q3
  intro o ho
  simp only [nine, Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show (a.M + 2) * 2 ^ W.depth + runLeaves L.offline.shape aT (wTC W).sh +
      (a.M + 1) * runLeaves L.link.shape aL (wLC W).sh +
      n * runLeaves L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh ≤ _
    rw [hd]
    exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · exact c8
  · exact c9

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.mW_le
#print axioms AtPublicFiles.ZetaAt.runLeaves_eq
#print axioms AtPublicFiles.ZetaAt.osW_of_caps
#print axioms AtPublicFiles.ZetaAt.zetaW_le
#print axioms AtPublicFiles.ZetaAt.maxCap_zero
#print axioms AtPublicFiles.ZetaAt.nine_card
