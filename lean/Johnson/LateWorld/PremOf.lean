-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/PremOf.lean: THE PREMISES OF THE STATEMENT OF INDEX PRIVACY (PremW,
Johnson/WholeKey/Premises.lean) GIVE THOSE OF THE STEP FROM THE HONEST SIDE THAT LAYS LATE TO THE
REDUCTION (PremLate, Johnson/LateWorld/SpecWrap.lean). It proves Spec.premLate
(Johnson/WholeKey/Assembly.lean).

This file states no goal of the release.

All clauses of PremLate but three are clauses of PremW or of its laws on the coins. The three say
that each set of coins which is drawn for a compiled run holds as many sibling digests as the run's
request tree is deep. The law on such coins (RunLaw, Johnson/WholeKey/CoinLaws.lean) says that the
list of sibling digests has the law of "that many uniform digests, as a list"; every member of the
enumeration is drawn with positive probability, so its list is one of these.

Main names (namespace OnBytes.LateWorld).
  RunLaw.path_length   every member of the enumeration has dq sibling digests.
  premLate             THE STATEMENT: OnBytes.WholeKey.Spec.premLate.

Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Assembly

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- Every member of the enumeration has dq sibling digests. -/
theorem _root_.OnBytes.WholeKey.RunLaw.path_length {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}
    {e : Enum (Coins lam L)} {nR nK nJ sFS ℓ ℓr dq : ℕ} {pad : Body L} {slot : ℕ}
    (h : RunLaw e nR nK nJ sFS ℓ ℓr dq pad slot) (n : Fin (e.n + 1)) :
    (e.e n).path.length = dq := by
  have hm : windowOf nR nK nJ (e.e n) ∈
      ((unif (Fin (e.n + 1))).map fun a => windowOf nR nK nJ (e.e a)).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨n, PMF.mem_support_uniformOfFintype n, rfl⟩
  rw [h.law] at hm
  obtain ⟨u, -, hu⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
  have h2 : (List.ofFn u.2.2.2 : List (Dig lam)) = (e.e n).path :=
    congrArg (fun z : Bits × (Fin nR → Bool → Fin nK → Fin nJ → Bits) × Bits × List (Dig lam) =>
      z.2.2.2) hu
  rw [← h2, List.length_ofFn]

/-- **THE STATEMENT.** -/
theorem premLate : OnBytes.WholeKey.Spec.premLate := by
  intro I X lam L Bd aT aL W S cA p a Sm ok Gs Ryes c u hP
  exact
    { ext := hP.ext
      runVals := hP.runVals
      freeT := hP.freeT
      freeL := hP.freeL
      freeB := hP.freeB
      wires := hP.wires
      ri := hP.coins.ri
      kT := hP.coins.kT
      kL := hP.coins.kL
      kB := hP.coins.kB
      pathT := hP.coins.coT.path_length
      pathL := hP.coins.coL.path_length
      pathB := hP.coins.coB.path_length
      seeds := hP.seeds }

end OnBytes.LateWorld

#print axioms OnBytes.WholeKey.RunLaw.path_length
#print axioms OnBytes.LateWorld.premLate
