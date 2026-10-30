-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Half.lean: AN ERROR OF INDEX PRIVACY SAYS NOTHING UNTIL IT IS BELOW ONE HALF; and
what index privacy on a range says of TWO REAL EXPERIMENTS.

General theorems with their proofs, and their use at two toys. This file states no goal of the
release.

WHY ONE HALF. Index privacy compares the real experiment at an index with an ideal experiment that
is the same for all indices with the same public parameters. So at two indices of the range with
the same public parameters, under one environment that is valid at both, the real views are within
ζ + ζ of each other (real_real), and that says something only where ζ + ζ < 1. An error "below 1" is
too low a bar. An example (typed at a toy: FoeScheme.guess_member, Johnson/WholeKey/FoeZeta.lean): a
prover sends a one-bit index in the clear; a simulator reads its guess off one bit of the verifier
messages that it is handed; at each index it is right at half of the verifier messages; so the
premise on simulators (Sims.Good) is met at z = 1/2, and the written error is below 1, while the
index is told. The negative tests of Johnson/WholeKey/Foes.lean and Johnson/WholeKey/Foes2.lean all
end in "1 ≤ ζ + ζ" or in a like inequality on a premise's numbers.
"ζ + ζ < 1" IS WHERE A STATEMENT OF INDEX PRIVACY BEGINS TO SPEAK. IT IS NECESSARY, NOT ENOUGH: TO
PASS IT IS NOT TO HIDE. Argued, not typed: a prover that tells the index in every proof that holds a
string, and hands no string with probability α, with a simulator that mixes the two indices, can sit
near (1 - α) / 2, below one half. What shuts out such a prover is ζ + ζ + α < 1, α the error of
completeness; the typed half of that: FoeScheme.teller_not_private
(Johnson/WholeKey/FoeScheme.lean): 1 ≤ ζ + ζ + 1/16 at a toy, whatever the simulator. SO A QUOTE
GIVES THE NUMBER. At the two toys ζ + ζ is at most 60/256 (about 0.23) and at most about 0.50: the
second toy shows little.

  real_real        for ANY scheme over typed oracles: index privacy on a range, two indices of the
                   range with the same public parameters, an environment that is valid at both: the
                   two REAL views are within ζ t N + ζ t N in statistical distance.
  (The numbers at the two toys: zeta_pad_le, zeta_pad2_le; that ζ + ζ < 1 there: zeta_pad_half,
  zeta_pad2_half: Johnson/WholeKey/Main.lean.)
  real_pad, real_pad2   THE THEOREM APPLIED, two real experiments against each other: at each toy
                   the real views at two indices of the range are within zetaW t N + zetaW t N.

Limits. Toys. The bounds are upper bounds. At the second toy ζ + ζ < 1 is shown at one query and
three requests; of other numbers nothing is said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Main

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **Two real experiments.** -/
theorem real_real {S : OSpec} {I X Wn PP IVK ISK Pf : Type} (R : ZKCP.Gen.RelPair I X Wn PP)
    (A : ZKCP.Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ) (Sim : ZKCP.Gen.Simulator S PP IVK X Pf)
    (ζ : ℕ → ℕ → ℝ≥0∞) (ok : I → Prop) (H : ZKCP.Gen.PrivacyOn R A B Sim ζ ok) (i i' : I)
    (hi : ok i) (hi' : ok i') (hpp : R.pp i = R.pp i') (Z : ZKCP.Gen.ViewEnv S IVK X Wn Pf)
    (hZ : Z.IsValid R B i) (hZ' : Z.IsValid R B i') (t : ℕ)
    (Vt : IVK → ZKCP.Gen.AdvVerifier S X Pf) (N : ℕ) (hb : ∀ ivk, (Vt ivk).QueryBound t) :
    sd (fun T => Rom.Pr (ZKCP.Gen.realExp A Vt Z i N) fun _ => T)
        (fun T => Rom.Pr (ZKCP.Gen.realExp A Vt Z i' N) fun _ => T) ≤ ζ t N + ζ t N := by
  have e : ZKCP.Gen.idealExp R Sim Vt Z i' N = ZKCP.Gen.idealExp R Sim Vt Z i N := by
    unfold ZKCP.Gen.idealExp
    rw [hpp]
  have a := (H i hi Z hZ t Vt N hb).1
  have b := (H i' hi' Z hZ' t Vt N hb).1
  rw [e, sd_comm] at b
  exact (sd_triangle _ _ _).trans (add_le_add a b)

/-! ## The first toy -/

/-- At the first toy the real views at the two indices are within zetaW t N + zetaW t N. -/
theorem real_pad (R : ZKCP.Gen.RelPair Bool Unit Unit Unit) (r₀ : Hiop.Seeded.pad.Rec)
    (i i' : Bool)
    (Z : ZKCP.Gen.ViewEnv (typedOracleFamily 8 Member.WP.K Member.CP)
      (FullKey 8 Hiop.Seeded.pad Member.aT Member.aL) Unit Unit (RequestProof 8 Hiop.Seeded.pad))
    (hZ : Z.IsValid R 1 i) (hZ' : Z.IsValid R 1 i') (t : ℕ)
    (Vt : FullKey 8 Hiop.Seeded.pad Member.aT Member.aL →
      ZKCP.Gen.AdvVerifier (typedOracleFamily 8 Member.WP.K Member.CP) Unit (RequestProof 8 Hiop.Seeded.pad))
    (N : ℕ) (hb : ∀ ivk, (Vt ivk).QueryBound t) :
    sd (fun T => Rom.Pr (ZKCP.Gen.realExp
          (argW Member.WP Member.SP Member.cAP r₀ Member.pP Member.atP.side) Vt Z i N) fun _ => T)
        (fun T => Rom.Pr (ZKCP.Gen.realExp
          (argW Member.WP Member.SP Member.cAP r₀ Member.pP Member.atP.side) Vt Z i' N)
          fun _ => T) ≤
      zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP t N +
        zetaW Member.WP Member.SP Member.pP Member.atP Member.cnP Member.nuP t N :=
  real_real R _ 1 _ _ _ (private_pad R r₀ i).1 i i' trivial trivial rfl Z hZ hZ' t Vt N hb

/-! ## The second toy -/

/-- At the second toy the real views at two indices in range are within zetaW t N + zetaW t N. -/
theorem real_pad2 (R : ZKCP.Gen.RelPair (Option Bool) Unit Unit Unit)
    (r₀ : Hiop.Seeded.Two.pad2.Rec) (i i' : Option Bool) (hi : Member2.ok2 i)
    (hi' : Member2.ok2 i')
    (Z : ZKCP.Gen.ViewEnv (typedOracleFamily 32 Member2.W2.K Member2.C2)
      (FullKey 32 Hiop.Seeded.Two.pad2 Member2.aT Member2.aL) Unit Unit
      (RequestProof 32 Hiop.Seeded.Two.pad2))
    (hZ : Z.IsValid R 1 i) (hZ' : Z.IsValid R 1 i') (t : ℕ)
    (Vt : FullKey 32 Hiop.Seeded.Two.pad2 Member2.aT Member2.aL →
      ZKCP.Gen.AdvVerifier (typedOracleFamily 32 Member2.W2.K Member2.C2) Unit (RequestProof 32 Hiop.Seeded.Two.pad2))
    (N : ℕ) (hb : ∀ ivk, (Vt ivk).QueryBound t) :
    sd (fun T => Rom.Pr (ZKCP.Gen.realExp
          (argW Member2.W2 Member2.S2 Member2.cA2 r₀ Member2.p2 Member2.at2.side) Vt Z i N)
          fun _ => T)
        (fun T => Rom.Pr (ZKCP.Gen.realExp
          (argW Member2.W2 Member2.S2 Member2.cA2 r₀ Member2.p2 Member2.at2.side) Vt Z i' N)
          fun _ => T) ≤
      zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2 t N +
        zetaW Member2.W2 Member2.S2 Member2.p2 Member2.at2 Member2.cn2 Member2.nu2 t N :=
  real_real R _ 1 _ _ _ (private_pad2 R r₀ i).1 i i' hi hi' rfl Z hZ hZ' t Vt N hb

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.real_pad2
#print axioms OnBytes.WholeKey.real_real
#print axioms OnBytes.WholeKey.real_pad
