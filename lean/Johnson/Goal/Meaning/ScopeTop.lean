-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ScopeTop.lean: from the statements on the integer matrices behind each
sub-proof to "the request is true under its policy", at all public files in the goals' scope, with
no further public premise.

`under_of_ords` (Johnson/Road/Lane5TopL.lean) has eleven public hypotheses, "the table of scales is
lawful" and "the policy is within its bounds". Here all thirteen are paid, for every set of public
files Z, from three facts:
  `VerifierAndGoals.InScope Z = true`                    the goals' own test on the public files;
  `VerifierAndGoals.readFiles Z = .ok pp`                the goals' own reader has returned pp;
  `publicOf Z.pol Z.KL lay = .ok X`            the verifier's own function has returned X.
The first two are the premises of the goals on soundness (`SoundAt`, `SoundUnderPolicyAt`,
Ladder.lean). The third is a step of a verifier that works with X.

What pays what.
  The eleven hypotheses: `Hd.eleven_of_core` (Johnson/Meaning/PublicCore.lean), from 41 numbers of
  the scan. The 41 numbers: `Hd.core_of_scope` (Johnson/Goal/Meaning/ScopeCore.lean), from the
  parameter file's bytes. Lawful, and the policy's bounds: `lawful_of_read`, `polCond_of_read`
    (Johnson/Meaning/Scope.lean): the reader tests them.
  One table and one policy: `readings_agree` (Johnson/Goal/Meaning/Ties.lean), at 48 layers, one of
  the 41.

Main theorems: `under_in_scope`; `ordsL_met_in_scope` (under the same three facts the bundle of
statements has a value).

What is not claimed. That a proof file which a verifier accepts has matrices with `OrdsL`. That the
three facts hold together at any files. The program does not import this file.
-/
import Johnson.Meaning.Scope
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Goal.Meaning.Ties

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Verify (publicOf layerShape)
open VerifiableInference.Meaning (readings_agree)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **At all public files in the goals' scope: the statements on the integer matrices, at the
verifier's own letters, give that the request is true under the policy that the goals' reader
returned, at the table of scales that it returned.** -/
theorem under_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {i : Cm.Idx} {x : Instance ppref}
    {M : ℕ → ℕ → ℕ → ℕ → ℤ} {MA : ℕ → Zs} (hre : x.r < x.e)
    (O : OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
      (Hd.shapeA X) i.mat x M MA) :
    Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x :=
  have T := readings_agree Z pp lay X hR h
  under_of_scope h (Hd.core_of_scope hZ hR h) hR (T.2 (Hd.layers_of_scope hZ hR h)) T.1 hre O

/-- **Under the same three facts the bundle of statements has a value.** -/
theorem ordsL_met_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (M : ℕ → ℕ → ℕ → ℕ → ℤ) (MA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
        OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
          (Hd.shapeA X) i.mat x M MA :=
  have T := readings_agree Z pp lay X hR h
  ordsL_met_scope h (Hd.core_of_scope hZ hR h) hR (T.2 (Hd.layers_of_scope hZ hR h)) T.1

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.under_in_scope
#print axioms OnBytes.Road.L5.ordsL_met_in_scope
