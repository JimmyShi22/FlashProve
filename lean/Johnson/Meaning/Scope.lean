-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/Scope.lean: from the statements on the integer matrices behind each sub-proof to
"the request is true under its policy", under public premises that are no narrower than the goals'
scope.

Why. `under_of_ords` (Johnson/Road/Lane5TopL.lean) has eleven public hypotheses, "the table of
scales is lawful" and "the policy is within its bounds". The theorems that pay them so far,
`under_of_public` and `under_of_file` (Johnson/Road/Lane5TopPub.lean, Lane5TopPol.lean), ask that 46
numbers of the parameter file and all words of the scale file are the reference's. The goals' scope
(`VerifierAndGoals.InScope`, Ladder.lean) leaves five of the 46 and the whole scale file free. Here the
eleven are paid from the other 41 numbers (`Hd.PublicCore`, Johnson/Meaning/PublicCore.lean), and
"lawful" and the policy's bounds from the goals' own reader of the public files, which tests them
(`settingsAtRef`, Johnson/Flat/SettingsRead.lean; `VerifierAndGoals.readFiles` is that function).

Main theorems:
  `lawful_of_read`, `polCond_of_read`: what the reader returns is a lawful table of scales, with a
    policy within the library's bounds.
  `under_of_core`: `under_of_ords` at the letters of the verifier's public part, with the eleven
    hypotheses paid from the 41 numbers.
  `under_of_scope`: the same at the reader's own table and policy.
  `ordsL_met_core`, `ordsL_met_scope`: under the same premises the bundle of statements has a value,
    so neither theorem is empty.

Two premises of `under_of_scope` are equations between the reader's values and the verifier's: the
table of scales (tS) and the policy (tP). They are theorems of other files.

What is not claimed. That a proof file which a verifier accepts has matrices with `OrdsL`. That a
parameter file has `Hd.PublicCore`: Johnson/Goal/Meaning/ScopeCore.lean shows it of all files in the
goals' scope. The program does not import this file.
-/
import Johnson.Meaning.PublicCore
import Johnson.Road.Lane5TopPol
import Johnson.Flat.ScalesAt
import Johnson.Flat.SettingsRead

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Flat (settingsAtRef settingsAtRef_lawful)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public} {pp : ScalesAndPolicy}

/-- **The table of scales that the goals' reader returns is lawful**: the reader tests it. -/
theorem lawful_of_read (hR : settingsAtRef pol KL = .ok pp) : (Cm.Scales.of pp).Lawful :=
  have l := settingsAtRef_lawful hR
  ⟨l.ff, l.sh, l.one, l.nf, l.km⟩

/-- **The policy that the goals' reader returns is within the library's bounds**: the reader tests
C < 2^32, theta ≤ C and cap ≤ 1,024. -/
theorem polCond_of_read (hR : settingsAtRef pol KL = .ok pp) : Policy.PolCond pp.pol := by
  obtain ⟨hC, hT, hc⟩ := (settingsAtRef_lawful hR).pol
  exact ⟨by omega, by omega, by omega⟩

/-- **The head with the cost ledger, at the verifier's public part and the 41 numbers.** The table
of scales is the verifier's; that it is lawful, and that the policy is within its bounds, are
hypotheses here. -/
theorem under_of_core (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hs : (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)).Lawful) {pl : AcceptancePolicy}
    (hpol : Policy.PolCond pl) {i : Cm.Idx} {x : Instance ppref} {Z : ℕ → ℕ → ℕ → ℕ → ℤ}
    {ZA : ℕ → Zs} (hre : x.r < x.e)
    (O : OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) pl (Hd.shapeA X) i.mat
      x Z ZA) :
    Policy.IsTrueUnder (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)) pl i x :=
  have E := Hd.eleven_of_core h A (Hd.npOf X.hS)
  have B := E.1
  under_of_ords B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head E.2.1 E.2.2.1
    E.2.2.2.1 hs hpol hre O

/-- **At the same premises the bundle has a value.** -/
theorem ordsL_met_core (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hs : (scalesOf (layerShape X.P) X.layers.sc (Hd.npOf X.hS)).Lawful) {pl : AcceptancePolicy}
    (hpol : Policy.PolCond pl) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
        OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) pl (Hd.shapeA X) i.mat
          x Z ZA :=
  have E := Hd.eleven_of_core h A (Hd.npOf X.hS)
  have B := E.1
  ordsL_met B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head E.2.1 E.2.2.2.2
    E.2.2.1 E.2.2.2.1 hs hpol

/-- **The head with the cost ledger, at the reader's own table of scales and policy.** h: the
verifier's function has returned X on the public files. A: 41 numbers of the parameter file are the
reference's. hR: the goals' reader has returned pp on the same parameter file and scale file. tS,
tP: the reader's table and policy are the verifier's. Then the statements on the integer matrices,
at the verifier's own letters, give that the request is true under the policy that the reader
returned, at the table that the reader returned. -/
theorem under_of_scope (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hR : settingsAtRef pol KL = .ok pp) (tS : Cm.Scales.of pp = scalesAt X)
    (tP : pp.pol = Hd.polOf X.hS) {i : Cm.Idx} {x : Instance ppref} {Z : ℕ → ℕ → ℕ → ℕ → ℤ}
    {ZA : ℕ → Zs} (hre : x.r < x.e)
    (O : OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
      (Hd.shapeA X) i.mat x Z ZA) :
    Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x := by
  have hs : (scalesAt X).Lawful := tS ▸ lawful_of_read hR
  have hpol : Policy.PolCond (Hd.polOf X.hS) := tP ▸ polCond_of_read hR
  rw [tS, tP]
  exact under_of_core h A hs hpol hre O

/-- **At the same premises the bundle has a value**, so `under_of_scope` is not empty there. -/
theorem ordsL_met_scope (h : publicOf pol KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hR : settingsAtRef pol KL = .ok pp) (tS : Cm.Scales.of pp = scalesAt X)
    (tP : pp.pol = Hd.polOf X.hS) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
        OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
          (Hd.shapeA X) i.mat x Z ZA :=
  ordsL_met_core h A (tS ▸ lawful_of_read hR : (scalesAt X).Lawful) (tP ▸ polCond_of_read hR)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.lawful_of_read
#print axioms OnBytes.Road.L5.polCond_of_read
#print axioms OnBytes.Road.L5.under_of_core
#print axioms OnBytes.Road.L5.ordsL_met_core
#print axioms OnBytes.Road.L5.under_of_scope
#print axioms OnBytes.Road.L5.ordsL_met_scope
