-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/TieR.lean: two lemmas beneath the row on the meaning
(Johnson/Goal/Meaning/Row.lean): what the 25 sub-proofs' conditions, in the library's letters, say
of the integer model.

TieSays: at every table of settings pp, every index i (a well-formed table of weights) and every
request x: some residual stream meets the plain statements of Johnson/Meaning/Says.lean at the
weights that i holds, if and only if x is true under pp's policy at i. It is book-keeping: "true
under the policy" unfolds to the integer program's own recursion, and Says writes that recursion as
a relation.

TieConstraints: at all public files in the goals' scope: r < e, and some lists of integer matrices
meet OrdsN (Johnson/Meaning/Lists.lean) at i's digits and x, if and only if x is true under the
policy at i. OrdsN: in each of the 25 sub-proofs every entry is below 2^18 in absolute value, every
identity of its segment is 0 modulo the protocol's prime, and every key is an entry of its lookup
table; and every copy of an array has the entries of its original.

Where the weight lies. The step from conditions modulo the prime to the integer program is the
library's (Policy.ledger_forces, spent by under_of_ords, Johnson/Road/Lane5TopL.lean), and so is the
way back (ordsL_of_true, Johnson/Road/Lane5TopLTrue.lean). New here: the lists by number, the goals'
own scope in place of the reference's files, and the two readers' agreement.

Whose the conditions are. Identities, key vectors and tables are the library's, read in the lists
through the library's dictionary (Johnson/Road/). For the labels of the layers' lists the dictionary
is the verifier's by a theorem; for the places of attention's cells it is written by a reading of
the verifier's text. No function of a verifier's sub-proof stands in OrdsN.

What is not claimed. That a proof file which a verifier accepts has lists with OrdsN. Nothing on
probabilities or on hiding. All is at the reference model's sizes. The lookup tables in the
conditions are the library's (tbRef).
-/
import Johnson.Meaning.Says
import Johnson.Meaning.Lists
import Johnson.Goal.Meaning.ScopeTop
import Johnson.Road.Lane5TopLTrue
import Johnson.Road.HeadZ

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model
open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (matIx)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)

/-- The settings are their scales with their policy. -/
theorem ppOf_of (pp : ScalesAndPolicy) : Policy.ppOf (Cm.Scales.of pp) pp.pol = pp := rfl

/-- **The plain statements say "true under the policy", no more and no less.** -/
def TieSays : Prop :=
  ∀ (pp : ScalesAndPolicy) (i : Cm.Idx) (x : Instance ppref),
    (∃ S, Says pp i.index.val x S) ↔ Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x

theorem tieSays : TieSays := fun pp i x =>
  (isTrueUnder_iff_says (Cm.Scales.of pp) pp.pol i x).symm

/-- **The sub-proofs' conditions, in the library's letters, say "true under the policy", no more and
no less.** -/
def TieConstraints : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (pp : ScalesAndPolicy) (lay : Option ByteArray) (X : Model.Verify.Public),
    VerifierAndGoals.InScope Z = true → VerifierAndGoals.readFiles Z = .ok pp → publicOf Z.pol Z.KL lay = .ok X →
    ∀ (i : Cm.Idx) (x : Instance ppref),
      (x.r < x.e ∧ ∃ (MG : ℕ → Mats ℤ) (MA : ℕ → Zs) (MH : Mats ℤ),
        OrdsN (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
          (Hd.shapeA X) i.mat x MG MA MH) ↔
        Policy.IsTrueUnder (Cm.Scales.of pp) pp.pol i x

theorem tieConstraints : TieConstraints := by
  intro Z pp lay X hZ hR h i x
  have A := Hd.core_of_scope hZ hR h
  have E := Hd.eleven_of_core h A (Hd.npOf X.hS)
  have B := E.1
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS' : Cm.Scales.of pp = scalesAt X := tS (A.num 2)
  constructor
  · rintro ⟨hre, MG, MA, MH, O⟩
    obtain ⟨h3, h1⟩ := Hd.parts_ref B.lay B.switches B.sized2
    have hXO : (matIx X.y).iXO < 256 := by
      show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 < 256
      omega
    exact under_in_scope hZ hR h hre (ordsL_of_lists hXO B.groups O)
  · intro T
    have hs : (scalesAt X).Lawful := tS' ▸ lawful_of_read hR
    have hpol : Policy.PolCond (Hd.polOf X.hS) := tP ▸ polCond_of_read hR
    have T' : Policy.IsTrueUnder (scalesAt X) (Hd.polOf X.hS) i x := by
      rw [← tS', ← tP]
      exact T
    exact ⟨T.2.1.1, _, _, _, lists_of_ordsL B.groups
      (ordsL_of_true B.lay B.switches B.sized B.sized2 B.p4 B.groups B.full B.head E.2.1
        E.2.2.2.2 E.2.2.1 E.2.2.2.1 hs hpol i x T')⟩

end Meaning

#print axioms Meaning.tieSays
#print axioms Meaning.tieConstraints
