-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/Rel2Guards.lean: the reference scales, and the scales of a table of Inst/Model/ProgTests.lean.

Main names:
  `sRef`, `lawful_sRef`: there is a lawful table of scales: the reference scales.
  `Scales.of`, `lawful_of`: the scales of a table `ScalesAndPolicy` of Inst/Model/ProgTests.lean (its policy
    dropped); they are lawful if the table is.

`empty_language` (Cm/RelTrueExp.lean): at the reference scales there is a well-formed index at which
no request is true; "a key was made" says nothing on "something can be proved under it".

Limits: what the head of Cm/RelTrue.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cm.Rel2Proofs
import Cm.RelProofs
import Cm.RelTrue

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All Inst.Model.ScalesSanity
  Inst.Model.ProgramRGuards Inst.Model.SanityRef

/-- the scales of a table `ScalesAndPolicy` of Inst/Model/ProgTests.lean -/
def Scales.of (pp : ScalesAndPolicy) : Scales := ⟨pp.w, pp.nf⟩

theorem lawful_of {pp : ScalesAndPolicy} (h : Lawful pp) : (Scales.of pp).Lawful :=
  ⟨h.ff, h.sh, h.one, h.nf, h.km⟩

/-- the reference scales -/
def sRef : Scales := Scales.of ppRef

theorem lawful_sRef : sRef.Lawful := lawful_of lawful_ref

end Cm
