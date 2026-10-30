-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarkKit.lean: the kind "lookup" (K3): the first of the two
hypotheses of the mark's bound (`CanAll`, Honest/K3/Good/MarkShare.lean), shown from the frame's own
law `drawsFit_typed` (Honest/Law/Due.lean): at a kit of verifier's messages that meets that law's
three clauses, and at data that bear the entries and kinds of the lookup's rounds. Conditional.
Definitions with code; one theorem.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, good
samples, share, kit and window. In this file: f is the lookup's face, C a kit and dsb the data of
the rounds of the lookup's member.

What is shown.
  `declOf f`: the lookup's rounds, as declared rounds. It bears the short name of `Law.declOf`
    (Honest/K3/Law/Statements.lean: one entry as a declared round), and lays that text over
    `entriesV f`.
  `nzFits f`: a test on public data: no entry of the lookup's rounds asks more elements other than 0
    than elements.
  `canAll_of_kit`: whatever such a kit's messages show is such as the lookup's rounds can sample.

Hypotheses that remain.
  `hC`: the three clauses on the kit. The frame's `kit_two` (Honest/Law/KitTwo.lean) has them at the
    kit at the release's field; it is not
    called here.
  `hk`: the data bear the rounds' entries and kinds (`KindFits`, Due.lean, round for round): a fact
    on a description's data; not shown in this file.
  `hz`: `nzFits f` accepts.

Imported. MarkShare.lean imports Honest/Law/Due.lean.

Limits. An implication. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open VerifiableInference.Desc (fieldPrimeWord)
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

/-- The lookup's rounds, as declared rounds. -/
def declOf (f : LFace) : List Fmt.DeclaredRound :=
  (VerifiableInference.Desc.K3.entriesV f).map fun e => { entry := e }

/-- No entry asks more elements other than 0 than elements. -/
def nzFits (f : LFace) : Bool := (declOf f).all fun z => decide (z.entry.drawNZ ≤ z.entry.drawE)

/-- **Whatever such a kit's messages show is such as the lookup's rounds can sample.** -/
theorem canAll_of_kit (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (f : LFace) (dsb : List RDT) (hk : List.Forall₂ KindFits dsb (declOf f))
    (hz : nzFits f = true) : CanAll C f dsb := fun ρ =>
  drawsFit_typed C hC dsb (declOf f) hk
    (fun z hzm => of_decide_eq_true (List.all_eq_true.1 hz z hzm)) ρ

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.canAll_of_kit
