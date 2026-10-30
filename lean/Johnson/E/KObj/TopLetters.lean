-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/TopLetters.lean: from "every block has its property" to the conclusion of
`VerifiableInference.OnPublicFiles.verify_sound` (Johnson/Top/OnFiles.lean).

For every protocol description d whose configuration, five sub-protocols and numbers are those of
an object O (four typed lists of bare blocks and a batch test: Johnson/E/KObj/Obj.lean), whatever
the honest sides: `O.Blocks` and the nine other named hypotheses give `Holes d`. Of the
twenty-two fields of `Holes d` thirteen come from the blocks. Definitions and proofs.
Main names:
  `CSP`, `Obj.csp`: a configuration with its five sub-protocols and their numbers; an object's.
  `Thirteen`, `Obj.thirteen`: the fields that speak of the five verifiers, from `O.Blocks`.
  `Rest d`: the nine others (numbers, wires, the record, the commitment, the meaning): each
    field's type is the definition `Hole.‹name› d` of Johnson/Top/OnFiles.lean.
  `holes_of`, `Describes`, `holes_of_blocks`: thirteen and nine are the twenty-two.
  `top_letters`: the conclusion of `verify_sound` about `verify d`.
Limits: it does not say that any object is the protocol that the programs run; that `O.Blocks` or
`Rest d` holds of anything; anything on completeness or on zero knowledge.

-/
import Johnson.E.KObj.Obj
import Johnson.Top.OnFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace KObj
open Rom ZKCP Iop Hiop Compile Compile.Batch Compile.Batch.Cms VerifiableInference
  VerifiableInference.OnPublicFiles

/-- a configuration with its five sub-protocols and their numbers -/
abbrev CSP : Type 1 := Σ C : ConfigurationWithOutOfDomainSample, Σ S : SubsR C, S.Nums

/-- the thirteen of Holes d's fields that speak of the five sub-protocols' verifiers -/
structure Thirteen (x : CSP) : Prop where
  know    : x.2.1.HypK x.2.2
  passes  : ∀ a y τ b, x.2.1.req.out a y τ = some b → b.2 = a.2
  copy    : ∀ y τ, (x.2.1.req.imp y τ).1 = y
  wf      : x.2.1.wf.IsLocal
  linOff  : x.2.1.linOff.IsLocal
  link    : x.2.1.link.IsLocal
  req     : x.2.1.req.IsLocal
  linOn   : x.2.1.linOn.ior.IsLocal
  coh     : x.2.1.linOn.ann.Coherent

/-- what an object at letters ends in -/
def Obj.csp (O : Obj) (H : O.Hon) : CSP := ⟨O.C, O.S H, O.P H⟩

/-- THE SPINE: every block has its property ⇒ the thirteen -/
theorem Obj.thirteen (O : Obj) (H : O.Hon) (h : O.Blocks) : Thirteen (O.csp H) :=
  ⟨Obj.hypK H h, Obj.passes H h, Obj.copy H h, (Obj.locals H h).1, (Obj.locals H h).2.1,
    (Obj.locals H h).2.2.1, (Obj.locals H h).2.2.2.1, (Obj.locals H h).2.2.2.2.1,
    (Obj.locals H h).2.2.2.2.2⟩

/-- the nine other named hypotheses of `Holes d`, under its own names -/
structure Rest (d : ProtocolDescription) : Prop where
  samplersT  : Hole.samplersT d
  samplersL  : Hole.samplersL d
  samplersB  : Hole.samplersB d
  below      : Hole.below d
  seedLaw    : Hole.seedLaw d
  wires      : Hole.wires d
  recordCode : Hole.recordCode d
  commitment : Hole.commitment d
  sound      : Hole.sound d

/-- thirteen and nine are the twenty-two -/
theorem holes_of (d : ProtocolDescription) (t : Thirteen ⟨d.C, d.S, d.P⟩) (r : Rest d) : Holes d :=
  { wfKnow := t.know.wf, linOffKnow := t.know.linOff, linkKnow := t.know.link,
    reqKnow := t.know.req, linOnKnow := t.know.linOn, passes := t.passes, copy := t.copy,
    wfLocal := t.wf, linOffLocal := t.linOff, linkLocal := t.link, reqLocal := t.req,
    linOnLocal := t.linOn, coherent := t.coh, samplersT := r.samplersT,
    samplersL := r.samplersL, samplersB := r.samplersB, below := r.below, seedLaw := r.seedLaw,
    wires := r.wires, recordCode := r.recordCode, commitment := r.commitment,
    sound := r.sound }

/-- d IS A DESCRIPTION OF THE OBJECT O: its configuration, sub-protocols and numbers are O's -/
def Describes (d : ProtocolDescription) (O : Obj) (H : O.Hon) : Prop :=
  (⟨d.C, d.S, d.P⟩ : CSP) = O.csp H

theorem holes_of_blocks (d : ProtocolDescription) (O : Obj) (H : O.Hon) (e : Describes d O H)
    (h : O.Blocks) (r : Rest d) : Holes d :=
  holes_of d (by rw [show (⟨d.C, d.S, d.P⟩ : CSP) = O.csp H from e]; exact O.thirteen H h) r

/-- **THE TOP AT LETTERS: FROM «EVERY BLOCK HAS ITS PROPERTY» TO THE SOUNDNESS OF verify d.** This
is said under the hypotheses that stand in the statement itself, which this comment does not list;
it is no claim that they hold. -/
theorem top_letters (d : ProtocolDescription) (O : Obj) (H : O.Hon) (e : Describes d O H)
    (h : O.Blocks) (r : Rest d) :
    SoundForWith (systemOf d) (extractorOf d) (systemOf d).IsModelOutput (soundnessErrorOf d) :=
  verify_sound d (holes_of_blocks d O H e h r)

end KObj

#print axioms KObj.Obj.thirteen
#print axioms KObj.holes_of
#print axioms KObj.holes_of_blocks
#print axioms KObj.top_letters
