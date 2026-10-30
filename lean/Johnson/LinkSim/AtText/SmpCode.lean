-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SmpCode.lean: the honest link prover's answer to the first sample, written as
one sum with its coefficients spelled out.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

Under Johnson/LinkSim/ no file calls smpCode.

What this file proves. Spec.smpCode, proved as smpCode, holds for all parameters: smAt = smAtC. smAt
(Johnson/Prover/Link/FrontWhole.lean) is the prover's answer to the first of the link proof's own
OOD samples. It is a sum over the entries of a member, one of the two folded rows' oracle messages
(Sz.memb, OnBytes/Slice/LinkAt.lean), with coefficients read off the library's data of that message.
smAtC is the same sum with its coefficients wMem written out. This is algebra on the prover's
algorithm: the same sum, its coefficients unfolded.

Why. One number among the library's data of a member's message is the larger of two products of
powers of the field's size (the field err of Sample.pad, Cb/Gen/OodDecPad.lean). By the definitions,
code that Lean compiles would build these data whole to read that one field. smAtC builds no such
data. The twin for the answer at a switch is in Johnson/LinkSim/AtText/AnsCode.lean.

The other names (namespace OnBytes.LinkSim.AtText).
  wMem S σ j      the coefficient at entry j of a member's message: at the pad's entry, the seed's
                  factor; elsewhere, the weight of the seed's point at the entry's vertex.
  smAtC           the sum, over a member's entries, of that coefficient times the entry.

Notes. Nothing is run here. That compiled code would build the library's data whole is by inspection
of the definitions, not proved. smAt by itself is evaluated nowhere.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontWhole

set_option autoImplicit false

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

/-- The first sample's coefficient at an entry of a member's message. -/
def wMem (S : Sz) (σ : (Fin (S.P.aR + S.P.aP) → GE) × GEˣ) (j : S.MJ) : GE :=
  Sum.elim (fun i : {j : S.MJ // j ≠ S.padJ} => Alg.eqk σ.1 fun t => (S.idxJ i.1).testBit t.val)
    (fun _ : Unit => σ.2.val * 1) (splitAt S.padJ j)

/-- **The first sample's answer, as one sum over a member's entries.** -/
def smAtC (S : Sz) (t : ℕ) (σ : (Fin (S.P.aR + S.P.aP) → GE) × GEˣ) (μ : (S.sg t).cIn.J → GE)
    (a : Bool) : GE :=
  ∑ j : S.MJ, wMem S σ j * μ (atJ S t a j)

/-- Statement only; proved as smpCode below. **The answer to the first sample equals the sum
smAtC**, for all parameters. -/
def Spec.smpCode : Prop :=
  ∀ (S : Sz) (t : ℕ) (σ : (Fin (S.P.aR + S.P.aP) → GE) × GEˣ) (μ : (S.sg t).cIn.J → GE) (a : Bool),
    smAt S t σ μ a = smAtC S t σ μ a

/-- Proof of Spec.smpCode. -/
theorem smpCode : Spec.smpCode := by
  intro S t σ μ a
  unfold smAt smAtC
  refine Finset.sum_equiv (Equiv.refl _)
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) fun j _ => ?_
  rfl

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.smpCode
