-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/AnsCode.lean: the honest link prover's answer at a switch, written as one
sum over the new tables' entries, with nothing defined by choice.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

Under Johnson/LinkSim/ no file calls ansCode.

What this file proves. Spec.ansCode, proved as ansCode, holds for all parameters: gAns = gAnsC. gAns
(Johnson/Prover/Link/SwitchMsg.lean) is the prover's answer at a switch to the link proof's own OOD
sample: the library's sample of the new message, over the library's data of a code switch (csSw,
OnBytes/Slice/CsData.lean). gAnsC is the same number, written as the sum over the new tables'
entries of each entry times its coefficient wAt. This is algebra on the prover's algorithm: one sum,
with its terms renamed.

Why. The library's data of a code switch name a new message's entries as "old message, old tails,
free entries" by a one-to-one renaming of the entries, whose inverse is defined by choice, and they
list the free entries by choice. So Lean can reason about gAns but cannot run it. gAnsC uses nothing
defined by choice. The twin for the answer to the first sample is in SmpCode.lean.

The other names (namespace OnBytes.LinkSim.AtText).
  wAt hf ρo j     the coefficient at entry j of the new tables: at the pad's entry, the seed's
                  factor; elsewhere, the weight of the seed's point at the entry's vertex.
  gAnsC           the sum, over the new tables' entries, of that coefficient times the entry, read
                  by its index (gTab, Johnson/Prover/Link/SwitchMsg.lean).

Proof: gMsg_tab and gMsg_place (Johnson/Prover/Link/SwitchMsg.lean); the sum is re-indexed along
that renaming.

Notes. Nothing is run here: gAnsC is not evaluated in this file.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchMsg

set_option autoImplicit false

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

variable {s s' : Sg}

/-- The answer's coefficient at an entry of the new tables. -/
def wAt (hf : CsFit s s') (ρo : (Fin s'.st.na → GE) × GEˣ) (j : s'.cIn.J) : GE :=
  Sum.elim (fun i : {j : s'.cIn.J // j ≠ csPad hf} =>
      Alg.eqk ρo.1 fun t => (cubeAt s' i.1).testBit t.val)
    (fun _ : Unit => ρo.2.val * 1) (splitAt (csPad hf) j)

/-- **The answer, as one sum over the new tables' entries.** -/
def gAnsC (hf : CsFit s s') (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE)
    (ρo : (Fin s'.st.na → GE) × GEˣ) : GE :=
  ∑ j : s'.cIn.J, wAt hf ρo j * gTab s μ' tl fr (outAt s' j)

/-- Statement only; proved as ansCode below. **The answer at a switch equals the sum gAnsC**, for
all parameters. -/
def Spec.ansCode : Prop :=
  ∀ (s s' : Sg) (hf : CsFit s s') (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE)
    (ρo : (Fin s'.st.na → GE) × GEˣ), gAns hf μ' tl fr ρo = gAnsC hf μ' tl fr ρo

/-- Proof of Spec.ansCode. -/
theorem ansCode : Spec.ansCode := by
  intro s s' hf μ' tl fr ρo
  unfold gAns gAnsC Cb.Ood.Sample.val
  refine Finset.sum_equiv (csPlace hf)
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) fun n _ => ?_
  rw [← gMsg_tab hf μ' tl fr (csPlace hf n), gMsg_place]
  rfl

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.ansCode
