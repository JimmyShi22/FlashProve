-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Idn12/Parts2.lean: CONDITIONAL: A SECOND FORM of 3 declarations of
Johnson/Desc/K5/Honest/Law/Parts.lean: `atIndex_total`, `start_atIndex_total`, `start_cells_total`.
Those take as a premise that the cells meet all three of the library's families of
identities on an attention segment (`AtIdn`, Johnson/Desc/K5/Honest/Law/Idn.lean). These take the
first two families alone (`Idn12`, Johnson/Desc/K5/Honest/Law/Idn12/Idn2.lean).

Why. CONDITIONALLY, `Idn12` follows from two items that the row of the segment's own rounds asks in
front (Johnson/Desc/K5/Honest/Law/IdnOfAsked.lean): among others under the library's head on the
public input as a hypothesis, hH and hc; none of these, nor the items, is shown. The third family on
the whole cube follows from no such item.

How. THE TEXT IS THE ELDER FILE's: each declaration named above with its docstring and its proof,
the premise's name exchanged, and each name of a declaration that has a second form exchanged for
that form's (a subscript 2 at its end). Every other lemma is called from the elder files, which are
imported and stay as they are.

Limits. Those of that file, whose head says what each premise is.
Every theorem is conditional.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Parts
import Johnson.Desc.K5.Honest.Law.Idn12.Starts2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open OnBytes.Model (Reading World Aff)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo UnitG Heard Pts chal weights inner wDivision wOn
  wAtIndex wCells batched)
open Inst.Model.AttSeg (Calls Pub)
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-- **The batch of the row maxima that were sent, under the powers that the verifier has heard, is
the summand's sum over the cube.** c: the challenges at which the sum is taken; c0: those at which
the maxima were sent; both read as one p. CONDITIONAL: see the head. -/
theorem atIndex_total₂ {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c c0 : Chal}
    (Dr : Drawn P c) (Dr0 : Drawn P c0) {pts : Pts} (hp : ptsOf P c0 = some pts) {p : Pub K}
    (I : IndexPts ρ P c p) (I0 : MaxPts ρ P c0 p) (A : Idn12 P.D (tOf ρ w)) {hd : Heard}
    (ho : hd.om = (heardAt P c fun _ => none).om) :
    ∑ b ∈ range P.x.pairs, ρ.val (hd.om.getD b zeroE) * ρ.val ((m6 P w c0).getD b zeroE) =
      ρ.val (sSF P w c).total := by
  rw [sf_start₂ ρ H w Pl Dr Dr0 hp I I0 A, Pl.pairs, ho]
  exact sum_congr rfl fun b hb => congrArg (· * _) (I.o b (mem_range.mp hb))

/-- **The form from which the verifier starts "the score at the index" is worth the summand's sum
over the cube**, where the maxima that were sent lie under their slots. CONDITIONAL: see the head.
-/
theorem start_atIndex_total₂ {W : World K} {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P)
    {c c0 : Chal} (Dr : Drawn P c) (Dr0 : Drawn P c0) {pts : Pts} (hp : ptsOf P c0 = some pts)
    {p : Pub K} (I : IndexPts ρ P c p) (I0 : MaxPts ρ P c0 p) (A : Idn12 P.D (tOf ρ w))
    {hd : Heard} (ho : hd.om = (heardAt P c fun _ => none).om)
    (hm : ∀ b < P.x.pairs, W.slot (hd.maxima + b) = ρ.val ((m6 P w c0).getD b zeroE)) :
    (batched P.x.pairs hd.om hd.maxima 1 0).value ρ W = ρ.val (sSF P w c).total := by
  rw [VerifiableInference.Desc.First.Att.P.batched_value,
    ← atIndex_total₂ ρ H w Pl Dr Dr0 hp I I0 A ho]
  refine sum_congr rfl fun b hb => ?_
  rw [show hd.maxima + (1 * b + 0) = hd.maxima + b by omega, hm b (mem_range.mp hb)]

/-- **The form from which the verifier starts "the index's cells are bits", the constant 0, is worth
the summand's sum over the cube.** CONDITIONAL: see the head. -/
theorem start_cells_total₂ {W : World K} {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P)
    {c : Chal} (Dr : Drawn P c) (hK : P.D.lT ≤ 2 ^ 4) (A : Idn12 P.D (tOf ρ w)) :
    (Aff.ofConst zeroE).value ρ W = ρ.val (sHB P w c).total := by
  rw [hb_zero₂ ρ H w Pl Dr hK A, Aff.value_ofConst, ρ.zero]

end H2K5.Honest

#print axioms H2K5.Honest.atIndex_total₂
#print axioms H2K5.Honest.start_atIndex_total₂
#print axioms H2K5.Honest.start_cells_total₂
