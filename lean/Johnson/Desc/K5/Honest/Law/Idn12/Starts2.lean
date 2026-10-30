-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Idn12/Starts2.lean: CONDITIONAL: A SECOND FORM of 3 declarations of
Johnson/Desc/K5/Honest/Law/Starts.lean: `hb_zero`, `sf_start`, `claim6_fronts`.
The first forms take as a premise that the cells meet all three of the library's families of
identities on an attention segment (`AtIdn`, Johnson/Desc/K5/Honest/Law/Idn.lean). These take the
first two families alone (`Idn12`, Johnson/Desc/K5/Honest/Law/Idn12/Idn2.lean), and, where the
third family was spent, what was spent of it: its batch at the lookup's point is 0 (`Rider`,
Johnson/Desc/K5/Honest/Law/Idn.lean).

Why. CONDITIONALLY, each of the two weaker premises follows from items that the row of the segment's
own rounds asks in front: `Idn12`, among others, under the library's head on the public input as a
hypothesis, hH and hc (Johnson/Desc/K5/Honest/Law/IdnOfAsked.lean); `Rider`, among others, under the
head, hc and K3 (RiderOfAsked.lean); none of these, nor the items, is shown. The third family on the
whole cube follows from no such item.

How. THE TEXT IS THE ELDER FILE's: each declaration named above with its docstring and its proof,
the premise's name exchanged, and each name of a declaration that has a second form exchanged for
that form's (a subscript 2 at its end). Every other lemma is called from the elder files, which are
imported and stay as they are.

Limits. Those of Johnson/Desc/K5/Honest/Law/Starts.lean, whose head says what each premise is.
Every theorem is conditional.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Starts
import Johnson.Desc.K5.Honest.Law.Idn12.Idn2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo W1 DivP Pts UnitG Pc eqTab eqAt cover piecesOf
  weights inner pcsSorted weights_eq KeyPtsAre UnitIs)
open Inst.Model.AttSeg hiding ibV
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-- **The sum of "the index's cells are bits" reads 0.** The statement names no challenges of the
library's: those made of the prover's are laid, at a made-up point of the lookup's. CONDITIONAL: see
the head. -/
theorem hb_zero₂ {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c : Chal} (Dr : Drawn P c)
    (hK : P.D.lT ≤ 2 ^ 4) (A : Idn12 P.D (tOf ρ w)) : ρ.val (sHB P w c).total = 0 := by
  rw [sHB_total ρ H w Pl Dr hK (bitPts_pubOf ρ P c fun _ => 0)]
  exact bitSum_zero₂ 4 A _

/-- **The sum of "the score at the index" reads as the batch of the row maxima that were sent.** c:
the challenges at which the sum is taken. c0: those at which the maxima were sent, in front of the
round that draws the batching element; both read as one p. The library's numbers of the lookup do
not enter step s16: made-up ones are laid. CONDITIONAL: see the head. -/
theorem sf_start₂ {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c c0 : Chal}
    (Dr : Drawn P c) (Dr0 : Drawn P c0) {pts : Pts} (hp : ptsOf P c0 = some pts) {p : Pub K}
    (I : IndexPts ρ P c p) (I0 : MaxPts ρ P c0 p) (A : Idn12 P.D (tOf ρ w)) :
    ρ.val (sSF P w c).total = ∑ b ∈ range P.D.nb, p.o b * ρ.val ((m6 P w c0).getD b zeroE) := by
  rw [sSF_total ρ H w Pl Dr ⟨fun _ => 0, 0, 0⟩ I, score_start₂ A]
  exact sum_congr rfl fun b hb => by rw [m6_reads ρ H w Dr0 hp I0 (mem_range.mp hb)]

/-- **The equation of the value product, of the values as they are sent**: c: the challenges at
which the two sums are taken; c0: those at which the accumulator's and the denominator's scalars
were sent, in front of the round that draws the batching element; both read as one p. Rd, in the
stead of the first form's premise on the three families: the batch of the third family at p's point
is 0. CONDITIONAL: see the head. -/
theorem claim6_fronts₂ {P : Pub5} (H : Sized P) (w : K5In) (Pl : Planned P) {c c0 : Chal}
    {Dv : DivIn} (h : divIn P c = some Dv) {pts0 : Pts} (hp0 : ptsOf P c0 = some pts0) {C : Calls}
    {p : Pub K} (R : DivPts ρ P C p Dv) (pr : PairsAre P.g Dv.d.pwW)
    (L0 : LonePts ρ P C p pts0.d) (Rd : Rider P.D C p.z (tOf ρ w)) :
    ρ.val (sVM P w c).total + ρ.val (sVD P w c).total - ρ.val (accV P w c0) -
      p.th * ρ.val (zcV P w c0) = 0 := by
  refine claim6_of_reads ρ (sVM_reads ρ w H Pl h R pr) (sVD_reads ρ H w Pl h R pr) ?_ ?_
    Rd
  · unfold accV
    rw [ofDiv_some hp0]
    exact acc_reads ρ H w L0
  · unfold zcV
    rw [ofDiv_some hp0]
    exact zc_reads ρ w L0

end H2K5.Honest

#print axioms H2K5.Honest.hb_zero₂
#print axioms H2K5.Honest.sf_start₂
#print axioms H2K5.Honest.claim6_fronts₂
