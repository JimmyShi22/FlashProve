-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/Means.lean: which clause of the library's relation of an attention segment the
sums of five sumchecks stand for. Statements alone.

The library writes the eight sumchecks of an attention segment as definitions on the cells of the
segment (Inst/Model/Att/Sums.lean: sumPhi, Phi18; Inst/Model/Att/KeyForms.lean: rv, rvM6). Its
relation on the cells (RFraw in Inst/Model/Att/Trace.lean) asks, among other things, that three
kinds of identities are 0 (idnVal: at1, at2, at3) and that the keys of the third call, which are
made of the accumulator AC, are rows of a table. The four statements of this file join the two.
Each is an equation between polynomials in the cells and the challenges, for all sizes, cells and
challenges.
 - BitsMean: the sum of step s21 is the identities at1 (a cell of the index is a bit), extended to
   the drawn point (tbi, tbg, tk) and batched over the pairs.
 - ScoreMean: the batched row maxima at the drawn point, minus the sum of step s16, are the
   identities at2 (the row maximum is the score at the index), extended to the drawn point (ti, tg)
   and batched over the pairs.
 - KeyMean: the sum of step 18 over its cube is the batch of the second maps of step s16 (the key at
   the index) at that step's end point (fi, fg, fn).
 - ValueMean: the sums of steps s11 and s12 add up to the rule value of the accumulator plus th
   times the sums of the softmax weights at the lookup's point. With th drawn after the values ACC
   and ZC were sent, this serves the keys made of AC and the identities at3 (the denominator is the
   sum of the softmax weights).

Main definitions: bitIdn, scoreIdn, BitsMean, ScoreMean, KeyMean, ValueMean.

What this file does not claim. It holds no theorem: each statement is a definition of type Prop
(proofs: bitsMean and scoreMean in Cb/Pv/Att/Mean/BitsScore.lean, keyMean in
Cb/Pv/Att/Mean/Key.lean, valueMean in Cb/Pv/Att/Mean/ValueBelow.lean). That an extension which is 0
at a drawn point comes from identities that are 0 everywhere holds only up to an error, which is not
counted here (the library counts it: Blocks.cnt_ext_zero_le). Nothing is said about a verifier, a
proof or hiding.


-/
import Inst.Model.Att.KeyForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

/-- The identities at1 of pair b, on the cube (i | g | k) of step s21; 0 where k is not the number
of a bit of a position. -/
def bitIdn {E : Type} [Field E] (D : Dim) (t : Raw → E) (b X : ℕ) : E :=
  if X % 2 ^ D.lK < D.lT then
    idnVal D t (.at1 (X % 2 ^ D.lK) b (X / 2 ^ D.lK % D.nG) (X / 2 ^ D.lK / D.nG))
  else 0

/-- The identities at2 of pair b, on the cube (i | g). -/
def scoreIdn {E : Type} [Field E] (D : Dim) (t : Raw → E) (b Y : ℕ) : E :=
  idnVal D t (.at2 b (Y % D.nG) (Y / D.nG))

/-- **The sum of the sumcheck for the bits is the batch of the identities at1 at the drawn
point.** -/
def BitsMean : Prop :=
  ∀ (E : Type) [Field E] (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E),
    sumPhi D C p t .s21 =
      ∑ b ∈ range D.nb, p.o'' b *
        ext (D.lT + D.lg + D.lK) (bitIdn D t b) (cat D.lT p.tbi (cat D.lg p.tbg p.tk))

/-- **The batched row maxima minus the sum of the sumcheck for the score at the index are the batch
of the identities at2 at the drawn point.** -/
def ScoreMean : Prop :=
  ∀ (E : Type) [Field E] (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E),
    (∑ b ∈ range D.nb, p.o b * rvM6 D p t b) - sumPhi D C p t .s16 =
      ∑ b ∈ range D.nb, p.o b * ext (D.lT + D.lg) (scoreIdn D t b) (cat D.lT p.ti p.tg)

/-- **The sum of the sumcheck for the key at the index is the batch of the keys at the index at the
end point of the sumcheck before it.** -/
def KeyMean : Prop :=
  ∀ (E : Type) [Field E] (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E),
    ∑ X ∈ range (2 ^ g18 D), Phi18 D p t (cubePt (g18 D) X) =
      ∑ b ∈ range D.nb, p.o' b *
        Bext D C p t .s16 b (cat D.lT p.fi (cat D.lg p.fg p.fn))

/-- **The two sums of the value product add up to the accumulator plus th times the sum of the
softmax weights, both at the lookup's point and batched over the pairs.** -/
def ValueMean : Prop :=
  ∀ (E : Type) [Field E] (D : Dim) (C : Calls) (p : Pub E) (t : Raw → E),
    sumPhi D C p t .s11 + sumPhi D C p t .s12 =
      rv D C p t .acc +
        p.th * ∑ b ∈ range D.nb, wp D C p.z .w3 b *
          rd2 D (yg D C p.z) (eqT D (yi D C p.z)) (EF D t b)

end Cb.Pv.Att
