-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsTop.lean: CONDITIONAL.

What is here. THE FORM THAT THE SECOND TOKEN SUMCHECK OF THE FEED-FORWARD LAYERS' ROUNDS LEAVES IS
WORTH, ON THE HONEST PART's ROUNDS, THE JOB's SUMMAND ON THE END VALUES AS `maskedEnds` WRITES THEM
(the true end values, each plus the last challenge times its mask entry; that the last round's
scalars read as these is TermsSent.lean's; the summand: the honest side's `Sides.summand`; no
function of the verifier makes that number): the statement of TermsLed.lean with its three premises
on the job paid by TermsAll.lean from public premises. One statement and its proof.

  `terms_KT_pub`   **the form's worth**

Limits. Those of TermsLed.lean, but for the three premises on the job; in their stead `TermsPub`
(TermsAll.lean) of what the two jobs share: eight clauses on public data and on the sizes of a
sampled point and of a table of the input's products, the public test `triPlainB` among them, which
no text of the verifier or of the honest parts asks; where one is false nothing is said. THE START
IS STILL A PREMISE (the slot of the claimed sum is worth the reading of the cube's total), and so is
the premise on the reading of the first challenge's inverse. No example of the premises together is
known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsLed
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE subE invE)
open OnBytes.Model (Reading Aff Fork World Level Tsc Forest.Heard)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum
open ProofFile.Honest.SumLaw

variable {V : Type} {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **THE FORM IS WORTH THE JOB's SUMMAND ON THE END VALUES AS `maskedEnds` WRITES THEM.** S: what
the two jobs share at the part's entry. -/
theorem terms_KT_pub (h : List Fmt.Drawn)
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn)
    (hh : h.length = Q.r0) (Wd : World GE) (name endName : String)
    (c : SumCoins name endName (termsSum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 2)) (hzx : (st.input.look h).zx = fo.zx)
    (hd : drawsOk ((termsSum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (termsSum Q)) c st seen dp = some rounds)
    (hs : ∀ i, i < ownSlots ((termsSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (G1.next + 1 + i) = hidingCoin c i)
    (S : OnBytes.Desc.First.K4.Honest.Sides)
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q st.input (ptsOf Q st.input st.heard) = some S)
    (P : TermsPub S)
    (j : Job) (hJ : jobTermsOn S = some j)
    (hfitJ : k4JobFits (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) j = true)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hσ : (Aff.slot G1.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hT : TapeIs (t.drop (k4StartAt Q 2)) rounds)
    (hW : G1'.hideRun tT.p.first (Array.replicate tT.p.walk.1.length zeroE) (subE zeroE oneE) =
      some G2)
    (hinv : Reading.gl.val (invE tT.p.eps) * Reading.gl.val tT.p.eps = 1) :
    o.H.KT.value Reading.gl Wd = Reading.gl.val (j.atEnds tT.r.toList
      (maskedEnds (j.ends tT.r.toList) (endRun c) (tT.p.r.toList.getD Q.P.y.h.lt zeroE))) := by
  have hj : jobTerms Q st.input (ptsOf Q st.input st.heard) = some j := by
    unfold jobTerms
    rw [hS]
    exact hJ
  have hy : S.v.y = Q.P.y := (sidesOf_pub hS).2
  exact terms_KT (V := V) h L ds hh Wd name endName c st seen dp rounds hst hzx hd ha hs j hj
    hfitJ hnE hσ
    (fun rs hr => (terms_three P hJ rs (by rw [hy]; exact hr)).1 _)
    (fun rs hr => (terms_three P hJ rs (by rw [hy]; exact hr)).2.1)
    (fun rs hr => (terms_three P hJ rs (by rw [hy]; exact hr)).2.2) hT hW hinv

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.terms_KT_pub
