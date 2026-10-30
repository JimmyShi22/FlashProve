-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinLib.lean: CONDITIONAL.

What is here. The hypothesis `JoinWorth` (StackStart.lean: the first pass of the batched sumcheck is
the lookup's join) in the library's letters: from the library's law on the start form
(`start_whole`, Johnson/Road/FormsKeysWhole.lean) and three equations.

  `joinWorth_lib`   **`JoinWorth` from the library's law and the three equations**

Limits. At the reading `Reading.gl`. THE THREE EQUATIONS ARE HYPOTHESES: (B1) the lookup's own part
is worth 0: the sum over the eight calls of the call's weight times (alpha less the call's number
times theta less the extension of the library's key vector at the call's point), plus the padding
trees' number, less what the form that the lookup's end leaves is worth; (B2) the library's `ClT` is
what the world holds under the slot of the second token sumcheck's claimed sum (TokGpos.lean's
`clT_total` has that it is the honest job's total, conditionally); (P0) the honest first pass's sum
is the library's `Sig0` (PassSig.lean has it, conditionally). So are the premises of the library's
law: eight factors, each worth what the library's `joinPart_keyVec'` concludes (hp: `parts_of_lines`
there has it where no call is longer than the library's: THE FULL SIZE ALONE); the points and
weights of the calls 0, 1, 2, 5 read as the library's at one z; the never-sent vector 0 is the
honest vector of the gated products; the hearing holds the second token sumcheck's structure (hT);
two inequalities on the library's sizes (hcap, hfe). THE WORLD W IS ONE in (B1), (B2) and hp; the
world of PassSig.lean's ties is another variable and may be another world (JoinOne.lean takes the
two as one). No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackStart
import Johnson.Road.FormsKeysWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE ceilLog2)
open OnBytes.Model (Reading Aff World Tsc)
open OnBytes.Model.Layer (Lay Heard)
open OnBytes.Road (padOf startOf startOf_value start_whole rPort elP ACCP TSP)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW Sig0 Sig1 ClT wc famsIn fSh hhU zpos zc aC keyVec)
open OnBytes.Desc.First.K4.Honest (StackData)

variable [scl : Scl]

/-- **`JoinWorth` FROM THE LIBRARY's LAW AND THREE EQUATIONS.** CONDITIONAL: on every hypothesis
named. -/
theorem joinWorth_lib (y : Lay) (shownT : Array E) (hv : ℕ → ℕ → Cb.Gl.E) (D : Dim)
    (t : Cell → Cb.Gl.E) (tb : Tables) (L0 : ℕ) (w : ℕ → LW Cb.Gl.E) (z zh : ℕ → Cb.Gl.E)
    (ζ : Fin 8 → ℕ → Cb.Gl.E) (W : World Cb.Gl.E) (H : Heard) (parts : List Aff) {tT : Tsc}
    (hT : H.tT = some tT) (hlen : parts.length = 8) (alpha theta : E)
    (hp : ∀ (c : Fin 8) (f : Aff), parts[c.val]? = some f →
      f.value Reading.gl W = Reading.gl.val alpha - (c.val : Cb.Gl.E) * Reading.gl.val theta -
        Blocks.ext (aC D c) (keyVec D t tb L0 w c) (ζ c) + TSP D t tb L0 w c (ζ c) +
        ∑ l ∈ Finset.range D.nl, elP D (ζ c) l *
          ((famsIn c l).map fun s => ACCP D t w (ζ c) s l).sum)
    (hcap : D.lT ≤ D.cap) (hfe : D.fe ≤ D.f)
    (hz : ∀ c : Fin 8, c ∈ [(0 : Fin 8), 1, 2, 5] → ∀ j, j < aC D c → ζ c j = zc D z c j)
    (hwc : ∀ c : Fin 8, c ∈ [(0 : Fin 8), 1, 2, 5] →
      Reading.gl.val (H.fo.e.getD c.val zeroE) = wc D z c)
    (hH : ∀ l, l < D.nl → ∀ j, j < fSh D l →
      hv 0 (l * 2 ^ ceilLog2 y.h.f + j) = hhU D t l j (zpos D z))
    (hB1 : (∑ c : Fin 8, Reading.gl.val (H.fo.e.getD c.val zeroE) *
        (Reading.gl.val alpha - (c.val : Cb.Gl.E) * Reading.gl.val theta -
          Blocks.ext (aC D c) (keyVec D t tb L0 w c) (ζ c))) +
      Reading.gl.val (padOf H) - H.fo.cEnd.value Reading.gl W = 0)
    (hB2 : ClT D t tb L0 w z = W.slot tT.sCl) {SD : StackData}
    (hP0 : passSum SD 0 = Sig0 D (rPort Reading.gl y shownT hv D t z zh) tb L0 w z zh) :
    JoinWorth H tT parts W SD := by
  have e := start_whole Reading.gl y shownT hv D t tb L0 w z zh ζ W H #[] parts hT hlen alpha theta
    hp hcap hfe hz hwc hH rfl
  have v := startOf_value Reading.gl W H #[] parts hT
  unfold JoinWorth
  rw [hP0]
  rw [v, hB1, hB2] at e
  linear_combination e

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.joinWorth_lib
