-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsTotal.lean: CONDITIONAL.

What is here. The sum that the second token sumcheck's honest job claims (`jobTermsOn`,
Johnson/Desc/K4/Honest/Terms.lean) is the extension, at the lookup's token point, of the tokens'
sums of products; and it is the library's `ClT` (Inst/Model/FF/Objects.lean) where at each token
that sum is the library's summand `Gpos` at the token's corner.

  `tokSum`   a token's sum of products
  `terms_total`   **the claimed sum, as an extension over the tokens**
  `terms_clT`   **it is the library's ClT**, under the tie at each token

Limits. At the reading `Reading.gl`. THE TIE AT EACH TOKEN (hG) IS A HYPOTHESIS: nothing here shows
it. So are: the token point has as many coordinates as a token has bits; it reads as the library's
token point; the library's sizes have f = 2 fe and as many bits of a position. No example of the
hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsJob
import Johnson.Road.FormsKeysSigT
import Johnson.Road.FormsKeysPortFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Road (pt clT_gpos)
open OnBytes.Road.K4.C (firstOf termsCube jobTermsOn_whole)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW ClT Gpos zpos)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw

/-- **A token's sum of products**: each product's weight (that of the first token) times its two
factors at token t. -/
noncomputable def tokSum (rows : TokRows) (t : ℕ) : Cb.Gl.E :=
  ∑ k ∈ Finset.range (firstOf rows).size, Reading.gl.val (wAt rows k) *
    (Reading.gl.val (aAt rows t k) * Reading.gl.val (bAt rows t k))

/-- **THE CLAIMED SUM, AS AN EXTENSION OVER THE TOKENS.** -/
theorem terms_total {S : Sides} {J : Job} (hJ : jobTermsOn S = some J)
    (hz : S.zt.size = S.v.y.h.lt) :
    ∃ rows, tokenRows S = some rows ∧ Reading.gl.val J.cube.total =
      Blocks.ext S.v.y.h.lt (tokSum rows) (pt Reading.gl S.zt) := by
  obtain ⟨rows, h1, _, _, _, rfl⟩ := jobTermsOn_whole hJ
  refine ⟨rows, h1, ?_⟩
  show Reading.gl.val (termsCube S rows).total = _
  rw [total_ext Reading.gl (termsCube S rows) S.zt rfl hz]
  refine Blocks.ext_congr (fun t _ => ?_) _
  rw [termsAt_read]
  show (((List.range (firstOf rows).size).map fun k =>
    (((firstOf rows).getD k (zeroE, zeroE, zeroE)).1, nEndT S.v.y + k,
      nEndT S.v.y + (firstOf rows).size + k)).map _).sum = _
  unfold tokSum
  rw [List.map_map, sum_by_number 0, List.length_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < (firstOf rows).size := Finset.mem_range.mp hk
  have eg : (List.range (firstOf rows).size).getD k 0 = k := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_range hk']
    rfl
  rw [eg]
  obtain ⟨m1, m2⟩ := terms_maps S rows k hk'
  show Reading.gl.val (wAt rows k) *
    (Reading.gl.val (((termsCube S rows).maps.getD (nEndT S.v.y + k) #[]).getD t zeroE) *
      Reading.gl.val (((termsCube S rows).maps.getD
        (nEndT S.v.y + (firstOf rows).size + k) #[]).getD t zeroE)) = _
  rw [m1, m2, aMaps_at rows k hk' t, bMaps_at rows k hk' t]

variable [scl : Scl]

/-- **THE CLAIMED SUM IS THE LIBRARY's ClT**, where at each token the sum of products is the
library's summand at the token's corner (hG). CONDITIONAL: on every hypothesis named. -/
theorem terms_clT {S : Sides} {J : Job} (hJ : jobTermsOn S = some J)
    (hz : S.zt.size = S.v.y.h.lt) (D : Dim) (t : Cell → Cb.Gl.E) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW Cb.Gl.E) (z : ℕ → Cb.Gl.E) (hf : D.f = 2 * D.fe) (hlt : D.lT = S.v.y.h.lt)
    (hzp : ∀ j, j < D.lT → zpos D z j = pt Reading.gl S.zt j)
    (hG : ∀ rows, tokenRows S = some rows → ∀ i, i < 2 ^ D.lT →
      tokSum rows i = Gpos D t tb L0 w z (Blocks.cubePt D.lT i)) :
    ClT D t tb L0 w z = Reading.gl.val J.cube.total := by
  obtain ⟨rows, h1, e⟩ := terms_total hJ hz
  rw [e, clT_gpos D t tb L0 w z hf, ← hlt,
    OnBytes.Road.ext_congr_pt D.lT _ hzp]
  exact Blocks.ext_congr (fun i hi => (hG rows h1 i hi).symm) _

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.terms_total
#print axioms ProofFile.Honest.K4.terms_clT
