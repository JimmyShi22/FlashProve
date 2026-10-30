-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/RestPowers.lean: THE SMALLNESS TEST: THE VERIFIER's TEST "THE WEIGHTS OF THE
DIGITS' ARRAY's TWO LAST VIRTUAL ROWS ARE THE POWERS OF THE BATCHING ELEMENT" (rkSelfTestP,
Johnson/Desc/First/TailClaims/SelfTests.lean) SAYS YES BEHIND THE STEP THAT LAYS THE WEIGHTS, UNDER
SIX PREMISES ON THE RECORD AND THE LEDGER IN FRONT OF THAT STEP (the first: the record's two vectors
are the powers of the ledger's own batching element, whichever element that is). Lemmas; none of the
library's goals. No prover stands in them; nothing on completeness, soundness or hiding.

  `powersLoop_ok`, `powers_ok`   every entry of Model.powers x n has words below the prime, whatever
      x
  **`powers_eq_powE`**   entry i of Model.powers x n is powE x i, as words, whatever x
  **`rest_powers`**   where the record's vectors are the powers of the ledger's batching element
      (`Powered`, OnBytes/Tie/Pv/Tail/EndClosed.lean), the ledger has the two rows, and the digits'
      array is another than the bits' and each matrix's: the test's conjunct, as the verifier's text
      has it, at the ledger coefBody tl g F
  `rest_sizes`   under the same premises: each of the two rows has as many weights as the digits'
      array has rows
By: ProdV.gl_inj (Johnson/Desc/First/ProdV/Drawn.lean) · K3.okE_pow
(Johnson/Top/H/K3Via/BridgeProof.lean) · MaskedSum.okE_mul, okE_one (Johnson/Top/H/P1Tie/Words.lean)
· powers_val, powersLoop_old (OnBytes/Tie/Pv/Tail/EndClaimsB.lean) · Reading.pow
(OnBytes/Model/HideLaws.lean) · coefBody_all (Johnson/Desc/First/TailClaims/CoefficientsAll.lean) ·
K9L.core_coefBody (Johnson/Desc/First/Batch/Law/Coef.lean) · `coef_powers`
(Johnson/Desc/K8/Honest/CoefClosed.lean).
Limits. One conjunct of one of the verifier's guards, and two of another. Its six premises are shown
of no state here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.CoefClosed
import Johnson.Desc.First.ProdV.Drawn
import Johnson.Top.H.K3Via.BridgeProof
import Johnson.Desc.First.TailClaims.CoefficientsAll
import Johnson.Desc.First.Batch.Law.Coef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (coefAll rowAt HasRow)
open OnBytes.Tie.Pv.Tail.Port (Powered powers_val powers_size powersLoop_old)
open VerifiableInference.Desc.First.TailClaims (coefBody)

/-- Every entry that the loop appends has words below the prime, where its first has. -/
theorem powersLoop_ok (x : E) : ∀ (n : Nat) (c : E) (a : Array E) (i : Nat), i < n →
    okE c = true → okE ((powersLoop x n c a).getD (a.size + i) zeroE) = true
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, c, a, 0, _, hc => by
    rw [powersLoop, Nat.add_zero, powersLoop_old x n _ _ a.size (by rw [Array.size_push]; omega)]
    simpa [Array.getD] using hc
  | n + 1, c, a, i + 1, h, _ => by
    have e : a.size + (i + 1) = (a.push c).size + i := by rw [Array.size_push]; omega
    rw [powersLoop, e]
    exact powersLoop_ok x n _ _ i (by omega) (Part.MaskedSum.okE_mul _ _)

/-- Every entry of the powers has words below the prime. -/
theorem powers_ok (x : E) (n i : Nat) (h : i < n) :
    okE ((powers x n).getD i zeroE) = true := by
  have k := powersLoop_ok x n oneE (Array.emptyWithCapacity n) i h Part.MaskedSum.okE_one
  simpa [powers] using k

/-- **Entry i of the powers is the power, as words.** -/
theorem powers_eq_powE (x : E) (n i : Nat) (h : i < n) :
    (powers x n).getD i zeroE = powE x i :=
  ProdV.gl_inj _ _ (powers_ok x n i h) (K3.okE_pow x i)
    (by rw [powers_val Reading.gl x n i h, Reading.gl.pow])

/-- **The conjunct on the two rows' weights.** -/
theorem rest_powers (tl : HTailF2) (g : Forest.Heard) (F : Fork) (nbW : Nat)
    (hP : Powered tl F.theta) (hR : HasRow F tl.ix.ZZ tl.zzRowReads)
    (hT : HasRow F tl.ix.ZZ tl.zzRowTies) (hB : tl.ix.BZ ≠ tl.ix.ZZ)
    (hm : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ) (hn : nbW = tl.zzBlocks) :
    ((List.range tl.tau).all fun u =>
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.getD u zeroE ==
          powE (coefBody tl g F).theta u &&
        (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).coef.getD u zeroE ==
          (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.getD u
            zeroE) = true := by
  subst hn
  obtain ⟨c4, c5⟩ := coef_powers tl g F hR hT hB hm
  have e4 : (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).coef =
      powers F.theta tl.tau := c4.trans hP.vt
  have e5 : (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * tl.zzBlocks + 1) {}).coef =
      powers F.theta tl.tau := c5.trans hP.vp
  have et : (coefBody tl g F).theta = F.theta := congrArg (·.2.1) (K9L.core_coefBody tl g F)
  rw [List.all_eq_true]
  intro u hu
  rw [e4, e5, et, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  exact ⟨powers_eq_powE F.theta tl.tau u (List.mem_range.1 hu), rfl⟩

/-- The two rows have as many weights as the digits' array has rows. -/
theorem rest_sizes (tl : HTailF2) (g : Forest.Heard) (F : Fork) (nbW : Nat)
    (hP : Powered tl F.theta) (hR : HasRow F tl.ix.ZZ tl.zzRowReads)
    (hT : HasRow F tl.ix.ZZ tl.zzRowTies) (hB : tl.ix.BZ ≠ tl.ix.ZZ)
    (hm : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ) (hn : nbW = tl.zzBlocks) :
    ((((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).coef.size == tl.tau &&
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).coef.size ==
        tl.tau) = true := by
  subst hn
  obtain ⟨c4, c5⟩ := coef_powers tl g F hR hT hB hm
  have e4 : (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * tl.zzBlocks) {}).coef =
      powers F.theta tl.tau := c4.trans hP.vt
  have e5 : (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * tl.zzBlocks + 1) {}).coef =
      powers F.theta tl.tau := c5.trans hP.vp
  rw [e4, e5, powers_size, Bool.and_eq_true, beq_iff_eq]
  exact ⟨rfl, rfl⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.powersLoop_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.powers_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.powers_eq_powE
#print axioms VerifiableInference.Desc.First.K8.Honest.rest_powers
#print axioms VerifiableInference.Desc.First.K8.Honest.rest_sizes
