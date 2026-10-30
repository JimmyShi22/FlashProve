-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/PowOfClose.lean: THE TWO CODES OF THE ROWS THAT A CLOSING CARRIES ON
STAND IN THE STATEMENT's LISTS OF CODES; SO, UNDER THE PROGRAM's TEST ON THE CODES' LENGTHS, THE
MAIN CODE's MESSAGE LENGTH IS A POWER OF TWO. Right behind a closing, and at every statement grown
out of the closing's: no state of the walk. Two statements with their proofs. Over the library
alone.

  `code_of_close` a yes of the frame's closing (`closeFrame`), and T grown out of the closing's
                    statement (`Grows`, Johnson/Desc/Grows.lean) ⊢ the carried rows' main code's
                    number is below the number of T's main codes, and their mask code's below that
                    of T's mask codes
  `pow_of_close` and `T.codes.lengthsOk = true` (OnBytes/Iop/Ground.lean) ⊢ 2 ^ (the logarithm of
                    the main code's message length) is that length

By, all the library's: `closeFrame_all` (Johnson/Goal/Meaning/RecK10.lean) · `closeFrame_iff`,
`fold_iff` (Johnson/Desc/First/Close/Law/CloseMeans.lean) · `foldShapeFits_iff`
(Johnson/Desc/Own/FoldMean.lean): the closing's own test on the fold's shape finds both codes in the
lists · `fold_grows` (Johnson/Goal/Meaning/GrowsSeated.lean) · `ell_pow`
(Johnson/Goal/Meaning/LaidInside.lean). NEAR, NOT CALLED: `head_oldCode_reached`,
`fin_oldCode_reached` (Returns/ArmsPlan.lean) and the field `oldCode` of `LinkPlain`
(Returns/LinkSent.lean): at reached fronts the carried rows' main code is c₀, FOR EVERY c₀ that
stands at the frame's shape's number: that one stands there is their premise · `TargetFits.oldCode`
(Johnson/Top/H0/Tw/K2/TargetMeans.lean): the same bound, out of a yes of the switch's own test on
its target · two sisters of `ell_pow`: `ell_of_lengthsOk`
(Johnson/Second/K08/BlocksInOfLayout.lean): for a code that is a member of the list · `pow_logEll`
(Johnson/Desc/K1/Law/When.lean): the same equation for any array of codes all of whose lengths pass
the test.

Limits. The test on the lengths is a premise here. Nothing on the mask code's length. Nothing on any
property.
-/
import Johnson.Desc.K2.Honest.Returns.ClosedReached
import Johnson.Goal.Meaning.LaidInside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Grows)
open VerifiableInference.Desc.First.Close (closeFrame closeFrame_iff fold_iff)
open Meaning.K2 (fold_grows closeFrame_all)

/-- **The carried rows' main code stands in the list of codes**, at every statement grown out of the
closing's. -/
theorem code_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T) :
    x.1.rows.code < T.codes.base.size ∧ x.1.rows.maskCode < T.codes.mask.size := by
  obtain ⟨-, -, -, -, -, hcode, hmask, -, -⟩ := closeFrame_all (f' := x.1) (S' := x.2) h
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ := (closeFrame_iff owed f S₀ es rs x.1 x.2).1 h
  obtain ⟨eB, es', rB, rs', -, -, m, -, row, L, S₁, hB, -, hF⟩ := hc
  have hg1 := fold_grows ((fold_iff _ _ _ _ _ _ _ _).2 hF)
  obtain ⟨eE, eR, rE, rR, -, -, -, -, hshape, -⟩ := hF
  obtain ⟨c, zk, h1, h2, -⟩ := (Own.foldShapeFits_iff _ _).1 hshape
  rw [hcode, hmask, (Grows.trans hg1 hg).1]
  exact ⟨(Array.getElem?_eq_some_iff.1 h1).1, (Array.getElem?_eq_some_iff.1 h2).1⟩

/-- **So, under the program's test on the codes' lengths, its length is a power of two.** -/
theorem pow_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T)
    (hC : T.codes.lengthsOk = true) :
    2 ^ (T.codes.base.getD x.1.rows.code default).logEll =
      (T.codes.base.getD x.1.rows.code default).ell :=
  Meaning.ell_pow hC (code_of_close h hg).1

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.code_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.pow_of_close
