-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ClaimsTrue.lean: the parameter A of the description made of the three files' protocols
as a concrete term (defined in this library, not a parameter) at any model sizes P, and the named
hypothesis "sound" of Johnson/Top/InnerCompiledVerifier.lean proved at the small-size input of
Johnson/Flat/TwoSizes.lean whose builder is buildReqAt P and whose model is nextTokenIn.

READ THIS FIRST. The library has a relaxed relation at the reference sizes alone. So here the claim
of a request is ITS TRUTH by the library's integer program at the sizes P (TrueBy, nextOfDigits:
Johnson/Flat/ClaimsAny.lean). "sound" is then nearly a definition, and ALL the weight lies on the
hypothesis "proofSound", which must give exact truth by that program. AT THE SMALL SIZES
nextOfDigits IS NOT THE SMALL EXAMPLE's MODEL: the program's five fixed tables are the reference's
(Johnson/Flat/ClaimsAny.lean, Limits; the rotary base 500,000: IntegerModel/Model.lean), and the
table of scales s is a parameter: the small example's own scale file is refused as not lawful (by an
evaluation that is in no file of this library; the intervals: Inst/Model/FF/ScalesDef.lean), and the
library's step from what sub-proofs check to the truth requires a lawful table. So with these terms
"proofSound" at the small example's files cannot be expected to hold. That nextOfDigits returns a
token at any list at the small sizes is not shown (Johnson/Flat/ClaimsAny.lean, Limits): if it never
does, the claim holds of no request and "sound" holds vacuously. "sound is proved at the small size"
must not be said without this.

States, at a decoder D, the matrix's numbers N, sizes P, a table of scales s:
  claimsTrue D N P s : D.Claims (ReqAt P): the matrices of Johnson/Flat/Claims.lean; in range: M
    holds digits; the claim: M holds digits W at which the request is true by nextOfDigits P k s W.
  sound_true_core: a built request of which the claim holds at M has the output tokens that
    nextTokenIn D N P s gives at M.
  meaningConditionFromDryRunAtSmallSize_paid: CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtSmallSize T), where T's builder is buildReqAt P and T's
    model nextTokenIn. Small are the decoder and the record; N, P and s are parameters. No
    lawfulness is required.

Limits: nothing on a protocol. See READ THIS FIRST.

-/
import Johnson.Flat.ClaimsAny
import Johnson.Flat.TwoSizes
import Johnson.Flat.TrueCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

open OnBytes.Slice Inst.Model VerifiableInference VerifiableInference.OnPublicFiles

/-- What the program's reader of a request asks beside the lengths, at the sizes P. -/
def WellFormedAt {P : Params} (x : Instance' P) : Prop := x.r < x.e ∧ (x.e < P.T → x.y.val = 0)

instance {P : Params} (x : Instance' P) : Decidable (WellFormedAt x) := by
  unfold WellFormedAt
  infer_instance

/-- The requests that the reader takes. -/
abbrev ReqAt (P : Params) : Type := {x : Instance' P // WellFormedAt x}

/-- The builder into these. -/
def buildReqAt (P : Params) (x' : List Token × List Token) (b : List Token) : Option (ReqAt P) :=
  (buildOf P x' b).bind fun x => if h : WellFormedAt x then some ⟨x, h⟩ else none

theorem buildReqAt_some {P : Params} {x' : List Token × List Token} {b : List Token} {x : ReqAt P}
    (h : buildReqAt P x' b = some x) : buildOf P x' b = some x.1 := by
  unfold buildReqAt at h
  cases hq : buildOf P x' b with
  | none =>
    rw [hq] at h
    cases h
  | some y =>
    rw [hq] at h
    have h' : (if hw : WellFormedAt y then some (⟨y, hw⟩ : ReqAt P) else none) = some x := h
    split at h'
    · cases h'
      rfl
    · cases h'

variable (D : DecR) (N : MatrixNums) (P : Params)

/-- The matrix holds the digits W. -/
def HoldsDigits (M : Cells D N) (W : Mat) : Prop :=
  Says D N M W ∧ Layout.WFW P (N.kLo + D.v) W N.rows

/-- **What the statements read of a decoded table**, at the sizes P and a table of scales s. -/
def claimsTrue (s : Cm.Scales) : D.Claims (ReqAt P) where
  Mat := Cells D N
  mat := cellsOf D N
  inRange := fun M => ∃ W, HoldsDigits D N P M W
  Rel := fun M x => ∃ W, HoldsDigits D N P M W ∧ TrueBy (nextOfDigits P (N.kLo + D.v) s W) x.1
  mat_cut := cellsOf_cut D N

variable {D N P}

/-- A matrix holds at most one matrix of digits. -/
theorem holdsDigits_unique {M : Cells D N} {W W' : Mat} (h : HoldsDigits D N P M W)
    (h' : HoldsDigits D N P M W') : W = W' :=
  OnPublicFiles.Flat.says_unique h.1 h'.1 (fun y hy c hc => h.2.1 y hy c hc)
    (fun y hy c hc => h'.2.1 y hy c hc)

theorem digitsIn_eq {M : Cells D N} {W : Mat} (h : HoldsDigits D N P M W) :
    digitsIn D N P M = some W := by
  have hex : ∃ W : Mat, Says D N M W ∧ Layout.WFW P (N.kLo + D.v) W N.rows := ⟨W, h⟩
  unfold digitsIn
  rw [dif_pos hex]
  exact congrArg some (holdsDigits_unique (Classical.choose_spec hex) h)

/-- **The meaning**: a built request of which the claim holds at M has the output tokens that the
program gives at the digits that M holds. -/
theorem sound_true_core (s : Cm.Scales) {M : Cells D N} {x' : List Token × List Token}
    {b : List Token} {x : ReqAt P} (hb : buildReqAt P x' b = some x)
    (hR : ∃ W, HoldsDigits D N P M W ∧ TrueBy (nextOfDigits P (N.kLo + D.v) s W) x.1) :
    ∀ position (hp : position < x'.2.length),
      nextTokenIn D N P s M (x'.1 ++ x'.2.take position) = some x'.2[position] := by
  obtain ⟨W, hW, ht⟩ := hR
  intro position hp
  unfold nextTokenIn
  rw [digitsIn_eq hW]
  show nextOfDigits P (N.kLo + D.v) s W (x'.1 ++ x'.2.take position) = some x'.2[position]
  have hb' := buildReqAt_some hb
  unfold buildOf at hb'
  split at hb'
  · exact OnPublicFiles.Flat.built_positions hb' _ (fun t h1 h2 => ht.2.1 t h1 h2) position hp
  · cases hb'

section
variable (N P) (s : Cm.Scales) (E : Coding (claimsTrue (srS.toDecR srZ 524285) N P s))
  (G : FilesParameters (ReqAt P) RecSmall)
  (Pv : (threeProtocolsFromDryRunAtSmallSize (claimsTrue (srS.toDecR srZ 524285) N P s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **"sound" at the small size.** See READ THIS FIRST in the head. -/
theorem meaningConditionFromDryRunAtSmallSize_paid
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize (claimsTrue (srS.toDecR srZ 524285) N P s) E G Pv)
    (hb : ∀ x' a, T.build x' a = buildReqAt P x' a)
    (hn : ∀ M l, T.nextToken M l = nextTokenIn (srS.toDecR srZ 524285) N P s M l) :
    CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtSmallSize T) := by
  intro i x' a x hbx hw position h
  obtain ⟨w, hw⟩ := hw
  show T.nextToken i (x'.1 ++ x'.2.take position) = some x'.2[position]
  rw [hn]
  exact sound_true_core s ((hb x' a).symm.trans hbx) hw.2 position h

end

end OnBytes.Flat
