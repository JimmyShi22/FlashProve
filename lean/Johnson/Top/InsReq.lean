-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InsReq.lean: the user's request and reply as ONE instance of the flat description at the
full size; and that the tie's shape reads this very term where the input's builder is buildReq.

The tie between the Lean program and the theorem's verifier (Johnson/Top/TieInnerCompiledVerifier.lean) reads
an instance off the user's statement: the field insOf of its shape. The system's verifier builds its
instance with the input's builder. The named hypothesis "sound" is paid
(Johnson/Flat/LedgerAtInnerCompilerInputReq.lean, ThreeFull.lean) where that builder is buildReq
(Johnson/Flat/LedgerClaim.lean).

One definition and five theorems.
  insReq x: buildReq at the prompt, the output tokens and the further tokens that
    OnBytes/K/Tokens.lean reads off the request file and the reply file of the statement x.
  buildOf_ppref, buildReq_iff: at the reference sizes buildOf (Johnson/Flat/Instance.lean) is
    requestOfTokens; buildReq returns q if and only if buildOf returns q's instance.
  insOf_eq: at the input innerCompilerInputFromDryRunAtFullSize T of Johnson/Flat/TwoSizes.lean, with the claim claimsReq and
    T's builder buildReq, for every InnerInputTieData: the shape's insOf is insReq.
  built_insReq: the front's law "built" (Johnson/Top/TieFront.lean) there: its own premise again,
    since the front's builder and three lists are the input's and OnBytes/K/Tokens.lean's.
  insReq_reads: an instance that insReq returns reads back to the statement's prompt and output
    tokens.

Limits: that insReq returns where the program says yes is not in this file
(Johnson/Top/InsReqWords.lean). EXACT MATCH ALONE: the claims of Johnson/Flat/ are those of the
strictest acceptance policy; at a parameter file with another policy the laws on insReq are silent.
Nothing on a protocol. The reference sizes.

-/
import Johnson.Top.TieInnerCompiledVerifier
import Johnson.Flat.LedgerAtInnerCompilerInputReq
import Johnson.Flat.BuiltOK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles

open OnBytes.Flat OnBytes.Slice
open OnBytes.K (UserStm InnerInputTieData innerInputTieShape innerInputTieFront)

/-- **The user's request and reply as one instance.** -/
def Flat.insReq (x : UserStm) : Option Flat.Req :=
  Flat.buildReq (OnBytes.K.promptOf x, OnBytes.K.outputOf x) (OnBytes.K.auxOf x)

/-- At the reference sizes buildOf is requestOfTokens. -/
theorem Flat.buildOf_ppref (a : List Token × List Token) (b : List Token) :
    buildOf Inst.Model.ppref a b = requestOfTokens a b := by
  have hV : 0 < Inst.Model.ppref.V := by decide
  unfold buildOf
  rw [dif_pos hV]
  exact buildAt_ppref hV a b

/-- **buildReq returns q if and only if buildOf, at the reference sizes, returns q's instance.** -/
theorem Flat.buildReq_iff {a : List Token × List Token} {b : List Token} {q : Flat.Req} :
    Flat.buildReq a b = some q ↔ buildOf Inst.Model.ppref a b = some q.val := by
  rw [Flat.buildOf_ppref]
  exact ⟨Flat.buildReq_some, fun h => Flat.buildReq_of_built h⟩

/-- What it returns reads back to the statement's prompt and output tokens. -/
theorem Flat.insReq_reads {x : UserStm} {i : Flat.Req} (h : Flat.insReq x = some i) :
    tokensOfRequest i.val = (OnBytes.K.promptOf x, OnBytes.K.outputOf x) :=
  Flat.buildReq_reads h

section
variable (N : MatrixNums) (s : Cm.Scales)
  (E : Coding (claimsReq (frS.toDecR frZ 402653181) N s)) (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **The instance at the tie's slot is insReq**, where T's builder is buildReq. -/
theorem insOf_eq (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a) (Tt : InnerInputTieData (innerCompilerInputFromDryRunAtFullSize T))
    (x : UserStm) : (innerInputTieShape Tt).insOf x = Flat.insReq x :=
  hb _ _

/-- The front builds the instance that the shape reads. -/
theorem built_insReq (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) E G P)
    (Tt : InnerInputTieData (innerCompilerInputFromDryRunAtFullSize T)) (x : UserStm) (i : (innerInputTieShape Tt).Ins x)
    (h : (innerInputTieShape Tt).insOf x = some i) :
    (innerInputTieFront Tt).build ((innerInputTieFront Tt).prompt x, (innerInputTieFront Tt).output x) ((innerInputTieFront Tt).aux x) =
      some ((innerInputTieFront Tt).ins x i) :=
  h

end

end VerifiableInference.OnPublicFiles
