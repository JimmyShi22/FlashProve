-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Instance.lean: what an index and an instance are for the three written proofs of
OnBytes/Flat/Frame.lean, and how an instance is built from a prompt and output tokens.

Definitions, and three equations. A configuration (`Hiop.ConfigurationWithOutOfDomainSample`, Hiop/RecConf.lean) has a type I of
indices and a type X of instances. A protocol description takes beside them `build : List Token ×
List Token → List Token → Option X` and `nextToken : I → List Token → Option Token`, where a token
is a number.

Main names:
  `Instance' P`: an instance at the model's numbers P (`Inst.Model.Instance P`): a window of P.T
    tokens below P.V, a reply token y, and two numbers r, e ≤ P.T that bound the covered positions.
  `tokensBelow V`, `requestAt P`, `buildAt P`: the text of `vocabularyTokens`,
    `IntegerModel.requestOf` and `requestOfTokens` (VerifiableInference/RequestOfTokens.lean) with P
    in the place of the reference numbers `Inst.Model.ppref`.
  `tokensBelow_ppref`, `requestAt_ppref`, `buildAt_ppref`: at the reference numbers they are those
    functions.
  `buildOf P`: `buildAt` without the premise that the vocabulary has a token.
  `sizesOf`, `sizesAt`, `exactPolicy`: the model's ten sizes off the parameter file, so that
    `Instance' P` and `buildOf P` are terms at every parameter file that the program's scan admits
    and whose acceptance policy is exact match.
  `requestWordsOf`, `replyWordsOf`: the words of the request file and of the reply file that say an
    instance, in the order in which `Model.Head.stFromCall` (OnBytes/Model/HeadLayout.lean) reads
    them.
  `Index`, `nextTokenAt s`: at the reference numbers, the index of Cm/RelBase.lean, a well-formed
    matrix of digits in the layout's shape, and the integer model's next token at the weights that
    the layout reads from it, at a table of scales s.
Limits: nothing on a protocol. THE ACCEPTANCE POLICY IS NO PART OF AN INSTANCE: exact match alone.
The program's scan is not all of the verifier's tests on a parameter file. That
`Model.Head.stFromCall` takes the words of `requestWordsOf`: Johnson/Flat/InstanceLaws.lean. An
index and a next token are given at the reference numbers alone: the integer model's functions name
these numbers outright.
-/
import IntegerModel.ModelOutput
import Cm.IdxFinite
import OnBytes.Model.HeadLayout
import OnBytes.Model.Config

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model VerifiableInference

/-- An instance at the model's numbers P. -/
abbrev Instance' (P : Params) : Type := Instance P

/-- The numbers as tokens of a vocabulary of V tokens; `none` if one of them is not below V. -/
def tokensBelow (V : ℕ) : List Token → Option (List (Fin V))
  | [] => some []
  | token :: rest =>
      if h : token < V then (tokensBelow V rest).map (⟨token, h⟩ :: ·) else none

/-- The instance of a prompt, output tokens and padding: a window of P.T tokens (the prompt, the
output, the padding, then token 0); r, the position of the prompt's last token; e = r + the output's
length. With P.T + 1 tokens in all, the last output token is outside the window, as y; otherwise y
is token 0. `none`: the prompt or the output is empty, or they have more than P.T + 1 tokens
together. -/
def requestAt (P : Params) (hV : 0 < P.V) (prompt output padding : List (Fin P.V)) :
    Option (Instance' P) :=
  if h : 0 < prompt.length ∧ 0 < output.length ∧ prompt.length + output.length ≤ P.T + 1 then
    some ⟨fun t => (prompt ++ output ++ padding).getD t.val ⟨0, hV⟩,
      (prompt ++ output).getD P.T ⟨0, hV⟩,
      ⟨prompt.length - 1, by have h1 := h.1; have h2 := h.2.1; have h3 := h.2.2; omega⟩,
      ⟨prompt.length - 1 + output.length,
          by have h1 := h.1; have h2 := h.2.1; have h3 := h.2.2; omega⟩⟩
  else none

/-- The same from numbers. `none` also if a number in one of the three lists is not below P.V. -/
def buildAt (P : Params) (hV : 0 < P.V) (x : List Token × List Token) (padding : List Token) :
    Option (Instance' P) :=
  match tokensBelow P.V x.1, tokensBelow P.V x.2, tokensBelow P.V padding with
  | some prompt, some output, some pad => requestAt P hV prompt output pad
  | _, _, _ => none

/-- At the reference numbers `tokensBelow` is `vocabularyTokens`. -/
theorem tokensBelow_ppref : ∀ list : List Token, tokensBelow ppref.V list = vocabularyTokens list
  | [] => rfl
  | token :: rest => by
      show (if h : token < ppref.V then (tokensBelow ppref.V rest).map (⟨token, h⟩ :: ·)
          else none) =
        (if h : token < ppref.V then (vocabularyTokens rest).map
          ((⟨token, h⟩ : IntegerModel.Token) :: ·) else none)
      rw [tokensBelow_ppref rest]

/-- At the reference numbers `requestAt` is `IntegerModel.requestOf`. -/
theorem requestAt_ppref (hV : 0 < ppref.V) (prompt output padding : List (Fin ppref.V)) :
    requestAt ppref hV prompt output padding = IntegerModel.requestOf prompt output padding := rfl

/-- At the reference numbers `buildAt` is `requestOfTokens`. -/
theorem buildAt_ppref (hV : 0 < ppref.V) (x : List Token × List Token) (padding : List Token) :
    buildAt ppref hV x padding = requestOfTokens x padding := by
  unfold buildAt requestOfTokens
  rw [tokensBelow_ppref, tokensBelow_ppref, tokensBelow_ppref]
  cases vocabularyTokens x.1 with
  | none => rfl
  | some prompt =>
    cases vocabularyTokens x.2 with
    | none => rfl
    | some output =>
      cases vocabularyTokens padding with
      | none => rfl
      | some pad => exact requestAt_ppref hV prompt output pad

/-- `buildAt`, and `none` for a vocabulary without a token. -/
def buildOf (P : Params) (x : List Token × List Token) (padding : List Token) :
    Option (Instance' P) :=
  if hV : 0 < P.V then buildAt P hV x padding else none

/-- The model's ten sizes, off the parameter file's lines lt, V, L, d, H, G, dh, f, fe, NE as the
program's scan holds them (`Model.Hdr`, OnBytes/Model/Config.lean). The window has 2 ^ lt tokens.
The other fields, the shifts and the numbers of the normalisations, are left at the reference
numbers': an instance reads T and V alone. -/
def sizesOf (h : Model.Hdr) : Params :=
  { ppref with
    T := 2 ^ h.lt, V := h.V, layers := h.L, d := h.d, nq := h.H, nkv := h.Gk, ch := h.dh, f := h.f,
    fe := h.fe, nexp := h.NE }

/-- True if the parameter file's lines C, theta, cap, sh, sT are those of the strictest acceptance
policy, under which a proof says that each checked token is the model's first choice
(`Model.exactMatch`, OnBytes/Model/Config.lean). -/
def exactPolicy (h : Model.Hdr) : Bool := Model.exactMatch h.clipC h.theta h.cap h.digSh h.tabS

/-- The sizes, off the parameter file's bytes. Refused where the program's scan refuses the file,
and where the file's acceptance policy is not exact match: the policy is no part of an instance, and
the claims of Johnson/Flat/Claims.lean are those of exact match alone. -/
def sizesAt (policy : ByteArray) : Except String Params := do
  let P ← Model.polScan policy
  if exactPolicy P.h then pure (sizesOf P.h) else throw "policy-not-exact-match"

/-- The words of the request file that says the instance: the P.T tokens, then r and e. -/
def requestWordsOf {P : Params} (x : Instance' P) : Array UInt32 :=
  (Array.ofFn fun t : Fin P.T => UInt32.ofNat (x.prompt t).val) ++
    #[UInt32.ofNat x.r, UInt32.ofNat x.e]

/-- The one word of the reply file: y. -/
def replyWordsOf {P : Params} (x : Instance' P) : Array UInt32 := #[UInt32.ofNat x.y.val]

/-- An index, at the reference numbers. -/
abbrev Index : Type := Cm.Idx

/-- The next token at an index, at a table of scales. -/
def nextTokenAt (s : Cm.Scales) (i : Index) (tokens : List Token) : Option Token :=
  IntegerModel.nextToken s i.index tokens

end OnBytes.Flat
