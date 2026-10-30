-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/BuiltOK.lean: the builder buildReq (Johnson/Flat/LedgerClaim.lean) is an honest decoder
of a prompt with output tokens: it does not look at whether the output is the model's.

Why. The named hypothesis "sound" says: if an instance is built from a prompt with output tokens and
is true at an index, the output tokens are the model's. A builder that refused everything would meet
it whatever the relation is. So a form in which "sound" is proved must say what its builder is.
meaningConditionFromDryRunAtFullSize_paid_req (Johnson/Flat/LedgerAtInnerCompilerInputReq.lean) fixes it to buildReq; this file has
buildReq's laws.

Five theorems.
  wellFormed_of_built, buildReq_of_built: every request that requestOfTokens builds is one that the
    program's reader takes; so buildReq refuses nothing that requestOfTokens builds: the cut of the
    instances to Req (Johnson/Flat/ClaimsReq.lean) loses no built request. By buildAt_ppref and
    buildAt_range of Johnson/Flat/Instance.lean and InstanceLaws.lean.
  buildReq_total: for ALL lists of tokens of the vocabulary, a prompt and an output that are not
    empty and have at most 1,025 tokens together, and any padding: buildReq returns a request.
  buildReq_reads: what buildReq returns reads back to the given prompt and output tokens
    (tokensOfRequest, VerifiableInference/RequestOfTokens.lean).
  buildReq_asks_no_model: for EVERY function f from lists of tokens to a next token, buildReq
  accepts some
    prompt with an output token that is not f's: after the prompt [0] it accepts both [0] and [1].

Limits: nothing on a protocol. The reference sizes.

-/
import Johnson.Flat.InstanceLaws
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model

/-- A built request has r < e, and y = 0 if e is before the window's end. -/
theorem wellFormed_of_built {x' : List Token × List Token} {b : List Token} {x : Instance ppref}
    (h : requestOfTokens x' b = some x) : WellFormed x := by
  have hV : 0 < ppref.V := x.y.pos
  rw [← OnBytes.Flat.buildAt_ppref hV] at h
  exact OnBytes.Flat.buildAt_range h

/-- The builder into the well-formed requests refuses nothing that requestOfTokens builds. -/
theorem buildReq_of_built {x' : List Token × List Token} {b : List Token} {x : Instance ppref}
    (h : requestOfTokens x' b = some x) :
    buildReq x' b = some ⟨x, wellFormed_of_built h⟩ := by
  unfold buildReq
  rw [h]
  exact dif_pos (wellFormed_of_built h)

/-- **The builder returns a request for every prompt and every output of tokens of the vocabulary,
of the right lengths**, whatever the output tokens are. -/
theorem buildReq_total (prompt output tail : List IntegerModel.Token) (h1 : 0 < prompt.length)
    (h2 : 0 < output.length) (h3 : prompt.length + output.length ≤ ppref.T + 1) :
    ∃ x : Req, buildReq (prompt.map Fin.val, output.map Fin.val) (tail.map Fin.val) = some x := by
  have e : requestOfTokens (prompt.map Fin.val, output.map Fin.val) (tail.map Fin.val) =
      IntegerModel.requestOf prompt output tail :=
    requestOfTokens_eq (vocabularyTokens_map_val prompt) (vocabularyTokens_map_val output)
      (vocabularyTokens_map_val tail)
  unfold IntegerModel.requestOf at e
  rw [dif_pos ⟨h1, h2, h3⟩] at e
  exact ⟨_, buildReq_of_built e⟩

/-- **What the builder returns reads back to the given prompt and output tokens.** -/
theorem buildReq_reads {x' : List Token × List Token} {b : List Token} {x : Req}
    (h : buildReq x' b = some x) : tokensOfRequest x.1 = x' :=
  tokensOfRequest_requestOfTokens (buildReq_some h)

/-- **The builder does not look at a model**: whatever function gives the next token, the builder
accepts a prompt with an output token that is not that function's. -/
theorem buildReq_asks_no_model (f : List Token → Option Token) :
    ∃ (x' : List Token × List Token) (x : Req), buildReq x' [] = some x ∧
      ∃ h : 0 < x'.2.length, f (x'.1 ++ x'.2.take 0) ≠ some x'.2[0] := by
  have hV0 : 0 < ppref.V := by decide
  have hV1 : 1 < ppref.V := by decide
  have h3 : 1 + 1 ≤ ppref.T + 1 := by decide
  by_cases hf : f [0] = some 0
  · obtain ⟨x, hx⟩ := buildReq_total [⟨0, hV0⟩] [⟨1, hV1⟩] [] Nat.one_pos Nat.one_pos h3
    refine ⟨([0], [1]), x, hx, Nat.one_pos, fun h => ?_⟩
    have h' : f [0] = some 1 := h
    rw [hf] at h'
    exact absurd (Option.some.inj h') (by decide)
  · obtain ⟨x, hx⟩ := buildReq_total [⟨0, hV0⟩] [⟨0, hV0⟩] [] Nat.one_pos Nat.one_pos h3
    exact ⟨([0], [0]), x, hx, Nat.one_pos, hf⟩

end VerifiableInference.OnPublicFiles.Flat

#print axioms VerifiableInference.OnPublicFiles.Flat.wellFormed_of_built
#print axioms VerifiableInference.OnPublicFiles.Flat.buildReq_of_built
#print axioms VerifiableInference.OnPublicFiles.Flat.buildReq_total
#print axioms VerifiableInference.OnPublicFiles.Flat.buildReq_reads
#print axioms VerifiableInference.OnPublicFiles.Flat.buildReq_asks_no_model
