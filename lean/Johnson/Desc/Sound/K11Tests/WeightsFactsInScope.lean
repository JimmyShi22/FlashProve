-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/WeightsFactsInScope.lean: SEVEN FACTS ON THE PUBLIC PARAMETERS HOLD AT
ALL PUBLIC FILES IN THE GOALS' SCOPE. They are the fields plan, tokens, sized, wsLay, lam, vocab and
dim of the list `K11Rest` of what is left beneath the named condition for the merge of the claims
on the committed table (kind K11): the closed premises of the lemma that joins the two sentences for
"weights". Statements and proofs; nothing is evaluated at particular files.

ALL SEVEN ARE CALLS OF THEOREMS THAT LIE ALREADY: this file gives them the list's names and types
no law anew.
  plan_fact      (parOf X.hS (workOf X)).ok = true      ok_in_scope
                                                        (Johnson/Goal/Meaning/HeadCondScope.lean)
  tokens_fact    X.T = X.hS.T   NO SCOPE                Fo.Pub.public_T
                                                        (OnBytes/Tie/Pv/Lookup/Ends/FoMadePub.lean)
  sized_fact     there is a shape of the committed table with the reference model's sizes at which
                 wsLayOf returns X's layout             Meaning.Emb.emb_public_in_scope
                                                        (Johnson/Goal/Meaning/EmbScope.lean)
  vocab_fact     X.hS.V = 202048                        numbers_in_scope (HeadCondScope.lean)
  dim_fact       X.hS.d = 5120                          numbers_in_scope
  lam_fact       X.H.lamS = 13                         Fo.public_lam (X.H.lamS = X.hS.lPd; no scope:
                                                        OnBytes/Tie/Pv/Lookup/Ends/FoGlueNames.lean)
                                                        with numbers_in_scope's lPd
  weights_facts  the seven together

X and lay are general: no premise on the plain road's public part is spent.

Limits. That the premises can be met together is not shown here. Nothing on a verifier's state.
Nothing on soundness.

-/
import Johnson.Goal.Meaning.HeadCondScope
import Johnson.Goal.Meaning.EmbScope
import Johnson.Desc.Kinds.Law.RowRides
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePub
import OnBytes.Tie.Pv.Lookup.Ends.FoGlueNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (ok_in_scope numbers_in_scope)

section
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}

/-- **tokens**: at everything that publicOf returns. -/
theorem tokens_fact (h : publicOf pol KL lay = .ok X) : X.T = X.hS.T := Fo.Pub.public_T h

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Verify.Public}

/-- **plan.** -/
theorem plan_fact (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok X) : (parOf X.hS (workOf X)).ok = true :=
  ok_in_scope hS hR hX _

/-- **sized and wsLay**, at one shape. -/
theorem sized_fact (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok X) :
    ∃ shW : WsShape, OnBytes.Road.SizedW shW Inst.Model.ppref ∧
      wsLayOf shW true Inst.Model.Layout.kRef = .ok X.layers.wsLay :=
  ⟨_, (Meaning.Emb.emb_public_in_scope hS hR hX).2.1,
    (Meaning.Emb.emb_public_in_scope hS hR hX).2.2.1⟩

/-- **lam.** -/
theorem lam_fact (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok X) : X.H.lamS = 13 :=
  (Fo.public_lam hX).trans (numbers_in_scope hS hR hX).lPd

/-- **vocab.** -/
theorem vocab_fact (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok X) : X.hS.V = 202048 := (numbers_in_scope hS hR hX).V

/-- **dim.** -/
theorem dim_fact (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok X) : X.hS.d = 5120 := (numbers_in_scope hS hR hX).d

/-- **THE SEVEN.** -/
theorem weights_facts (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok X) :
    (parOf X.hS (workOf X)).ok = true ∧ X.T = X.hS.T ∧
      (∃ shW : WsShape, OnBytes.Road.SizedW shW Inst.Model.ppref ∧
        wsLayOf shW true Inst.Model.Layout.kRef = .ok X.layers.wsLay) ∧
      X.H.lamS = 13 ∧ X.hS.V = 202048 ∧ X.hS.d = 5120 :=
  ⟨plan_fact hS hR hX, tokens_fact hX, sized_fact hS hR hX, lam_fact hS hR hX,
    vocab_fact hS hR hX, dim_fact hS hR hX⟩

end

end LT28.K11Tests

#print axioms LT28.K11Tests.tokens_fact
#print axioms LT28.K11Tests.plan_fact
#print axioms LT28.K11Tests.sized_fact
#print axioms LT28.K11Tests.lam_fact
#print axioms LT28.K11Tests.vocab_fact
#print axioms LT28.K11Tests.dim_fact
#print axioms LT28.K11Tests.weights_facts
