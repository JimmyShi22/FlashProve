-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09Kind.lean: THE BATCHING KIND's FIELD OF THE KINDS' LAWS, AT THE CLOSED CONSTANT:
«‹the kind's one named condition› → the kind's share in the form in which a kind's law is counted»
(`AtMgA.Kind`, Johnson/P5J/RowsAtAll.lean). Calls of Johnson/Desc/First/Link/Law/K09Cond.lean; no
more. Cut over RowsAtAll.lean: the meaning is the closed constant (`mgAtAll h`); the one «reached»
is the fence that the join spends (`h.toAtMg.rch`: reached, and the statement's public part is a
typed instance's).

What is said.
  `AtMgA.K9Cond h 𝔏`: `K9Cond` at the numbers, the closed meaning, the written lists, that fence,
    the extractor and the pieces of the seated term. `k09_kind`: **`h.Kind 𝔏 .K9` from it.**
    `k09_behind_at`: **from the same condition: `TiedAtR` at the place behind each of the 25
    batchings** (of the kind «frame»; numbers 14 m + 10; the head's 348), at the same fence.

Limits. BOOK-KEEPING. THE CONDITION IS THE DEBT: no member is known. 𝔏 is an argument: whoever
states the condition as a hypothesis lays the closed term in. Nothing on soundness.

-/
import Johnson.P5J.RowsAtAll
import Johnson.Desc.First.Link.Law.K09Cond

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.LinkJoin (k09_tied k09_behind k9Fit_links batchAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE BATCHING KIND's ONE NAMED CONDITION, AT THE CLOSED CONSTANT.** -/
def AtMgA.K9Cond (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) : Prop :=
  VerifiableInference.Desc.LinkJoin.K9Cond
    (F := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
    (At.N Zp cF) (mgAtAll h) fullLinks At.ps h.toAtMg.rch (h.toAtMg.ex 𝔏) (h.toAtMg.row 𝔏)

/-- **THE FIELD.** -/
theorem k09_kind (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (C : h.K9Cond 𝔏) : h.Kind 𝔏 .K9 :=
  k09_tied k9Fit_links C

/-- **THE PLACE BEHIND EACH BATCHING**, from the same condition, at the same fence. -/
theorem k09_behind_at (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (C : h.K9Cond 𝔏) (m : ℕ)
    (hm : m < fullLinks.length) (hb : batchAt fullLinks At.ps m + 1 + 1 < At.ps.length) :
    ∀ q, (h.toAtMg.row 𝔏)[batchAt fullLinks At.ps m + 1]? = some q →
      TiedAtR (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
        (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch
        (batchAt fullLinks At.ps m + 1)
        (q.withMap (h.toAtMg.ex 𝔏 (batchAt fullLinks At.ps m + 1))) :=
  fun q hq => k09_behind C m hm hb q hq

end P5J

#print axioms P5J.k09_kind
#print axioms P5J.k09_behind_at
