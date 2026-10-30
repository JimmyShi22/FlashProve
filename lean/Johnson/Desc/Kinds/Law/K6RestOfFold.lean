-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6RestOfFold.lean: TWO PREMISES OF THE LAW OF THE OUTPUT HEAD'S OWN ROUNDS AT
THE COMPOSED MEANING (Law/K6LawAtMgAll.lean: the fields rest and restB of K6DueMg), IN THESE FIELDS'
OWN WORDS, FROM THE FACTS THAT THE LAWS TAKE FROM "REACHED" (another author's
Johnson/Desc/First/FoldFacts.lean). Statements and proofs: two calls of Law/K6RestAt.lean.

What is said. Rch: a condition beside the table's promise, a parameter. d: the public numbers that
the facts read.
  foldAt_of_facts    five fields of FoldFacts (seatsCarried, msgShapes, codes, liveShape,
      liveLayout) at a statement with Rch k a whose state bears no mark, where d.sent is the
      composed meaning's own and its layout is lay6.
  **rest_of_fold**, **restB_of_fold**   the two fields.
WHAT IS LEFT IN FRONT OF THE TWO, BESIDE FoldFacts AND WHAT THE LAW HOLDS ALREADY (the seated
sub-protocol, the place at 341, the table's test pubFit): hd, hlay (equations on parameters); huH
(the composed meaning's open parameter uH at 24 is this kind's term); hC (ONE TEST WITH CODE ON
PUBLIC PARAMETERS: seatsK6C).

Every letter under "there is": in rest: aK (pinned by K9.segAt? at the state behind), cU (by the
open segment's list of arrays).
What it does not say. THE WITNESSES INSIDE Rch ARE NOT SPENT: five facts on the state in front alone
are taken; nothing is concluded on any transcript. FoldFacts is a premise: statements alone, paid by
nobody here. That the test accepts is no theorem (one evaluation: see its file). The full chain
alone. Nothing on soundness. 
-/
import Johnson.Desc.Kinds.Law.K6RestAt
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning pubFit FoldData FoldFacts)
open VerifiableInference.Desc.Sound (Piece Frame MsgT onQ linksFull MgData mgAll)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
  (Fr : Frame) (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (d : FoldData) (reqW : P → Array UInt32)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- **Five fields, at one statement.** -/
theorem foldAt_of_facts (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull PS)
    (hd : d.sent = D.sent) (hlay : D.layout = lay6) (k : ℕ) (a : (P × S) × Fr.E.Str)
    (hr : Rch k a) (hm : a.1.2.failed = none) : FoldAt d.L d.M D.cs D.shape lay6 a.1.2 :=
  ⟨FF.seatsCarried k a hr hm, FF.msgShapes k a hr hm,
    (FF.codes k a hr hm).trans (by rw [hd]; rfl),
    (FF.liveShape k a hr hm).trans (by rw [hd]; rfl),
    (FF.liveLayout k a hr hm).trans (by rw [hd]; exact hlay)⟩

variable {bef : List (ℕ × ℕ)} {B bS : Block S Claim}
  {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}

/-- **The field rest of K6DueMg.** -/
theorem rest_of_fold (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hfit : pubFit (MGA).more linksFull PS = true)
    (hp : PS[341]? = some { chain := 1, link := some 24, piece := 4, kind := .K6 })
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull PS)
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    (huH : D.uH 24 = uHeadK6 Wp 24) :
    ∀ a τ b, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∃ aK cU, RecordRest D.arr D.N Wp lay6 num (num 24 0) 0 (p8K6 Wp 24) D.St b.1.2 aK cU :=
  fun a τ b ha hr hm hb _ =>
    recordRest_behind D Mg lay6 num Fr d.L d.M Hs hfit hp a b τ ha hm hb
      (foldAt_of_facts D lay6 Fr Rch d reqW FF hd hlay 341 a hr hm) hC huH

/-- **The field restB of K6DueMg.** -/
theorem restB_of_fold (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hfit : pubFit (MGA).more linksFull PS = true)
    (hp : PS[341]? = some { chain := 1, link := some 24, piece := 4, kind := .K6 })
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull PS)
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true) :
    ∀ a τ b, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∀ aK, K9.segAt? b.1.2 = some aK →
      MatsSeated (colsB Wp) D.arr D.N Wp (D.N.sent 24 0) aK num lay6 :=
  fun a τ b ha hr hm hb _ aK hK =>
    matsB_behind D Mg lay6 num Fr d.L d.M Hs hfit hp a b τ ha hm hb
      (foldAt_of_facts D lay6 Fr Rch d reqW FF hd hlay 341 a hr hm) hC aK hK

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.rest_of_fold
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.restB_of_fold
