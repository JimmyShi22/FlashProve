-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07KindOfFacts.lean.
WHAT IT DOES NOT SHOW. No soundness. THE NEXT TOKEN's KIND's LAW IN THE FORM IN WHICH A KIND's LAW
IS COUNTED (P5J/RowsAtAll.lean: AtMgA.Kind), NOT FOR NOTHING: BESIDE THE HEAD AND q₁, q₂, q₃ (L's
three lists are the IOP's own) SEVEN PREMISES STAY, BY NAME: TWO TESTS WITH CODE ON PUBLIC DATA:
book, fenceT (no theorem; evaluated true, in these terms, AT ONE STORED FULL-SIZE SET's THREE PUBLIC
FILES, while the statement is general in the public part and the chain) · TWO CLOSED FACTS: hs (the
place whose switch opens group 24 stands at the head) and hb (the piece's base is at most the number
of the first chain's trees): each a theorem of the code switching's files, not called here (hs also
evaluated at that set) · THREE FACTS ALONG "REACHED" AT 338, AT UNMARKED STATES ALONE: bookInOrder
(at the switch's own first tree), bookFits, rowsSent: the letters of three fields of FoldFacts. NO
EXAMPLE IN LEAN SHOWS THAT THE HEAD AND THESE CAN BE MET TOGETHER: NOTHING COUNTS AS PROVED. At the
format's second hash function itself alone. The full size alone.
WORDS. "The counted form", "the closed constant": as in Law/K07AtMg.lean. "Reached":
AtMg.rch: reached, at a typed instance's public part. "Unmarked": the verifier's state bears
no mark of failure.
LETTERS. No "there is" in the statement. No free letter but the head's own and L.
OBJECT. AtMgA.Kind h L at the kind K7.
USER. The kinds' join.
WHAT IT IS. THE WHOLE ROAD IN ONE STATEMENT: FOUR CALLS. The debt "carry 23"
(Law/K7CarryAtHead.lean) pays the condition's last field (Law/K7CondOfLaid.lean); the condition
gives the law at "reached and unmarked" (Law/K07AtMg.lean: k07_of_cond, general in that letter); the
law comes back to "reached" (Law/TiedRMonoOn.lean: KindTiedR.of_unmarked).
WHY OVER "REACHED AND UNMARKED": a marked state is inside every promise, and the fold facts ask
"unmarked": so at a marked state in front nothing is in hand; the chain of promises' ties hand
"unmarked" beside "reached".
NEAREST RELATIVE: the skeleton's own file for this kind
(Goal/Skeleton/Kinds/K7Left.lean [not in this library]:
k07_kind_left) ends in the same field from book, fenceT and K7Carry at its own name for "reached and
unmarked": NOT IMPORTED HERE.

-/
import Johnson.Desc.Kinds.Law.K7CarryAtHead
import Johnson.Desc.Kinds.Law.TiedRMonoOn
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (HTailF2)
open OnBytes.Params (ReqLayout ReqShape)
open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc (Strs Place Block FileDescription Oracle KindName)
open VerifiableInference.Desc.First (S Numbers ModelPart Meaning PubData flatPlacesOf rowSegs sampledIn
  openSets start Item readsOpen pubHeld pubSets pubStep pubRowM pubOfItems stepOpen rowOf)
open VerifiableInference.Desc.K13 (indexIsC indexThereC)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_rest withFresh)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2 (par9)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The driver's list of places, at the full chain. -/
local notation "PS" => flatPlacesOf linksFull true

/-- **THE NEXT TOKEN's LAW, IN THE COUNTED FORM, FROM THE HEAD AND SEVEN NAMED PREMISES.** -/
theorem k07_kind_of_facts (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (book : First.bookFit (dAt h).N PS (toldOf cF.blocksInOrder) = true)
    (fenceT : First.fenceFit (dAt h).N linksFull PS = true)
    (hs : (ProofFile.pAtK2 Zp 23).stands = .head)
    (hb : ∀ q, (h.toAtMg.row L)[338]? = some q → q.base ≤ D.t₁)
    (bookInOrder : ∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstBook (par9 (ProofFile.pAtK2 Zp 23)).firstTree a.1.2 = true)
    (bookFits : ∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
      VerifiableInference.Desc.K12.Door.atFirstFits a.1.2 = true)
    (rowsSent : ∀ a, h.toAtMg.rch 338 a → a.1.2.failed = none →
      ∀ o ∈ OnBytes.singleRowsOracles a.1.2.live.frame.rows, o < a.1.2.book.place.size) :
    h.Kind L KindName.K7 := by
  unfold P5J.AtMgA.Kind
  exact KindTiedR.of_unmarked
    (k07_of_cond h L.c₀ _ _
      (k7Cond_of_laid h L q₁ q₂ q₃ (fun k a => h.toAtMg.rch k a ∧ ¬ a.1.2.failed ≠ none) book fenceT
        (k7Carry_at_head h L q₁ q₂ q₃ _ (fun _ u => u.2) book hs hb
          (fun a u => bookInOrder a u.1) (fun a u => bookFits a u.1)
          (fun a u => rowsSent a u.1))))

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07_kind_of_facts
