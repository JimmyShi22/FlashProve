-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsOwedAt.lean: WHAT THE READING LAW AT THE CONSTANT OWED IS PAID: AT EVERY BORDER OF
THE FIRST CHAIN EVERY RIDER's SENTENCE READS ONLY WHAT THE TABLE BOOKS, UNDER THE HEAD, FoldFacts
AND THREE CLOSED TESTS. Four theorems.

Why. `AtMgA.readsOk_at` (Johnson/P5J/ReadsAtHead.lean) stands under `ReadsOwed`: six named fields.
Each has a payer: in this folder's files and in others, named below. Here they are laid in.

What is said. `AtMgA.readsOwed`: `ReadsOwed h h.toAtMg.rch M L` at M := the listed shapes and L :=
the listed seats: `hid`: five congruences (Johnson/P5J/ReadsDigitsAt.lean, ReadsHidAt.lean,
ReadsHeadAt.lean) · `book`: Johnson/P5J/BookPremAt.lean, from FoldFacts at the head · `wtForms`:
`wtK6_reads` (Johnson/Desc/Kinds/Law/WtK6Reads.lean) · `carry`: `carryAtZ_reads`
(Johnson/Top/H0/K2Caller/CarryAnyW.lean) · `worth`: `worth_reads_at` · `fit`: by the kernel
(Johnson/P5J/RidersFitAt.lean). `AtMgA.readsOk`: so `ReadsOkAtQR` at every border up to the last, at
`h.toAtMg.rch`. `AtMgA.reads_at_place`: the same in the form in which a kind's condition asks it: at
the border of a place of the written list, at `At.arr Zp`, `At.N Zp cF`, `fullLinks`.
`AtMgA.reads_at_kind`: with the kind named (it plays no part).

The premises: the head `AtMgA` · FoldFacts at the head's own letters (a theorem elsewhere, under one
public test) · THREE CLOSED TESTS ON PUBLIC DATA: no place that the hidden data reads is a pad's
(`padsAtZ`) · the listed seats have the index masks' seat at its number · the list's bound
(`planBelowB`).

Limits. Nothing on soundness. The three tests are shown met here by nobody.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.RidersFitAt
import Johnson.P5J.BookPremAt
import Johnson.P5J.ReadsDigitsAt
import Johnson.Desc.Kinds.Law.WtK6Reads
import Johnson.Top.H0.K2Caller.CarryAnyW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace P5J
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.Sound (ReadsOkAtQR mgBase frameAt allOf)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.K13.Law (planBelowB)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (wtK6_reads)
open VerifiableInference.Desc.First.K2Caller (carryAtZ_reads)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {L : Laid}

/-- **All six fields.** -/
theorem AtMgA.readsOwed (h : AtMgA o Z D r Zp Np cF x)
    (FF : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps)
    (hp : OffPad.padsAtZ Zp = true)
    (hseat : L.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index)
    (hbelow : planBelowB L At.ps.length (At.told cF) = true) :
    ReadsOwed h
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      h.toAtMg.rch (msgsOfChain Zp.made.proof.1) L where
  hid := h.hidReads hp (digits_reads_at h)
  book := h.bookPrem FF hseat hbelow
  wtForms := fun m j a y w w' hc hw => wtK6_reads _ _ _ _ _ _ _ _ _ At.links m j a y w w' hc hw
  carry := fun m a y w w' hc hw => carryAtZ_reads _ _ m a y w w' hc hw
  worth := fun i => worth_reads_at h mgBase (fun _ _ _ _ _ _ _ hw => hw) At.ps _ _ i
  fit := h.fit

/-- **At every border of the first chain.** -/
theorem AtMgA.readsOk (h : AtMgA o Z D r Zp Np cF x)
    (FF : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L) At.reqW At.links At.ps)
    (hp : OffPad.padsAtZ Zp = true)
    (hseat : L.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index)
    (hbelow : planBelowB L At.ps.length (At.told cF) = true) (i : ℕ) (hi : i ≤ At.ps.length) :
    ReadsOkAtQR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      h.𝔇.arr h.𝔇.N (mgAtAll h) At.links At.ps (fun a => a) h.toAtMg.rch i :=
  h.readsOk_at
    (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
    h.toAtMg.rch (h.readsOwed FF hp hseat hbelow) i hi

/-- **In the form in which a kind's condition asks it.** -/
theorem AtMgA.reads_at_place (h : AtMgA o Z D r Zp Np cF x) {M : List OnBytes.OracleShape}
    (O : ReadsOwed h
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0) h.toAtMg.rch M L) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a →
      ReadsOkAtQR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch i :=
  fun i _ ha => h.readsOk_at
    (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
    h.toAtMg.rch O i (Nat.le_of_lt (List.getElem?_eq_some_iff.1 ha).1)

theorem AtMgA.reads_at_kind (h : AtMgA o Z D r Zp Np cF x) {M : List OnBytes.OracleShape}
    (O : ReadsOwed h
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0) h.toAtMg.rch M L) (kd : KindName) :
    ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = kd →
      ReadsOkAtQR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) h.toAtMg.rch i :=
  fun i a ha _ => h.reads_at_place O i a ha

end P5J

#print axioms P5J.AtMgA.readsOwed
#print axioms P5J.AtMgA.readsOk
#print axioms P5J.AtMgA.reads_at_place
#print axioms P5J.AtMgA.reads_at_kind
