-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LettersAll.lean: THE STRUCTURE OF THE COMPOSED MEANING's LETTERS (MgData: 29 fields) WITH 27 FIELDS LAID AT TERMS AND TWO HANDED IN. One definition, six theorems. H's seat is in the label's form: one term with headPart's seatLay, by its definition. wt AND cr1 ARE ARGUMENTS: neither has a closed term here. headPart | digitsPart are written out at this structure's own fields. A joint build of many files.
  At.𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR : MgData …: A STRUCTURE WRITTEN OUT, A FIELD A LINE, EACH FROM ONE DEFINITION:
    ours (Johnson/P5J/LettersAt.lean | LettersAt2.lean): links · cs · N · G · arr · smp · ms · decT · put · H · reqB · shape · layout · lk · rw · P13 · built (the public part's built links)
    the terms of other parts of the library (Johnson/P5J/LettersAt3*.lean): d1 · mat13 · digitsPart · rq · headPart · uA · uH · uL
    THE TWO FIELDS WITHOUT A TERM: wt (the sentence "weights" at the output head) · cr1 (the sentence "carry"): TWO ARGUMENTS.
    the lookups' two (Johnson/P5J/Rad3Seat3At.lean): rad3 · seat3
  HANDED IN UNDER A NAMED CONDITION THAT THE HEAD CARRIES (NO DEFAULT THAT ANSWERS IN SILENCE): x (the output head's lookup's place: headAt (X Zp) = some x). nR: the structure's index (the number of rows of the last sub-protocols' matrix): laid by nobody.
  𝔇All_fix_five | _head | _arm | _headArm | _lay: laying any of the five other layings over it changes nothing (rfl, a theorem a laying): each line IS that laying's term · 𝔇All_fix: laying the sixteen closed fields of 𝔇At over it changes nothing (rfl): SO EVERY THEOREM STATED AT "𝔇At … 𝔇₀ FOR ALL 𝔇₀" SPEAKS OF IT.
Limits. A definition. SILENT DEFAULTS INSIDE THE FIELDS' TERMS ARE NOT FENCED HERE: the page of named tests lists them (ncl's 0 · the attention arm's 0 · rad3's 0 | seat3's (0, 0) · rad's 0 · the positions' 0 · the feed-forward arm's two, of which one is names3's empty list). NO EXAMPLE shows that any of these sentences can be met. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LettersRec3
import Johnson.P5J.LettersAt3Head
import Johnson.P5J.LettersAt3Arm
import Johnson.P5J.LettersAt3HeadArm
import Johnson.P5J.LettersAt3Lay
import Johnson.P5J.Rad3Seat3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MgData SeatsNamed GroupsSeated)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) {pp : Inst.Model.ScalesAndPolicy}
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181)
    OnBytes.Flat.numsFull pp))
  (hs : Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
  (lay : ByteArray)
  (hL : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
  (hN : SeatsNamed (arr Zp) (N Zp cF) (Meaning.sizesOf (X Zp))
    (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))))
  (hG : GroupsSeated (ms Zp lay) (N Zp cF))
  (x : VerifiableInference.Desc.First.Look.Place)
  (wt cr1 : ℕ → ProofFile.InstPub × TS → VerifiableInference.Desc.Strs →
    VerifiableInference.Desc.Wit (VerifiableInference.Desc.Sound.CellsQ OnBytes.Flat.numsFull.rows
      (colsAt OnBytes.Flat.numsFull)) Tok VerifiableInference.Desc.Sound.MsgT → Prop)

/-- **THE STRUCTURE OF LETTERS, WRITTEN OUT.** -/
noncomputable def 𝔇All (nR : ℕ) :
    MgData ProofFile.Inst ProofFile.InstPub Tok OnBytes.Flat.numsFull.rows (colsAt OnBytes.Flat.numsFull) nR (X Zp) where
  d1 := d1 Zp
  links := links
  built := Zp.made.p.built.links
  P13 := P13 Zp
  cs := cs Zp
  N := N Zp cF
  G := F0T o Zp Np cF
  arr := arr Zp
  smp := smp Zp
  ms := ms Zp lay
  decT := decT o Zp Np cF E hs
  put := put
  H := H o Zp Np cF E hs lay hL hN hG
  headPart := VerifiableInference.Desc.Kinds.Head.Law.headPartK6 (cs Zp) (arr Zp) (ms Zp lay) (N Zp cF)
    (Meaning.sizesOf (X Zp)) (VerifiableInference.Desc.Kinds.Head.Law.seatLay (X Zp) (layout Zp) (num Zp)) (X Zp)
    (VerifiableInference.Desc.Kinds.Head.Law.plAt (num Zp 24 0) 0) (tabH x) put
    (VerifiableInference.Desc.Sound.oneDec (decT o Zp Np cF E hs) (H o Zp Np cF E hs lay hL hN hG)) tokHOf
  digitsPart := VerifiableInference.OnPublicFiles.digitsPartK3 (X Zp)
    ⟨cs Zp, shape Zp, layout Zp, Zp.made.p.built.links.map (·.arrayOf)⟩
    (VerifiableInference.OnPublicFiles.k3StoredAt (rad3At Zp lay) (arr Zp) (seat3At Zp))
  reqB := reqB
  shape := shape Zp
  layout := layout Zp
  lk := lk Zp
  uL := uL Zp
  uA := uA Zp
  uH := uH Zp
  wt := wt
  rw := rw Zp
  mat13 := mat13 Zp nR
  rad3 := rad3At Zp lay
  seat3 := seat3At Zp
  rq := rq Zp
  cr1 := cr1

/-- **Each of the other files' layings, laid over it, changes nothing**: so each of these lines IS that laying's own term at this structure's own fields. Five theorems, a laying each. -/
theorem 𝔇All_fix_five (nR : ℕ) : 𝔇At3 Zp (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) = 𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR := rfl

theorem 𝔇All_fix_head (nR : ℕ) : 𝔇AtHead Zp x (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) = 𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR := rfl

theorem 𝔇All_fix_arm (nR : ℕ) : 𝔇AtArm Zp (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) = 𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR := rfl

theorem 𝔇All_fix_headArm (nR : ℕ) : 𝔇AtHeadArm Zp (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) = 𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR := rfl

theorem 𝔇All_fix_lay (nR : ℕ) : 𝔇AtLay Zp (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) = 𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR := rfl

/-- **Laying 𝔇At's closed fields over it changes nothing.** -/
theorem 𝔇All_fix (nR : ℕ) :
    𝔇At o Zp Np cF E hs lay hL hN hG (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) =
      𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR := rfl

end P5J.At

#print axioms P5J.At.𝔇All_fix
#print axioms P5J.At.𝔇All_fix_five
#print axioms P5J.At.𝔇All_fix_head
#print axioms P5J.At.𝔇All_fix_arm
#print axioms P5J.At.𝔇All_fix_headArm
#print axioms P5J.At.𝔇All_fix_lay
