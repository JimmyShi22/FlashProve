-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5PickAll.lean: kind K5: THE PICK: THE LETTERS THAT THE PAYER OF THE KIND's LAW PICKS (K5Pick, K5LeftAt.lean: 28 fields of data), AT THE COMPOSED MEANING's CLOSED CONSTANT, AND K5Owes AT THAT PICK FROM WHAT IS LEFT.

Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)

Main names:
  `k5PickAll h g a x₁ xd Lk blk B hS kr`: the pick. NINETEEN LETTERS ARE TERMS at the head h and the group g (Zof := zofAll h g among them); NINE ARE ARGUMENTS: a · x₁ · xd · Lk · blk (each fixed by an equation: what an option returns: K5RestOpen.lean shows that
    a · x₁ · Lk · blk are there at g < 12) · B · hS · kr (the piece's and the plan's rows).
  `owes_at_pick`: **K5Owes at the pick**, in the letters of K5LeftAt's field owes, from K5Table's four, K5RestLeftAll's nine, PadsAll h and ∃ idx, K5CellsCond h a x₁ idx.
Is it empty here? A definition; and an implication from K5RestLeftAll · PadsAll · K5CellsCond, WHICH ARE SHOWN AT NOTHING.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5LeftAt
import Johnson.Desc.First.Att.Door.Law.K5RestLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open OnBytes.Road.L5 (Zs)
open P5J (AtMgA mgAtAll TS)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The pick at the closed constant.** -/
noncomputable def k5PickAll {Fr : Frame} (g : ℕ) (a : Attention.Plan) (x₁ xd : Look.Place) (Lk : Link S Claim) (blk B : Block S Claim)
    (hS : Forest.Shape) (kr : ℕ) :
    K5Pick ProofFile.InstPub (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok OnBytes.Flat.numsFull.rows Fr h.𝔇.sent where
  Ix := IdxQ
  in0 := mgB0.inOrder
  c5 := fun p => (_root_.Meaning.backReq (h.𝔇.reqB p)).isSome
  D13 := d13 h.𝔇
  before := beforeAll Zp g
  a := a
  x := x₁
  xd := xd
  rad := h.𝔇.l3.rad
  uL := h.𝔇.uL
  uH := h.𝔇.uH
  wt := h.𝔇.wt
  seat := seatAll h x₁
  smpR := smpRAll h x₁
  lk := P5J.At.lk Zp
  Lk := Lk
  same := ProofFile.sameReply
  blk := blk
  claimC := K3Lot.ofForm
  nm := "planes"
  Hd := VerifiableInference.OnPublicFiles.Flat.Holds
  bsW := h.𝔇.H.base
  dP := h.𝔇.digitsPart
  body := bodyAll h.𝔇
  Zof := zofAll h g
  hS := hS
  kr := kr
  B := B

/-- **K5Owes at the pick, from K5Table's four, the nine and the three conditions of the field cells.** -/
theorem owes_at_pick {Fr : Frame} {Ld : Laid} {Ms : List OracleShape} {bs g : ℕ} {a : Attention.Plan} {x₁ xd : Look.Place}
    {pl : VerifiableInference.Desc.Place} {O : List Item} {Q : List Pub} {Lk : Link S Claim} {blk B : Block S Claim} {hS : Forest.Shape} {kr : ℕ}
    (hg : g < 12) (ha : (P5J.At.X Zp).A[g]? = some a)
    (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) (hLk : P5J.At.lk Zp (2 * g + 1) = some Lk)
    (hb : k5AtN (P5J.At.X Zp) (2 * g + 1) g (beforeAll Zp g) = some blk) (T : K5Table g LFullK pl O Q)
    (hO : PadsAll h) (C : ∃ idx, K5CellsCond h a x₁ idx) (U : K5RestLeftAll h Ld Ms bs g a x₁ pl O) :
    K5Owes (Fr := Fr) (mgPlus (mgAtAll h) mgB0.more h.𝔇.pubD Ld Ms mgB0.pub h.𝔇.sent.codes) mgB0 h.𝔇.pubD h.𝔇.sent h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).in0 Ld Ms (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).D13 bs (P5J.At.X Zp) g
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).before (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).a
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).x LFullK pl (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).rad O Q
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).seat (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).smpR
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).lk (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).Lk
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).same (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).blk
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).claimC (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).nm
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).Hd (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).bsW
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).dP (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).body
      (k5PickAll (Fr := Fr) h g a x₁ xd Lk blk B hS kr).Zof :=
  { toK5Table := T
    toK5Rest := rest_of_left (Fr := Fr) h hg ha hx hLk hb T.openQ hO C U }

end

end H2K5.Door

#print axioms H2K5.Door.k5PickAll
#print axioms H2K5.Door.owes_at_pick
