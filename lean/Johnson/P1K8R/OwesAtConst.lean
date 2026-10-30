-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/OwesAtConst.lean: FOUR OF THE PREMISES OF drawBlind_mg (BlindAtMg.lean) AT THE CLOSED
CONSTANT's STRUCTURE OF LETTERS (P5J.At.𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR,
Johnson/P5J/LettersAll.lean: there wt and cr1 are
arguments).
  const_decT    the one decoder has one value in front of the draw's yes and behind it: it does not read the first chain's state at all (P5J.At.noRec_decT, Johnson/P5J/LettersAt.lean).
  const_req     so has what the reading of a witness takes for the request: it reads the public part alone.
  const_links   the constant's list of the segments' sorts is the written list at which K8's ties stand.
  const_head    the output head's part of the model's relation goes back over the draw: ONE CALL of headPartK6_goesBack (Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean) at the relation "one public part, and the draw's yes between the two states"; its two premises: the request's reader (const_req's like) and the reader of the heard reply (tokHOf_blind: it reads the chain's results, which the draw leaves).
  mgOwes_const  MgOwes at the constant FROM THE FOUR FIELDS THAT ARE LEFT: smp · wt (an argument of the constant) · readers · fence.
LIMITS. Four of ten premises. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.BlindAtMg
import Johnson.P5J.LettersAll
import Johnson.Desc.Kinds.Law.HeadPartsGoBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated linksFull)
open VerifiableInference.Desc.First.K8 (TlBlind Drawn SameBelow blind_out)
open P5J.At

section
variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
  {pp : Inst.Model.ScalesAndPolicy}
  (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt
    (OnBytes.Slice.frS.toDecR OnBytes.Slice.frZ 402653181) OnBytes.Flat.numsFull pp))
  (hs : Desc.K14.Law.fullShapeB
    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true)
  (lay : ByteArray)
  (hL : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
  (hN : SeatsNamed (arr Zp) (N Zp cF) (Meaning.sizesOf (X Zp))
    (Meaning.seatBy (Meaning.fLay (layout Zp) (num Zp)) (X Zp) (Meaning.sizesOf (X Zp))))
  (hG : GroupsSeated (ms Zp lay) (N Zp cF))
  (x : VerifiableInference.Desc.First.Look.Place)
  (wt cr1 : ℕ → ProofFile.InstPub × P5J.TS → VerifiableInference.Desc.Strs →
    VerifiableInference.Desc.Wit (VerifiableInference.Desc.Sound.CellsQ OnBytes.Flat.numsFull.rows
      (P5J.colsAt OnBytes.Flat.numsFull)) Tok VerifiableInference.Desc.Sound.MsgT → Prop)
  (nR : ℕ)

/-- The one decoder has one value in front of the draw's yes and behind it. -/
theorem const_decT : ∀ c z,
    TlBlind fun s => (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).decT c (z, s) :=
  fun _ _ _ _ _ => rfl

/-- What the reading of a witness takes for the request reads the public part alone. -/
theorem const_req : ∀ z,
    TlBlind fun s => (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).H.req (z, s) :=
  fun _ _ _ _ => rfl

/-- The constant's list of the segments' sorts is the written list. -/
theorem const_links : (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).links = linksFull := by
  show P5J.fullLinks = linksFull
  decide

/-- The heard reply's token has one value in front of the draw's yes and behind it. -/
theorem tokHOf_blind {P : Type} (z : P) : TlBlind fun s => P5J.tokHOf (z, s) := fun s t h => by
  show P5J.tokVOf ((t.replyTok?).getD 0) = P5J.tokVOf ((s.replyTok?).getD 0)
  unfold VerifiableInference.Desc.First.S.replyTok?
  rw [blind_out s t h]

/-- The output head's part goes back over the draw: by headPartK6_goesBack. -/
theorem const_head (base : ℕ) : ∀ p i z s t y y' w, Drawn s t → SameBelow base y y' →
    (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).headPart p i (z, t) y' w →
    (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).headPart p i (z, s) y w := by
  intro p i z s t y y' w h _ hp
  exact VerifiableInference.Desc.Kinds.Head.Law.headPartK6_goesBack _ _ _ _ _ _ _ _ _ _ _ _
    (fun a _ b _ => a.1 = b.1 ∧ Drawn a.2 b.2)
    (fun a _ b _ hr => by
      show (Meaning.backReq (reqB a.1)).getD d₀ = (Meaning.backReq (reqB b.1)).getD d₀
      rw [hr.1])
    p
    (fun _ a _ b _ hr => by
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      obtain ⟨e, hd⟩ := hr
      exact (tokHOf_blind b1 a2 b2 hd).symm)
    i (z, s) y (z, t) y' w ⟨rfl, h⟩ hp

/-- **WHAT IS LEFT OF MgOwes AT THE CONSTANT**: four of its seven fields: the reader of OOD samples,
the sentence "weights" (an argument of the constant), the earlier runs' readers, the fence. -/
theorem mgOwes_const (l base : ℕ)
    (hsmp : ∀ z, TlBlind fun s => (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).smp (z, s))
    (hwt : ∀ z s t y y' w, Drawn s t → SameBelow base y y' → wt l (z, t) y' w → wt l (z, s) y w)
    (hrd : ∀ k r, k < pcOf l → ∀ p ∈ (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).runs l k r,
      TlBlind (((𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).Rd l).forms p.1 p.2))
    (hf : ∀ y ∈ VerifiableInference.Desc.First.sampledIn
      (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).N
      ((VerifiableInference.Desc.First.openSets linksFull
        (VerifiableInference.Desc.First.flatPlacesOf linksFull true)
        (VerifiableInference.Desc.First.start linksFull))[ixOf l]?.getD []), y.1 < base) :
    MgOwes (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR) l base where
  decT := const_decT o Zp Np cF E hs lay hL hN hG x wt cr1 nR
  smp := hsmp
  req := const_req o Zp Np cF E hs lay hL hN hG x wt cr1 nR
  head := const_head o Zp Np cF E hs lay hL hN hG x wt cr1 nR base
  wt := hwt
  readers := hrd
  fence := hf

end

end P1K8T

#print axioms P1K8T.const_decT
#print axioms P1K8T.const_req
#print axioms P1K8T.const_links
#print axioms P1K8T.const_head
#print axioms P1K8T.mgOwes_const
