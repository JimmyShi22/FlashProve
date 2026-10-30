-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadersAtConst.lean: THE FIELD «readers» OF MgOwes AT THE CLOSED CONSTANT's LETTERS
(P5J.At.𝔇All, Johnson/P5J/LettersAll.lean), AT THE 24 LINKS IN FRONT OF THE OUTPUT HEAD's AND AT THE
HEAD's, FROM WHAT IS STILL OWED AT THE CALLING KINDS' ADDRESSES. A joining.
  open_linkAt       at an opening's letters (IM.Open): ProofFile.linkAt Z m = c.links[m]?: by ProofFile's own linkAt_of | chainOfSeat_older (Johnson/Desc/ProofFile/Law/LinkAtLaw.lean).
  readers_const     l < 24 · in scope · an opening's letters at the constant's own public part Zp · headLink (X Zp) = 24 · the head's callers' readers are blind (hrH: k3Readers_blind's premise) · what the calling kind's sub-protocol at link l states is RunBlind (hcall) ⟹ MgOwes.readers' clause at 𝔇All.
  readers_const_head  the like at l = 24, with the blindness of the second hole's reader as one premise more (hsil; on it: k6Silent_blind, Johnson/Desc/Kinds/Law/K6TlBlind.lean).
LIMITS. At OnBytes.secondHashFunction alone. hrH · hcall · hsil are shown nowhere here. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.OwesAtConst
import Johnson.P1K8R.ReadersJoin
import Johnson.Desc.ProofFile.Law.LinkAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated linksFull)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (TlBlind RunBlind)
open VerifiableInference.Desc.K9 (statesOfLink holesAt)
open VerifiableInference.OnPublicFiles (headLink)
open ProofFile (Cl)
open P5J.At

/-- At an opening's letters ProofFile's link number m is the seated chain's. -/
theorem open_linkAt {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) (m : ℕ) :
    ProofFile.linkAt Z m = c.links[m]? := by
  refine ProofFile.Law.linkAt_of Z c ?_ m
  show ProofFile.chainOfSeat Z (ProofFile.pureSeat ProofFile.emptySecondHashFunction Z) = .ok c
  rw [ProofFile.Law.chainOfSeat_older Z ProofFile.emptySecondHashFunction o]
  unfold ProofFile.chainOfSeat ProofFile.partsOf
  rw [O.made]
  show ((ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).base.bind fun base =>
    ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road) = .ok c
  rw [O.places]
  exact O.chain

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

theorem readers_const {P : VerifierAndGoals.PublicFiles} {pp' : Inst.Model.ScalesAndPolicy} {lay' : ByteArray}
    {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp')
    (O : IM.Open OnBytes.secondHashFunction P.pol lay' P.KL F Zp Bs base c A B)
    (hH : headLink (X Zp) = 24)
    (hrH : ∀ iU3, TlBlind (VerifiableInference.Desc.Kinds.Head.callerReaders
      (VerifiableInference.Desc.Kinds.Head.planesAt iU3)))
    {l : ℕ} (hl : l < 24)
    (hcall : ∃ Lk, c.links[l]? = some Lk ∧
      ∀ ρ ∈ statesOfLink Lk (IM.k3Ix l false + 1), RunBlind (ρ.2 0)) :
    ∀ k r, k < pcOf l → ∀ p ∈ (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).runs l k r,
      TlBlind (((𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).Rd l).forms p.1 p.2) :=
  mg_readers (Nat.le_of_lt hl) (const_links o Zp Np cF E hs lay hL hN hG x wt cr1 nR)
    (by
      rw [hH]
      exact beq_false_of_ne (Nat.ne_of_lt hl))
    (states_of_two (Nat.le_of_lt hl) (const_links o Zp Np cF E hs lay hL hN hG x wt cr1 nR) c
      (fun m => open_linkAt O m)
      (k3_states_blind hS hR O (k3Readers_blind _ hrH) l (Nat.lt_succ_of_lt hl) false) hcall)

theorem readers_const_head {P : VerifierAndGoals.PublicFiles} {pp' : Inst.Model.ScalesAndPolicy} {lay' : ByteArray}
    {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp')
    (O : IM.Open OnBytes.secondHashFunction P.pol lay' P.KL F Zp Bs base c A B)
    (hrH : ∀ iU3, TlBlind (VerifiableInference.Desc.Kinds.Head.callerReaders
      (VerifiableInference.Desc.Kinds.Head.planesAt iU3)))
    (hcall : ∃ Lk, c.links[24]? = some Lk ∧
      ∀ ρ ∈ statesOfLink Lk (IM.k3Ix 24 false + 1), RunBlind (ρ.2 0))
    (hsil : ∀ l' b name, c.links[24]? = some l' →
      TlBlind ((holesAt (X Zp) (headLink (X Zp)) 24 l').silent b name)) :
    ∀ k r, k < pcOf 24 → ∀ p ∈ (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).runs 24 k r,
      TlBlind (((𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).Rd 24).forms p.1 p.2) :=
  mg_readers_head (Nat.le_refl 24) (const_links o Zp Np cF E hs lay hL hN hG x wt cr1 nR)
    fun k r hk p hp l' hl' =>
      ⟨fun ρ hρ hn => states_of_two (Nat.le_refl 24)
          (const_links o Zp Np cF E hs lay hL hN hG x wt cr1 nR) c (fun m => open_linkAt O m)
          (k3_states_blind hS hR O (k3Readers_blind _ hrH) 24 (by decide) false) hcall
          k r hk p hp l' hl' ρ hρ hn,
        hsil l' p.1 p.2 ((open_linkAt O 24).symm.trans hl')⟩

end

end P1K8T

#print axioms P1K8T.open_linkAt
#print axioms P1K8T.readers_const
#print axioms P1K8T.readers_const_head
