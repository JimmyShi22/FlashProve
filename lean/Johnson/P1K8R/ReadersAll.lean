-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadersAll.lean: THE FIELD «readers» OF MgOwes AT THE CLOSED CONSTANT's LETTERS
(P5J.At.𝔇All, Johnson/P5J/LettersAll.lean), SORT
OF SEGMENT BY SORT OF SEGMENT, WITH RESULTS ON K4 AND ON THE OUTPUT HEAD (K6) JOINED IN.
  readers_const_layers     AT THE 12 FEED-FORWARD LINKS l = 2 g (g < 12): in scope · an opening's letters at Zp · headLink (X Zp) = 24 · the ground's public data are the constant's ⟹ MgOwes.readers' clause at 𝔇All: NO OTHER PREMISE: by readers_const_front (WalkK3At.lean) and k4_states_blind (Johnson/Road/K4/K4StatesBlind.lean).
  readers_const_attention  at the 12 attention links l = 2 g + 1: the like, FROM ONE PREMISE: what K5's sub-protocol there states is RunBlind.
  readers_const_head2      at the head's link 24: ReadersAtConst.lean's readers_const_head WITHOUT hsil: the second hole's reader is paid by readersAt_blind_head (Johnson/Desc/Kinds/Law/K6TlBlind.lean); left: what K6's sub-protocol there states is RunBlind · the head's callers' readers of the planes' matrix are blind (hrH) · headLink (X Zp) = 24.
LIMITS. At OnBytes.secondHashFunction alone. No example. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.WalkK3At
import Johnson.Road.K4.K4StatesBlind
import Johnson.Desc.Kinds.Law.K6TlBlind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated linksFull runsAt)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (TlBlind RunBlind)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.OnPublicFiles (headLink)
open ProofFile (Cl)
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

variable {P : VerifierAndGoals.PublicFiles} {pp' : Inst.Model.ScalesAndPolicy} {lay' : ByteArray} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem readers_const_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp')
    (O : IM.Open OnBytes.secondHashFunction P.pol lay' P.KL F Zp Bs base c A B)
    (hH : headLink (X Zp) = 24) (hW : Bs.G₀.W = X Zp) (g : ℕ) (hg : g < 12) :
    ∀ k r, k < pcOf (2 * g) →
      ∀ p ∈ (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).runs (2 * g) k r,
      TlBlind (((𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).Rd (2 * g)).forms p.1 p.2) := by
  have h24 : 2 * g < 24 := by omega
  have e : IM.k3Ix (2 * g) false + 1 = 2 := by
    show ((if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0)) + 1 = 2
    rw [if_neg (Nat.ne_of_lt h24)]
    rfl
  refine readers_const_front o Zp Np cF E hs lay hL hN hG x wt cr1 nR hS hR O hH hW h24 ?_
  rw [e]
  exact OnBytes.Road.K4.k4_states_blind hS hR O g hg

theorem readers_const_attention (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp')
    (O : IM.Open OnBytes.secondHashFunction P.pol lay' P.KL F Zp Bs base c A B)
    (hH : headLink (X Zp) = 24) (hW : Bs.G₀.W = X Zp) (g : ℕ) (hg : g < 12)
    (h5 : ∃ Lk, c.links[2 * g + 1]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk 2, RunBlind (ρ.2 0)) :
    ∀ k r, k < pcOf (2 * g + 1) →
      ∀ p ∈ (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).runs (2 * g + 1) k r,
      TlBlind (((𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).Rd (2 * g + 1)).forms p.1 p.2) := by
  have h24 : 2 * g + 1 < 24 := by omega
  have e : IM.k3Ix (2 * g + 1) false + 1 = 2 := by
    show ((if false = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0)) + 1 = 2
    rw [if_neg (Nat.ne_of_lt h24)]
    rfl
  refine readers_const_front o Zp Np cF E hs lay hL hN hG x wt cr1 nR hS hR O hH hW h24 ?_
  rw [e]
  exact h5

theorem readers_const_head2 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp')
    (O : IM.Open OnBytes.secondHashFunction P.pol lay' P.KL F Zp Bs base c A B)
    (hH : headLink (X Zp) = 24)
    (hrH : ∀ iU3, TlBlind (VerifiableInference.Desc.Kinds.Head.callerReaders
      (VerifiableInference.Desc.Kinds.Head.planesAt iU3)))
    (h6 : ∃ Lk, c.links[24]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk 3, RunBlind (ρ.2 0)) :
    ∀ k r, k < pcOf 24 → ∀ p ∈ (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).runs 24 k r,
      TlBlind (((𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).Rd 24).forms p.1 p.2) := by
  intro k r hk p hp
  have hLk := const_links o Zp Np cF E hs lay hL hN hG x wt cr1 nR
  have hn : (p.2 == "K8.equations") = false := runs_not_ahead (Nat.le_refl 24) k r hk p (by
    have hp' : p ∈ runsAt (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).links 24 k r := hp
    rw [hLk] at hp'
    exact hp')
  have H := VerifiableInference.Desc.Kinds.Head.Law.readersAt_blind_head
    (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).lk (X Zp) 24 p.1 p.2 hn
    (fun l' hl' ρ hρ hnm => states_of_two (Nat.le_refl 24) hLk c (fun m => open_linkAt O m)
      (k3_states_blind hS hR O (k3Readers_blind _ hrH) 24 (by decide) false) h6
      k r hk p hp l' hl' ρ hρ hnm)
  show TlBlind ((VerifiableInference.Desc.K9.readersAt
    (𝔇All o Zp Np cF E hs lay hL hN hG x wt cr1 nR).lk (X Zp) (headLink (X Zp)) 24).forms p.1 p.2)
  rw [hH]
  exact H

end

end P1K8T

#print axioms P1K8T.readers_const_layers
#print axioms P1K8T.readers_const_attention
#print axioms P1K8T.readers_const_head2
