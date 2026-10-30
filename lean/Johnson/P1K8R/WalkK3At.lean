-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/WalkK3At.lean: THE LOOKUPS' ADDRESSES, SHARPER: THE
CALLING KINDS' READERS OF THE PLANES' MATRIX ARE ASKED AT THE LINK IN HAND ALONE: so at the 24 links
in front of the output head's NOTHING IS ASKED OF THE HEAD's CALLER.
  theStated_cut        K3.theStated reads its letter «readers» at the address's own link alone: cutting that letter to this link turns nothing.
  theStated_blind_at   theStated_blind (Johnson/Desc/First/Batch/Law/BlindRunsK3.lean) with its premise hr cut to the address's link: by that theorem itself, at the cut letter.
  k3Readers_blind_at   at a link that is not the head's: the lot's own readers (K3Lot.readersAt) are blind: NO PREMISE (attention: readersOfO_blind, Johnson/Desc/First/Batch/Law/BlindRunsK5.lean; layers: there is none).
  k3_states_blind_at   WalkK3.lean's k3_states_blind with hr at link l alone.
  readers_const_front  **ReadersAtConst.lean's readers_const WITHOUT hrH**: l < 24 · in scope · an opening's letters at Zp · headLink (X Zp) = 24 · hcall ⟹ MgOwes.readers' clause at 𝔇All.
LIMITS. At OnBytes.secondHashFunction alone. hcall is shown nowhere here. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.ReadersAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Place Claim)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated linksFull)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (TlBlind RunBlind ClaimsBlind theStated_blind readersOfO_blind)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.OnPublicFiles (headLink)
open ProofFile (Cl)
open P5J.At

theorem theStated_cut (claim : Aff → Claim)
    (readers : ℕ → Option (VerifiableInference.Desc.K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) :
    VerifiableInference.Desc.K3.theStated claim
        (fun i => if a.link = some i then readers i else none) X codes shape a =
      VerifiableInference.Desc.K3.theStated claim readers X codes shape a := by
  unfold VerifiableInference.Desc.K3.theStated
  cases h : a.link with
  | none => rfl
  | some i => simp

theorem theStated_blind_at (claim : Aff → Claim)
    (readers : ℕ → Option (VerifiableInference.Desc.K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (hr : ∀ i r, a.link = some i → readers i = some r → TlBlind r) {b : Block S Claim}
    (h : VerifiableInference.Desc.K3.theStated claim readers X codes shape a = some b) :
    ClaimsBlind b := by
  rw [← theStated_cut] at h
  refine theStated_blind claim _ (fun i r hi => ?_) X codes shape a h
  by_cases e : a.link = some i
  · rw [if_pos e] at hi
    exact hr i r e hi
  · rw [if_neg e] at hi
    exact nomatch hi

theorem k3Readers_blind_at (X : Verify.Public) (l : ℕ)
    (hh : VerifiableInference.Desc.K3.isHead X l = false) :
    ∀ r, K3Lot.readersAt X l = some r → TlBlind r := by
  intro r h
  unfold K3Lot.readersAt at h
  dsimp only at h
  generalize (if X.p4 = true then 2 else 1) = step at h
  rw [hh] at h
  rw [if_neg Bool.false_ne_true] at h
  by_cases h2 : (l % step == 0) = true
  · rw [if_pos h2] at h
    exact nomatch h
  · rw [if_neg h2] at h
    obtain ⟨A, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact readersOfO_blind A

theorem k3_states_blind_at {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hr : ∀ r, K3Lot.readersAt Bs.G₀.W l = some r → TlBlind r) (digits : Bool) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∀ ρ ∈ statesOfLink Lk (IM.k3Ix l digits), RunBlind (ρ.2 0) := by
  obtain ⟨Lk, b, b', e1, e2, e3, ha⟩ := IM.k3_of hS hR O l hl digits
  refine ⟨Lk, e1, states_blind e2 (claimsBlind_alone ha
    (theStated_blind_at _ _ _ _ _ _ (fun i r hi h => ?_) e3) (theStated_leaves _ _ _ _ _ _ e3))⟩
  obtain rfl : l = i := Option.some.inj hi
  exact hr r h

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

theorem readers_const_front {P : VerifierAndGoals.PublicFiles} {pp' : Inst.Model.ScalesAndPolicy} {lay' : ByteArray}
    {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp')
    (O : IM.Open OnBytes.secondHashFunction P.pol lay' P.KL F Zp Bs base c A B)
    (hH : headLink (X Zp) = 24) (hW : Bs.G₀.W = X Zp) {l : ℕ} (hl : l < 24)
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
      (k3_states_blind_at hS hR O l (Nat.lt_succ_of_lt hl)
        (k3Readers_blind_at _ l (by
          rw [hW]
          show (l == headLink (X Zp)) = false
          rw [hH]
          exact beq_false_of_ne (Nat.ne_of_lt hl))) false) hcall)

end

end P1K8T

#print axioms P1K8T.theStated_blind_at
#print axioms P1K8T.k3_states_blind_at
#print axioms P1K8T.readers_const_front
