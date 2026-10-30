-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due2.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION
AT THE CLOSED CONSTANT, SECOND COUNT: `k03_cond_due2` : `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), by one call of `k03_cond_due`
(Johnson/P5J/K03Due.lean, which does not turn). FROM the head, q₁ q₂ q₃ and:
  ONE CONDITION ON EVERY REACHED STATE: F : `First.FoldFacts` at "reached" := `h.toAtMg.rch` and at
    `At.foldD Zp cF L` (the field fold of the head `AtMgR`: no new condition);
  SEVEN TESTS WITH CODE: digRow · headRow · fenceFit · padsAtZ · oneC l, namedC l (l < 24) · offC;
  AT THE 24 CALLS' PLACES: `CallsLastR` (tie · othersPub · othersP · rides);
  AT THE 25 CALLS' PLACES: `ObjLastR` (hB · hTests · h6 · hBare);
  AT THE 25 DIGITS' PLACES: `DigLastR` (othersPub · othersP · rides · hB · hTests · h6);
  AT THE HEAD's CALLS: `HeadShortR` (parts · model · rides).

PAID HERE BEYOND `k03_cond_due`: fold and the eleven facts along the fold at all fifty places
(Johnson/P5J/K03FoldAt.lean) · one, own at every element (Johnson/P5J/K03OneOwnAt.lean) · pubSent,
pubFree, hnS at all fifty (Johnson/P5J/K03PubAt.lean, K03PubHeadAt.lean) · hHead
(Johnson/P5J/K03HeadSmallAt.lean). THE LETTERS ARE CLOSED: idx l :=
`idxAt (At.sentAt Zp) (At.num Zp) l` · Ld := L · M := `msgsOfChain Zp.made.proof.1` · nos l :=
`(At.foldD Zp cF L).ownAt l 3` · n l := the number of slots of the segment's digits' place.

Limits: all of the above are premises; no member is known. At secondHashFunction alone. Nothing on soundness by
itself; nothing on hiding.


-/
import Johnson.P5J.K03Last
import Johnson.P5J.K03HeadSmallAt
import Johnson.P5J.K03FoldAt
import Johnson.P5J.K03OneOwnAt
import Johnson.P5J.K03PubHeadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (attAt layAt digAt lookAt tlAt idxAt)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ)
open VerifiableInference.Desc.K12.Door (msgsOfChain)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- The digits' reader's place is the table's own. -/
theorem k03_look_dig {X : Verify.Public} {l : ℕ} {y : VerifiableInference.Desc.First.Look.Place}
    {tl : HTailF2} (h : digAt X l = some (y, tl)) : lookAt X l true = some y := by
  unfold VerifiableInference.Desc.First.Look.digAt at h
  obtain ⟨x', hx', h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl', -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨s, -, h⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, -⟩ := Prod.mk.inj h
  exact hx'

/-- The number of slots of a segment's digits' place (0 where the table has none). -/
def At.nsDig (Zp : ProofFile.Pub) (l : ℕ) : ℕ := ((lookAt (At.X Zp) l true).map (·.ns)).getD 0

theorem At.nsDig_at {l : ℕ} {y : VerifiableInference.Desc.First.Look.Place}
    (h : lookAt (At.X Zp) l true = some y) : At.nsDig Zp l = y.ns := by
  unfold At.nsDig
  rw [h]
  rfl

set_option maxHeartbeats 4000000 in
/-- **WHAT IS STILL DUE, SECOND COUNT.** -/
theorem k03_cond_due2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (arrs : Array (Nat × String)) (z₀ : ProofFile.InstPub)
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (F : VerifiableInference.Desc.First.FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF L)
      At.reqW At.links At.ps)
    (hDig : VerifiableInference.Desc.K3Asks.digRow (At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true)
    (hRow : VerifiableInference.Desc.K3Asks.headRow (At.X Zp) = true)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) = true)
    (hp : OffPad.padsAtZ Zp = true)
    (hOne : ∀ l < 24, h.oneC l = true) (hNamed : ∀ l < 24, h.namedC l = true)
    (hOff : h.toAtMg.offC = true)
    (Sd : ∀ l < 25, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l y q b'
          ((At.foldD Zp cF L).ownAt l 3) (At.nsDig Zp l) L (msgsOfChain Zp.made.proof.1))
    (Oa : ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        ObjLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q
          b' L (msgsOfChain Zp.made.proof.1))
    (Ol : ∀ l < 25, ∀ y, layAt (At.X Zp) l = some y →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        ObjLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q
          b' L (msgsOfChain Zp.made.proof.1))
    (Oh : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        ObjLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K 24 false) 24 x
          q b' L (msgsOfChain Zp.made.proof.1))
    (Hs : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        HeadShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (At.seats Zp) s₀ x
          q b' arrs (IM.k3Place 24 false) (MgAt.nextOf 24 false) (At.told cF))
    (Va : ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        CallsLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (At.num Zp)
          (idxAt (At.sentAt Zp) (At.num Zp) l) (IM.k3Place l false) (k3K l false) l y tl q b')
    (Vl : ∀ l < 25, ∀ y tl, layAt (At.X Zp) l = some y → tlAt (At.X Zp) l = some tl →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        CallsLastR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (At.num Zp)
          (idxAt (At.sentAt Zp) (At.num Zp) l) (IM.k3Place l false) (k3K l false) l y tl q b') :
    h.K3Cond 𝔏 := by
  have link : ∀ {l : ℕ} {y : VerifiableInference.Desc.First.Look.Place},
      lookAt (At.X Zp) l false = some y → y.link = l :=
    fun hy => lookAt_link hy
  refine k03_cond_due h 𝔏 q₁ q₂ q₃ s₀ (fun l => idxAt (At.sentAt Zp) (At.num Zp) l) arrs z₀ hDig
    hRow hg hp (fun l => (At.foldD Zp cF L).ownAt l 3) (At.nsDig Zp) L (msgsOfChain Zp.made.proof.1)
    ?_ ?_ ?_ (k03_hHead h) ?_ Hs ⟨k03_fold h F, ?_, ?_⟩
  · intro l hl y tl hy q hq b' hb'
    have hk := k03_look_dig hy
    refine digShort_of_last _ _ _ l y q b' _ _ _ _ (k03_hLive h F _) (k03_hGroups h F _)
      (k03_hLink_at h F hl hk) (k03_hNext h F hl) (k03_hOwn h F hl) (k03_hSeats h F _)
      (k03_hShapes h F _) ?_ ?_ (Sd l hl y tl hy q hq b' hb')
    · rw [At.nsDig_at hk]
      exact k03_pubFree_look h hl hk
    · rw [At.nsDig_at hk]
      exact k03_hnS y
  · intro l hl y A tl hy q hq b' hb'
    have hk := k03_look_att h hl hy
    exact objShort_of_last _ _ _ _ _ _ _ _ _ _ _ (k03_hLive h F _) (k03_hGroups h F _)
      (k03_hSeats h F _) (k03_hShapes h F _) (k03_pubSent_calls h hk) (k03_pubFree_look h hl hk)
      (Oa l hl y A tl hy q hq b' hb')
  · intro l hl y hy q hq b' hb'
    have hk := k03_look_lay h hl hy
    exact objShort_of_last _ _ _ _ _ _ _ _ _ _ _ (k03_hLive h F _) (k03_hGroups h F _)
      (k03_hSeats h F _) (k03_hShapes h F _) (k03_pubSent_calls h hk) (k03_pubFree_look h hl hk)
      (Ol l hl y hy q hq b' hb')
  · intro q hq b' hb'
    exact objShort_of_last _ _ _ _ _ _ _ _ _ _ _ (k03_hLive h F _) (k03_hGroups h F _)
      (k03_hSeats h F _) (k03_hShapes h F _) (k03_pubSent_head h h.headAt)
      (k03_pubFree_head h h.headAt) (Oh q hq b' hb')
  · intro l hl y A tl hy q hq b' hb'
    have hk := link (k03_look_att h hl hy)
    have h24 : l < 24 := by have := attAt_odd hy; omega
    refine callsShort_of_last _ _ _ _ _ _ _ _ _ _ tl q b' ?_ ?_ (Va l hl y A tl hy q hq b' hb')
    · rw [hk]
      exact h.one_at hl (hOne l h24)
    · rw [hk]
      exact h.own_at hl (hNamed l h24) hOff
  · intro l hl y tl hy ht q hq b' hb'
    have hk := link (k03_look_lay h hl hy)
    have h24 : l < 24 := k03_lay_lt h hl hy
    refine callsShort_of_last _ _ _ _ _ _ _ _ _ _ tl q b' ?_ ?_ (Vl l hl y tl hy ht q hq b' hb')
    · rw [hk]
      exact h.one_at hl (hOne l h24)
    · rw [hk]
      exact h.own_at hl (hNamed l h24) hOff

end P5J

#print axioms P5J.k03_look_dig
#print axioms P5J.At.nsDig_at
#print axioms P5J.k03_cond_due2
