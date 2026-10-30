-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION AT
THE CLOSED CONSTANT, IN ONE THEOREM: `k03_cond_due`: `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean) from the head, "the pieces are the
pieces of the description's own three lists" and:
  FOUR TESTS WITH CODE: the door's two rows (digRow, headRow) · fenceFit · padsAtZ;
  AT THE FOLD AND THE 24 CALLS' PLACES: `K3ShortR` (fold · per place: tie, one, own · othersPub,
    othersP, rides) and `ObjShortR` (what objects leaves);
  AT THE 25 DIGITS' PLACES: `DigShortR`;
  AT THE HEAD's CALLS: `HeadShortR` (parts, model, rides) · `ObjShortR` · hHead.
Two calls: `k03_cond_short` (Johnson/P5J/K03LeftAt.lean), `k03_head_at`
(Johnson/P5J/K03HeadAt.lean).

Limits: all of these are premises; no member is known. hHead is asked at all strings: whether the
constant's `headPartK6` has it is not shown.
(Where this and lean/THEOREM.md differ, the page
holds.)
At secondHashFunction alone. Nothing on soundness by itself;
nothing on hiding.


-/
import Johnson.P5J.K03LeftAt
import Johnson.P5J.K03HeadAt

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
open VerifiableInference.Desc.First.Look (attAt layAt digAt)
open VerifiableInference.Desc.Kinds.Head.Law (OffPad.padsAtZ)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- **WHAT IS STILL DUE.** -/
theorem k03_cond_due (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (idx : ℕ → ℕ → ℕ) (arrs : Array (Nat × String))
    (z₀ : ProofFile.InstPub)
    (hDig : VerifiableInference.Desc.K3Asks.digRow (At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true)
    (hRow : VerifiableInference.Desc.K3Asks.headRow (At.X Zp) = true)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) = true)
    (hp : OffPad.padsAtZ Zp = true)
    (nos : ℕ → Array ℕ) (n : ℕ → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (M : List OracleShape)
    (S : ∀ l < 25, ∀ y tl, digAt (At.X Zp) l = some (y, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l y q b' (nos l) (n l) Ld M)
    (Oa : ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        ObjShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q
          b' Ld M)
    (Ol : ∀ l < 25, ∀ y, layAt (At.X Zp) l = some y →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
        ObjShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y q
          b' Ld M)
    (hHead : ∀ (z : ProofFile.InstPub) (s s' : VerifiableInference.Desc.First.S) i y y' w, SameBut s s' →
      (h.toAtMg.𝔇 h.𝔇).headPart .small i (z, s') y' w →
      (h.toAtMg.𝔇 h.𝔇).headPart .small i (z, s) y w)
    (Oh : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        ObjShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K 24 false) 24 x
          q b' Ld M)
    (Hs : ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        HeadShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (At.seats Zp) s₀ x
          q b' arrs (IM.k3Place 24 false) (MgAt.nextOf 24 false) (At.told cF))
    (V : K3ShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes Zp.first.shape
      (h.toAtMg.row 𝔏) (At.num Zp) idx (_root_.Meaning.tlAt (At.X Zp))) :
    h.K3Cond 𝔏 :=
  k03_cond_short h 𝔏 q₁ q₂ q₃ s₀ idx arrs z₀ hDig hRow hg hp nos n Ld M S Oa Ol
    (k03_head_at h 𝔏 q₁ q₂ q₃ s₀ arrs hg Ld M hHead Oh Hs) V

end P5J

#print axioms P5J.k03_cond_due
