-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03RidesAt.lean: THE KIND "LOOKUP" (K3): WHAT RIDES PAST THE LOOKUP ON A SEGMENT's
CALLS, AT ALL 25 SEGMENTS, AT THE CLOSED CONSTANT: the field rides of `CallsLastR`
(Johnson/P5J/K03Last.lean) and of `HeadShortR` (Johnson/P5J/K03HeadAt.lean), by one call of
another author's `ridesAtR_calls_ledger` (Johnson/Desc/Sound/MgAt/K3RidesLedger.lean). One closed
test with code and six theorems: two by the kernel (one a negative test), the others joinings.
  `k3CallsPinIB`, `k3CallsPinI_full`, `k3CallsPinI_control`: the item "the index masks' message is
    pinned" is open at the calls' border of each of the 25 segments: by the kernel; at the chain's
    start it is not.
  `k03_pieceAt`: in the goals' scope the calls' piece of segment l, by the kind's own text, is the
    written place's.
  `k03_hHeadAll`: the output head's part, AT EVERY PART, goes back over a step that is SameBut: by
    another author's `headPart_atAll_reply` (Johnson/Desc/Kinds/Law/HeadCutsAtAll.lean).
  `k03_index_low`: the tree of the index masks' message lies below the piece's base: from
    `k03_base_at` (Johnson/P5J/K03PiecesAt.lean) and the closed test; under hg : `fenceFit … =
    true`.
  `k03_rides_calls`: the field.
Limits: joinings. The head h, the free letters' three equations and hg are premises, as in
`k03_dig_at`. `fenceFit` at the constant's numbers has been evaluated true at both full-size sets
of public files, with a tight negative test: an evaluation. That `lookAt` answers at a segment's
calls is a binder. The digits' 25 places are not touched. The full size alone. No soundness is
claimed.

-/
import Johnson.P5J.K03Terms
import Johnson.P5J.K03PiecesAt
import Johnson.P5J.K03BookAt
import Johnson.Desc.Sound.MgAt.K3RidesLedger
import Johnson.Desc.First.Look.K3RidesR
import Johnson.Desc.First.Look.K3PlaceAt
import Johnson.Desc.Kinds.Law.HeadCutsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Item openSets start sampledIn fenceFit)
open VerifiableInference.Desc.First.Look (lookAt placeAt_iff)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- The index masks' pin is open at the calls' border of every segment. -/
def k3CallsPinIB : Bool :=
  (List.range 25).all fun l =>
    ((openSets linksFull PS (start linksFull))[k3K l false]?.getD []).contains Item.pinI

set_option maxRecDepth 1000000 in
theorem k3CallsPinI_full : k3CallsPinIB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: at the chain's start it is not open. -/
theorem k3CallsPinI_control :
    ((openSets linksFull PS (start linksFull))[0]?.getD []).contains Item.pinI = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- In scope the calls' piece, by the kind's own text, is the written place's. -/
theorem k03_pieceAt (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (l : ℕ) :
    (IM.k3Place l false).piece = VerifiableInference.Desc.K3.pieceAt (At.X Zp) l false := by
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  unfold VerifiableInference.Desc.K3.pieceAt VerifiableInference.Desc.K3.isHead
  rw [p4, ng]
  by_cases e : l = 24
  · subst e
    rfl
  · simp [IM.k3Place, IM.k3Ix, e]

/-- **The head's part, at every part, goes back over a step that is SameBut.** -/
theorem k03_hHeadAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (base : ℕ) :
    ∀ p i, GoesBack (relOf SameBut base) ((h.toAtMg.𝔇 h.𝔇).headPart p i) := by
  rintro p i ⟨z, s⟩ y ⟨z', t⟩ y' w ⟨e, T, -⟩ hw
  obtain rfl : z = z' := e
  exact Eq.mp (VerifiableInference.Desc.Kinds.Head.Law.headPart_atAll_reply h p i z s t y y' w
    (congrArg (·.reply) T.out)) hw

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
  (hg : fenceFit (At.N Zp cF) linksFull PS = true)
include q₁ q₂ q₃ hg

/-- The index masks' tree lies below the piece's base. -/
theorem k03_index_low {l : ℕ} (hl : l < 25) (q) (hq : (h.toAtMg.row 𝔏)[k3K l false]? = some q) :
    (At.N Zp cF).index.1 < q.base := by
  refine k03_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (k03_blocks_at h.toAtMg) (k03_bookHeld_at Zp Np cF) hg l hl
    false q hq _ ?_
  have h0 := List.all_eq_true.1 k3CallsPinI_full l (List.mem_range.2 hl)
  have hm : Item.pinI ∈ (openSets linksFull PS (start linksFull))[k3K l false]?.getD [] := by
    simpa using h0
  unfold sampledIn
  exact List.mem_flatMap.2 ⟨.pinI, hm, List.mem_singleton.2 rfl⟩

/-- **THE FIELD rides AT THE 25 CALLS' PLACES, AT THE CONSTANT.** -/
theorem k03_rides_calls : ∀ l < 25, ∀ x, lookAt (At.X Zp) l false = some x →
    ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
      RidesAtR
        (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
          (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
        (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch (k3K l false) q b' := by
  intro l hl x hx q hq b' hb'
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have hback := Pc.back l hl false q hq
  exact ridesAtR_calls_ledger
    (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
    (h.toAtMg.𝔇 h.𝔇) mgBase (At.seats Zp) (k03_es h) (k03_hD h) (k03_hd h) h.toAtMg.rch
    (k3K l false) q b' (K3Lot.k03_at_full l hl false) rfl
    (by
      show (if (false : Bool) = true then 6 else 1) + (if l = 24 then 1 else 0) + 1 ≤ 3
      by_cases e : l = 24 <;> simp [e])
    hback
    (calls_seated_sameBut K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp) Zp.first.codes
      Zp.first.shape (IM.k3Place l false) b' hb' (Pc.planOk l hl false b' hb') l rfl
      (k03_pieceAt h.toAtMg l) (placeAt_iff.2 ⟨x, hx, rfl⟩) q hback)
    (k03_index_low h 𝔏 q₁ q₂ q₃ hg hl q hq)
    (fun _ _ _ _ => rfl)
    (k03_hHeadAll h q.base)

end

end P5J

#print axioms P5J.k3CallsPinI_full
#print axioms P5J.k3CallsPinI_control
#print axioms P5J.k03_pieceAt
#print axioms P5J.k03_hHeadAll
#print axioms P5J.k03_index_low
#print axioms P5J.k03_rides_calls
