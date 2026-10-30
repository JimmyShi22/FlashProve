-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03BareAt.lean: THE KIND "LOOKUP" (K3): "THE ROWS THAT THE LOOKUP's VERIFIER HAS HEARD ARE BARE" (the field hBare of ObjShortR, Johnson/P5J/K03ObjAt.lean) AT THE CONSTANT, AT ALL 25 LOOKUPS ON A SEGMENT's CALLS: by one call of calls_hBare_mgAll (Johnson/Desc/Sound/MgAt/K3CallsBareAt.lean). One abbreviation, two theorems. A joining: by calls alone.
  BareR Dm Mg Rch claim k q b' : Prop: the field's sentence (lifted by program). IT NAMES NO PLACE OF A LOOKUP: so lookAt's place serves as the premise at all 25 segments, the output head's among them.
  k03_hBare: UNDER h : AtMgA OnBytes.secondHashFunction …, 𝔏 : Free … with the three equations q₁ q₂ q₃, l < 25, lookAt X l false = some x, the row's piece q and the kind's constant b' at the calls' place of segment l: BareR at 𝔇 := h.toAtMg.𝔇 h.𝔇 · mgBase · h.toAtMg.rch · K3Lot.ofForm · k := k3K l false.
  ALL TEN PREMISES OF calls_hBare_mgAll ARE PAID: NOTHING STAYS A TEST: h (the constant is the kind's stated block at the address) · hOk | hback (k03_pieces_at) · hlook · hi (rfl) · hsub | hpcT (K3Lot.k03_sub_full) · hpc (K3Lot.k03_place) · hk (K3Lot.k03_at_full) · hfit (hfit_mgAll).
  k03_objShort_bare: A TRIPWIRE: laid as the field hBare into a value of ObjShortR, it types: Lean's own word that BareR is the field to the letter.
Limits. The head is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on what the rows are worth. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03ObjAt
import Johnson.Desc.Sound.MgAt.K3CallsBareAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc (Link)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)


local notation "PS" => Desc.First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (k : ℕ)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (b' : Desc.Block Desc.First.S Desc.Claim)

/-- The field's sentence. -/
abbrev BareR : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, (Desc.K3.seatCalls claim).heard v.1 = some g → ∀ f ∈ g.rows.toList, Bare f

end

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
  (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- **THE FIELD hBare AT THE CONSTANT, AT ALL 25 LOOKUPS ON THE CALLS.** -/
theorem k03_hBare (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) {x : Place} (hx : lookAt (At.X Zp) l false = some x)
    (q) (hq : (h.toAtMg.row 𝔏)[k3K l false]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b') :
    BareR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) q b' := by
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l false b' hb
  obtain ⟨sub, hsub, hpcT, -⟩ := K3Lot.k03_sub_full l hl
  exact calls_hBare_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm
    (IM.k3Place l false) (k3K l false) l sub x q b' (K3Lot.readersAt (At.X Zp)) Zp.first.codes
    Zp.first.shape hb (Pc.planOk l hl false b' hb) (Pc.back l hl false q hq) hx rfl hsub hpcT hpc
    (K3Lot.k03_at_full l hl false) (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase k03_hM)

/-- **A TRIPWIRE: the sentence is ObjShortR's field hBare to the letter.** -/
theorem k03_objShort_bare (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) {x : Place} (hx : lookAt (At.X Zp) l false = some x)
    (q) (hq : (h.toAtMg.row 𝔏)[k3K l false]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b')
    (y : Place) (Ld : VerifiableInference.Desc.K12.Door.Laid) (M : List OracleShape)
    (S : ObjShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y
      q b' Ld M) :
    ObjShortR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (k3K l false) l y
      q b' Ld M :=
  { S with hBare := k03_hBare h 𝔏 q₁ q₂ q₃ hl hx q hq b' hb }

end P5J

#print axioms P5J.k03_hBare
#print axioms P5J.k03_objShort_bare
