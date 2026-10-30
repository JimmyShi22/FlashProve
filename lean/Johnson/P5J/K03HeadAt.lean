-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03HeadAt.lean: the kind "lookup" (K3): THE LEDGER's FAMILY AT THE OUTPUT HEAD's CALLS,
AT THE CLOSED CONSTANT: `HeadRestR` (Johnson/Desc/Sound/MgAt/K3Mean.lean) FROM WHAT IS LEFT OF IT.

Main names:
  `HeadShortR`: two of `HeadRestR`'s fields (parts, rides) and one of its field left's (model), in
    their own texts (laid by a program): parts (the
    promise behind) · model (`HeadModelR`: Johnson/Desc/First/Look/K3HeadModelR.lean) · rides.
  `k03_head_at`: the field head of `K3LeftR` (Johnson/Desc/Sound/MgAt/K3OwedLeft.lean) to the
    letter, at the constant's own letters. PAID HERE: hs, hsome, hsent, hfits, hbase
    (Johnson/P5J/K03HeadTestsAt.lean; hbase under fenceFit) · objects (`k03_objects_head`:
    Johnson/P5J/K03HeadObjAt.lean, from `ObjShortR` at the head's calls' place) · smallBack
    (`headMg_smallBack`: Johnson/Desc/First/Look/K3HeadSmallBack.lean).

LEFT, AS PREMISES: fenceFit · `HeadShortR` · `ObjShortR` · hHead: "the output head's part 'small'
goes back over what an accept of the lookup leaves", AT ALL STRINGS y, y': WHETHER THE CONSTANT's
`headPartK6` HAS IT IS NOT SHOWN: it can hold only if that part does not read the strings.
(Where this and lean/THEOREM.md differ, the page holds.)

Limits: no member is known. At secondHashFunction alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03HeadTestsAt
import Johnson.P5J.K03HeadObjAt
import Johnson.Desc.First.Look.K3HeadModelR
import Johnson.Desc.First.Look.K3HeadSmallBack
import Johnson.Desc.Sound.MgAt.K3OwedLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning ModelPart shift)
open VerifiableInference.Desc (Wit)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {Fr : Frame} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

/-- **What is left at the output head's calls.** -/
structure HeadShortR {Cl : Type} (claim : Aff → Cl) (seats : List (ℕ × ℕ)) (s₀ : Desc.First.S)
    (x : Desc.First.Look.Place)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (arrs : Array (Nat × String)) (pl pl' : Desc.Place)
    (told : List (List Desc.Oracle)) : Prop where
  /-- where the piece accepts: the promise behind -/
  parts : ∀ B', SeatOf b' B' → ∀ z : P,
    BehindPartsR (Fr := Fr) x (Params.settingOf X.P.frame) 𝔇.N (mgAll 𝔇 Mg) linksFull PS z
      (k3K 24 false) 24 3 arrs pl pl' told
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
      (fun u => Rch (k3K 24 false) ((z, u.1), u.2))
  /-- model -/
  model : ∀ B', SeatOf b' B' → ∀ z : P,
    letI := k3SizesAt X
    letI := k3PolicyAt X
    letI := 𝔇.rq z
    HeadModelR (Fr := Fr) 𝔇.G (k3AdrAt X) x X.H.tl 𝔇.sent 𝔇.l3.rad 𝔇.l3.oW 𝔇.l3.wOf 𝔇.l3.nr
      𝔇.l3.nc (Params.settingOf X.P.frame) (fun j => 𝔇.l3.seat x.link false j.1) 𝔇.l3.arr
      (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x)
      (Stored.smpWc (rows := rows) (cols := cols)) (Stored.strWc 𝔇.decT s₀ z) 𝔇.l3.msgW k3QAny
      (fun w => Flat.InRange w.cells) (fun u => Rch (k3K 24 false) ((z, u.1), u.2)) claim 𝔇.N
      (mgAll 𝔇 Mg) linksFull PS z (k3K 24 false) 24
      (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
  rides : RidesAtR 𝔇.N (mgAll 𝔇 Mg) Rch (k3K 24 false) q b'

end

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

set_option maxHeartbeats 4000000 in
/-- **THE LEDGER's FAMILY AT THE HEAD's CALLS, AT THE CONSTANT.** -/
theorem k03_head_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (arrs : Array (Nat × String))
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) = true)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (M : List OracleShape)
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
          q b' arrs (IM.k3Place 24 false) (MgAt.nextOf 24 false) (At.told cF)) :
    ∀ y, VerifiableInference.Desc.Kinds.Head.Law.headAt (At.X Zp) = some y →
      ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
        HeadRestR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm (At.seats Zp) s₀ y
          q b' arrs (IM.k3Place 24 false) (MgAt.nextOf 24 false) (At.told cF) := by
  intro y hy q hq b' hb'
  obtain rfl : x = y := Option.some.inj (h.headAt.symm.trans hy)
  have T := k03_head_seats h
  have S := Hs q hq b' hb'
  exact
    { hs := k03_head_hs h
      hbase := k03_head_base h 𝔏 q₁ q₂ q₃ hg q hq
      hsome := T.1
      hsent := T.2.1
      hfits := T.2.2
      parts := S.parts
      left := fun B' hB z =>
        letI := k3SizesAt (At.X Zp)
        letI := k3PolicyAt (At.X Zp)
        letI := (h.toAtMg.𝔇 h.𝔇).rq z
        headLeft_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (k03_objects_head h Ld M h.headAt q b' (Oh q hq b' hb') B' hB z) (S.model B' hB z)
          (headMg_smallBack (h.toAtMg.𝔇 h.𝔇) mgBase (fun c z s s' => k03_hd h c (z, s') (z, s) rfl)
            (headLink_in_scope h.toAtMg.scope h.toAtMg.reads h.toAtMg.pubOne) z (hHead z)
            (strictAt B' q))
      rides := S.rides }

end P5J

#print axioms P5J.k03_head_at
