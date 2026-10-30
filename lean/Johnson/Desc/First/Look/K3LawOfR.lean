-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LawOfR.lean: K03_law IN THE SECOND FORM: the kind "lookup" (K3): every
piece of the kind is tied at the table of joints, with "reached" in hand (`KindTiedR`,
Johnson/Desc/Sound/TiedR.lean), at the IOP as written in Lean for the proof file, in the goals'
scope, at the full size's written lists: FROM THREE STRUCTURES.

Main names:
  `k03_seatLaws_ofR`: `K3PlanR` (the public parameters; K3Base.lean) · `K3Pieces` (the maker's
    pieces) · `K3MeanR` (the meaning; K3MeansR.lean) give `SeatLawsR` at all fifty places: at the
    digits by `seatLawsR_of_digMeanR`, at attention's and the layers' calls by
    `att_seatLawsR_of_mean` and `lay_seatLawsR_of_mean` (the lookups' authors'), at the output
    head's calls by `k3_head_seatLawsR`.
  `k03_law_ofR`: so `KindTiedR … KindName.K3` (`K3Lot.k03_kindTiedR`).

OF THE FACTS ALONG THE FOLD the four rows' OWN PROOFS spend one: `OwnIs` at the border in front (the
field ownIn). Their other fields "in front" have Rch in hand too, and some will want it where they
are paid at a term (the head's tokIn: "the heard reply is a token").

Limits: the three structures are premises: `K3MeanR` is shown at no term and not tried for
emptiness; N, Mg, Rch, E, the readers and the guard are letters. Nothing on soundness by itself;
nothing on hiding.


-/
import Johnson.Desc.First.Look.K3MeansR
import Johnson.P5K3R.SitsKindsR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn shift pubFit)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy]

section
variable {P Cells Tok Xi : Type} {Fr : Frame} {G : Desc.FileDescription Xi} {X : Verify.Public}
  {codes : Codes} {shape : Params.ReqShape}
  {Dl : Desc.K3Asks.Sent} {L : K3Letters Cells Tok} {N : Numbers}
  {Mg : Meaning P (Desc.Wit Cells Tok MsgT)}
  {Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop}
  {pieces : List (Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit Cells Tok MsgT))}
  {smpC : (x : Desc.First.Look.Place) → Desc.First.S →
    (i : Fin (sigListCalls Dl.up L.rad x.link).length) → Option ((attSg x Dl.up L.rad).om i).Smp}
  {smpD : (x : Desc.First.Look.Place) → Desc.First.S →
    (i : Fin (digList x Dl.up L.rad).length) → Option ((digSg x Dl.up L.rad).om i).Smp}
  {smpW : Desc.First.S → Option L.oW.Smp} {strW : P → Fr.E.Str → L.oW.Str}
  {adr : HeadAdr} {rq : P → Desc.Kinds.Head.Request} {Q : Fork → Prop}
  {gd : Desc.Wit Cells Tok MsgT → Prop}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame

/-- **`SeatLawsR` AT ALL FIFTY PLACES.** -/
theorem k03_seatLaws_ofR {floor : ℕ} (hP : K3PlanR X Dl L floor)
    (hQ : K3Pieces X codes shape pieces)
    (M : K3MeanR G X codes shape Dl.up L N Mg Rch pieces smpC smpD smpW strW adr rq Q gd) :
    ∀ l, l < 25 → ∀ (d : Bool) q, pieces[k3K l d]? = some q →
      ∀ b', k3Const X codes shape l d = some b' →
        SeatLawsR linksFull PS (k3K l d) q N Mg Rch b' := by
  intro l hl d q hq b' hb
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l d b' hb
  have hOk := hQ.planOk l hl d b' hb
  have hbk := hQ.back l hl d q hq
  have hcp := hQ.cap l hl d q hq
  cases d with
  | true =>
    obtain ⟨x, tl, hx, hB⟩ := hP.digB L.rad l hl
    obtain ⟨sub, hsub, -, hpcT⟩ := K3Lot.k03_sub_full l hl
    exact seatLawsR_of_digMeanR G X Dl.up L N Mg Rch K3Lot.ofForm (K3Lot.readersAt X) codes shape
      (IM.k3Place l true) (k3K l true) l sub x tl (smpD x) q b' hb hOk
      (K3Lot.k03_at_full l hl true) rfl hsub hpcT hpc hx Cb.Gl.p hB hbk
      (hQ.rounds l hl true q hq _ (placeAt_digAt hx)) hcp (M.dig l hl sub hsub x tl hx q hq b' hb)
  | false =>
    by_cases h24 : l = 24
    · subst h24
      obtain ⟨x, hx, hB, hpl⟩ := hP.head
      have m := M.head x hx q hq b' hb
      obtain ⟨σ₀⟩ := m.smp0
      obtain ⟨σW₀⟩ := m.smpW0
      have e : placeAt X 24 false = some (Desc.First.Look.P.ofPlace SET false x) := by
        have e0 : placeAt X (headLink X) false = some (Desc.First.Look.P.ofPlace SET false x) :=
          letI : Desc.Kinds.Head.Request := ⟨fun _ => 0, 0, 0⟩
          placeAt_headAt hx
        rwa [hP.head24] at e0
      have hl' : (IM.k3Place 24 false).link = some (headLink X) := by
        rw [hP.head24]
      have hpc' : (IM.k3Place 24 false).piece = Desc.K3.pieceAt X (headLink X) false := by
        rw [hP.head24]
        exact hpc
      exact k3_head_seatLawsR (floor := floor) G (fun j => L.seat x.link false j.1) L.arr (smpC x)
        smpW strW L.msgW Q gd Rch rq K3Lot.ofForm (K3Lot.readersAt X) codes shape
        (IM.k3Place 24 false) b' q hb hOk hx hl' hpc' hbk hB hpl (hP.entries 24 hl _ e)
        (hQ.rounds 24 hl false q hq _ e) hcp m.hsmp m.hsmpW m.hstrW m.hseat σ₀ σW₀ m.table m.rides
    · have hl24 : l < 24 := by omega
      rcases Nat.mod_two_eq_zero_or_one l with h0 | h1
      · obtain ⟨x, tl, hx, htl, H, hpl⟩ := hP.lay l hl24 h0
        have e := placeAt_layAt hx
        exact lay_seatLawsR_of_mean G K3Lot.ofForm (K3Lot.readersAt X) codes shape hb hOk rfl hpc e
          hbk H hpl (hP.entries l hl _ e) (hQ.rounds l hl false q hq _ e) hcp
          (M.lay l hl x tl hx htl q hq b' hb)
      · obtain ⟨x, A, tl, hx, H⟩ := hP.att l hl24 h1
        have e := placeAt_attAt hx
        exact att_seatLawsR_of_mean G K3Lot.ofForm (K3Lot.readersAt X) codes shape hb hOk rfl hpc e
          hbk H (hP.entries l hl _ e) (hQ.rounds l hl false q hq _ e) hcp
          (M.att l hl x A tl hx q hq b' hb)

end

section
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (KindName)

/-- **THE KIND's LAW, SECOND FORM, FROM THE THREE STRUCTURES.** hE: the table's extractor lays
nothing at the kind's places. -/
theorem k03_law_ofR {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Desc.Block Desc.First.S ProofFile.Cl)} {c : Desc.Chain Desc.First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B)
    {Cells Tok Xi : Type} {D : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    {T : ThreeAt (ckP .two) D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Desc.Wit Cells Tok MsgT)}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub (Desc.Wit Cells Tok MsgT))
    (Rch : ℕ → (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (E : ℕ → (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      Desc.Wit Cells Tok MsgT → Desc.Wit Cells Tok MsgT)
    (hE : ∀ l, l < 25 → ∀ d : Bool, ∀ a b w, E (k3K l d) a b w = w)
    (G : Desc.FileDescription Xi) (Dl : Desc.K3Asks.Sent) (L : K3Letters Cells Tok)
    {smpC : (x : Desc.First.Look.Place) → Desc.First.S →
      (i : Fin (sigListCalls Dl.up L.rad x.link).length) →
      Option ((attSg x Dl.up L.rad).om i).Smp}
    {smpD : (x : Desc.First.Look.Place) → Desc.First.S →
      (i : Fin (digList x Dl.up L.rad).length) → Option ((digSg x Dl.up L.rad).om i).Smp}
    {smpW : Desc.First.S → Option L.oW.Smp}
    {strW : ProofFile.InstPub → (frameAt D all D.key₁ T.ft₁).E.Str → L.oW.Str}
    {adr : HeadAdr} {rq : ProofFile.InstPub → Desc.Kinds.Head.Request} {Q : Fork → Prop}
    {gd : Desc.Wit Cells Tok MsgT → Prop}
    {floor : ℕ} (hP : K3PlanR Bs.G₀.W Dl L floor)
    (hQ : K3Pieces Bs.G₀.W Z.first.codes Z.first.shape (T.p₁ :: T.l₁))
    (M : K3MeanR G Bs.G₀.W Z.first.codes Z.first.shape Dl.up L N Mg Rch (T.p₁ :: T.l₁) smpC smpD
      smpW strW adr rq Q gd) :
    KindTiedR N Mg linksFull (Desc.First.flatPlacesOf linksFull true) Rch E (T.p₁ :: T.l₁)
      KindName.K3 :=
  K3Lot.k03_kindTiedR hS hR O hT N Mg Rch E hE (k03_seatLaws_ofR hP hQ M)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k03_seatLaws_ofR
#print axioms VerifiableInference.OnPublicFiles.k03_law_ofR
