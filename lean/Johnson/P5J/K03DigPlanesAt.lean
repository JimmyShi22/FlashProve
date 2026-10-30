-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03DigPlanesAt.lean: THE TERMS THAT THE LOOKUPS' LAW ON THE KEPT ITEM formsIn l (2 + shift sub) "planes" LEAVES, PAID AT THE CLOSED CONSTANT, UNDER THE HEAD; AND THE ITEM ITSELF THERE. THE THIRTEEN WHOLE: the call goes to the lookups' law that does not ask the premise hrHead.
  k03_rawP: GENERAL IN THE SORT: at every written link l whose calling kind has readers rd (K3Lot.readersAt (At.X Zp) l = some rd): ONE link lk with 𝔇.lk l = some lk; the lookup's place p on the calls; and what lk states under "planes" at the block 1 + shift sub IS the lookup's own run at p.lm and rd. By k03_planes_raw (Johnson/Desc/First/Look/K03StatesRaw.lean), carried to the constant's letters (IM.Open.W · LaidAt.linkAt).
  k03_rawP_att: at attention's twelve (l = 2 g + 1, g < 12): rd = readersOfO a, a the plan's g-th attention plan (H2K5.Door.readersAt_att).
  k03_rawP_head: at the output head's link 24: rd = callerReaders (planesAt 0), and 0 IS iU3At (At.X Zp) (P4.readers_head · ReadsNamed.public_third).
k03_rawP IS SPENT AT THIRTEEN LINKS: K3Lot.readersAt answers at attention's twelve and at the head's link, and at no layers' link (there the item is idle).
THEY ARE THE PREMISES hlk · hrawP · hrdA · hrdH OF THE LOOKUPS' hPlanesIt_dig_free (Johnson/Desc/Sound/MgAt/K3DigitsPlanesHead.lean).
  **k03_planesIt**: THE ITEM AT THE CONSTANT: at every written link, not at a layers' segment: behind an accept of the seated digits' piece (u to v), under SameBut u.1 v.1 · DigLeft u.1 v.1 and the ledger's own fenced hands, the composed public test at formsIn l (2 + shift sub) "planes" holds: THE PREMISE hPlanesIt OF hForms_dig_mgAll (Johnson/Desc/Sound/MgAt/K3DigitsFormsJoin.lean) IN ITS OWN TEXT at 𝔇 := h.toAtMg.𝔇 h.𝔇 · mgBase · h.toAtMg.rch. ONE CALL of hPlanesIt_dig_free an arm; the credit is the lookups'. FROM THE HEAD ALONE (and the binders that name the piece and the block).
  **k03_planesIt_att · k03_planesIt_head**: the same at attention's twelve and at the output head's link, the sort written out.
  hrHead («the run "planes" itself answers at the state in front») MAY BE FALSE AT A STATE UNDER THE PROMISE; the lookups' law goes round it (there the kept test passes whichever of the run and the link's second hole answers): NOBODY NEEDS IT.

Limits. The three terms and k03_sorts_full are equations between closed terms: nothing on a state. k03_planesIt | k03_planesIt_att | k03_planesIt_head speak of the state BEHIND an accept of the seated digits' piece, under the ledger's fenced hands (the promise in front · reached · no mark): an implication; that such an accept exists is not shown. The head is a premise; a member of it is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/).
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03ObjTerms
import Johnson.Desc.First.Look.K03StatesRaw
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.P4SR.PlanesAtSeat
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.Sound.AtDriver
import Johnson.P5K3R.SitsAddr
import Johnson.P5J.K03PiecesAt
import Johnson.P5J.K03Terms
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker OnBytes.Model Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.Desc.First.Look (digAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true
local notation "WTc" => Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT

/-- **What the constant's link l states under "planes" is the lookup's own run at the calling kind's
readers.** -/
theorem k03_rawP (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub)
    (rd : VerifiableInference.Desc.K3.Readers VerifiableInference.Desc.First.S)
    (hr : K3Lot.readersAt (At.X Zp) l = some rd) :
    ∃ (lk : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim)
      (p : VerifiableInference.Desc.First.Look.P),
      (h.toAtMg.𝔇 h.𝔇).lk l = some lk ∧ placeAt (At.X Zp) l false = some p ∧
      (statesOfLink lk (1 + shift sub)).find? (fun y => y.1 == "planes") =
        some ("planes", VerifiableInference.Desc.K3.planesRun
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) p.lm rd) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have eW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨sub', hsub', h2, -⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have e1 : IM.k3Ix l false = 1 + shift sub' := by
    have e2 : IM.k3Ix l false + 1 = 2 + shift sub' := h2
    omega
  obtain ⟨lk, p, hk, hp, hf⟩ := k03_planes_raw h.scope h.reads O l hl rd (by rw [eW]; exact hr)
  rw [eW] at hp
  rw [e1] at hf
  exact ⟨lk, p, (h.laid.linkAt l).trans hk, hp, hf⟩

/-- **At attention's twelve.** -/
theorem k03_rawP_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) :
    ∃ (lk : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim)
      (p : VerifiableInference.Desc.First.Look.P) (a : Attention.Plan),
      (h.toAtMg.𝔇 h.𝔇).lk (2 * g + 1) = some lk ∧ (At.X Zp).A[g]? = some a ∧
      placeAt (At.X Zp) (2 * g + 1) false = some p ∧
      (statesOfLink lk (1 + shift .attention)).find? (fun y => y.1 == "planes") =
        some ("planes", VerifiableInference.Desc.K3.planesRun
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) p.lm
          (VerifiableInference.Desc.First.Att.P.readersOfO a)) := by
  obtain ⟨h4, -, -, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨-, a, hA, -⟩ := Meaning.scope_plans24 h.scope h.reads h.pubOne g hg
  have hsub : linksFull[2 * g + 1]? = some ModelPart.attention := by
    interval_cases g <;> rfl
  obtain ⟨lk, p, hk, hp, hf⟩ := k03_rawP h (by omega) hsub _ (H2K5.Door.readersAt_att h4 hA)
  exact ⟨lk, p, a, hk, hA, hp, hf⟩

/-- **At the output head's link.** -/
theorem k03_rawP_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    iU3At (At.X Zp) = 0 ∧
    ∃ (lk : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim)
      (p : VerifiableInference.Desc.First.Look.P),
      (h.toAtMg.𝔇 h.𝔇).lk 24 = some lk ∧ placeAt (At.X Zp) 24 false = some p ∧
      (statesOfLink lk (1 + shift .head)).find? (fun y => y.1 == "planes") =
        some ("planes", VerifiableInference.Desc.K3.planesRun
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) p.lm
          (VerifiableInference.Desc.Kinds.Head.callerReaders
            (VerifiableInference.Desc.Kinds.Head.planesAt 0))) := by
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  have hU : (At.X Zp).H.tl.ix.U.getD 2 none = some 0 :=
    VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_third h.pubOne
  have hH : VerifiableInference.Desc.K3.isHead (At.X Zp) 24 = true := by
    unfold VerifiableInference.Desc.K3.isHead
    rw [h4, hN]
    rfl
  refine ⟨by unfold iU3At; rw [hU]; rfl, ?_⟩
  exact k03_rawP h (by omega) (by rfl) _ (P4.readers_head hH hU)

/-- The sorts of the written links, by the kernel. -/
theorem k03_sorts_full : ∀ l < 25, (linksFull[l]? = some ModelPart.attention → l % 2 = 1 ∧ l < 24) ∧
    (linksFull[l]? = some ModelPart.head → l = 24) := by
  decide +kernel

/-- **THE ITEM "planes" BEHIND THE DIGITS' PIECE, AT THE CONSTANT: hPlanesIt's OWN TEXT.** -/
theorem k03_planesIt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {y : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt (At.X Zp) l = some (y, tl))
    (q) (hq : (h.toAtMg.row 𝔏)[k3K l true]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b') :
    sub ≠ .layers → ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) FrD VerifiableInference.Desc.First.S ProofFile.Cl WTc).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
        (fun s => (z, s)) (k3K l true) u →
      h.toAtMg.rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsIn l (2 + shift sub) "planes") (z, v.1) =
          true := by
  intro hnl
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  cases sub with
  | layers => exact absurd rfl hnl
  | attention =>
    obtain ⟨ho, h24⟩ := (k03_sorts_full l hl).1 hsub
    obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    obtain ⟨lk, p, a, hk, -, -, hf⟩ := k03_rawP_att h (g := g) (by omega)
    exact hPlanesIt_dig_free (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes
      Zp.first.shape k03_hM hl hsub hx q b' hb (Pc.planOk _ hl true b' hb) (Pc.back _ hl true q hq)
      rfl lk hk p.lm _ hf (fun _ => ⟨a, rfl⟩) (fun e => by cases e) hnl
  | head =>
    obtain rfl : l = 24 := (k03_sorts_full l hl).2 hsub
    obtain ⟨-, lk, p, hk, -, hf⟩ := k03_rawP_head h
    exact hPlanesIt_dig_free (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes
      Zp.first.shape k03_hM hl hsub hx q b' hb (Pc.planOk _ hl true b' hb) (Pc.back _ hl true q hq)
      rfl lk hk p.lm _ hf (fun e => by cases e) (fun _ => ⟨0, rfl⟩) hnl

/-- **AT ATTENTION's TWELVE.** -/
theorem k03_planesIt_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) (hsub : linksFull[l]? = some ModelPart.attention)
    {y : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt (At.X Zp) l = some (y, tl))
    (q) (hq : (h.toAtMg.row 𝔏)[k3K l true]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b') :
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) FrD VerifiableInference.Desc.First.S ProofFile.Cl WTc).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
        (fun s => (z, s)) (k3K l true) u →
      h.toAtMg.rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsIn l (2 + shift ModelPart.attention) "planes")
          (z, v.1) = true :=
  k03_planesIt h 𝔏 q₁ q₂ q₃ hl hsub hx q hq b' hb (by decide)

/-- **AT THE OUTPUT HEAD's LINK: THE THIRTEENTH.** -/
theorem k03_planesIt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) (hsub : linksFull[l]? = some ModelPart.head)
    {y : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt (At.X Zp) l = some (y, tl))
    (q) (hq : (h.toAtMg.row 𝔏)[k3K l true]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b') :
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) FrD VerifiableInference.Desc.First.S ProofFile.Cl WTc).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
        (fun s => (z, s)) (k3K l true) u →
      h.toAtMg.rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsIn l (2 + shift ModelPart.head) "planes")
          (z, v.1) = true :=
  k03_planesIt h 𝔏 q₁ q₂ q₃ hl hsub hx q hq b' hb (by decide)

end P5J

#print axioms P5J.k03_rawP
#print axioms P5J.k03_rawP_att
#print axioms P5J.k03_rawP_head
#print axioms P5J.k03_sorts_full
#print axioms P5J.k03_planesIt
#print axioms P5J.k03_planesIt_att
#print axioms P5J.k03_planesIt_head
