-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/K03DigFormsAt.lean: THE LOOKUP ARGUMENTS ON THE DIGITS: THE ONE DEBT THAT IS LEFT OF
THE FIELD othersPub THERE (`DigFormsR`, Johnson/P5J/K03DigOthersAt.lean: "across an accept of the
digits' piece every public test formsIn that is open behind holds behind"), IN ITS OWN TEXT, AT THE
CLOSED CONSTANT, AT ALL 25 SEGMENTS. **A JOINING, NO PAYMENT: THREE NAMED PREMISES STAY BEYOND THE
HEAD `AtMgA`: NONE OF THE THREE IS SHOWN HERE; NONE IS SHOWN FALSE.**
  THE THREE PREMISES (`DigItemR` at one item each; the hands lifted by program off the lookup's
    files' own binders): formsIn l (3 + shift sub) "own" (every sort) · formsIn l (2 + shift
    sub) "planes" · formsIn l (joinAt sub) "join" (where the sort is not the layers').
  **`k03_digForms`**: `forms_of_live` (Johnson/Desc/Sound/MgAt/K3DigitsFormsLive.lean: OTHER
    items, those of the written lists that name no run, hold outright) after `hForms_dig_mgAll`
    (Johnson/Desc/Sound/MgAt/K3DigitsFormsJoin.lean: the live items), whose other premises are
    paid: the pieces: `k03_pieces_at` · the book: `k03_book_at`, `k03_tells_at` · the seats:
    `k03_digits_seats` · the masks' three tests: `k03_hB_digits`, and
    `AtMg.hTests_digits`, `AtMg.h6_at_head` (Johnson/P2LawR/MasksAtHead.lean) · the facts along
    the fold: `atMgR_rch_of_head`, `k03_hLive` …, `k03_frame` · the slots: `k03_slots_all`,
    `k03_ns_pos_dig` · the link and the four finds: `k03_finds_dig` · the guard: `k03_hpass`,
    `k03_hsame` · the test in front: `k03_sFvFits_dig`.

Limits. See the first paragraph. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles`
and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone.

Nothing on soundness.

-/
import Johnson.P5J.K03DigPartsAt
import Johnson.P5J.K03DigOthersAt
import Johnson.P5J.K03MaskBAt
import Johnson.P5J.K03FoldAt
import Johnson.P5J.K03BookAt
import Johnson.P5J.K03SeatsAt
import Johnson.P5J.K03ObjInAt
import Johnson.P5J.StartAtHead
import Johnson.P2LawR.MasksAtHead
import Johnson.Desc.Sound.MgAt.K3DigitsFormsJoin
import Johnson.Desc.Sound.MgAt.K3DigitsFormsLive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Fr : VerifiableInference.Desc.Sound.Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (l : ℕ)
  (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (b' : Desc.Block Desc.First.S ProofFile.Cl)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- One public test behind an accept of the digits' piece, under the field's own fenced hands. -/
abbrev DigItemR (it : Pub) : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
  (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
    Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
  SameBut u.1 v.1 → DigLeft u.1 v.1 →
  onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
  Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
    (mgAll Dm Mg).pub it (z, v.1) = true

end

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift joinAt)
open VerifiableInference.Desc.First.Look

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

set_option maxHeartbeats 4000000 in
/-- **DigFormsR AT THE CONSTANT, AT ALL 25, UNDER THE THREE ITEMS.** -/
theorem k03_digForms (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {l : ℕ} (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    {x : Place} {tl : HTailF2} (hx : digAt (At.X Zp) l = some (x, tl))
    (q) (hq : (h.toAtMg.row 𝔏)[k3K l true]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b')
    (hOwnIt : DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b'
      (.formsIn l (3 + shift sub) "own"))
    (hPlanesIt : sub ≠ .layers → DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b'
      (.formsIn l (2 + shift sub) "planes"))
    (hJoinIt : sub ≠ .layers → DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b'
      (.formsIn l (joinAt sub) "join")) :
    DigFormsR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l sub q b' := by
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  have hlook : lookAt (At.X Zp) l true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  have elk : x.link = l := lookAt_link hlook
  obtain ⟨lk, hlk, hrawO, hrawG, hO6, hG6⟩ := k03_finds_dig h hl hsub
  have hTests := h.toAtMg.hTests_digits R.listed hl
  have live := hForms_dig_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes
    Zp.first.shape k03_hM hl hsub hx q b' hb (Pc.planOk l hl true b' hb) (Pc.back l hl true q hq)
    (At.told cF) (k03_book_at Zp cF) (k03_tells_at h.toAtMg l hl true) rfl
    (k03_digits_seats h hl hlook).1 (k03_hB_digits h l hl x hlook) lk passR k03_hpass
    (nos := (At.foldD Zp cF L).ownAt l 3) (n := x.ns) (Ld := L)
    (M := VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1)
    (k03_hLive h R.fold (k3K l true)) (k03_hGroups h R.fold (k3K l true))
    (fun z a hr hu => (k03_frame h R.fold hl z a hr hu).1.trans elk.symm)
    (fun z a hr hu => (k03_frame h R.fold hl z a hr hu).2.1)
    (fun z a hr hu => (k03_frame h R.fold hl z a hr hu).2.2)
    (k03_hSeats h R.fold (k3K l true)) (k03_hShapes h R.fold (k3K l true))
    (k03_slots_all h hl hlook) (Nat.le_refl _) (by rw [elk]; exact hTests) h.toAtMg.h6_at_head hlk
    (k03_ns_pos_dig h hl hlook) hrawO hrawG k03_hsame
    ⟨_, _, hO6, fun _ _ _ hr _ => hr⟩ ⟨_, _, hG6, fun _ _ _ hr _ => hr⟩
    (fun _ _ z u _ _ _ _ _ hu hr hun => k03_sFvFits_dig h hl z u hu hr hun)
    hOwnIt hPlanesIt hJoinIt
  intro B' hN z u τ v hout T DL hu hr hun
  exact forms_of_live (h.toAtMg.𝔇 h.𝔇) mgBase rfl hsub (z, v.1)
    (live B' hN z u τ v hout T DL hu hr hun)

end P5J

#print axioms P5J.k03_digForms
