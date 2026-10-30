-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03ObjInAt.lean: THE KIND "LOOKUP" (K3): AT THE 25 LOOKUPS ON A SEGMENT's CALLS, AT THE
COMPOSED MEANING's OWN PARAMETERS: BEHIND AN ACCEPT THE PUBLIC TEST formsInT l pc "objects" HOLDS
(pc 2 in front of the head's segment; 3 there). Two definitions (sentences); theorems.
  `K03MaskAt h l q b'`, `K03MergeAt h l q b'`: THE TWO PREMISES THAT STAY, BY NAME:
    `objIn_mgAll`'s own hmask and hmerge (Johnson/Desc/Sound/MgAt/K3CallsObjIn.lean) at
    these parameters, at the border k3K l false: each a fact on the state behind an accept: "the
    mask row's message is sent and seated among the segment's own" · "no heard row's slot is the
    merge's".
  `runsOf_calls`, `k03_runs_calls`: the table's name "objects" at the calls' piece stands for TWO
    runs, and so does the parameter runs: [(k3Ix l false, "objects"), (k3Ix l false, "guests")].
  `k03_hsame`, `k03_hfind2`: the guard passes where nothing turns · one link for the readers and for
    both finds: the run "objects" at the calls' seat, and the run "guests" WITHOUT A GUEST
    (`k03_objects_of`, `k03_guests_of`, Johnson/Desc/First/Look/K03States.lean).
  `k03_onIn_calls`: in front, at a reached state without a mark on which the promise holds, the
    lookup's own test on what it is handed accepts: as it is derived inside
    `othersPub_att_mgAll`.
  `k03_objIn_calls` (l < 24): ends, to the letter, in the premise hObj of
    Johnson/P5J/K03OthersPubAt.lean's two theorems. hlook and hsP are handed: at attAt's place:
    k03_look_att and attAt_shape; at layAt's: k03_look_lay and that file's k03_shape_lay.
  `k03_objIn_head`: ends, to the letter, in the premise of Johnson/P5J/K03HeadPartsAt.lean's theorem
    (its other order of premises).
  BOTH: one call of `objIn_pc` (Johnson/Desc/Sound/MgAt/K3CallsObjInPc.lean), at pc := 2 | 3. NOT of
  `objIn_mgAll`: its premise hruns (a list of one run) is false at these parameters.
Limits. K03MaskAt and K03MergeAt are premises: no member is shown; no run shows a sentence over
every reached state. The head AtMgA is a premise. At OnBytes.secondHashFunction. The full size alone. Nothing on
soundness.

-/
import Johnson.P5J.K03LeftAt
import Johnson.Desc.Sound.MgAt.K3CallsOthers
import Johnson.Desc.Sound.MgAt.K3Tests
import Johnson.P5J.K03HeadPartsAt
import Johnson.P5J.K03ObjTerms
import Johnson.Desc.Sound.MgAt.K3CallsObjInPc

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
open VerifiableInference.Desc.First (ModelPart shift Pub)
open VerifiableInference.Desc.First.Look (attAt layAt lookAt)
open VerifiableInference.Desc.K9 (segAt? maskSeat mergeOf holesAt)
open VerifiableInference.Desc.First.Look (k3LookIn_onIn)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option quotPrecheck false in
local notation "PieceD" => VerifiableInference.Desc.Sound.Piece (_root_.Run.ckP .two) FrD
  (ProofFile.InstPub × VerifiableInference.Desc.First.S)
  VerifiableInference.Desc.Claim (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT)

/-- **The mask row's message is sent and seated among the segment's own**, behind an accept. -/
def K03MaskAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (q : PieceD)
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S
      VerifiableInference.Desc.Claim) : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
    (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
    onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K l false) u →
    h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
    (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
    ∀ c, segAt? v.1 = some c → (maskSeat ((h.toAtMg.𝔇 h.𝔇).N.sent l 0) c).isSome = true

/-- **No heard row's slot is the merge's**, behind an accept. -/
def K03MergeAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (q : PieceD)
    (b' : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S
      VerifiableInference.Desc.Claim) : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
    (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
    onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
      (k3K l false) u →
    h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
    (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
    ∀ g, v.1.lookHeard? = some g → ∀ f ∈ g.rows.toList, ∀ y ∈ f.slots.toList,
      mergeOf v.1 ≠ some y.1

/-- At the three sorts the table's name "objects" at the calls' piece stands for two runs. -/
theorem runsOf_calls (sub : ModelPart) :
    VerifiableInference.Desc.First.runsOf sub (2 + shift sub) "objects" =
      [(1 + shift sub, "objects"), (1 + shift sub, "guests")] := by
  cases sub <;> decide

/-- **The parameter runs at the calls' piece.** -/
theorem k03_runs_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (sub : ModelPart) (hs : linksFull[l]? = some sub) :
    (h.toAtMg.𝔇 h.𝔇).runs l (2 + shift sub) "objects" =
      [(IM.k3Ix l false, "objects"), (IM.k3Ix l false, "guests")] := by
  have e : (h.toAtMg.𝔇 h.𝔇).runs l (2 + shift sub) "objects" =
      VerifiableInference.Desc.First.runsOf sub (2 + shift sub) "objects" := by
    show runsAt At.links l (2 + shift sub) "objects" = _
    unfold runsAt
    rw [show At.links[l]? = some sub from hs]
    rfl
  rw [e, runsOf_calls, (k03_ix l hl sub hs).1]

/-- **In front the lookup's own test on what it is handed accepts.** -/
theorem k03_onIn_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {y : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt (At.X Zp) l false = some y)
    (hpcX : (IM.k3Place l false).piece = VerifiableInference.Desc.K3.pieceAt (At.X Zp) l false) :
    ∀ (z : ProofFile.InstPub) (u : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l false) u →
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
      VerifiableInference.Desc.K3.k3OnIn
        (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame) false y)
        u.1 = true := by
  intro z u hu _ hf
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  have hfront := onQ_front hu hf
  exact k3LookIn_onIn (fLook_at (k3At_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) l false hlook z u.1 (by
    rw [← hpcX, hpc]
    exact hfront _ (List.mem_append_left _
      (calls_asks_open (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS (k3K l false)
        (IM.k3Place l false) l sub (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl)
        (K3Lot.k03_at_full l hl false) rfl hs' hpc _ (by simp)))))

/-- The guard passes where nothing turns. -/
theorem k03_hsame : ∀ t, passR t t := fun t => by
  unfold passR ProofFile.sameReply
  exact beq_self_eq_true _

/-- **ONE LINK FOR hlink AND BOTH FINDS, AT THE CALLS.** -/
theorem k03_hfind2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) :
    ∃ l : VerifiableInference.Desc.Link VerifiableInference.Desc.First.S
        VerifiableInference.Desc.Claim,
      (h.toAtMg.𝔇 h.𝔇).Rd m = VerifiableInference.Desc.K9.readersOfLink
        (holesAt (At.X Zp) (headLink (At.X Zp)) m l) l ∧
      (∃ nm run, (VerifiableInference.Desc.K9.statesOfLink l (IM.k3Ix m false)).find?
          (fun r => r.1 == "objects") = some (nm, run) ∧
        RunOver passR run (objectsRun (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm))) ∧
      ∃ nm run, (VerifiableInference.Desc.K9.statesOfLink l (IM.k3Ix m false)).find?
          (fun r => r.1 == "guests") = some (nm, run) ∧
        RunOver passR run (guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest
          VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim))) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨l, h1, h2⟩ := k03_objects_of h.scope h.reads O m hm false
  obtain ⟨l', h1', h2'⟩ := k03_guests_of h.scope h.reads O m hm false
  obtain rfl : l = l' := Option.some.inj (h1.symm.trans h1')
  exact ⟨l, k03_hlink h m l h1, ⟨_, _, h2, k03_over _⟩, _, _, h2', k03_over _⟩

/-- In front of the head's segment the calls' piece is 2. -/
theorem k03_piece_calls : ∀ l, l < 24 → (IM.k3Place l false).piece = 2 := by decide

set_option maxHeartbeats 4000000 in
/-- **hObj AT THE 24 CALLS' PLACES IN FRONT OF THE HEAD's, AT THE CONSTANT.** -/
theorem k03_objIn_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) {l : ℕ} (hl : l < 24)
    {y : VerifiableInference.Desc.First.Look.Place} (hlook : lookAt (At.X Zp) l false = some y)
    (hsP : (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame)
      false y).shape = some y.fs) :
    ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
    K03MaskAt h l q b' → K03MergeAt h l q b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l false) u →
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT l 2 "objects") (z, v.1) = true := by
  intro q hq b' hb' hmask hmerge
  have hl5 : l < 25 := by omega
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l false b' hb'
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl5
  have hsh : 2 + shift sub = 2 := hpc.symm.trans (k03_piece_calls l hl)
  have hruns := k03_runs_calls h l hl5 sub hs'
  rw [hsh] at hruns
  obtain ⟨lk, hRd, hfind, hfindG⟩ := k03_hfind2 h l hl5
  exact objIn_pc (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape hb'
    (K.planOk l hl5 false b' hb') (K.back l hl5 false q hq) rfl hpcX hlook hsP
    (k03_onIn_calls h hl5 hlook hpcX) hruns k03_atS2_calls hRd k03_hpass k03_hsame
    hfind hfindG hmask hmerge

/-- The head's place has the shape that the sub-protocol's own parameters make. -/
theorem k03_shape_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf (At.X Zp).P.frame)
      false x).shape = some x.fs := by
  have hx := h.headAt
  unfold VerifiableInference.Desc.Kinds.Head.Law.headAt at hx
  obtain ⟨y, -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 hx
  exact hk

/-- At the head's segment the calls' piece is 3. -/
theorem k03_piece_head : (IM.k3Place 24 false).piece = 3 := by decide

set_option maxHeartbeats 4000000 in
/-- **hObj AT THE HEAD's CALLS, AT THE CONSTANT.** -/
theorem k03_objIn_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
    K03MaskAt h 24 q b' → K03MergeAt h 24 q b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v, (strictAt B' q).ior.red.out u τ = some v →
      SameBut u.1 v.1 →
      onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
        (fun s => (z, s)) (k3K 24 false) u →
      h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT 24 3 "objects") (z, v.1) = true := by
  intro q hq b' hb' hmask hmerge B' hB z u τ v hy hsb hu hr hf
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape 24 false b' hb'
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full 24 (by omega)
  have hsh : 2 + shift sub = 3 := hpc.symm.trans k03_piece_head
  have hruns := k03_runs_calls h 24 (by omega) sub hs'
  rw [hsh] at hruns
  obtain ⟨lk, hRd, hfind, hfindG⟩ := k03_hfind2 h 24 (by omega)
  exact objIn_pc (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape hb'
    (K.planOk 24 (by omega) false b' hb') (K.back 24 (by omega) false q hq) rfl hpcX
    (k03_look_head h) (k03_shape_head h) (k03_onIn_calls h (by omega) (k03_look_head h) hpcX)
    hruns k03_atS2_calls hRd k03_hpass k03_hsame hfind hfindG hmask hmerge B' hB z u v hu hr hf
    ⟨τ, hy⟩ hsb

end P5J

#print axioms P5J.runsOf_calls
#print axioms P5J.k03_runs_calls
#print axioms P5J.k03_onIn_calls
#print axioms P5J.k03_hsame
#print axioms P5J.k03_hfind2
#print axioms P5J.k03_objIn_calls
#print axioms P5J.k03_shape_head
#print axioms P5J.k03_objIn_head
