-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
NOT TRIED FOR EMPTINESS: no place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsHeadItems.lean: the lookup on the digits of the output head's
segment's approximate range proof: THE TWO ITEMS THAT WERE LEFT AT THAT SEGMENT: formsIn l 4 "own"
(the output head's kind's runs "norm", "policy", "logits") AND formsIn l 4 "join": THE COMPOSED
PUBLIC TESTS HOLD BEHIND AN ACCEPT OF THE SEATED PIECE, IN THE ITEMS' OWN FENCED TEXTS (hJoinHead of
hJoinIt_dig, MgAt/K3DigitsJoinIt.lean; hOwnElse of hOwnIt_dig, MgAt/K3DigitsOwnAtt.lean, at that
sort): by own_formsIn_pass_seat, join_formsIn_pass_seat (Johnson/Top/H/Keep/HeadOwnAtSeat.lean).
THEY CROSS THE STEP WITHOUT A ROUND. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  own_kept_dig_head, join_kept_dig_head: at the whole seated sub-protocol's decide: K3Pass by
    k3_digits_step_pass · SamePlanes by k3_digits_step_samePlanes · Alike by k3_digits_step_alike
    (K3DigitsHeadAlike.lean) · what was heard at the calls' seat by k3_digits_step_leaves · the
    debts by k3_digits_step_hob (MgAt/K3DigitsPlanesHead.lean).
  hOwnHead_dig, hJoinHead_dig: under the field's own hands; «the output head's segment is open» off
    the promise's book-keeping.
  digOwed_head: digOwed_own with hJoinHead struck and hOwnElse narrowed to a layers' segment
    (hOwnLay).
WHAT IS LEFT AT THE OUTPUT HEAD's SEGMENT. TERMS, in another house's shapes: K (K6States: what the
seated link states under the four names lies under that kind's own runs) · hBo, hBj (the way back
under the guard on the reply: the two fields of that house's K6Back, by another pen's reading) ·
hAc. A FACT ON THE STATE IN FRONT, UNDER THE HANDS: hReady (K6Ready at what the state shows): NO
PAYER HAS TYPECHECKED AGAINST ANY OF THESE HERE.
OBJECT. One term of the type Meaning; the kind's ledger.
USER. Nobody yet. Meant: K3LeftR.dig.
LETTERS. Those of digOwed_own; hH, iU3, lkN, pieceN, par.





Limits. A rule over letters. "own" at a layers' segment stays a premise.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.HeadOwnAtSeat
import Johnson.Desc.First.Look.K3DigitsHeadAlike
import Johnson.Desc.Sound.MgAt.K3DigitsOwnAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub More Meaning shift joinAt pubFit pubSets pubStep
  pubRowM pubOfItems stepOpen openSets start sampledIn bookFit saysNone standOf standAt runsOf)
open VerifiableInference.Desc.K9 (readerOf readersOfLink statesOfLink LinkHoles holesAt)
open VerifiableInference.Desc.K3 (planesRun joinRun)
open VerifiableInference.Desc.First.Att.P (readersOfO keysOfO runsN)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders seatAt asClaim callerKeys)
open VerifiableInference.Desc.Kinds.Head.Law (K6States K6Ready Sees)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **THE KEPT "own" AT THE OUTPUT HEAD's SEGMENT.** -/
theorem own_kept_dig_head (lk : Desc.Link Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (claim : Aff → Desc.Claim)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) (hsub : linksFull[l]? = some .head)
    (hlk : Dm.lk l = some lk)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) (hm : Desc.K3.isHead X l = true)
    {o : Desc.First.HeadOwn} (hhead : s.here = .head o)
    (hH : OnBytes.Model.Head.Shape) (iU3 lkN pieceN : ℕ) (par : Desc.Kinds.Head.Par)
    (K : K6States hH iU3 par lkN pieceN (statesOfLink lk) 3)
    (hReady : ∀ z' U, Sees s z' U → K6Ready hH iU3 par z' U)
    (hBo : ∀ name run run',
      (statesOfLink lk 3).find? (fun r => r.1 == name) = some (name, run) →
      (Desc.Kinds.Head.kind asClaim (seatAt hH iU3) lkN pieceN par).claims.lookup name =
        some run' →
      ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
    (ht : (mgAll Dm Mg).pub (.formsIn l 4 "own") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l 4 "own") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  have A := k3_digits_step_samePlanes claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  have al := k3_digits_step_alike claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hhead Q
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [runs_head.2.2.2.1] at hpm
  rw [rd_holesAt Dm hlk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  rcases hpm with rfl | rfl | rfl
  · exact ⟨(by decide : ("norm" == "K8.equations") = false), fun hin =>
      own_formsIn_pass_seat X (headLink X) l hm lk 3 _ hH iU3 lkN pieceN par Q A al K hReady hBo
        (Or.inl rfl) hin⟩
  · exact ⟨(by decide : ("policy" == "K8.equations") = false), fun hin =>
      own_formsIn_pass_seat X (headLink X) l hm lk 3 _ hH iU3 lkN pieceN par Q A al K hReady hBo
        (Or.inr (Or.inl rfl)) hin⟩
  · exact ⟨(by decide : ("logits" == "K8.equations") = false), fun hin =>
      own_formsIn_pass_seat X (headLink X) l hm lk 3 _ hH iU3 lkN pieceN par Q A al K hReady hBo
        (Or.inr (Or.inr rfl)) hin⟩

/-- **THE KEPT "join" AT THE OUTPUT HEAD's SEGMENT.** -/
theorem join_kept_dig_head (lk : Desc.Link Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (claim : Aff → Desc.Claim)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) (hsub : linksFull[l]? = some .head)
    (hlk : Dm.lk l = some lk)
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) (hm : Desc.K3.isHead X l = true)
    {o : Desc.First.HeadOwn} (hhead : s.here = .head o)
    (hH : OnBytes.Model.Head.Shape) (iU3 lkN pieceN : ℕ) (par : Desc.Kinds.Head.Par)
    (K : K6States hH iU3 par lkN pieceN (statesOfLink lk) 3)
    (hReady : ∀ z' U, Sees s z' U → K6Ready hH iU3 par z' U)
    (hBj : ∀ run,
      (statesOfLink lk 3).find? (fun r => r.1 == "join") = some ("join", run) →
      ∀ k t y, joinRun (Desc.K3.seatCalls asClaim) (callerKeys par (seatAt hH iU3)) k t = .ok y →
        y.2.out.reply = t.out.reply → run k t = .ok y)
    (hAc : AtS2 (Desc.K3.seatCalls asClaim))
    (ht : (mgAll Dm Mg).pub (.formsIn l 4 "join") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l 4 "join") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  have A := k3_digits_step_samePlanes claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  have al := k3_digits_step_alike claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hhead Q
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [runs_head.2.2.1] at hpm
  rw [rd_holesAt Dm hlk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  obtain rfl := hpm
  exact ⟨(by decide : ("join" == "K8.equations") = false), fun hin =>
    join_formsIn_pass_seat X (headLink X) l hm lk 3 _ hH iU3 lkN pieceN par Q A al K hReady hBj hAc
      hLk (k3_digits_step_hob claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd Q) hin⟩

/-- **"own" AT THE OUTPUT HEAD's SEGMENT, UNDER THE FIELD's OWN HANDS.** -/
theorem hOwnHead_dig (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl))
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (hback : q.back = []) (hlinks : Dm.links = linksFull)
    (lk : Desc.Link Desc.First.S Desc.Claim) (hlk : Dm.lk l = some lk)
    (hH : OnBytes.Model.Head.Shape) (iU3 lkN pieceN : ℕ) (par : Desc.Kinds.Head.Par)
    (K : sub = .head → K6States hH iU3 par lkN pieceN (statesOfLink lk) 3)
    (hBo : sub = .head → ∀ name run run',
      (statesOfLink lk 3).find? (fun r => r.1 == name) = some (name, run) →
      (Desc.Kinds.Head.kind asClaim (seatAt hH iU3) lkN pieceN par).claims.lookup name =
        some run' →
      ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
    (hBj : sub = .head → ∀ run,
      (statesOfLink lk 3).find? (fun r => r.1 == "join") = some ("join", run) →
      ∀ k t y, joinRun (Desc.K3.seatCalls asClaim) (callerKeys par (seatAt hH iU3)) k t = .ok y →
        y.2.out.reply = t.out.reply → run k t = .ok y)
    (hAc : AtS2 (Desc.K3.seatCalls asClaim))
    (hReady : sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        ∀ z' U, Sees u.1 z' U → K6Ready hH iU3 par z' U) :
    sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (3 + shift sub) "own") (z, v.1) = true := by
  intro hsH B' hN z u τ v hout T DL hu hR hun
  have hu0 := hu
  have hShape : Desc.First.shapeAt linksFull PS[k3K l true]? u.1 = true := by
    obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := hu0
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      exact h1.1.1.1.1.1
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l true b' hb
  obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have hlook : lookAt X l true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  obtain ⟨-, -, -, cols, hd0⟩ := piece_hears_below
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT) B' rfl hback u τ v hout
  have hd := hN.1.2 _ _ _ _ hd0
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  have hfront : ∀ p ∈ frontDig mgMore l, (mgAll Dm Mg).pub p (z, u.1) = true := by
    obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := hu
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      have hp := h1.1.2
      unfold Desc.First.pubHeld at hp
      rw [List.all_eq_true, eM] at hp
      exact hp
  obtain ⟨-, hkept⟩ := digits_sorted hl hsub
  have hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 = true := by
    have hOpen := digits_lookIn_open (mgAll Dm Mg).more linksFull PS (k3K l true)
      (IM.k3Place l true) l sub' (hfit_mgAll Dm Mg hM) (K3Lot.k03_at_full l hl true) rfl hsub hpcT
      (.lookIn l (7 + shift sub')) (by simp)
    rw [eM] at hOpen
    have hp := hfront _ (List.mem_append_left _ hOpen)
    rw [hpcT.symm.trans hpc] at hp
    exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l true hlook z u.1 hp)
  obtain ⟨F, hF, hS, -⟩ := k3OnIn_ledger hIn
  have hSt : standOf u.1 = .link sub' := by
    have h0 := List.all_eq_true.1 digStandAt_full l (List.mem_range.2 hl)
    unfold digStandRowB at h0
    have h1 := of_decide_eq_true h0
    rw [hsub, Option.getD_some] at h1
    rw [K3Lot.k03_at_full l hl true] at hShape
    unfold Desc.First.shapeAt at hShape
    simp only [Bool.and_eq_true, beq_iff_eq] at hShape
    rw [hShape.1.1, h1]
  subst hsH
  obtain ⟨o, hhead⟩ := here_head_of_stand hSt
  have mO : Pub.formsIn l 4 "own" ∈ keptDigits l .head := by simp [keptDigits]
  exact own_kept_dig_head Dm Mg lk (K3Lot.readersAt X) codes shape (IM.k3Place l true) b'
    K3Lot.ofForm hb hOk rfl hpc hlinks hsub hlk z u.1 v.1 _ cols hd hF hS
    (isHead_of_piece (hpc.symm.trans hpcT)) hhead hH iU3 lkN pieceN par (K rfl)
    (hReady rfl B' hN z u τ v hout T DL hu hR hun) (hBo rfl) (hfront _ (hkept _ mO))

/-- **"join" AT THE OUTPUT HEAD's SEGMENT, UNDER THE FIELD's OWN HANDS.** -/
theorem hJoinHead_dig (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl))
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (hback : q.back = []) (hlinks : Dm.links = linksFull)
    (lk : Desc.Link Desc.First.S Desc.Claim) (hlk : Dm.lk l = some lk)
    (hH : OnBytes.Model.Head.Shape) (iU3 lkN pieceN : ℕ) (par : Desc.Kinds.Head.Par)
    (K : sub = .head → K6States hH iU3 par lkN pieceN (statesOfLink lk) 3)
    (hBo : sub = .head → ∀ name run run',
      (statesOfLink lk 3).find? (fun r => r.1 == name) = some (name, run) →
      (Desc.Kinds.Head.kind asClaim (seatAt hH iU3) lkN pieceN par).claims.lookup name =
        some run' →
      ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
    (hBj : sub = .head → ∀ run,
      (statesOfLink lk 3).find? (fun r => r.1 == "join") = some ("join", run) →
      ∀ k t y, joinRun (Desc.K3.seatCalls asClaim) (callerKeys par (seatAt hH iU3)) k t = .ok y →
        y.2.out.reply = t.out.reply → run k t = .ok y)
    (hAc : AtS2 (Desc.K3.seatCalls asClaim))
    (hReady : sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        ∀ z' U, Sees u.1 z' U → K6Ready hH iU3 par z' U) :
    sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (joinAt sub) "join") (z, v.1) = true := by
  intro hsH B' hN z u τ v hout T DL hu hR hun
  have hu0 := hu
  have hShape : Desc.First.shapeAt linksFull PS[k3K l true]? u.1 = true := by
    obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := hu0
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      exact h1.1.1.1.1.1
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l true b' hb
  obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have hlook : lookAt X l true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  obtain ⟨-, -, -, cols, hd0⟩ := piece_hears_below
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT) B' rfl hback u τ v hout
  have hd := hN.1.2 _ _ _ _ hd0
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  have hfront : ∀ p ∈ frontDig mgMore l, (mgAll Dm Mg).pub p (z, u.1) = true := by
    obtain ⟨-, hm | ⟨h1, -, -, -⟩⟩ := hu
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      have hp := h1.1.2
      unfold Desc.First.pubHeld at hp
      rw [List.all_eq_true, eM] at hp
      exact hp
  obtain ⟨-, hkept⟩ := digits_sorted hl hsub
  have hIn : Desc.K3.k3OnIn
      (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 = true := by
    have hOpen := digits_lookIn_open (mgAll Dm Mg).more linksFull PS (k3K l true)
      (IM.k3Place l true) l sub' (hfit_mgAll Dm Mg hM) (K3Lot.k03_at_full l hl true) rfl hsub hpcT
      (.lookIn l (7 + shift sub')) (by simp)
    rw [eM] at hOpen
    have hp := hfront _ (List.mem_append_left _ hOpen)
    rw [hpcT.symm.trans hpc] at hp
    exact k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l true hlook z u.1 hp)
  obtain ⟨F, hF, hS, -⟩ := k3OnIn_ledger hIn
  have hSt : standOf u.1 = .link sub' := by
    have h0 := List.all_eq_true.1 digStandAt_full l (List.mem_range.2 hl)
    unfold digStandRowB at h0
    have h1 := of_decide_eq_true h0
    rw [hsub, Option.getD_some] at h1
    rw [K3Lot.k03_at_full l hl true] at hShape
    unfold Desc.First.shapeAt at hShape
    simp only [Bool.and_eq_true, beq_iff_eq] at hShape
    rw [hShape.1.1, h1]
  subst hsH
  obtain ⟨o, hhead⟩ := here_head_of_stand hSt
  have mJ : Pub.formsIn l 4 "join" ∈ keptDigits l .head := by simp [keptDigits]
  exact join_kept_dig_head Dm Mg lk (K3Lot.readersAt X) codes shape (IM.k3Place l true) b'
    K3Lot.ofForm hb hOk rfl hpc hlinks hsub hlk z u.1 v.1 _ cols hd hF hS
    (isHead_of_piece (hpc.symm.trans hpcT)) hhead hH iU3 lkN pieceN par (K rfl)
    (hReady rfl B' hN z u τ v hout T DL hu hR hun) (hBj rfl) hAc (hfront _ (hkept _ mJ))

/-- **INTO THE LEDGER's OWN STRUCTURE: hJoinIt WHOLE; hOwnIt BUT FOR THE LAYERS.** -/
theorem digOwed_head (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl))
    (smp : Desc.First.S → (i : Fin (digList x Dm.sent Dm.l3.rad).length) →
      Option ((digSg x Dm.sent Dm.l3.rad).om i).Smp)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (hback : q.back = []) (told : List (List Desc.Oracle))
    (hbf : bookFit Dm.N PS told = true)
    (hn : told[(k3K l true)]? = some [])
    (hbaseS : ∀ e ∈ sampledIn Dm.N
        ((openSets linksFull PS (start linksFull))[(k3K l true)]?.getD []),
      e.1 < q.base)
    (hlinks : Dm.links = linksFull)
    (hBase : ∀ r (z : P) (s s' : Desc.First.S), Mg.pub r (z, s') = Mg.pub r (z, s))
    (hPb : ∀ r c, (saysNone r).isSome = true → Mg.pubP r c)
    (rides : RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b')
    (hSome : ∀ i, ∃ y ∈ Dm.ms,
      Alike y ⟨digSending x Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1), i⟩)
    (hSent : ∀ i : Fin (digList x Dm.sent Dm.l3.rad).length,
      ∃ t ∈ [2, 0, 1], Dm.l3.seat x.link true i.1 ∈ Dm.N.sent l t)
    (hFits : Desc.Sound.SeatFits Dm.G Dm.sent.codes (digList x Dm.sent Dm.l3.rad)
      fun j => Dm.l3.seat x.link true j.1)
    (hB : maskB Dm.sent (digList x Dm.sent Dm.l3.rad) x.link x.arrays.ns = true)
    (pr : ℕ) (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
    (hrun : (pr, "objects") ∈ Dm.runs l (7 + shift sub) "objects")
    (hah : Dm.ah pr "objects" = false) (hlink : Dm.Rd l = readersOfLink H lk)
    (pass : Desc.First.S → Desc.First.S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatDigits K3Lot.ofForm)))
    {nos : Array ℕ} {n : ℕ} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    (hLive : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hLink : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.link = x.link)
    (hNext : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.next = .laterOrClose)
    (hOwn : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.own = nos)
    (hSeats : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → Desc.K12.Door.atFirstShapes M a.1 = true)
    (hns : (Dm.built[l]?).map (·.ns) = some n)
    (hnS : n ≤ x.arrays.ns)
    (hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
      (Dm.N.group l) (Dm.l3.seat x.link true) = true)
    (h6 : oneShapeB Dm.ms = true)
    (hlk : Dm.lk l = some lk) (hpos : 0 < x.arrays.ns)
    (hrawO : (statesOfLink lk (1 + shift sub)).find? (fun y => y.1 == "objects") =
      some ("objects", objectsRun (Desc.K3.seatCalls K3Lot.ofForm)))
    (hrawG : (statesOfLink lk (1 + shift sub)).find? (fun y => y.1 == "guests") =
      some ("guests", guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim))))
    (hsame : ∀ t, pass t t)
    (hfO : ∃ n r, (statesOfLink lk (6 + shift sub)).find? (fun y => y.1 == "objects") =
        some (n, r) ∧ RunOver pass r (objectsRun (Desc.K3.seatDigits K3Lot.ofForm)))
    (hfG : ∃ n r, (statesOfLink lk (6 + shift sub)).find? (fun y => y.1 == "guests") =
        some (n, r) ∧
      RunOver pass r (guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim))))
    (hfits : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        Desc.K3.sFvFitsB u.1 = true)
    (hstA : sub = .attention → ∃ A : Attention.Plan, statesOfLink lk 2 = runsN A ∧
      ∀ y ∈ runsN A, y.1 ≠ "join" → ∀ (n : ℕ) (t : Desc.First.S)
        (e : List Desc.Claim × Desc.First.S), y.2 n t = .ok e → e.2 = t)
    (hOwnLay : sub = .layers → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (3 + shift sub) "own") (z, v.1) = true)
    (lm : ℕ) (rd : Desc.K3.Readers Desc.First.S)
    (hrawP : (statesOfLink lk (1 + shift sub)).find? (fun y => y.1 == "planes") =
      some ("planes", planesRun (Desc.K3.seatCalls K3Lot.ofForm) lm rd))
    (hrdA : sub = .attention → ∃ A, rd = readersOfO A)
    (hrdH : sub = .head → ∃ iU3, rd = callerReaders (planesAt iU3))
    (hrawJ : sub = .attention → ∃ A : Attention.Plan,
      (statesOfLink lk 2).find? (fun y => y.1 == "join") =
        some ("join", joinRun (Desc.K3.seatCalls K3Lot.ofForm) (keysOfO A)))
    (hH : OnBytes.Model.Head.Shape) (iU3 lkN pieceN : ℕ) (par : Desc.Kinds.Head.Par)
    (K : sub = .head → K6States hH iU3 par lkN pieceN (statesOfLink lk) 3)
    (hBo : sub = .head → ∀ name run run',
      (statesOfLink lk 3).find? (fun r => r.1 == name) = some (name, run) →
      (Desc.Kinds.Head.kind asClaim (seatAt hH iU3) lkN pieceN par).claims.lookup name =
        some run' →
      ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
    (hBj : sub = .head → ∀ run,
      (statesOfLink lk 3).find? (fun r => r.1 == "join") = some ("join", run) →
      ∀ k t y, joinRun (Desc.K3.seatCalls asClaim) (callerKeys par (seatAt hH iU3)) k t = .ok y →
        y.2.out.reply = t.out.reply → run k t = .ok y)
    (hAc : AtS2 (Desc.K3.seatCalls asClaim))
    (hReady : sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        ∀ z' U, Sees u.1 z' U → K6Ready hH iU3 par z' U) :
    DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch K3Lot.ofForm Dm.ms (IM.k3Place l true)
      (MgAt.nextOf l true) (k3K l true) l sub x tl smp q b' told :=
  digOwed_own Dm Mg Rch codes shape hM hl hsub hx smp q b' hb hOk hback told hbf hn hbaseS
    hlinks hBase hPb rides hSome hSent hFits hB pr H lk hrun hah hlink pass hpass hfind hLive
    hGroups hLink hNext hOwn hSeats hShapes hns hnS hTests h6 hlk hpos hrawO hrawG hsame hfO hfG
    hfits hstA
    (fun hna => by
      cases sub with
      | attention => exact absurd rfl hna
      | layers => exact hOwnLay rfl
      | head =>
        exact hOwnHead_dig Dm Mg Rch codes shape hM hl hsub hx q b' hb hOk hback hlinks lk hlk hH
          iU3 lkN pieceN par K hBo hBj hAc hReady rfl)
    lm rd hrawP hrdA hrdH hrawJ
    (hJoinHead_dig Dm Mg Rch codes shape hM hl hsub hx q b' hb hOk hback hlinks lk hlk hH iU3 lkN
      pieceN par K hBo hBj hAc hReady)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.own_kept_dig_head
#print axioms VerifiableInference.OnPublicFiles.join_kept_dig_head
#print axioms VerifiableInference.OnPublicFiles.hOwnHead_dig
#print axioms VerifiableInference.OnPublicFiles.hJoinHead_dig
#print axioms VerifiableInference.OnPublicFiles.digOwed_head
