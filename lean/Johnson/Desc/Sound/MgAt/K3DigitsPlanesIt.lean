-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean: the lookup on the digits of a segment's approximate
range proof: THE PREMISE hPlanesIt OF hForms_dig_mgAll (MgAt/K3DigitsFormsJoin.lean: «the composed
public test at formsIn l (2 + shift sub) "planes" holds behind an accept of the seated piece», not
at a layers' segment), IN ITS OWN TEXT, UNDER THE FIELD's OWN FENCED PREMISES: planes_kept_dig_att,
planes_kept_dig_head (MgAt/K3DigitsFormsPlanes.lean) with what they ask of the state in front LIFTED
OFF THE PROMISE. Joinings and four evaluations by the kernel. NO RESULT ON THE PROTOCOL.

Main names.
  THE LIFTS. here_att_of_stand, here_head_of_stand with digStandAt_full (by the kernel, at all 25:
    the table's book-keeping says at the digits' place «a segment of that sort is open»;
    digStandAt_control: A NEGATIVE TEST): which sort of segment is open · planesFront_mgMore (by the
    kernel, at all 25: the calls' item lookOut is open or tied in front of the digits' place, and
    leftOn is among the public items open there; planesFront_control: A NEGATIVE TEST) with the
    lookups' layer's readers (K3At.lookOut, K3At.pLeftOn at k3At_mgAll): the calls' test behind and
    the sentence at leftOn.
  pieceAt_calls, notHead_of_piece: the calls' piece and «not the output head's segment» off the
    digits' piece.
  hPlanesIt_dig: THE END.
  digOwed_planes: digOwed_items with hPlanesIt struck for what hPlanesIt_dig asks.
WHAT IS LEFT, BOOKED. TERMS: hrawP (what lk states under "planes" at the calls' piece is the
lookup's own run at the calling kind's readers rd: the shape of k03_planes_raw) · hrdA, hrdH (rd is
the attention kind's, the output head's kind's reader: K3Lot.readersAt's two arms). AT THE OUTPUT
HEAD's SEGMENT, UNDER THE PREMISES: hrHead (the run itself answers at the state in front): NOBODY
PAYS IT.
OBJECT. One term of the type Meaning; functions with code of the table of joints at closed lists.
Its small lemmas and evaluations are used by K3DigitsPlanesHead.lean (Johnson/Desc/Sound/MgAt/)
and others; hPlanesIt_dig by K3DigitsPlanesFound.lean alone; digOwed_planes by no other file.
LETTERS. Those of digOwed_items; lm, rd.


Compiled with the whole library.


Limits. A rule over letters. The closed list mgMore of the build apart; the full size's lists.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsFormsJoin
import Johnson.Desc.Sound.MgAt.K3DigitsFormsPlanes

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
  pubRowM pubOfItems stepOpen openSets start sampledIn bookFit saysNone standOf standAt)
open VerifiableInference.Desc.K9 (readerOf readersOfLink statesOfLink LinkHoles holesAt)
open VerifiableInference.Desc.K3 (planesRun)
open VerifiableInference.Desc.First.Att.P (readersOfO)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- The calls' piece off the digits'. -/
theorem pieceAt_calls (X : Verify.Public) (l : ℕ) :
    Desc.K3.pieceAt X l false + 5 = Desc.K3.pieceAt X l true := by
  unfold Desc.K3.pieceAt
  split <;> rfl

/-- Not the output head's segment. -/
theorem notHead_of_piece {X : Verify.Public} {l : ℕ} (h : Desc.K3.pieceAt X l true = 7) :
    (l == headLink X) = false := by
  unfold Desc.K3.pieceAt at h
  cases hh : Desc.K3.isHead X l with
  | true =>
    rw [hh] at h
    cases h
  | false => exact hh

/-- The table's book-keeping at the digits' place of one segment. -/
def digStandRowB (l : ℕ) : Bool :=
  decide (standAt linksFull (IM.k3Place l true) = .link ((linksFull[l]?).getD .layers))

set_option maxRecDepth 100000 in
theorem digStandAt_full : (List.range 25).all digStandRowB = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **A negative test.** -/
theorem digStandAt_control :
    decide (standAt linksFull (IM.k3Place 0 true) = .link .attention) = false := by
  decide +kernel

/-- The two items on the lookup on the calls, in front of the digits' place of one segment. -/
def planesFrontRowB (M : More) (l : ℕ) : Bool :=
  (frontDig M l).contains (.lookOut l (IM.k3Place l false).piece) &&
    ((pubSets M linksFull PS)[k3K l true]?.getD []).contains (.leftOn l)

set_option maxRecDepth 1000000 in
theorem planesFront_mgMore : (List.range 25).all (planesFrontRowB mgMore) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test.** -/
theorem planesFront_control :
    (frontDig mgMore 0).contains (.lookOut 1 (IM.k3Place 1 false).piece) = false := by
  decide +kernel

theorem here_att_of_stand {s : Desc.First.S} (h : standOf s = .link .attention) :
    ∃ w, s.here = .att w := by
  unfold standOf at h
  cases hh : s.here with
  | att w => exact ⟨w, rfl⟩
  | between => rw [hh] at h; cases h
  | lay _ => rw [hh] at h; cases h
  | fin _ => rw [hh] at h; cases h
  | mem _ => rw [hh] at h; cases h
  | head _ =>
    rw [hh] at h
    have h' : (if s.inLink then Desc.First.Stand.link ModelPart.head else .headFront) =
        .link .attention := h
    split at h' <;> cases h'

theorem here_head_of_stand {s : Desc.First.S} (h : standOf s = .link .head) :
    ∃ o, s.here = .head o := by
  unfold standOf at h
  cases hh : s.here with
  | head o => exact ⟨o, rfl⟩
  | between => rw [hh] at h; cases h
  | lay _ => rw [hh] at h; cases h
  | att _ => rw [hh] at h; cases h
  | fin _ => rw [hh] at h; cases h
  | mem _ => rw [hh] at h; cases h

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **hPlanesIt.** -/
theorem hPlanesIt_dig (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl))
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (hback : q.back = []) (hlinks : Dm.links = linksFull)
    (lk : Desc.Link Desc.First.S Desc.Claim) (hlk : Dm.lk l = some lk) (lm : ℕ)
    (rd : Desc.K3.Readers Desc.First.S)
    (hrawP : (statesOfLink lk (1 + shift sub)).find? (fun y => y.1 == "planes") =
      some ("planes", planesRun (Desc.K3.seatCalls K3Lot.ofForm) lm rd))
    (hrdA : sub = .attention → ∃ A, rd = readersOfO A)
    (hrdH : sub = .head → ∃ iU3, rd = callerReaders (planesAt iU3))
    (hrHead : sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (readerOf (statesOfLink lk) (1 + shift sub) "planes" u.1).isSome = true) :
    sub ≠ .layers → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, v.1) = true := by
  intro hnl B' hN z u τ v hout T DL hu hR hun
  have hu0 := hu
  obtain ⟨hShape, hQ⟩ : Desc.First.shapeAt linksFull PS[k3K l true]? u.1 = true ∧
      ∀ p ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k3K l true]?.getD [],
        (mgAll Dm Mg).pubP p (z, u.1) := by
    obtain ⟨-, hm | ⟨h1, -, -, h4⟩⟩ := hu0
    · exact absurd hun hm
    · simp only [Bool.and_eq_true] at h1
      exact ⟨h1.1.1.1.1.1, h4⟩
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
  have mPl : Pub.formsIn l (2 + shift sub') "planes" ∈ keptDigits l sub' := by
    cases sub' with
    | layers => exact absurd rfl hnl
    | attention =>
      show Pub.formsIn l 2 "planes" ∈ keptDigits l .attention
      simp [keptDigits]
    | head =>
      show Pub.formsIn l 3 "planes" ∈ keptDigits l .head
      simp [keptDigits]
  have ht := hfront _ (hkept _ mPl)
  -- which sort of segment is open
  have hSt : standOf u.1 = .link sub' := by
    have h0 := List.all_eq_true.1 digStandAt_full l (List.mem_range.2 hl)
    unfold digStandRowB at h0
    have h1 := of_decide_eq_true h0
    rw [hsub, Option.getD_some] at h1
    rw [K3Lot.k03_at_full l hl true] at hShape
    unfold Desc.First.shapeAt at hShape
    simp only [Bool.and_eq_true, beq_iff_eq] at hShape
    rw [hShape.1.1, h1]
  -- the two items on the lookup on the calls
  have hFr := List.all_eq_true.1 planesFront_mgMore l (List.mem_range.2 hl)
  unfold planesFrontRowB at hFr
  rw [Bool.and_eq_true] at hFr
  have m1 : Pub.lookOut l (IM.k3Place l false).piece ∈ frontDig mgMore l := by
    simpa using hFr.1
  have m2 : Pub.leftOn l ∈ (pubSets mgMore linksFull PS)[k3K l true]?.getD [] := by
    simpa using hFr.2
  have ePc : (IM.k3Place l false).piece = Desc.K3.pieceAt X l false := by
    have a1 := pieceAt_calls X l
    obtain ⟨s2, hs2, a2, -⟩ := K3Lot.k03_sub_full l hl
    obtain rfl : s2 = sub' := Option.some.inj (hs2.symm.trans hsub)
    omega
  have hLfAt : k3LeftOnItemAt X l u.1 := by
    have h0 := hQ _ (by rw [eM]; exact m2)
    rw [(k3At_mgAll Dm Mg).pLeftOn] at h0
    exact h0
  obtain ⟨pc, hpcAt, hLf⟩ := hLfAt
  have hO : Desc.K3.k3OnOut pc u.1 = true := by
    have h0 := hfront _ m1
    rw [ePc, (k3At_mgAll Dm Mg).lookOut] at h0
    unfold k3OnOutAt at h0
    rw [hpcAt] at h0
    exact h0
  have hdc : pc.digits = false := by
    unfold placeAt at hpcAt
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hpcAt
    rfl
  cases sub' with
  | layers => exact absurd rfl hnl
  | attention =>
    obtain ⟨w, hatt⟩ := here_att_of_stand hSt
    obtain ⟨A, rfl⟩ := hrdA rfl
    exact planes_kept_dig_att Dm Mg lk (K3Lot.readersAt X) codes shape (IM.k3Place l true) b'
      K3Lot.ofForm hb hOk rfl hpc hlinks hsub hlk atS2_calls_ofForm z u.1 v.1 _ cols hd hF hS rfl
      hnl (notHead_of_piece (hpc.symm.trans hpcT)) lm A hatt hdc hO hLf hrawP ht
  | head =>
    obtain ⟨o, hhead⟩ := here_head_of_stand hSt
    obtain ⟨iU3, rfl⟩ := hrdH rfl
    exact planes_kept_dig_head Dm Mg lk (K3Lot.readersAt X) codes shape (IM.k3Place l true) b'
      K3Lot.ofForm hb hOk rfl hpc hlinks hsub hlk atS2_calls_ofForm z u.1 v.1 _ cols hd hF hS rfl
      hnl lm iU3 hhead hdc hO hLf (hrHead rfl B' hN z u τ v hout T DL hu hR hun) hrawP ht

/-- **INTO THE LEDGER's OWN STRUCTURE, hPlanesIt STRUCK.** -/
theorem digOwed_planes (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
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
    (hOwnIt : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
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
    (hrHead : sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (readerOf (statesOfLink lk) (1 + shift sub) "planes" u.1).isSome = true)
    (hJoinIt : sub ≠ .layers → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (joinAt sub) "join") (z, v.1) = true) :
    DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch K3Lot.ofForm Dm.ms (IM.k3Place l true)
      (MgAt.nextOf l true) (k3K l true) l sub x tl smp q b' told :=
  digOwed_items Dm Mg Rch codes shape hM hl hsub hx smp q b' hb hOk hback told hbf hn hbaseS hlinks
    hBase hPb rides hSome hSent hFits hB pr H lk hrun hah hlink pass hpass hfind hLive hGroups hLink
    hNext hOwn hSeats hShapes hns hnS hTests h6 hlk hpos hrawO hrawG hsame hfO hfG hfits hOwnIt
    (hPlanesIt_dig Dm Mg Rch codes shape hM hl hsub hx q b' hb hOk hback hlinks lk hlk lm rd hrawP
      hrdA hrdH hrHead)
    hJoinIt

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.pieceAt_calls
#print axioms VerifiableInference.OnPublicFiles.notHead_of_piece
#print axioms VerifiableInference.OnPublicFiles.digStandAt_full
#print axioms VerifiableInference.OnPublicFiles.digStandAt_control
#print axioms VerifiableInference.OnPublicFiles.planesFront_mgMore
#print axioms VerifiableInference.OnPublicFiles.planesFront_control
#print axioms VerifiableInference.OnPublicFiles.here_att_of_stand
#print axioms VerifiableInference.OnPublicFiles.here_head_of_stand
#print axioms VerifiableInference.OnPublicFiles.hPlanesIt_dig
#print axioms VerifiableInference.OnPublicFiles.digOwed_planes
