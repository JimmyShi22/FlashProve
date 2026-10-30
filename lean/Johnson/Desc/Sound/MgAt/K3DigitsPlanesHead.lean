-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsPlanesHead.lean: the lookup on the digits of a segment's approximate
range proof: hPlanesIt (MgAt/K3DigitsPlanesIt.lean) WITH ITS LAST PREMISE ON A STATE STRUCK: hrHead
(«at the output head's segment the run "planes" itself answers at the state in front»), which nobody
paid: by planes_formsIn_pass_head (Johnson/Top/H/Keep/HeadHoleFwd.lean): there the kept test passes
whichever of the run and the link's second hole answers. IT CROSSES THE STEP WITHOUT A ROUND.
Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  k3_digits_step_hob: a debt that is unpaid behind the WHOLE seated sub-protocol was unpaid in front
    (k3_digits_hob across the lookup's own rounds; the step without a round lays the count of
    planned claims alone: quietAt_ledger).
  planes_kept_dig_head_free: planes_kept_dig_head (MgAt/K3DigitsFormsPlanes.lean) without hr.
  hPlanesIt_dig_free: hPlanesIt_dig without hrHead: its proof laid by program, the output
    head's arm turned.
  digOwed_planes_free: digOwed_planes without hrHead.
WHAT IS LEFT OF "planes". TERMS ALONE: hrawP, hrdA, hrdH (their payer spent: hPlanesIt_dig_found,
MgAt/K3DigitsPlanesFound.lean, which this file imports) · hlk, hlinks, hM · the place's and the
piece's: hl, hsub, hx, hb, hOk, hback.
OBJECT. One term of the type Meaning; Desc.K3.theStated's value at the digits' address.
Used by K3DigitsJoinIt.lean (Johnson/Desc/Sound/MgAt/), K03DigPlanesAt.lean (Johnson/P5J/), 2 more.
LETTERS. Those of digOwed_planes.


Compiled with the whole library.


Limits. A rule over letters.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.HeadHoleFwd
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesFound

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
open VerifiableInference.Desc.K3 (planesRun unpaid)
open VerifiableInference.Desc.First.Att.P (readersOfO)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **A debt that is unpaid behind the whole seated sub-protocol was unpaid in front.** -/
theorem k3_digits_step_hob {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F G : Fork} (Q : K3Pass s s₂ F G) :
    ∀ j, unpaid G j = true → unpaid F j = true := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd
  obtain ⟨G0, Q0⟩ := k3_digits_pass claim a.piece laid sent P' [] s s' _ gs' hyes Q.front Q.sizedF
  have H0 := k3_digits_hob claim a.piece laid sent P' [] s s' _ gs' hyes Q0
  rcases hstep with e | ⟨f, hf, hfs⟩
  · have e1 : s₂.fork? = some G0 := by
      rw [e]
      exact Q0.behind
    obtain rfl : G = G0 := Option.some.inj (Q.behind.symm.trans e1)
    exact H0
  · obtain ⟨F₂, c, hF₂, hG₂, -⟩ := quietAt_ledger X i f hf s' s₂ hfs
    obtain rfl : G0 = F₂ := Option.some.inj (Q0.behind.symm.trans hF₂)
    obtain rfl : G = { G0 with planClaimsF := c } := Option.some.inj (Q.behind.symm.trans hG₂)
    exact fun j hj => H0 j hj

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **AT THE OUTPUT HEAD's SEGMENT, WHOEVER ANSWERS.** -/
theorem planes_kept_dig_head_free (lk : Desc.Link Desc.First.S Desc.Claim)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Desc.Claim)
    (claim : Aff → Desc.Claim)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hlinks : Dm.links = linksFull) {sub : ModelPart} (hsub : linksFull[l]? = some sub)
    (hlk : Dm.lk l = some lk) (hA : AtS2 (Desc.K3.seatCalls claim))
    (z : P) (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂) {F : Fork} (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F) {B₀ : ℕ} (hB₀ : B₀ = 1 + shift sub)
    (hnl : sub ≠ .layers) (hm : Desc.K3.isHead X l = true) (lm iU3 : ℕ)
    {o : Desc.First.HeadOwn} (hhead : s.here = .head o)
    {pc : Desc.First.Look.P} (hdc : pc.digits = false) (hO : Desc.K3.k3OnOut pc s = true)
    (hLf : k3LeftOnItem pc s)
    (hrawP : (statesOfLink lk B₀).find? (fun x => x.1 == "planes") =
      some ("planes", planesRun (Desc.K3.seatCalls claim) lm (callerReaders (planesAt iU3))))
    (ht : (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, s) = true) :
    (mgAll Dm Mg).pub (.formsIn l (2 + shift sub) "planes") (z, s₂) = true := by
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
    hF hS
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd
  refine formsIn_pass_mgAll Dm Mg hlinks hsub z s s₂ (fun p hpm => ?_) ht
  rw [he_planes sub hnl, ← hB₀] at hpm
  rw [rd_holesAt Dm hlk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  obtain rfl := hpm
  exact ⟨(by decide : ("planes" == "K8.equations") = false), fun hin =>
    planes_formsIn_pass_head X (headLink X) l hm lk B₀ _ claim hA Q
      (k3_digits_step_samePlanes claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd) hLk
      (k3_digits_step_hob claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd Q) lm iU3
      (hwin_of_onOut hdc hF hO hLf) (find_eq_of_raw hrawP) hhead hin⟩

/-- **hPlanesIt, WITH NO PREMISE ON WHO ANSWERS AT THE OUTPUT HEAD.** -/
theorem hPlanesIt_dig_free (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
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
    (hrdH : sub = .head → ∃ iU3, rd = callerReaders (planesAt iU3)) :
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
    exact planes_kept_dig_head_free Dm Mg lk (K3Lot.readersAt X) codes shape (IM.k3Place l true) b'
      K3Lot.ofForm hb hOk rfl hpc hlinks hsub hlk atS2_calls_ofForm z u.1 v.1 _ cols hd hF hS rfl
      hnl (isHead_of_piece (hpc.symm.trans hpcT)) lm iU3 hhead hdc hO hLf hrawP ht

/-- **INTO THE LEDGER's OWN STRUCTURE, hPlanesIt STRUCK.** -/
theorem digOwed_planes_free (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
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
    (hPlanesIt_dig_free Dm Mg Rch codes shape hM hl hsub hx q b' hb hOk hback hlinks lk hlk lm rd
      hrawP hrdA hrdH)
    hJoinIt

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_digits_step_hob
#print axioms VerifiableInference.OnPublicFiles.planes_kept_dig_head_free
#print axioms VerifiableInference.OnPublicFiles.hPlanesIt_dig_free
#print axioms VerifiableInference.OnPublicFiles.digOwed_planes_free
