-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsJoinIt.lean: the lookup on the digits of a segment's approximate
range proof: THE PREMISE hJoinIt OF hForms_dig_mgAll (MgAt/K3DigitsFormsJoin.lean: «the composed
public test at formsIn l (joinAt sub) "join" holds behind an accept of the seated piece», not at a
layers' segment), IN ITS OWN TEXT, UNDER THE FIELD's OWN FENCED PREMISES: AT AN ATTENTION SEGMENT BY
join_kept_dig_att (MgAt/K3DigitsFormsJoinAtt.lean), with «an attention segment is open» lifted off
the promise's book-keeping (digStandAt_full, here_att_of_stand: MgAt/K3DigitsPlanesIt.lean); AT THE
OUTPUT HEAD's SEGMENT IT STAYS A PREMISE. Joinings. NO RESULT ON THE PROTOCOL.

Main names.
  hJoinIt_dig: THE END.
  digOwed_join: digOwed_planes_free (MgAt/K3DigitsPlanesHead.lean) with hJoinIt struck for what
    hJoinIt_dig asks.
WHAT IS LEFT OF "join". A TERM, AT ATTENTION: hrawJ (what lk states under "join" at the caller's
piece is the lookup's run at the attention kind's keys: the conclusion of
K05_join_of_open, Johnson/H2K5R/JoinAtOpen.lean: not imported; no payer has typechecked here). AT
THE OUTPUT HEAD's SEGMENT, UNDER THE PREMISES: hJoinHead (the item itself): NOBODY PAYS IT.
(Where this and lean/THEOREM.md differ, the page
holds.)
OBJECT. One term of the type Meaning; the kind's ledger.
Used by K03JoinItAttAt.lean (Johnson/P5J/).
LETTERS. Those of digOwed_planes_free.


Compiled with the whole library.


Limits. A rule over letters.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesHead
import Johnson.Desc.Sound.MgAt.K3DigitsFormsJoinAtt

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
open VerifiableInference.Desc.K3 (planesRun joinRun)
open VerifiableInference.Desc.First.Att.P (readersOfO keysOfO)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT

/-- **hJoinIt.** -/
theorem hJoinIt_dig (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl))
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (hback : q.back = []) (hlinks : Dm.links = linksFull)
    (lk : Desc.Link Desc.First.S Desc.Claim) (hlk : Dm.lk l = some lk)
    (hrawJ : sub = .attention → ∃ A : Attention.Plan,
      (statesOfLink lk 2).find? (fun y => y.1 == "join") =
        some ("join", joinRun (Desc.K3.seatCalls K3Lot.ofForm) (keysOfO A)))
    (hJoinHead : sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (joinAt sub) "join") (z, v.1) = true) :
    sub ≠ .layers → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (joinAt sub) "join") (z, v.1) = true := by
  intro hnl B' hN z u τ v hout T DL hu hR hun
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
  cases sub' with
  | layers => exact absurd rfl hnl
  | attention =>
    obtain ⟨w, hatt⟩ := here_att_of_stand hSt
    obtain ⟨A, hJ⟩ := hrawJ rfl
    have mJ : Pub.formsIn l 2 "join" ∈ keptDigits l .attention := by simp [keptDigits]
    exact join_kept_dig_att Dm Mg lk (K3Lot.readersAt X) codes shape (IM.k3Place l true) b'
      K3Lot.ofForm hb hOk rfl hpc hlinks hsub hlk K3Lot.ofForm atS2_calls_ofForm z u.1 v.1 _ cols hd
      hF hS (notHead_of_piece (hpc.symm.trans hpcT)) A hatt hJ (hfront _ (hkept _ mJ))
  | head => exact hJoinHead rfl B' hN z u τ v hout T DL hu hR hun

/-- **INTO THE LEDGER's OWN STRUCTURE, hJoinIt STRUCK.** -/
theorem digOwed_join (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
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
    (hrawJ : sub = .attention → ∃ A : Attention.Plan,
      (statesOfLink lk 2).find? (fun y => y.1 == "join") =
        some ("join", joinRun (Desc.K3.seatCalls K3Lot.ofForm) (keysOfO A)))
    (hJoinHead : sub = .head → ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        (mgAll Dm Mg).pub (.formsIn l (joinAt sub) "join") (z, v.1) = true) :
    DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch K3Lot.ofForm Dm.ms (IM.k3Place l true)
      (MgAt.nextOf l true) (k3K l true) l sub x tl smp q b' told :=
  digOwed_planes_free Dm Mg Rch codes shape hM hl hsub hx smp q b' hb hOk hback told hbf hn hbaseS
    hlinks hBase hPb rides hSome hSent hFits hB pr H lk hrun hah hlink pass hpass hfind hLive
    hGroups hLink hNext hOwn hSeats hShapes hns hnS hTests h6 hlk hpos hrawO hrawG hsame hfO hfG
    hfits hOwnIt lm rd hrawP hrdA hrdH
    (hJoinIt_dig Dm Mg Rch codes shape hM hl hsub hx q b' hb hOk hback hlinks lk hlk hrawJ
      hJoinHead)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hJoinIt_dig
#print axioms VerifiableInference.OnPublicFiles.digOwed_join
