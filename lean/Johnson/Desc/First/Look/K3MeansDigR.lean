-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3MeansDigR.lean: the lookup on the digits of a segment's approximate range
proof: WHAT ONE DIGITS' PLACE ASKS OF THE TABLE OF JOINTS' MEANING IN THE SECOND FORM OF
THE CHAIN OF PROMISES, AS ONE LEAN STRUCTURE: DigMeanR: the premises on N, Mg, Rch and the reader of
samples of k3_digits_seatLawsR (K3DigitsSeatLaws.lean), at the full size's written lists, in the
order and letters of the structure DigMean of the kind's assembly
(Johnson/Desc/First/Look/K3Means.lean: not imported); that it gives SeatLawsR; and
that most of it is paid under K3At. NO RESULT ON THE PROTOCOL.

Main names.
  RidesAtR: the second of SeatLawsR's four, at the full size's written lists.
  DigMeanR: NINETEEN FIELDS. Against DigMean's twenty-one: hAsk, fOrder, fLive are out; ownIn is in;
    fObj is asked at the state behind an accept alone; behind has lost the door's item; Rch k ((z,
    a.1), a.2) stands in hand in ownIn, fObj, behind, rides.
  seatLawsR_of_digMeanR: the plan's premises and DigMeanR give SeatLawsR linksFull PS k q N Mg Rch
    b': one call of k3_digits_seatLawsR.
  digMeanR_of: DigMeanR under K3At X Dn L Mg: of its nineteen fields SIX are paid: fLook, fPl, fKe
    (K3At.lean) · fDig (fDig_part, where Mg.constr at lookDigits is digitsPartK3: K3FillDigits.lean)
    · behind (k3_digits_behind_at: K3DigitsBehind.lean; with inOrder_sameBut, held_sameBut,
    calls_shown, calls_noColl) · hDec (decodes_at_seat); thirteen are handed through under their own
    names.
WHAT THE SIX COST. hK (K3At). The place: hx, hi, hsub, hpcT, hpc, hk. Bools on the table and the
numbers: hk1 with hfitS (sameStand) · hTab (digTableB) · hbf (bookFit) with hn. On Mg's filling:
hdigF · hdecF with hd · hInR, hHeldR · hshownF, hnoCollF. On the public parameters: hbaseS. Where
the piece accepts: hsm · othersPub · othersP.
OBJECT. As in K3DigitsSeatLaws.lean, at the full size's written lists.
Used by K3CallsMeanR.lean, K3DigitsRestR.lean, K3LawOfR.lean (Johnson/Desc/First/Look/) and 44 more.
LETTERS. G, X, Dn, L, N, Mg, Rch, claim; a, k, l, sub, x, tl, smp, q, b'; in digMeanR_of also a',
told, decT, cs, ms, smpT.

Compiled with the whole library.
Limits. A structure of premises: shown at no term. A rule over letters, Rch among them. Nothing on
hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsAtSig
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers openSets pubSets start
  sampledIn shift pubFit pubRowM stepOpen pubStep pubOfItems sameStand bookFit)

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (X : Verify.Public)
  (Dn : Desc.First.Look.Sent) (L : K3Letters Cells Tok) (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Cl)

local notation "WT" => Desc.Wit Cells Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
set_option quotPrecheck false in
local notation "PieceT" => Piece (ckP .two) Fr (P × Desc.First.S) Cl WT

/-- **Every open item that the row does not close rides, second form.** -/
def RidesAtR (k : ℕ) (q : PieceT) (b' : Desc.Block Desc.First.S Cl) : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : P) a τ b w i,
    onQ N Mg linksFull PS (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
    onQ N Mg linksFull PS (fun s => (z, s)) (k + 1) b →
    relQ N Mg linksFull PS (fun s => (z, s)) (k + 1) b w →
    openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k i →
    ¬ insQ linksFull PS k i → meansQ N Mg (fun s => (z, s)) i a w

/-- **At the digits, second form.** sub: the segment's sort. -/
structure DigMeanR (a : Desc.Place) (k l : ℕ) (sub : ModelPart) (x : Desc.First.Look.Place) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dn L.rad).length) →
      Option ((digSg x Dn L.rad).om i).Smp)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) : Prop where
  hfit : pubFit Mg.more linksFull PS = true
  hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET true x) []).planOk =
        true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET true x) []).decide s rs
        cols = .ok s' → smp s' = smp s
  hseat : ∀ i : Fin (digList x Dn L.rad).length, (L.seat x.link true i.1).1 < q.base
  smp0 : Nonempty (digSg x Dn L.rad).Smp
  hS : ∀ s Gk, smp (Desc.First.S.putFork s Gk) = smp s
  hH : ∀ (s : Desc.First.S) a c, s.here = .head a →
    smp { s with here := .head { a with claim := some c } } = smp s
  hSeat : ∀ i : Fin (digList x Dn L.rad).length, L.seat x.link true i.1 ∈
    sampledIn N ((openSets linksFull PS (start linksFull))[k]?.getD [])
  fLook : ∀ (z : P), ∀ s, Mg.pub (.ledger l) (z, s) = true →
    Mg.pub (.lookIn l (7 + shift sub)) (z, s) = true →
    Mg.pub (.linkFresh l) (z, s) = true → Mg.pub (.freeAbove l) (z, s) = true →
    k3LookIn (Desc.First.Look.P.ofPlace SET true x) (Dn.arrayOf.getD x.link #[]) s = true
  fCf : ∀ (z : P), ∀ (i : Fin (digList x Dn L.rad).length) s y,
    Mg.held (L.seat x.link true i.1).1 (L.seat x.link true i.1).2 (z, s) = true →
    Mg.shown (L.seat x.link true i.1).1 (L.seat x.link true i.1).2 y →
    Mg.noColl (L.seat x.link true i.1).1 (L.seat x.link true i.1).2 (z, s) y →
    CfAt G Dn.codes (digList x Dn L.rad) (fun j => L.seat x.link true j.1) smp i s y
  fObj : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    a.1.failed = none → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace SET true x) b.1 = true →
    DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) (k + 1) b →
    ∀ w, Mg.forms l (7 + shift sub) "objects" (z, b.1) (strsOf Fr b.2) w →
    ∀ g F', (Desc.K3.seatDigits claim).fork b.1 = some F' →
    (Desc.K3.seatDigits claim).heard b.1 = some g →
    K3OutRows tl.f9 5 x.F.next
      (digNu x tl Dn L.rad (fun j => L.seat x.link true j.1) L.arr w) Reading.gl g F'
  fPl : ∀ (z : P), ∀ s y w, Mg.worth l (7 + shift sub) "planes" (z, s) y w → ∀ g F',
    (Desc.K3.seatDigits claim).fork s = some F' →
    (Desc.K3.seatDigits claim).heard s = some g →
    K3OutPlanes tl.f9 5 x.F.next
      (digNu x tl Dn L.rad (fun j => L.seat x.link true j.1) L.arr w) Reading.gl g F'
  fKe : ∀ (z : P), ∀ s y w, Mg.worth l (7 + shift sub) "keys" (z, s) y w → ∀ g F',
    (Desc.K3.seatDigits claim).fork s = some F' →
    (Desc.K3.seatDigits claim).heard s = some g →
    K3OutKeys tl.f9 5 x.F.next (digNu x tl Dn L.rad (fun j => L.seat x.link true j.1) L.arr w)
      (forK Cb.Gl.E
        (DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
        (zext (digMu x Dn L.rad (fun j => L.seat x.link true j.1) L.arr w))) Reading.gl g F'
  fPin : ∀ (z : P), ∀ s y w, (∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent l t, Mg.pin e.1 e.2 (z, s) y w) →
    PinSig G Dn.codes (digList x Dn L.rad) (fun j => L.seat x.link true j.1) smp L.arr
      (fun _ => True) s y w
  pinBack : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b w,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
    ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent l t,
    Mg.pin e.1 e.2 (z, b.1) (strsOf Fr b.2) w → Mg.pin e.1 e.2 (z, a.1) (strsOf Fr a.2) w
  fDig : ∀ (z : P), ∀ s y w,
    DgP.DigIn tl (enOf x.arrays) (digMu x Dn L.rad (fun j => L.seat x.link true j.1) L.arr w) →
    Mg.constr l .lookDigits (z, s) y w
  /-- the state's own numbers are the plan's at this segment: a fact along the fold -/
  ownIn : ∀ (z : P) a, onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a →
    Rch k ((z, a.1), a.2) → a.1.failed = none → OwnIs Dn x.link a.1
  behind : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
    a.1.failed = none → SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace SET true x) b.1 = true →
    Mg.decodes (z, b.1) (strsOf Fr b.2) →
    DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) (k + 1) b
  hDec : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
    Mg.decodes (z, a.1) (strsOf Fr a.2) → Mg.decodes (z, b.1) (strsOf Fr b.2)
  rides : RidesAtR N Mg Rch k q b'

/-- **DigMeanR GIVES WHAT THE KIND's FILES OWE AT THE SEAT.** -/
theorem seatLawsR_of_digMeanR (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place) (k l : ℕ) (sub : ModelPart)
    (x : Desc.First.Look.Place) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dn L.rad).length) →
      Option ((digSg x Dn L.rad).om i).Smp)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hk : PS[k]? = some a) (hi : a.link = some l) (hsub : linksFull[l]? = some sub)
    (hpcT : a.piece = 7 + shift sub) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hx : digAt X l = some (x, tl)) (pp : ℕ) (hB : digB SET x tl Dn L.rad pp = true)
    (hback : q.back = [])
    (hR : List.Forall₂ SameAs q.ds (Desc.First.Look.P.ofPlace SET true x).rounds)
    (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (M : DigMeanR G X Dn L N Mg Rch claim a k l sub x tl smp q b') :
    SeatLawsR linksFull PS k q N Mg Rch b' := by
  obtain ⟨σ₀⟩ := M.smp0
  exact k3_digits_seatLawsR G linksFull claim readers X codes shape PS k a b' q h hOk hk l hi sub
    hsub hpcT hpc N Mg Rch M.hfit hx Dn L.rad pp hB (fun j => L.seat x.link true j.1) L.arr smp
    hback hR hcap M.hsmp M.hseat σ₀ M.hS M.hH M.hSeat M.fLook M.fCf M.fObj M.fPl M.fKe M.fPin
    M.pinBack M.fDig M.ownIn M.behind M.hDec M.rides

/-- **DigMeanR UNDER K3At.** -/
theorem digMeanR_of (hK : K3At X Dn L Mg) (a : Desc.Place) (k l : ℕ) (sub : ModelPart)
    (x : Desc.First.Look.Place) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dn L.rad).length) →
      Option ((digSg x Dn L.rad).om i).Smp)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl)
    (hx : digAt X l = some (x, tl)) (hi : a.link = some l)
    (hsub : linksFull[l]? = some sub) (hpcT : a.piece = 7 + shift sub)
    (hpc : a.piece = Desc.K3.pieceAt X l true) (hk : PS[k]? = some a)
    (hfit : pubFit Mg.more linksFull PS = true)
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim)
        a.piece laid sent (Desc.First.Look.P.ofPlace SET true x) []).planOk =
          true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim)
        a.piece laid sent (Desc.First.Look.P.ofPlace SET true x) []).decide s rs
          cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i : Fin (digList x Dn L.rad).length, (L.seat x.link true i.1).1 < q.base)
    (smp0 : Nonempty (digSg x Dn L.rad).Smp)
    (hS : ∀ s Gk, smp (Desc.First.S.putFork s Gk) = smp s)
    (hH : ∀ (s : Desc.First.S) a c, s.here = .head a →
      smp { s with here := .head { a with claim := some c } } = smp s)
    (hSeat : ∀ i : Fin (digList x Dn L.rad).length, L.seat x.link true i.1 ∈
      sampledIn N ((openSets linksFull PS (start linksFull))[k]?.getD []))
    (fCf : ∀ (z : P), ∀ (i : Fin (digList x Dn L.rad).length) s y,
      Mg.held (L.seat x.link true i.1).1 (L.seat x.link true i.1).2 (z, s) = true →
      Mg.shown (L.seat x.link true i.1).1 (L.seat x.link true i.1).2 y →
      Mg.noColl (L.seat x.link true i.1).1 (L.seat x.link true i.1).2 (z, s) y →
      CfAt G Dn.codes (digList x Dn L.rad) (fun j => L.seat x.link true j.1) smp i s y)
    (fObj : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
      onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      a.1.failed = none → SameBut a.1 b.1 →
      Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace SET true x) b.1 = true →
      DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) (k + 1) b →
      ∀ w, Mg.forms l (7 + shift sub) "objects" (z, b.1) (strsOf Fr b.2) w →
      ∀ g F', (Desc.K3.seatDigits claim).fork b.1 = some F' →
      (Desc.K3.seatDigits claim).heard b.1 = some g →
      K3OutRows tl.f9 5 x.F.next
        (digNu x tl Dn L.rad (fun j => L.seat x.link true j.1) L.arr w) Reading.gl g F')
    (fPin : ∀ (z : P), ∀ s y w, (∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent l t, Mg.pin e.1 e.2 (z, s) y w) →
      PinSig G Dn.codes (digList x Dn L.rad) (fun j => L.seat x.link true j.1) smp L.arr
        (fun _ => True) s y w)
    (pinBack : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b w,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out a τ = some b →
      ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent l t,
      Mg.pin e.1 e.2 (z, b.1) (strsOf Fr b.2) w → Mg.pin e.1 e.2 (z, a.1) (strsOf Fr a.2) w)
    (ownIn : ∀ (z : P) a, onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → OwnIs Dn x.link a.1)
    (hdigF : ∀ a y w, Mg.constr l .lookDigits a y w = digitsPartK3 X Dn L l a y w)
    (a' : Desc.Place) (hk1 : PS[k + 1]? = some a') (hfitS : sameStand linksFull a a' = true)
    (hTab : digTableB Mg.more linksFull PS k a l (shift sub) = true)
    (told : List (List Desc.Oracle)) (hbf : bookFit N PS told = true) (hn : told[k]? = some [])
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × Desc.First.S → Option Cells)
    (hdecF : Mg.decodes = decodesOf decT)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → decT c y' = decT c y)
    (hInR : InOrderReads Mg) (hHeldR : HeldReads Mg) (cs : Codes) (ms : List Mem)
    (smpT : P × Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
    (hshownF : Mg.shown = shownJT cs G ms) (hnoCollF : Mg.noColl = noCollJT cs G smpT ms)
    (hbaseS : ∀ e ∈ sampledIn N ((openSets linksFull PS (start linksFull))[k]?.getD []),
      e.1 < q.base)
    (hsm : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out u τ = some v →
      ∀ y ∈ ms, smpT (z, v.1) y.1 y.2 = smpT (z, u.1) y.1 y.2)
    (othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a) ++
        pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
          (Desc.First.rowOf linksFull a)),
      k3Like r = false → Mg.pub r (z, v.1) = true)
    (othersP : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a),
      (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → Mg.pubP r (z, v.1))
    (rides : RidesAtR N Mg Rch k q b') :
    DigMeanR G X Dn L N Mg Rch claim a k l sub x tl smp q b' := by
  have hlook : lookAt X l true = some x := by
    unfold digAt at hx
    obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
    obtain rfl : x' = x := congrArg Prod.fst hx
    exact h1
  have e7 : 7 + shift sub = Desc.K3.pieceAt X l true := hpcT.symm.trans hpc
  have hOpen := digits_lookIn_open Mg.more linksFull PS k a l sub hfit hk hi hsub hpcT
    (.lookIn l (7 + shift sub)) (by simp)
  refine ⟨hfit, hsmp, hseat, smp0, hS, hH, hSeat, ?_, fCf, fObj, ?_, ?_, fPin, pinBack, ?_, ownIn,
    ?_, ?_, rides⟩
  · -- fLook
    intro z s _ h2 _ _
    exact fLook_at hK l true hlook z s (by rw [← e7]; exact h2)
  · -- fPl
    intro z s y w hw
    exact fPl_at hK claim l hx z s y w (by rw [← e7]; exact hw)
  · -- fKe
    intro z s y w hw
    exact fKe_at hK claim l hx z s y w (by rw [← e7]; exact hw)
  · -- fDig
    intro z s y w hw
    rw [hdigF]
    exact fDig_part X Dn L l hx (z, s) y w hw
  · -- behind
    intro B' hN z u τ v hout hu hR hun T hOut hdec DL
    have hOnIn : Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace SET true x) u.1 = true := by
      have hu' := hu
      obtain ⟨-, hor⟩ := hu'
      rcases hor with hbad | ⟨hBb, -, -, -⟩
      · exact absurd hun hbad
      · simp only [Bool.and_eq_true] at hBb
        have hp : Mg.pub (.lookIn l (7 + shift sub)) (z, u.1) = true :=
          List.all_eq_true.1 hBb.1.2 _ (List.mem_append_left _ hOpen)
        rw [e7] at hp
        exact k3LookIn_onIn (fLook_at hK l true hlook z u.1 hp)
    refine k3_digits_behind_at linksFull X Dn L Mg hK N PS k a a' hk hk1 hfitS l hi sub hsub hpcT
      hpc hTab hlook z u v hu hOnIn T hOut hdec DL (inOrder_sameBut hInR T z) told hbf hn
      (fun e _ he => held_sameBut hHeldR T e.1 e.2 z he) ?_ ?_
      (othersPub B' hN z u τ v hout T DL hu hR hun) (othersP B' hN z u τ v hout T DL hu hR hun)
    · intro e he hs
      rw [hshownF] at hs ⊢
      exact calls_shown cs G ms
        (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
          Piece (ckP .two) Fr Desc.First.S Cl WT) _ hbaseS u v ⟨τ, hout⟩ e he hs
    · intro e he hs
      rw [hnoCollF] at hs ⊢
      exact calls_noColl cs G smpT ms z
        (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
          Piece (ckP .two) Fr Desc.First.S Cl WT) _ hbaseS (hsm B' hN z) u v ⟨τ, hout⟩ e he hs
  · -- hDec
    intro B' _ z u τ v hout hdu
    rw [hdecF] at hdu ⊢
    exact decodes_at_seat decT hd z
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl WT) u v τ hout hdu

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.seatLawsR_of_digMeanR
#print axioms VerifiableInference.OnPublicFiles.digMeanR_of
