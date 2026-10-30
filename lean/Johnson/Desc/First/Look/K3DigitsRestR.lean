-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsRestR.lean: the lookup on the digits of a segment's approximate
range proof: WHAT IS LEFT OF DigMeanR (K3MeansDigR.lean) WHERE THE MEANING's FIELDS ON THE ORACLE
MESSAGES ARE THE TABLE's OWN SENTENCES, AS ONE LEAN STRUCTURE WITH EACH FIELD BOOKED; and DigMeanR
from it. NO RESULT ON THE PROTOCOL.

Main names.
  DigRestR: FOURTEEN FIELDS, in four sorts. TESTS ON THE TABLE, THE NUMBERS AND THE PUBLIC
    PARAMETERS (Bools; for an evaluation): hfit · hOp · hk1 · hfitS · hTab · hbf · hn · and hbaseS
    (every sampled tenant that is open in front lies below the piece's base). ON THE PLAN AND THE
    TWO READERS OF SAMPLES: sits (DigSits, K3DigitsSig.lean). A FACT ALONG THE FOLD: ownIn. WHERE
    THE PIECE ACCEPTS: fObj · othersPub · othersP · rides.
  digMeanR_of_rest: K3At, seven equations or light sentences on the meaning (hpinF, hnoCollF,
    hshownF, hdecF, hdigF, hInR, hHeldR), two on its parameters (hread: the reader of samples reads
    the statement and the book alone; hd: the decoder does not read the verifier's state), the
    place, and DigRestR give DigMeanR.
PAID HERE, OF DigMeanR's NINETEEN FIELDS: SIX by digMeanR_of (fLook, fPl, fKe, fDig, behind, hDec) ·
fCf, fPin (digits_cf, digits_pinIn) · pinBack (digits_pinBack) · hsmp, hS, hH (digits_reader,
K3DigitsMean.lean) · hSeat (digits_hSeat) · hseat (hSeat with hbaseS) · smp0 (digSmp_nonempty,
K3SmpMember.lean): FIFTEEN. HANDED THROUGH: hfit, fObj, ownIn, rides.
OBJECT. As in K3DigitsSeatLaws.lean, at the full size's written lists.
USER. digMeanR_mgAll (Johnson/Desc/Sound/MgAt/K3Digits.lean).
LETTERS. G, X, Dn, L, N, Mg, Rch, claim; smpT, ms; a, a', k, l, sub, x, tl, smp, q, b', told; decT,
f, readers, codes, shape, z₀.


Compiled with the whole library.
Limits. A structure of premises: shown at no term. A rule over letters. Nothing on hiding.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3MeansDigR
import Johnson.Desc.First.Look.K3DigitsMean
import Johnson.Desc.First.Look.K3SmpMember

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
  (smpT : P × Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf Dn.codes s.l).om i).Smp) (ms : List Mem)

local notation "WT" => Desc.Wit Cells Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
set_option quotPrecheck false in
local notation "PieceT" => Piece (ckP .two) Fr (P × Desc.First.S) Cl WT

/-- **WHAT IS LEFT AT ONE DIGITS' PLACE.** -/
structure DigRestR (a a' : Desc.Place) (k l : ℕ) (sub : ModelPart) (x : Desc.First.Look.Place)
    (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dn L.rad).length) →
      Option ((digSg x Dn L.rad).om i).Smp)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) (told : List (List Desc.Oracle)) : Prop where
  /-- a test on the table and the meaning's list of extra public tests -/
  hfit : pubFit Mg.more linksFull PS = true
  /-- a test on the table: the segment's three pins are open in front -/
  hOp : digitsOpenB linksFull PS k l = true
  /-- the next place -/
  hk1 : PS[k + 1]? = some a'
  /-- a test on the table -/
  hfitS : sameStand linksFull a a' = true
  /-- a test on the table and the meaning's list of extra public tests -/
  hTab : digTableB Mg.more linksFull PS k a l (shift sub) = true
  /-- a test on the numbers -/
  hbf : bookFit N PS told = true
  hn : told[k]? = some []
  /-- on the numbers and the piece: every sampled tenant that is open in front lies below -/
  hbaseS : ∀ e ∈ sampledIn N ((openSets linksFull PS (start linksFull))[k]?.getD []),
    e.1 < q.base
  /-- on the plan (some, sent, fits) and the two readers of samples (bySeat, smpIs) -/
  sits : DigSits G x Dn L.rad (fun j => L.seat x.link true j.1) smpT smp ms N l
  /-- a fact along the fold -/
  ownIn : ∀ (z : P) a, onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a →
    Rch k ((z, a.1), a.2) → a.1.failed = none → OwnIs Dn x.link a.1
  /-- where the piece accepts -/
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
  othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a) ++
      pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k]?.getD [])
        (Desc.First.rowOf linksFull a)),
    k3Like r = false → Mg.pub r (z, v.1) = true
  othersP : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (ckP .two) Fr Desc.First.S Cl WT).ior.red.out u τ = some v →
    SameBut u.1 v.1 → DigLeft u.1 v.1 →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
    u.1.failed = none →
    ∀ r ∈ pubStep ((pubSets Mg.more linksFull PS)[k]?.getD []) (pubRowM Mg.more linksFull a),
    (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → Mg.pubP r (z, v.1)
  rides : RidesAtR N Mg Rch k q b'

/-- **DigMeanR FROM WHAT IS LEFT.** -/
theorem digMeanR_of_rest (hK : K3At X Dn L Mg) (a a' : Desc.Place) (k l : ℕ) (sub : ModelPart)
    (x : Desc.First.Look.Place) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dn L.rad).length) →
      Option ((digSg x Dn L.rad).om i).Smp)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) (told : List (List Desc.Oracle))
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes)
    (shape : Params.ReqShape)
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hback : q.back = [])
    (hx : digAt X l = some (x, tl)) (hi : a.link = some l)
    (hsub : linksFull[l]? = some sub) (hpcT : a.piece = 7 + shift sub)
    (hpc : a.piece = Desc.K3.pieceAt X l true) (hk : PS[k]? = some a) (z₀ : P)
    (hpinF : Mg.pin = pinJT Dn.codes G L.arr smpT ms)
    (hnoCollF : Mg.noColl = noCollJT Dn.codes G smpT ms)
    (hshownF : Mg.shown = shownJT Dn.codes G ms)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × Desc.First.S → Option Cells)
    (hdecF : Mg.decodes = decodesOf decT)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → decT c y' = decT c y)
    (hdigF : ∀ a y w, Mg.constr l .lookDigits a y w = digitsPartK3 X Dn L l a y w)
    (hInR : InOrderReads Mg) (hHeldR : HeldReads Mg)
    (f : P → Statement × TreeBook → (s : Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf Dn.codes s.l).om i).Smp)
    (hread : ∀ z s, smpT (z, s) = f z (s.st, s.book))
    (R : DigRestR G X Dn L N Mg Rch claim smpT ms a a' k l sub x tl smp q b' told) :
    DigMeanR G X Dn L N Mg Rch claim a k l sub x tl smp q b' := by
  have hopen := digits_open_of R.hOp
  have hSeat := digits_hSeat N (fun j : Fin (digList x Dn L.rad).length => L.seat x.link true j.1)
    R.sits.sent hopen
  have hbase : ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent l t, e.1 < q.base := by
    intro t ht e he
    refine R.hbaseS e ?_
    unfold sampledIn
    exact List.mem_flatMap.2 ⟨_, hopen t ht, he⟩
  obtain ⟨r1, r2, r3⟩ := digits_reader (smpT := smpT) z₀ R.sits.smpIs f hread claim a.piece
    (Desc.First.Look.P.ofPlace SET true x)
  refine digMeanR_of G X Dn L N Mg Rch claim hK a k l sub x tl smp q b' hx hi hsub hpcT hpc hk
    R.hfit r1 (fun i => R.hbaseS _ (hSeat i)) (digSmp_nonempty x Dn L.rad) r2 r3 hSeat ?_ R.fObj ?_
    ?_ R.ownIn hdigF a' R.hk1 R.hfitS R.hTab told R.hbf R.hn decT hdecF hd hInR hHeldR Dn.codes ms
    smpT hshownF hnoCollF R.hbaseS ?_ R.othersPub R.othersP R.rides
  · -- fCf
    intro z i s y _ _ hn
    rw [hnoCollF] at hn
    exact digits_cf G R.sits z i s y hn
  · -- fPin
    intro z s y w hp
    rw [hpinF] at hp
    exact digits_pinIn G L.arr R.sits z s y w hp
  · -- pinBack
    intro B' hB' z u τ v w hout t ht e he hp
    rw [hpinF] at hp ⊢
    exact digits_pinBack Dn.codes G L.arr smpT ms N l claim readers X codes shape a b' h q hback
      hbase f hread B' hB' z u τ v w hout t ht e he hp
  · -- hsm
    intro B' hB' z u τ v hout y _
    rw [digits_samples Dn.codes smpT claim readers X codes shape a b' h q hback f hread B' hB' z u
      τ v hout]

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digMeanR_of_rest
