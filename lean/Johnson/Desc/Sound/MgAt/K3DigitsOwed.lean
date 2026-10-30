-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsOwed.lean: the lookup on the digits of a segment's approximate range
proof: A BUILDER INTO THE KIND's LEDGER's OWN STRUCTURE DigOwedR
(Johnson/Desc/Sound/MgAt/K3Owed.lean: what is owed at one digits' place, each debt
once), at the ledger's own letters, at the composed meaning mgAll Dm Mg: FIVE OF ITS FOURTEEN FIELDS
ARE PAID HERE; nine pass through as plain premises in its own texts. No new structure. One theorem:
a joining. NO RESULT ON THE PROTOCOL.

Main names.
  atS2_ofForm: the seat at the kind's own letter K3Lot.ofForm meets AtS2 (its claims are plain
    forms).
  digOwed_mgAll: … → DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch K3Lot.ofForm Dm.ms
    (IM.k3Place l true) (MgAt.nextOf l true) (k3K l true) l sub x tl smp q b' told.
PAID HERE. hfit, hTab (MgAt/K3Tests.lean: by the kernel at the closed list, under hM) · hOp, hfitS
(K3DigitsClosed.lean: by the kernel) · fObj (digObjR_mgAll, MgAt/K3DigitsObj.lean, with
digMaskR_of_facts, K3DigitsMaskAt.lean, and askFree_mgAll).
PASS THROUGH, IN THE LEDGER's OWN TEXTS (laid by program): hbf, hn, hbaseS, othersPub, othersP,
rides, some, sent, fits.
WHAT fObj STILL ASKS, EACH BOOKED.
  FACTS ALONG THE FOLD AT THE BORDER IN FRONT: hLive, hGroups, hLink, hNext, hOwn, hSeats, hShapes.
  TESTS ON THE LIST OF ROUNDS AND THE MEMBERS: hB (maskB) · hnS (n ≤ x.arrays.ns) · hTests
    (maskTestsB) · h6 (oneShapeB).
  TERMS OF Dm's READERS OF THE CLAIMS ON LINEAR FORMS: hrun, hah, hlink, pass with hpass, hfind.
  ON THE TERM's TEST AT freeAbove l: pubFree.
  THE PIECE: hOk, hback.
OBJECT. One term of the type Meaning; the kind's ledger.
Used by K3DigitsFormsJoin.lean and K3DigitsOwedForms.lean (Johnson/Desc/Sound/MgAt/) and 1 more.
LETTERS. Dm, Mg, Rch; codes, shape; l, sub, x, tl, smp, q, b', told; nos, n, Ld, M; pr, H, lk, pass.


Compiled with the whole library.


The ledger's two texts othersPub, othersP at the digits bear two premises behind the promise in
front: «reached» (Rch k ((z, u.1), u.2)) and «no mark» (u.1.failed = none).

Limits. A rule over letters. The premises are shown together at no term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3Owed
import Johnson.Desc.Sound.MgAt.K3Tests
import Johnson.Desc.Sound.MgAt.K3DigitsObj
import Johnson.Desc.First.Look.K3DigitsClosed
import Johnson.Desc.First.Look.K3DigitsMaskAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift pubFit pubSets pubStep pubRowM pubOfItems
  stepOpen openSets start sampledIn bookFit)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles)

/-- The seat at the kind's own letter. -/
theorem atS2_ofForm : AtS2 (Desc.K3.seatDigits K3Lot.ofForm) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **INTO THE LEDGER's OWN STRUCTURE.** -/
theorem digOwed_mgAll (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
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
    (othersPub : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)) ++
        pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[(k3K l true)]?.getD [])
          (Desc.First.rowOf linksFull (IM.k3Place l true))),
      k3Like r = false → (mgAll Dm Mg).pub r (z, v.1) = true)
    (othersP : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)),
      (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → (mgAll Dm Mg).pubP r (z, v.1))
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
    (pubFree : ∀ (z : P) s, (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
      H2K5.Door.freeAboveB n s = true)
    (hnS : n ≤ x.arrays.ns)
    (hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
      (Dm.N.group l) (Dm.l3.seat x.link true) = true)
    (h6 : oneShapeB Dm.ms = true) :
    DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch K3Lot.ofForm Dm.ms (IM.k3Place l true)
      (MgAt.nextOf l true) (k3K l true) l sub x tl smp q b' told := by
  obtain ⟨hpc, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt X) X codes shape l true b' hb
  obtain ⟨sub', hsub', -, hpcT⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub' = sub := Option.some.inj (hsub'.symm.trans hsub)
  have hfit := hfit_mgAll Dm Mg hM
  exact
    { hfit := hfit
      hOp := (digClosed_at l hl).2
      hfitS := (digClosed_at l hl).1
      hTab := hTab_mgAll Dm Mg hM l hl sub' hsub
      hbf := hbf
      hn := hn
      hbaseS := hbaseS
      fObj := digObjR_mgAll Dm Mg Rch K3Lot.ofForm (IM.k3Place l true) (k3K l true) l sub' x tl q b'
        (K3Lot.readersAt X) codes shape hb hOk hback hx rfl hsub hpcT hpc
        (K3Lot.k03_at_full l hl true) hfit atS2_ofForm hB pr H lk hrun hah hlink pass hpass hfind
        (digMaskR_of_facts X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch Dm.ms (k3K l true) l x q b' hLive
          hGroups hLink hNext hOwn hSeats hShapes (askFree_mgAll Dm Mg hM l hl) pubFree hnS hTests
          hSome h6)
      othersPub := othersPub
      othersP := othersP
      rides := rides
      some := hSome
      sent := hSent
      fits := hFits }

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.atS2_ofForm
#print axioms VerifiableInference.OnPublicFiles.digOwed_mgAll
