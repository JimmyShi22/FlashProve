-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsOwedForms.lean: the lookup on the digits of a segment's approximate
range proof: THE BUILDER INTO THE KIND's LEDGER's DigOwedR (digOwed_mgAll, MgAt/K3DigitsOwed.lean)
WITH ONE FIELD MORE PAID: othersPub, by othersPub_dig_mgAll (MgAt/K3DigitsOthers.lean): SIX OF THE
FOURTEEN FIELDS ARE NOW PAID; eight pass through in the ledger's own texts. One theorem: two calls.
NO RESULT ON THE PROTOCOL.

Main name.
  digOwed_forms: as digOwed_mgAll, with the premise othersPub struck and in its place: hForms (the
    tests formsIn l pc r of the written lists keptDigits, newDigits at the state behind, under the
    field's own premises) · hlinks (the composed meaning's list of sorts is the written one) ·
    hBase (the meaning beneath's public test reads no state).
PASS THROUGH STILL: hbf, hn, hbaseS, othersP, rides, some, sent, fits.
OBJECT. One term of the type Meaning; the kind's ledger.
Used by K3DigitsFormsLive.lean (Johnson/Desc/Sound/MgAt/).
LETTERS. Those of digOwed_mgAll.


Compiled with the whole library.


The ledger's two texts othersPub, othersP at the digits bear two premises behind the promise in
front: «reached» (Rch k ((z, u.1), u.2)) and «no mark» (u.1.failed = none).

Limits. A rule over letters. The premises are shown together at no term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsOwed
import Johnson.Desc.Sound.MgAt.K3DigitsOthers

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

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **INTO THE LEDGER's OWN STRUCTURE, othersPub PAID.** -/
theorem digOwed_forms (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
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
    (hForms : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        ∀ r ∈ keptDigits l sub ++ newDigits l sub, (∃ pc nm, r = .formsIn l pc nm) →
        (mgAll Dm Mg).pub r (z, v.1) = true)
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
      (MgAt.nextOf l true) (k3K l true) l sub x tl smp q b' told :=
  digOwed_mgAll Dm Mg Rch codes shape hM hl hsub hx smp q b' hb hOk hback told hbf hn hbaseS
    (othersPub_dig_mgAll Dm Mg Rch codes shape hM hlinks hBase hl hsub hx q b' hb hOk hback hForms)
    othersP rides hSome hSent hFits hB pr H lk hrun hah hlink pass hpass hfind hLive hGroups hLink
    hNext hOwn hSeats hShapes pubFree hnS hTests h6

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digOwed_forms
