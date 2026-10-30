-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3Means.lean: the kind "lookup" (K3): WHAT ONE PLACE OF THE KIND ASKS OF THE
TABLE OF JOINTS' MEANING, A STRUCTURE A SORT OF PLACE; and the public tests on the plan. Cut out of
Johnson/Desc/First/Look/K3LawOf.lean on the lookups' authors' ask, SO THAT IT STANDS ON THE RULES
AND THE KIND's OWN FILES ALONE: no file of the proof file's description or of its seats lies
beneath: the place a, its number k in the written list, the segment l and the reader of claims are
letters here.

Main names:
  `strictAt B' q`: the piece over the carried record that holds the strict reading of B', with q's
    numbers: the piece of which `SeatLaws` speaks.
  `RidesAt`: the second of `SeatLaws`' four, at the full size's written lists.
  `DigMean`, `AttMean`, `LayMean`, `HeadMean`: the premises on N, Mg and the readers of samples
    of the four theorems that end in `SeatLaws` (`k3_digits_seatLaws`, `k3_att_seatLaws`,
    `k3_lay_seatLaws_z`, `k3_head_seatLaws_z`), at one place, one piece q and the constant b'. strW,
    the reader of the stored table's string, is a function of the public part.
  `K3Plan`: what is asked of the plan alone: at the digits and the head as Bools, at attention's
    and the layers' calls as the sentences that the laws spend.
  `placeAt_digAt`: the digits' place's parameters are the link's own.

Limits: definitions and one small lemma: nothing is shown of any block. The structures are premises
of Johnson/Desc/First/Look/K3LawOf.lean [not in this library]'s theorems: shown at no term. The
full size's written lists alone. Nothing on soundness; nothing on hiding.


-/
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.Look.K3DigitsSeatLaws
import Johnson.Desc.First.Look.K3SeatLawsZ
import Johnson.Desc.First.Look.K3PlaceAtCopies
import Johnson.Desc.First.Look.K3FillWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn shift pubFit)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr)

/-- The digits' place's parameters are the link's own. -/
theorem placeAt_digAt {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {tl : HTailF2}
    (hx : digAt X i = some (x, tl)) :
    placeAt X i true = some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) := by
  unfold digAt at hx
  obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨t, -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨rfl, -⟩ := Prod.mk.inj hx
  unfold placeAt
  rw [h1]
  rfl

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy]

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (X : Verify.Public)
  (Dn : Desc.First.Look.Sent) (L : K3Letters Cells Tok) (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT)) (claim : Aff → Cl)

local notation "WT" => Desc.Wit Cells Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "SET" => Params.settingOf X.P.frame
set_option quotPrecheck false in
local notation "PieceT" => Piece (ckP .two) Fr (P × Desc.First.S) Cl WT

/-- The piece of which `SeatLaws` speaks. -/
abbrev strictAt (B' : Desc.Block Desc.First.S Cl) (q : PieceT) :
    Piece (ckP .two) Fr Desc.First.S Cl WT :=
  ⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩

/-- **Every open item that the row does not close rides.** -/
def RidesAt (k : ℕ) (q : PieceT) (b' : Desc.Block Desc.First.S Cl) : Prop :=
  ∀ B', SeatOf b' B' → ∀ (z : P) a τ b w i,
    onQ N Mg linksFull PS (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
    (strictAt B' q).ior.red.out a τ = some b →
    onQ N Mg linksFull PS (fun s => (z, s)) (k + 1) b →
    relQ N Mg linksFull PS (fun s => (z, s)) (k + 1) b w →
    openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k i →
    ¬ insQ linksFull PS k i → meansQ N Mg (fun s => (z, s)) i a w

/-- **At attention's calls.** -/
structure AttMean (a : Desc.Place) (k l : ℕ) (x : Desc.First.Look.Place) (A : Attention.Shape)
    (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (sigListCalls Dn L.rad x.link).length) →
      Option ((attSg x Dn L.rad).om i).Smp)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) : Prop where
  hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).planOk =
        true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).decide s rs
        cols = .ok s' → smp s' = smp s
  hseat : ∀ i : Fin (sigListCalls Dn L.rad x.link).length, (L.seat x.link false i.1).1 < q.base
  smp0 : Nonempty (attSg x Dn L.rad).Smp
  table : ∀ B', SeatOf b' B' → ∀ z : P,
    AttAtTable (Fr := Fr) G x A tl Dn L.rad SET (fun j => L.seat x.link false j.1) L.arr smp
      claim N Mg linksFull PS z k l
      (fun a c => ∃ τ, (strictAt B' q).ior.red.out a τ = some c)
  rides : RidesAt N Mg k q b'

/-- **At the layers' calls.** -/
structure LayMean (a : Desc.Place) (k l : ℕ) (x : Desc.First.Look.Place) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (sigListCalls Dn L.rad x.link).length) →
      Option ((attSg x Dn L.rad).om i).Smp)
    (smpW : Desc.First.S → Option L.oW.Smp) (strW : P → Fr.E.Str → L.oW.Str)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) : Prop where
  hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).planOk =
        true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).decide s rs
        cols = .ok s' → smp s' = smp s
  hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).planOk =
        true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).decide s rs
        cols = .ok s' → smpW s' = smpW s
  hstrW : ∀ (z : P) y (τ : Tr (uLT (ckP .two) q.ds)),
    strW z (behind (ckP .two) Fr q.base q.ds y τ) = strW z y
  hseat : ∀ i : Fin (sigListCalls Dn L.rad x.link).length, (L.seat x.link false i.1).1 < q.base
  smp0 : Nonempty (attSg x Dn L.rad).Smp
  smpW0 : Nonempty L.oW.Smp
  table : ∀ B', SeatOf b' B' → ∀ z : P,
    LayAtTable (Fr := Fr) G x (pubAt X (l / Desc.First.Look.stepOf X)) tl Dn L.rad L.oW L.wOf L.nr
      L.nc SET (fun j => L.seat x.link false j.1) L.arr smp smpW (strW z) L.msgW claim N Mg
      linksFull PS z k l (fun a c => ∃ τ, (strictAt B' q).ior.red.out a τ = some c)
  rides : RidesAt N Mg k q b'

/-- **At the head's calls.** rq: the kind's letter "the request", of the public part. -/
structure HeadMean (a : Desc.Place) (k l : ℕ) (adr : HeadAdr)
    (rq : P → Desc.Kinds.Head.Request) (Q : Fork → Prop)
    (gd : Desc.Wit Cells Tok MsgT → Prop) (x : Desc.First.Look.Place)
    (smp : Desc.First.S → (i : Fin (sigListCalls Dn L.rad x.link).length) →
      Option ((attSg x Dn L.rad).om i).Smp)
    (smpW : Desc.First.S → Option L.oW.Smp) (strW : P → Fr.E.Str → L.oW.Str)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) : Prop where
  hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).planOk =
        true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).decide s rs
        cols = .ok s' → smp s' = smp s
  hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).planOk =
        true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim)
      a.piece laid sent (Desc.First.Look.P.ofPlace SET false x) []).decide s rs
        cols = .ok s' → smpW s' = smpW s
  hstrW : ∀ (z : P) y (τ : Tr (uLT (ckP .two) q.ds)),
    strW z (behind (ckP .two) Fr q.base q.ds y τ) = strW z y
  hseat : ∀ i : Fin (sigListCalls Dn L.rad x.link).length, (L.seat x.link false i.1).1 < q.base
  smp0 : Nonempty (attSg x Dn L.rad).Smp
  smpW0 : Nonempty L.oW.Smp
  table : ∀ B', SeatOf b' B' → ∀ z : P, letI := rq z
    HeadAtTable (Fr := Fr) G adr x X.H.tl Dn L.rad L.oW L.wOf L.nr L.nc SET
      (fun j => L.seat x.link false j.1) L.arr smp smpW (strW z) L.msgW Q gd claim N Mg
      linksFull PS z k l (fun a c => ∃ τ, (strictAt B' q).ior.red.out a τ = some c)
  rides : RidesAt N Mg k q b'

/-- **At the digits.** sub: the link's sort. -/
structure DigMean (a : Desc.Place) (k l : ℕ) (sub : ModelPart) (x : Desc.First.Look.Place) (tl : HTailF2)
    (smp : Desc.First.S → (i : Fin (digList x Dn L.rad).length) →
      Option ((digSg x Dn L.rad).om i).Smp)
    (q : PieceT) (b' : Desc.Block Desc.First.S Cl) : Prop where
  hfit : pubFit Mg.more linksFull PS = true
  hAsk : liveName l ∈ (Mg.more.rows linksFull a).asks
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
  fObj : ∀ (z : P), ∀ s y w, Mg.forms l (7 + shift sub) "objects" (z, s) y w → ∀ g F',
    (Desc.K3.seatDigits claim).fork s = some F' →
    (Desc.K3.seatDigits claim).heard s = some g →
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
    (strictAt B' q).ior.red.out a τ = some b →
    ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent l t,
    Mg.pin e.1 e.2 (z, b.1) (strsOf Fr b.2) w → Mg.pin e.1 e.2 (z, a.1) (strsOf Fr a.2) w
  fDig : ∀ (z : P), ∀ s y w,
    DgP.DigIn tl (enOf x.arrays) (digMu x Dn L.rad (fun j => L.seat x.link true j.1) L.arr w) →
    Mg.constr l .lookDigits (z, s) y w
  fOrder : ∀ (z : P), ∀ s, Mg.inOrder (z, s) = true → s.st.codes = Dn.codes
  fLive : ∀ (z : P), ∀ s, Mg.pub (liveItem l) (z, s) = true ↔ LiveIs Dn s
  behind : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
    (strictAt B' q).ior.red.out a τ = some b →
    onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) k a → a.1.failed = none →
    SameBut a.1 b.1 →
    Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace SET true x) b.1 = true →
    Mg.decodes (z, b.1) (strsOf Fr b.2) → Mg.pub (liveItem l) (z, b.1) = true →
    DigLeft a.1 b.1 → onQ (Fr := Fr) N Mg linksFull PS (fun s => (z, s)) (k + 1) b
  hDec : ∀ B', SeatOf b' B' → ∀ (z : P) a τ b,
    (strictAt B' q).ior.red.out a τ = some b →
    Mg.decodes (z, a.1) (strsOf Fr a.2) → Mg.decodes (z, b.1) (strsOf Fr b.2)
  rides : RidesAt N Mg k q b'

end

section
variable {Cells Tok : Type} (X : Verify.Public) (Dn : Desc.First.Look.Sent)
  (L : K3Letters Cells Tok)

local notation "SET" => Params.settingOf X.P.frame

/-- **What is asked of the plan alone.** att, lay: as the sentences that the laws spend (the Bools
`attBAt`, `layBAt` give them: `attOK_of_attBAt`, `layOK_of_layBAt`; so do theorems in scope). -/
structure K3Plan (pp floor : ℕ) : Prop where
  dig : ∀ l < 25, ∃ x tl, digAt X l = some (x, tl) ∧ digB SET x tl Dn L.rad pp = true
  att : ∀ l < 24, l % 2 = 1 → ∃ x A tl, attAt X l = some (x, A, tl) ∧ AttOK SET x A tl Dn L.rad
  lay : ∀ l < 24, l % 2 = 0 → ∃ x tl, layAt X l = some x ∧ tlAt X l = some tl ∧ LayOK SET x ∧
    (Forest.planeCols x.fs x.lm).toBool = true
  head : ∃ x, Desc.Kinds.Head.Law.headAt X = some x ∧
    Desc.Kinds.Head.Law.headB floor x.fs = true ∧ (Forest.planeCols x.fs x.lm).toBool = true
  head24 : headLink X = 24
  entries : ∀ l < 25, ∀ p, placeAt X l false = some p → p.entries.isSome = true

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.placeAt_digAt
