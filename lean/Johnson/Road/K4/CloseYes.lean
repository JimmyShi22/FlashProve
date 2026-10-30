-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseYes.lean: Johnson/Road/K4/CloseVal.lean AT A YES OF THE PIECE THAT HOLDS K4's
OWN BLOCK (`Yes`, Johnson/Road/K4/CarriageHeard.lean), in a group that is not the first: the
carriage's maps, the tape, the chain's value and the field `coin`. Three definitions and four
theorems. Glue: no new argument, no count.

  `Plan4.mapsAt A N Ex hds`: the carriage's maps at a piece whose written rounds are K4's declared
    ones (hds : pc.ds = dsLater par): `Plan4.mapsK4` carried along hds. `Plan4.mapsAt_ok`:
    `Maps.OK`.
  `tapeAt par pc τ`: the tape that K4's hearing hears at the transcript τ of the piece's stretch.
  `Plan4.nzAt`: on it no further challenge reads 0.
  `Plan4.ClaimsAt A N tk hds τ x a`: at the seven states and targets a: `TailH.Claims` holds of the
    data read off that tape, at the first statement x and the token point.
  `Plan4.val_of_claims`: under `ClaimsAt`: the chain's value on the maps' image of τ is `z7` of
    these data, for the same seven states and targets.
  `Plan4.coin_of_yes`: at a `Yes`, under `ClaimsAt`: the coefficient drawn in the sumcheck of the
    terms, as the chain reads it, is not 0: the field `coin` of `Plan4.HeardL` | `HeardO`.

Limits. `ClaimsAt`, `Plan4.Meets` and hds ARE PREMISES. A group that is not the first. Those of
CloseVal.lean and CarriageHeard.lean.
-/
import Johnson.Road.K4.CloseVal
import Johnson.Road.K4.CarriageHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Aff)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.P1 (NzT Adds7 TailNums tapeW)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open Inst.Model (Scl)
open _root_.Run (ckP)

variable [scl : Scl] {M X T Wt Cl : Type} {Fr : Frame} {Q : Plan4 Cb.Gl.E M X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The carriage's maps at a piece whose written rounds are K4's declared ones. -/
noncomputable def Plan4.mapsAt (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par) :
    Maps pc.ds (Q.full.own.toOwn.ch.R Ex).shape :=
  (Plan4.mapsK4 A N Ex).castD hds

theorem Plan4.mapsAt_ok (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par) :
    (Plan4.mapsAt A N Ex hds).OK :=
  Maps.ok_castD hds (Plan4.mapsK4_ok A N Ex)

/-- The tape that K4's hearing hears at a transcript of the piece's stretch. -/
def tapeAt (par : Par) (pc : Piece (ckP .two) Fr T Cl Wt) (τ : Tr (uLT (ckP .two) pc.ds)) :
    Tape :=
  tapeW noDigest pc.ds τ (entries par.P par.hp par.g)

/-- On it no further challenge reads 0. -/
theorem Plan4.nzAt (A : Q.Meets par hS pcl) (tk : Array Nat) {ds : List RDT}
    (e : ds = dsLater par) (τ : Tr (uLT (ckP .two) ds)) (es : List Fmt.Entry) :
    NzT Q.full.own.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      ((tapeW noDigest ds τ es).drop 1) := by
  subst e
  exact Plan4.nz_at A tk τ es

/-- `TailH.Claims` at the data read off the tape, at some seven states and targets. -/
def Plan4.ClaimsAt (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail) (tk : Array Nat)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par)
    (τ : Tr (uLT (ckP .two) pc.ds)) (x : X) (a : Adds7 Q.full.own.toOwn.tail) : Prop :=
  (k4Tail (Plan4.tailMK A N) { par.P with tokv := tk } par.hp (tapeAt par pc τ)
    (Plan4.nzAt A tk hds τ _) a).Claims (x, ptOf Q (tapeAt par pc τ))

/-- **The chain's value on the maps' image of the transcript.** -/
theorem Plan4.val_of_claims (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : ExtSpec) (tk : Array Nat) {pc : Piece (ckP .two) Fr T Cl Wt}
    (hds : pc.ds = dsLater par) (τ : Tr (uLT (ckP .two) pc.ds)) (z : X × Ex.Str)
    (a : Adds7 Q.full.own.toOwn.tail) (hc : Plan4.ClaimsAt A N tk hds τ z.1 a) :
    (Q.full.own.toOwn.ch.val Ex z ((Plan4.mapsAt A N Ex hds).view τ)).1 =
      (k4Tail (Plan4.tailMK A N) { par.P with tokv := tk } par.hp (tapeAt par pc τ)
        (Plan4.nzAt A tk hds τ _) a).z7 (z.1, ptOf Q (tapeAt par pc τ)) :=
  Plan4.val_at A N Ex tk hds τ _ _ a z.1 z.2 hc

/-- **The field `coin`.** -/
theorem Plan4.coin_of_yes (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : ExtSpec) (L : Seat T) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par)
    (s : T × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc s τ fo o G) (z : X × Ex.Str) (a : Adds7 Q.full.own.toOwn.tail)
    (hc : Plan4.ClaimsAt A N (L.tokv s.1) hds τ z.1 a) :
    (Q.full.layVO Q.full.wPart).epsOK
      (Q.full.own.toOwn.ch.val Ex z ((Plan4.mapsAt A N Ex hds).view τ)).1 :=
  Plan4.coin_at A N Ex (L.tokv s.1) hds τ _ _ a z.1 z.2 hc (small_of_all _ _ _ Y.small) Y.hears

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.mapsAt_ok
#print axioms OnBytes.Road.K4.Plan4.val_of_claims
#print axioms OnBytes.Road.K4.Plan4.coin_of_yes
