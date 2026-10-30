-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CloseYesFirst.lean: Johnson/Road/K4/CloseValFirst.lean AT A YES OF THE PIECE THAT
HOLDS K4's OWN BLOCK (`Yes`, Johnson/Road/K4/CarriageHeard.lean), IN THE FIRST GROUP: the carriage's
maps, the tape, the chain's value and the field `coin`. The twin of
Johnson/Road/K4/CloseYes.lean. Two definitions and six theorems. Glue: no new argument, no count.

  `Plan4F.mapsAtF A N Ex hds`: the carriage's maps at a piece whose written rounds are K4's declared
    ones (hds : pc.ds = dsFirst par): `Plan4F.mapsK4F` carried along hds. `Plan4F.mapsAtF_ok`:
    `Maps.OK`.
  `Plan4F.nzAtF`: on the tape that K4's hearing hears (`tapeAt`, CloseYes.lean), behind the three
    points' rounds, no further challenge reads 0.
  `Plan4F.ClaimsAtF A N tk hds τ x a`: `TailH.Claims` holds of the data read off that tape, at the
    seven states and targets a, at the first statement x with the three points.
    `Plan4F.claimsAtF_exist`: THERE ARE SUCH a, AT EVERY TRANSCRIPT, WITH NO FURTHER PREMISE
    (`claims_exist`,
    OnBytes/Desc/First/P1/ClaimsFree.lean): states and targets are free letters. So
    `ClaimsAtF` at SOME a says nothing of K4's records.
  `Plan4F.val_of_claimsF`: under `ClaimsAtF`: the chain's value on the maps' image of τ is `z7` of
    these data.
  `Plan4F.coin_of_yesF`: at a `Yes`, under `ClaimsAtF`: the coefficient drawn in the sumcheck of the
    terms, as the chain reads it, is not 0. `Plan4F.coin_yesF`: so at every `Yes`, outright: the
    field `coin` of `Plan4F.HeardL`.

Limits. `Plan4F.MeetsF` and hds ARE PREMISES; `ClaimsAtF` at a is one of `val_of_claimsF` and
`coin_of_yesF`. The first group. Those of
CloseValFirst.lean and CarriageHeard.lean.
-/
import Johnson.Road.K4.CloseValFirst
import Johnson.Road.K4.CloseYes
import OnBytes.Desc.First.P1.ClaimsFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open Cb.Pv.Lay.End.Gated (tailW)
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Aff)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.P1 (NzT Adds7 TailNums tapeW tailT claims_exist)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open Inst.Model (Scl)
open _root_.Run (ckP)

variable [scl : Scl] {M X T Wt Cl : Type} {Fr : Frame} {Q : Plan4F Cb.Gl.E M X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The carriage's maps at a piece whose written rounds are K4's declared ones. -/
noncomputable def Plan4F.mapsAtF (A : Q.MeetsF par hS pcl)
    (N : TailNums Q.fullF.ownF.toOwn.tail) (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt}
    (hds : pc.ds = dsFirst par) : Maps pc.ds ((chFF Q.fullF).R Ex).shape :=
  (Plan4F.mapsK4F A N Ex).castD hds

theorem Plan4F.mapsAtF_ok (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par) :
    (Plan4F.mapsAtF A N Ex hds).OK :=
  Maps.ok_castD hds (Plan4F.mapsK4F_ok A N Ex)

/-- Behind the three points' rounds no further challenge reads 0. -/
theorem Plan4F.nzAtF (A : Q.MeetsF par hS pcl) (tk : Array Nat) {ds : List RDT}
    (e : ds = dsFirst par) (τ : Tr (uLT (ckP .two) ds)) (es : List Fmt.Entry) :
    NzT Q.fullF.ownF.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      (tb3 (tapeW noDigest ds τ es)) := by
  subst e
  exact Plan4F.nz_atF A tk τ es

/-- `TailH.Claims` at the data read off the tape, at seven states and targets. -/
def Plan4F.ClaimsAtF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (tk : Array Nat) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (τ : Tr (uLT (ckP .two) pc.ds)) (x : X) (a : Adds7 Q.fullF.ownF.toOwn.tail) : Prop :=
  (tailT (Plan4F.tailMKF A N) (ksOf { par.P with tokv := tk } par.hp) (tb3 (tapeAt par pc τ))
    (Plan4F.nzAtF A tk hds τ _) a).Claims (x3Of Q x (tapeAt par pc τ))

/-- There are such states and targets, at every transcript: no further premise. -/
theorem Plan4F.claimsAtF_exist (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (tk : Array Nat) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (τ : Tr (uLT (ckP .two) pc.ds)) (x : X) : ∃ a, Plan4F.ClaimsAtF A N tk hds τ x a :=
  claims_exist (Plan4F.tailMKF A N) (ksOf { par.P with tokv := tk } par.hp)
    (tb3 (tapeAt par pc τ)) (Plan4F.nzAtF A tk hds τ _) (x3Of Q x (tapeAt par pc τ))

/-- **The first chain's value on the maps' image of the transcript.** -/
theorem Plan4F.val_of_claimsF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : ExtSpec) (tk : Array Nat) {pc : Piece (ckP .two) Fr T Cl Wt}
    (hds : pc.ds = dsFirst par) (τ : Tr (uLT (ckP .two) pc.ds)) (z : X × Ex.Str)
    (a : Adds7 Q.fullF.ownF.toOwn.tail) (hc : Plan4F.ClaimsAtF A N tk hds τ z.1 a) :
    ((chFF Q.fullF).val Ex z ((Plan4F.mapsAtF A N Ex hds).view τ)).1 =
      (tailT (Plan4F.tailMKF A N) (ksOf { par.P with tokv := tk } par.hp)
        (tb3 (tapeAt par pc τ)) (Plan4F.nzAtF A tk hds τ _) a).z7 (x3Of Q z.1 (tapeAt par pc τ)) :=
  Plan4F.val_atF A N Ex tk hds τ _ _ a z.1 z.2 hc

/-- The coefficient is not 0, under `ClaimsAtF` at a. -/
theorem Plan4F.coin_of_yesF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : ExtSpec) (L : Seat T) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (s : T × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc s τ fo o G) (z : X × Ex.Str) (a : Adds7 Q.fullF.ownF.toOwn.tail)
    (hc : Plan4F.ClaimsAtF A N (L.tokv s.1) hds τ z.1 a) :
    ((tailW Q.fullF).b3
      ((chFF Q.fullF).val Ex z ((Plan4F.mapsAtF A N Ex hds).view τ)).1).2.eps ≠ 0 := by
  rw [Plan4F.val_of_claimsF A N Ex (L.tokv s.1) hds τ z a hc]
  have hh : hear engFl { par.P with tokv := L.tokv s.1 } par.hp par.g fo (L.fork s.1)
      (tapeAt par pc τ) = some (o, G, []) := Y.hears
  have hs : SmallTape (tapeAt par pc τ) := small_of_all _ _ _ Y.small
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, v1, v2, v5, u4, u5, cl, _, _, hz,
    _, _, c3, _⟩ := own_callsG hh
  rw [tb3_eq _ A.hg] at c3
  exact tail_coin (Plan4F.tailMKF A N) (((hs.drop 1).drop 1).drop 1) c3 hz
    (Plan4F.nzAtF A (L.tokv s.1) hds τ _) a _ hc

/-- **The field `coin`**, at every `Yes`, outright. -/
theorem Plan4F.coin_yesF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : ExtSpec) (L : Seat T) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (s : T × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc s τ fo o G) (z : X × Ex.Str) :
    ((tailW Q.fullF).b3
      ((chFF Q.fullF).val Ex z ((Plan4F.mapsAtF A N Ex hds).view τ)).1).2.eps ≠ 0 := by
  obtain ⟨a, hc⟩ := Plan4F.claimsAtF_exist A N (L.tokv s.1) hds τ z.1
  exact Plan4F.coin_of_yesF A N Ex L hds s τ Y z a hc

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.mapsAtF_ok
#print axioms OnBytes.Road.K4.Plan4F.val_of_claimsF
#print axioms OnBytes.Road.K4.Plan4F.coin_of_yesF
#print axioms OnBytes.Road.K4.Plan4F.claimsAtF_exist
#print axioms OnBytes.Road.K4.Plan4F.coin_yesF
