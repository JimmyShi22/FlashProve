-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRefFirst.lean: Johnson/Road/K4/CloseK5First.lean's TOP AT ONE NAMED VALUE: the
first group's value at the library's reference sizes (`refLF`, Johnson/Road/K4/RefValueFirst.lean)
with its letters, THE TOKENS AMONG THEM, read off a seat as `Plan4KF` reads them
(Johnson/Road/K4/ValueSeatFirst.lean), at a public record X of which `PublicSteps pol KL X`
(Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean: the steps of the public part that take no hash)
holds, in the first group. THE TOP's PREMISES ON PUBLIC NUMBERS ARE CONCLUDED FROM THESE STEPS, ONE
RECORD OF SENTENCES ON X, `RefPub X p.g` (Johnson/Road/K4/RefPub.lean), AND la = 16. The twin of
Johnson/Road/K4/CloseRef.lean. Two definitions and four theorems. Glue: the statements of
RefValueFirst.lean, RefPubFirst.lean, RefPubStepsFirst.lean, RefPubStepsFrontFirst.lean,
MemberFrontFirst.lean laid into `Plan4KF.k04LawAt_K5F`. No draw, no count. CloseRef.lean's record
`RefSeat`, its `mats`, `toK`, `letters`, `nTX`, `nIX` are taken as they stand (`toK` and `letters`
at the group 0).

  `RefSeat.toKF`: the value as a `Plan4KF`: `toK` at the group 0 with one slot more in ns, and ls :=
    6, nb := 80, gB := 7.
  `RefSeat.toLF_eq`: THE TWO ROADS GIVE ONE VALUE (by unfolding): (U.toKF nT nI).toLF is `refLF` at
    U's letters and at the tokens tok x q := (U.L.tokv x).getD q 0.
  `RefSeat.atRecF`, `RefSeat.atRecF_toLF`: the value at a record and a place.
  `RefSeat.meetsF`: `Plan4F.MeetsF` holds of it.
  `RefSeat.k04LawAt_refF`: `K04LawAt U.L Sm Lt part p bk pc` at a piece whose errors are the cap.
    CONCLUDED INSIDE, from `PublicSteps`, `RefPub`, la = 16 and the premises on the place:
    `MeetsF` · C · hk · `ValueIs` · `ValueMoreF` · the public lines · the rotary tables' fit · of
    `FrontIs` the lines fo, pub, ok · the matrices' zeros, D.P = ppref and kW = kRef (by make).
    `FrontIs`' line n0 is the premise hn, handed through.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE: `PublicSteps pol KL X` (paid by
`publicSteps_of` where `publicOf` returns X, by `publicSteps_of_O` where `publicOfO o` does, at
every o) · `RefPub X p.g` (who pays it: CloseRef.lean's head) · la = 16 · the plan's size of the
vocabulary is ppref.V · `EmbNums` (Johnson/Meaning/EmbWeight.lean) at the plan's layout · the
section's table of scales is the record's · the place holds the record's layers and the group's
plan; g is 0 · the value's layout is the record's · the seat's two laws wherever the seat finds the
lookup's return · pc.ds, pc.back, that the errors are the cap · n0 is first + the number of elements
that the lookup hears · THE PROMISE IN FRONT GIVES `K3LeftAt` AT THE SEAT's OWN READERS, AT THE
PLAN's SHAPE AND lmb, AND AT A LETTER Q3 THAT BOUNDS THE NUMBER OF SLOTS OF THE LEDGER IN FRONT OF
THE LOOKUP BY U.ns + 1 · EVERY LINE OF `LettersAreF` · EVERY LINE OF `ReadsAre` · kept · THE LINE ON
`Lt.wo` (it gives `WoRowF`). Nothing shows that these can be met together. The letters `Sem`,
`Letters`, part, fe, Ex, nu, first, Q3 and those of `RefSeat` are filled by nobody. The reference
sizes alone. The first group alone. USER: `RefSeat.k04LawAt_refFillF` (CloseRefFillFirst.lean).

-/
import Johnson.Road.K4.CloseK5First
import Johnson.Road.K4.CloseRef
import Johnson.Road.K4.MemberFrontFirst
import Johnson.Road.K4.RefPubStepsFrontFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Fork Forest.elems)
open OnBytes.Model.Layer (Lay nEndT)
open OnBytes.Model.Verify (Public layerShape)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par Seat)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters K04LawAt)
open VerifiableInference.OnPublicFiles (K3LeftAt)
open Inst.Model (Scl tbRef ppref)
open Meaning.Emb (EmbNums)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (Dim LW ref_chOK)

variable [scl : Scl] {M T Wt Cl : Type} {Fr : Frame}

/-- The first group's value at the reference sizes, its letters read off the seat. -/
noncomputable def RefSeat.toKF (U : RefSeat M T) (nT nI : ℕ) : Plan4KF M T where
  toPlan4K :=
    { U.toK 0 (by norm_num) nT nI with ns := (U.toK 0 (by norm_num) nT nI).ns + 1 }
  ls := 6
  nb := 80
  gB := 7
  hnb := by norm_num
  hd := ref_hd

/-- **The two roads give one value**, the tokens being the seat's. -/
theorem RefSeat.toLF_eq (U : RefSeat M T) (nT nI : ℕ) :
    (U.toKF nT nI).toLF =
      refLF (U.letters 0 (by norm_num) nT nI) (fun x q => (U.L.tokv x).getD q 0) nT nI := rfl

/-- The first group's value at a record and a place. -/
noncomputable abbrev RefSeat.atRecF (U : RefSeat M T) (X : Public) (p : Par) : Plan4KF M T :=
  U.toKF (nTX X) (nIX X p)

theorem RefSeat.atRecF_toLF (U : RefSeat M T) (X : Public) (p : Par) :
    (U.atRecF X p).toLF = refLF (U.letters 0 (by norm_num) (nTX X) (nIX X p))
      (fun x q => (U.L.tokv x).getD q 0) (nTX X) (nIX X p) := rfl

variable {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **`MeetsF` holds of it**, at a record with `PublicSteps` and `RefPub`, in the first group, where
la is 16. -/
theorem RefSeat.meetsF (U : RefSeat M T) (St : PublicSteps pol KL X)
    (B : RefPub X p.g) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) (hg0 : (p.g == 0) = true)
    (hla : (layerShape X.P).la = 16) :
    (U.atRecF X p).toLF.planF.MeetsF p (layerShape X.P) X.P.polCalls := by
  rw [U.atRecF_toLF]
  exact refSF_meets _ _ _ _ St B hP hG hg0 hla

/-- **`K04LawAt` at the reference value, at a seat, in the first group**, at a piece whose errors
are the cap: from `PublicSteps`, `RefPub`, la = 16, the premises on the table of scales, the
place, the layout and the seat, the piece's rounds and back, that its errors are the cap, n0, the
bound on Q3, the promise's line, `LettersAreF`, `ReadsAre`, the size of the vocabulary, `EmbNums`,
kept and the line on `Lt.wo`. -/
theorem RefSeat.k04LawAt_refF (hscl : scl = sclX X p.g) (U : RefSeat M T)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) (hy : U.y = X.layers.y)
    (hseat : ∀ x fo, U.L.look x = some fo → SeatOk U.L x)
    (Sm : Sem Wt) (Lt : Letters T Wt Fr) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block T Cl) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst p) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → M)
    (hback : pc.back = []) (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds))
    (lw : ℕ → LW Cb.Gl.E) {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ} {Q3 : Fork → Prop}
    (hn : U.n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (on : ∀ a, Lt.on a →
      K3LeftAt (fun s => some (U.L.fork s)) U.L.look p.P.y.fo p.P.y.h.lmb first Q3 a.1)
    (Ml : Plan4LF.LettersAreF (U.meetsF St B hP hG hg0 hla) U.L Sm Lt Ex pc hds
      (fun a => (a.1, fe a)) part nu first)
    (R : ReadsAre p Sm nu p.hp.tl p.P.y.fo fun w => U.mats (part w))
    (hV : p.P.V = ppref.V) (NE : EmbNums p.P.y)
    (kept : ∀ a τ fo o G, Lt.on a → Yes U.L p pc a τ fo o G → Lt.on' (behindOf U.L pc a τ o G))
    (hwo : ∀ b w o, Lt.wo b w → U.L.own b.1 = some o → (U.atRecF X p).WoRowF p o (part w)) :
    K04LawAt U.L Sm Lt part p bk pc := by
  obtain ⟨s0, H, N⟩ := refSF_frontIs (T := T) (Wt := Wt) (Fr := Fr)
    (U.letters 0 (by norm_num) (nTX X) (nIX X p)) (fun x q => (U.L.tokv x).getD q 0)
    (nTX X) (nIX X p) St B hP hG
  have V : Plan4L.ValueIs (U.atRecF X p).toLF.toPlan4L p (layerShape X.P) := by
    rw [U.atRecF_toLF]
    exact refSF_valueIs hscl _ _ St B hP hG hg0 hla
  have V2 : Plan4LF.ValueMoreF (U.atRecF X p).toLF := by
    rw [U.atRecF_toLF]
    exact refF_valueMore _ _ _ _
  have hy' : (U.atRecF X p).y = p.P.y := by
    rw [hP]
    exact hy
  exact (U.atRecF X p).k04LawAt_K5F (U.meetsF St B hP hG hg0 hla) Sm Lt Ex bk pc hds fe part hback
    hcap ref_chOK (fun l _ => refP_hk hscl B hG l) V V2 lw
    (fun F hF => Nat.le_trans (hQ F hF)
      (Nat.succ_le_succ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)))) hy'
    (fun _ _ _ _ hb => if_neg hb) hseat H
    (fun a τ fo o G Y => refPF_rope (U.letters 0 (by norm_num) (nTX X) (nIX X p))
      (fun x q => (U.L.tokv x).getD q 0) (nTX X) (nIX X p) B hP U.L pc a τ fo o G Y)
    Ml (N U.L Lt first Q3 hn on) R rfl rfl hV NE kept hwo

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.toLF_eq
#print axioms OnBytes.Road.K4.RefSeat.atRecF_toLF
#print axioms OnBytes.Road.K4.RefSeat.meetsF
#print axioms OnBytes.Road.K4.RefSeat.k04LawAt_refF
