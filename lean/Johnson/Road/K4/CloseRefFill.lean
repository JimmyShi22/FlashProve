-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRefFill.lean: `K04LawAt` AND `K04Law` (Johnson/Desc/Plain/K04Plain.lean) AT THE
REFERENCE VALUE (`RefSeat`, Johnson/Road/K4/CloseRef.lean) AND AT THE FILLING OF THE STATEMENT's
LETTERS OF Johnson/Road/K4/CloseFill.lean, in a group that is not the first. Two theorems: calls of
`RefSeat.k04LawAt_ref` and `k04Law_of_dec` at `Plan4K.semOf`, `Plan4K.nuOf`, `Plan4K.lettersOf`. No
new argument.

  `RefSeat.k04LawAt_refFill`, `RefSeat.k04Law_refFill`: WHAT THEY TAKE: `PublicSteps pol KL X` ·
  `RefPub X p.g` (RefPub.lean) · the table of scales is the record's; the place holds the record's
  layers and the group's plan; g is not 0 and below 12; the value's layout is the record's · the
  seat's two laws wherever the seat finds the lookup's return · the piece's rounds are K4's, it puts
  no round behind them, its errors are the cap · n0 is first + the number of elements that the
  lookup hears; Q3 bounds the number of slots · ctx0 rides back from behind a yes to in front · dec
  reads the same behind a yes as in front · kept. The planes' matrix's rows and columns are
  concluded (`planes_steps`, RefPubSteps.lean).

Limits. K04_law IS NOT PROVED BY THIS: IT IS `K04Law` AT LETTERS CHOSEN FOR THIS ROAD, UNDER THE
PREMISES NAMED ABOVE. Who pays `RefPub`: CloseRef.lean's head. That the items of the table of joints
are the filling's sentences or follow from them is not shown (CloseFill.lean's head). on0, on',
ctx0, dec, part, fe, Ex, first, Q3 and the letters of `RefSeat` are filled by nobody. That some
record meets the promise in front, and that what the row opens is met at some yes, is shown by
nothing here. The reference sizes alone. USER: `RefSeat.k04Law_refS` (CloseRefFillS.lean).

-/
import Johnson.Road.K4.CloseRef
import Johnson.Road.K4.CloseFill
import Johnson.Road.K4.MemberPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Fork Forest.elems)
open OnBytes.Model.Verify (Public layerShape)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (K04Law K04LawAt)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {M T Wt Cl : Type} {Fr : Frame} {pol KL : ByteArray}
  {X : Public} {p : Par} {tk : Array Nat}

/-- **`K04LawAt` at the reference value and the filling, in a group that is not the first**: from
`PublicSteps`, `RefPub`, the premises on the table of scales, the place, the layout and the seat,
the piece's rounds and back, that its errors are the cap, n0, the bound on Q3, «ctx0 rides back»,
«dec reads the same behind a yes» and kept. -/
theorem RefSeat.k04LawAt_refFill (hscl : scl = sclX X p.g) (U : RefSeat M T) (hg : p.g < 12)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hy : U.y = X.layers.y)
    (hseat : ∀ x fo, U.L.look x = some fo → SeatOk U.L x)
    (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater p) (fe : T × Fr.E.Str → Ex.Str)
    (part : Wt → M) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (lw : ℕ → LW Cb.Gl.E) {first : ℕ}
    {Q3 : Fork → Prop} {on0 on' : T × Fr.E.Str → Prop} {ctx0 : T × Fr.E.Str → Wt → Prop}
    {dec : T × Fr.E.Str → M} (hn : U.n0 = first + Forest.elems X.layers.y.fo)
    (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (hc0 : ∀ a τ fo o G w,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → ctx0 (behindOf U.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → dec (behindOf U.L pc a τ o G) = dec a)
    (kept : ∀ a τ fo o G,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → on' (behindOf U.L pc a τ o G)) :
    K04LawAt U.L ((U.atRec X p hg).semOf part p.hp.tl)
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 on' ctx0 dec) part p bk pc :=
  RefSeat.k04LawAt_ref hscl U hg St B hP hG hg0 hy hseat _ _ Ex bk pc hds fe part
    hback hcap lw hn hQ (fun _ ha => ha.2)
    ((U.atRec X p hg).lettersAre_fill part (U.meets hg St B hP hG hg0) Ex pc hds fe
      ((U.atRec X p hg).ctx_fill part pc hc0 hd))
    ((U.atRec X p hg).readsAre_fill part (planes_steps St hP hG).1 (planes_steps St hP hG).2) kept
    (fun _ _ o hw ho => hw o ho)

/-- **`K04Law` at the reference value and the filling**, from the same premises; the pin is laid
into ctx by make. -/
theorem RefSeat.k04Law_refFill (hscl : scl = sclX X p.g) (U : RefSeat M T) (hg : p.g < 12)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hy : U.y = X.layers.y)
    (hseat : ∀ x fo, U.L.look x = some fo → SeatOk U.L x)
    (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater p) (fe : T × Fr.E.Str → Ex.Str)
    (part : Wt → M) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (lw : ℕ → LW Cb.Gl.E) {first : ℕ}
    {Q3 : Fork → Prop} {on0 on' : T × Fr.E.Str → Prop} {ctx0 : T × Fr.E.Str → Wt → Prop}
    {dec : T × Fr.E.Str → M} (hn : U.n0 = first + Forest.elems X.layers.y.fo)
    (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (hc0 : ∀ a τ fo o G w,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → ctx0 (behindOf U.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → dec (behindOf U.L pc a τ o G) = dec a)
    (kept : ∀ a τ fo o G,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → on' (behindOf U.L pc a τ o G)) :
    K04Law U.L ((U.atRec X p hg).semOf part p.hp.tl)
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 on' ctx0 dec) p bk pc :=
  k04Law_of_dec U.L _ _ part p bk pc hback
    (RefSeat.k04LawAt_refFill hscl U hg St B hP hG hg0 hy hseat Ex bk pc hds fe part
      hback hcap lw hn hQ hc0 hd kept)
    dec (fun _ _ hw => hw.2) hd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.k04LawAt_refFill
#print axioms OnBytes.Road.K4.RefSeat.k04Law_refFill
