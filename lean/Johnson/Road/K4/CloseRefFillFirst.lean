-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRefFillFirst.lean: `K04LawAt` AND `K04Law` (Johnson/Desc/Plain/K04Plain.lean)
IN THE FIRST GROUP, AT THE REFERENCE VALUE AT A SEAT (`RefSeat.atRecF`,
Johnson/Road/K4/CloseRefFirst.lean) AND THE FILLING OF Johnson/Road/K4/CloseFillFirst.lean. The twin
of Johnson/Road/K4/CloseRefFill.lean. Two theorems: calls. Glue: `lettersAreF_fill`, `ctx_fillF`
(CloseFillFirst.lean), `Plan4K.readsAre_fill` (CloseFill.lean), `planes_steps` (RefPubSteps.lean: it
names no group) laid into `RefSeat.k04LawAt_refF`; the pin by `k04Law_of_dec` (ClosePin.lean). No
new argument, no draw, no count.

Limits. K04_law IS NOT PROVED BY THIS: IT IS `K04Law` AT LETTERS CHOSEN FOR THIS ROAD, UNDER
PREMISES. WHAT STAYS A PREMISE: `PublicSteps pol KL X` · `RefPub X p.g` · la = 16 · the plan's size
of the vocabulary is ppref.V · `EmbNums` at the plan's layout · the table of scales is the record's
· the place holds the record's layers and the group's plan; g is 0 · the value's layout is the
record's · the seat's two laws · pc.ds, pc.back, that the errors are the cap · n0; the bound on Q3 ·
ctx0 rides back; dec reads the same behind a yes as in front · kept. All limits of
CloseFillFirst.lean and CloseRefFirst.lean stand. ctx HOLDS «part w is dec a» BY MAKE
(CloseFillFirst.lean's head): no step of soundness lies in the passage from `K04LawAt` to `K04Law`
here. The reference sizes alone. The first group alone. USER: `RefSeat.k04Law_refSF`
(CloseRefFillSFirst.lean).
-/
import Johnson.Road.K4.CloseRefFirst
import Johnson.Road.K4.CloseFillFirst

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
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {M T Wt Cl : Type} {Fr : Frame} {pol KL : ByteArray}
  {X : Public} {p : Par} {tk : Array Nat}

/-- **`K04LawAt` at the reference value and the filling, in the first group**: from `PublicSteps`,
`RefPub`, la = 16, the premises on the table of scales, the place, the layout and the seat, the
piece's rounds and back, that its errors are the cap, n0, the bound on Q3, «ctx0 rides back», «dec
reads the same behind a yes», kept, the size of the vocabulary and `EmbNums`. -/
theorem RefSeat.k04LawAt_refFillF (hscl : scl = sclX X p.g) (U : RefSeat M T)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) (hy : U.y = X.layers.y)
    (hseat : ∀ x fo, U.L.look x = some fo → SeatOk U.L x)
    (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst p) (fe : T × Fr.E.Str → Ex.Str)
    (part : Wt → M) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (lw : ℕ → LW Cb.Gl.E) {first : ℕ}
    {Q3 : Fork → Prop} {on0 on' : T × Fr.E.Str → Prop} {ctx0 : T × Fr.E.Str → Wt → Prop}
    {dec : T × Fr.E.Str → M} (hn : U.n0 = first + Forest.elems X.layers.y.fo)
    (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (hc0 : ∀ a τ fo o G w,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → ctx0 (behindOf U.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → dec (behindOf U.L pc a τ o G) = dec a)
    (kept : ∀ a τ fo o G,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → on' (behindOf U.L pc a τ o G))
    (hV : p.P.V = ppref.V) (NE : EmbNums p.P.y) :
    K04LawAt U.L ((U.atRecF X p).toPlan4K.semOf part p.hp.tl)
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 on' ctx0 dec) part p bk pc :=
  RefSeat.k04LawAt_refF hscl U St B hP hG hg0 hla hy hseat _ _ Ex bk pc hds fe part
    hback hcap lw hn hQ (fun _ ha => ha.2)
    ((U.atRecF X p).lettersAreF_fill part (U.meetsF St B hP hG hg0 hla) Ex pc hds fe
      ((U.atRecF X p).ctx_fillF part pc hc0 hd))
    ((U.atRecF X p).toPlan4K.readsAre_fill part (planes_steps St hP hG).1
      (planes_steps St hP hG).2) hV NE kept (fun _ _ o hw ho => hw o ho)

/-- **`K04Law` at the reference value and the filling, in the first group**: from `PublicSteps`,
`RefPub`, la = 16, the premises on the table of scales, the place, the layout and the seat, the
piece's rounds and back, that its errors are the cap, n0, the bound on Q3, «ctx0 rides back», «dec
reads the same behind a yes», kept, the size of the vocabulary and `EmbNums`; the pin is had from
«part w is dec a», which ctx holds by make. -/
theorem RefSeat.k04Law_refFillF (hscl : scl = sclX X p.g) (U : RefSeat M T)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) (hy : U.y = X.layers.y)
    (hseat : ∀ x fo, U.L.look x = some fo → SeatOk U.L x)
    (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst p) (fe : T × Fr.E.Str → Ex.Str)
    (part : Wt → M) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (lw : ℕ → LW Cb.Gl.E) {first : ℕ}
    {Q3 : Fork → Prop} {on0 on' : T × Fr.E.Str → Prop} {ctx0 : T × Fr.E.Str → Wt → Prop}
    {dec : T × Fr.E.Str → M} (hn : U.n0 = first + Forest.elems X.layers.y.fo)
    (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (hc0 : ∀ a τ fo o G w,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → ctx0 (behindOf U.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → dec (behindOf U.L pc a τ o G) = dec a)
    (kept : ∀ a τ fo o G,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 on' ctx0 dec).on a →
      Yes U.L p pc a τ fo o G → on' (behindOf U.L pc a τ o G))
    (hV : p.P.V = ppref.V) (NE : EmbNums p.P.y) :
    K04Law U.L ((U.atRecF X p).toPlan4K.semOf part p.hp.tl)
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 on' ctx0 dec) p bk pc :=
  k04Law_of_dec U.L _ _ part p bk pc hback
    (RefSeat.k04LawAt_refFillF hscl U St B hP hG hg0 hla hy hseat Ex bk pc hds fe part
      hback hcap lw hn hQ hc0 hd kept hV NE)
    dec (fun _ _ hw => hw.2) hd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.k04LawAt_refFillF
#print axioms OnBytes.Road.K4.RefSeat.k04Law_refFillF
