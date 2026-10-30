-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRefFillS.lean: `K04Law` (Johnson/Desc/Plain/K04Plain.lean) AT THE FIRST CHAIN's
RECORD (`seatS`), AT THE REFERENCE VALUE (`RefSeat`, CloseRef.lean) AND THE FILLING OF
CloseFill.lean, in a group that is not the first, WITH WHAT HOLDS AT THAT SEAT LAID IN. A definition
and one theorem: a call of `RefSeat.k04Law_refFill`. Glue: `seatOk_S` (CloseSeated.lean),
`kept_of_yes` (KeptOfYes.lean), `sameRead_of_yes` (RidesBack.lean). No new argument.

  `keptS p b`: THE PROMISE BEHIND, FILLED BY MAKE: the record of b has what every yes of K4's block
  leaves (necessary, not sufficient): there is a record s with `KeptAtS p s b.1` (KeptAtS.lean).
  Nothing says that s is the record in front; nobody spends it.
  `RefSeat.k04Law_refS`: `K04Law` at every block bk and every type of claims. CONCLUDED AT THE SEAT:
  the seat's two laws · kept · «ctx0 rides back» and «dec reads the same behind a yes», each from
  ONE LINE ON THE LETTER, ASKED INSIDE THE PROMISE IN FRONT ALONE: it reads of a statement only what
  a yes leaves (`SameRead`: of the carried record: seven fields; in a layers' link all of the link
  but the ledger and what K4 heard; elsewhere four readers of the link · the stored table · the
  trees sent in front of the stretch).

WHAT IT STILL TAKES: `PublicSteps pol KL X` (who pays it: CloseRef.lean's limits) · `RefPub X p.g`
(RefPub.lean; who pays it: CloseRef.lean's head) · the table of scales is the record's; the place
holds the record's layers and the group's plan; g is not 0 and below 12; the value's layout is the
record's; its seat is `seatS` · the piece's rounds are K4's, it puts no round behind them, its
errors are the cap · n0 is first + the number of elements that the lookup hears; Q3 bounds the
number of slots · the two lines on ctx0 and dec. And, inside `K04Law`: the piece holds `below bk`,
and bk hears as K4's own block at the seat (`HearsAs`).

Limits. K04_law IS NOT PROVED BY THIS: IT IS `K04Law` AT LETTERS CHOSEN FOR THIS ROAD, UNDER THE
PREMISES NAMED ABOVE. That the items and promises of the table of joints are the filling's
sentences, or bound them (four implications: the table's promise in front gives the filling's; at a
yes the filling's promise behind gives the table's; what the table's row opens gives what the
filling's opens; what the filling's closes gives what the table's closes), is not shown. ctx HOLDS
«part w is dec a» BY MAKE (CloseFill.lean's head): no step of soundness lies in the passage from
`K04LawAt` to `K04Law` here. THE PROMISE IN FRONT HOLDS `K3LeftAt`, WHICH NO FILE HERE PROVES OF ANY
RECORD. on0, ctx0, dec, part, fe, Ex, first, Q3 and the other letters of `RefSeat` are filled by
nobody. That what the row opens is met at some yes is shown by nothing here. USER:
`RefSeat.k04Law_scopeS` (CloseScopeS.lean [not in this library]). The reference sizes alone.

-/
import Johnson.Road.K4.CloseRefFill
import Johnson.Road.K4.CloseSeated
import Johnson.Road.K4.RidesBack

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
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (K04Law)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

/-- The promise behind, by make: a record with what every yes of K4's block leaves. -/
def keptS {Fr : Frame} (p : Par) (b : S × Fr.E.Str) : Prop := ∃ s, KeptAtS p s b.1

variable [scl : Scl] {M Wt Cl : Type} {Fr : Frame} {pol KL : ByteArray}
  {X : Public} {p : Par} {tk : Array Nat}

/-- **`K04Law` at the first chain's record, the reference value and the filling, in a group that is
not the first**: from `PublicSteps`, `RefPub`, the premises on the table of scales, the place,
the layout and the seat, the piece's rounds and back, that its errors are the cap, n0, the bound on
Q3 and the two lines on ctx0 and dec. -/
theorem RefSeat.k04Law_refS (hscl : scl = sclX X p.g) (U : RefSeat M S) (hU : U.L = seatS)
    (hg : p.g < 12) (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hy : U.y = X.layers.y) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block S Cl) (pc : Piece (ckP .two) Fr S Cl Wt)
    (hds : pc.ds = dsLater p) (fe : S × Fr.E.Str → Ex.Str) (part : Wt → M)
    (hback : pc.back = []) (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds))
    (lw : ℕ → LW Cb.Gl.E) {first : ℕ} {Q3 : Fork → Prop} {on0 : S × Fr.E.Str → Prop}
    {ctx0 : S × Fr.E.Str → Wt → Prop} {dec : S × Fr.E.Str → M}
    (hn : U.n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (hctx : ∀ (x y : S × Fr.E.Str) w,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 (keptS p) ctx0 dec).on x →
      SameRead pc.base x y → ctx0 y w → ctx0 x w)
    (hdec : ∀ x y : S × Fr.E.Str,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 (keptS p) ctx0 dec).on x →
      SameRead pc.base x y → dec y = dec x) :
    K04Law U.L ((U.atRec X p hg).semOf part p.hp.tl)
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 (keptS p) ctx0 dec) p bk pc := by
  obtain ⟨y, nM, nR, nC, raw, maskAt, matAt, idxAt, L, n0, ns, nx, v7⟩ := U
  obtain rfl : L = seatS := hU
  exact RefSeat.k04Law_refFill hscl _ hg St B hP hG hg0 hy
    (fun _ _ hl => seatOk_S hl) Ex bk pc hds fe part hback hcap lw hn hQ
    (fun a _ _ _ _ w ha Y h => hctx a _ w ha (sameRead_of_yes Y) h)
    (fun a _ _ _ _ ha Y => hdec a _ ha (sameRead_of_yes Y))
    (fun a _ _ _ _ _ Y => ⟨a.1, kept_of_yes Y⟩)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.k04Law_refS
