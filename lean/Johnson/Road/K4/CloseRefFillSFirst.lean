-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRefFillSFirst.lean: `K04Law` (Johnson/Desc/Plain/K04Plain.lean) IN THE FIRST
GROUP, AT THE FIRST CHAIN's RECORD (`seatS`), AT THE REFERENCE VALUE (`RefSeat.atRecF`,
CloseRefFirst.lean) AND THE FILLING OF CloseFillFirst.lean, WITH WHAT HOLDS AT THAT SEAT LAID IN.
The twin of Johnson/Road/K4/CloseRefFillS.lean. One theorem: a call of `RefSeat.k04Law_refFillF`.
Glue: `seatOk_S` (CloseSeated.lean), `kept_of_yes` (KeptOfYes.lean), `sameRead_of_yes`
(RidesBack.lean), `keptS` (CloseRefFillS.lean): NONE OF THEM NAMES A GROUP: they are taken as they
stand. No new argument.

  `RefSeat.k04Law_refSF`: `K04Law` at every block bk and every type of claims. CONCLUDED AT THE
    SEAT: the seat's two laws · kept · «ctx0 rides back» and «dec reads the same behind a yes», each
    from one line on the letter, asked inside the promise in front alone (`SameRead`).

AT THIS SEAT THE TOKENS OF (J11) ARE seatS.tokv s, read as (seatS.tokv s).getD q 0.

Limits. K04_law IS NOT PROVED BY THIS: IT IS `K04Law` AT LETTERS CHOSEN FOR THIS ROAD, UNDER
PREMISES. WHAT IT STILL TAKES: `PublicSteps pol KL X`, `RefPub X p.g`, la = 16, the plan's size of
the vocabulary is ppref.V, `EmbNums` at the plan's layout (the file that pays the five at all public
files in the goals' scope, CloseScopeSFirst.lean, is not in this library) · the table of scales is
the record's; the place holds the record's layers and the group's plan; g is 0; the value's layout
is the record's; its seat is `seatS` · the piece's rounds are K4's in the first group, it puts no
round behind them, its errors are the cap · n0; Q3 bounds the number of slots · the two lines on
ctx0 and dec. And, inside `K04Law`: the piece holds `below bk`, and bk hears as K4's own block at
the seat. That the items and promises of the table of joints are the filling's sentences, or bound
them as CloseTo.lean [not in this library] asks, is not shown: AMONG THEM THAT THE ITEM idn MEANS
THE 17 IDENTITIES AND (J11) AT THE SEAT's TOKENS, AND THAT THE ITEM wo GIVES THE ROW's SENTENCE
`WoRowF`, WHICH SAYS «THERE ARE». THE PROMISE IN FRONT HOLDS `K3LeftAt`, WHICH NO FILE HERE PROVES
OF ANY RECORD. on0, ctx0, dec, part, fe, Ex, first, Q3 and the other letters of `RefSeat` are filled
by nobody. The reads are true by make. ctx HOLDS «part w is dec a» BY MAKE (CloseFillFirst.lean's
head): no step of soundness lies in the passage from `K04LawAt` to `K04Law` here. `keptS` is
necessary, not sufficient (CloseRefFillS.lean's head); nobody spends it. OBJECT: the block bk is a
letter; inside `K04Law` it hears as K4's own block at the seat. USER: `RefSeat.k4_own_refSF`
(CloseAtTableFirst.lean), `RefSeat.k04Law_scopeSF` (CloseScopeSFirst.lean [not in this library]).
LETTERS: by the caller's choice: the table of scales, the value's layout, seat and n0. The reference
sizes alone. The first group alone.
-/
import Johnson.Road.K4.CloseRefFillFirst
import Johnson.Road.K4.CloseRefFillS

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
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {M Wt Cl : Type} {Fr : Frame} {X : Public} {p : Par} {tk : Array Nat}

/-- **`K04Law` at the first chain's record, the reference value and the filling, in the first
group**: from `PublicSteps`, `RefPub`, la = 16, the premises on the table of scales, the place, the
layout and the seat, the piece's rounds and back, that its errors are the cap, n0, the bound on Q3,
the two lines on ctx0 and dec, the size of the vocabulary and `EmbNums`. -/
theorem RefSeat.k04Law_refSF {pol KL : ByteArray} (hscl : scl = sclX X p.g) (U : RefSeat M S)
    (hU : U.L = seatS) (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true)
    (hla : (layerShape X.P).la = 16) (hy : U.y = X.layers.y) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block S Cl) (pc : Piece (ckP .two) Fr S Cl Wt)
    (hds : pc.ds = dsFirst p) (fe : S × Fr.E.Str → Ex.Str) (part : Wt → M)
    (hback : pc.back = []) (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds))
    (lw : ℕ → LW Cb.Gl.E) {first : ℕ} {Q3 : Fork → Prop} {on0 : S × Fr.E.Str → Prop}
    {ctx0 : S × Fr.E.Str → Wt → Prop} {dec : S × Fr.E.Str → M}
    (hn : U.n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (hctx : ∀ (x y : S × Fr.E.Str) w,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 (keptS p) ctx0 dec).on x →
      SameRead pc.base x y → ctx0 y w → ctx0 x w)
    (hdec : ∀ x y : S × Fr.E.Str,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 (keptS p) ctx0 dec).on x →
      SameRead pc.base x y → dec y = dec x)
    (hV : p.P.V = ppref.V) (NE : EmbNums p.P.y) :
    K04Law U.L ((U.atRecF X p).toPlan4K.semOf part p.hp.tl)
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 (keptS p) ctx0 dec) p bk pc := by
  obtain ⟨y, nM, nR, nC, raw, maskAt, matAt, idxAt, L, n0, ns, nx, v7⟩ := U
  obtain rfl : L = seatS := hU
  exact RefSeat.k04Law_refFillF hscl _ St B hP hG hg0 hla hy
    (fun _ _ hl => seatOk_S hl) Ex bk pc hds fe part hback hcap lw hn hQ
    (fun a _ _ _ _ w ha Y h => hctx a _ w ha (sameRead_of_yes Y) h)
    (fun a _ _ _ _ ha Y => hdec a _ ha (sameRead_of_yes Y))
    (fun a _ _ _ _ _ Y => ⟨a.1, kept_of_yes Y⟩) hV NE

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.k04Law_refSF
