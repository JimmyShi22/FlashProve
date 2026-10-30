-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRefFillKFirst.lean: `K04Law` (Johnson/Desc/Plain/K04Plain.lean) at the
verifier's state in the first chain (`seatS`), at the reference value and the filling of
CloseFillFirst.lean, IN THE FIRST GROUP, WITH A PROMISE BEHIND THAT REMEMBERS THE ACCEPTING RUN. The
twin of Johnson/Road/K4/CloseRefFillK.lean's theorem. One theorem: a call of
`RefSeat.k04Law_refFillF`. `keptFrom` (CloseRefFillK.lean) names no group: it is taken as it stands.
No new argument.

OBJECT, WHY: as in CloseRefFillK.lean: whoever must show a line at the statement b behind (the lines
forms and wo of `K4Lines`) has with `keptS p b` no accepting run and no promise in front in hand;
with `keptFrom on0 p pc b` it has both. USER: `RefSeat.k4_own_refKF` (CloseAtTableKFirst.lean).
LETTERS: as in CloseRefFillSFirst.lean; on' is `keptFrom on0 p pc`.

WHAT IT STILL TAKES: all that `RefSeat.k04Law_refSF` (CloseRefFillSFirst.lean) takes, word for word,
with `keptFrom on0 p pc` in the place of `keptS p`.

Limits. K04_law IS NOT PROVED BY THIS: it is `K04Law` at letters chosen for this road, under the
premises named in CloseRefFillSFirst.lean; every limit said there holds here. `keptFrom` is filled
by make: it says nothing of whether an accepting run exists. The reference sizes alone. The first
group alone.
-/
import Johnson.Road.K4.CloseRefFillSFirst
import Johnson.Road.K4.CloseRefFillK

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

/-- **`K04Law` at the verifier's state in the first chain, the reference value and the filling whose
promise behind remembers the accepting run, in the first group**: from the premises of
`RefSeat.k04Law_refSF`, with `keptFrom on0 p pc` in the place of `keptS p`. -/
theorem RefSeat.k04Law_refKF {pol KL : ByteArray} (hscl : scl = sclX X p.g) (U : RefSeat M S)
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
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 (keptFrom on0 p pc) ctx0 dec).on x →
      SameRead pc.base x y → ctx0 y w → ctx0 x w)
    (hdec : ∀ x y : S × Fr.E.Str,
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 (keptFrom on0 p pc) ctx0 dec).on x →
      SameRead pc.base x y → dec y = dec x)
    (hV : p.P.V = ppref.V) (NE : EmbNums p.P.y) :
    K04Law U.L ((U.atRecF X p).toPlan4K.semOf part p.hp.tl)
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3 on0 (keptFrom on0 p pc) ctx0 dec)
      p bk pc := by
  obtain ⟨y, nM, nR, nC, raw, maskAt, matAt, idxAt, L, n0, ns, nx, v7⟩ := U
  obtain rfl : L = seatS := hU
  exact RefSeat.k04Law_refFillF hscl _ St B hP hG hg0 hla hy
    (fun _ _ hl => seatOk_S hl) Ex bk pc hds fe part hback hcap lw hn hQ
    (fun a _ _ _ _ w ha Y h => hctx a _ w ha (sameRead_of_yes Y) h)
    (fun a _ _ _ _ ha Y => hdec a _ ha (sameRead_of_yes Y))
    (fun a τ fo o G ha Y => ⟨a, τ, fo, o, G, ha.1, Y, rfl⟩) hV NE

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.k04Law_refKF
