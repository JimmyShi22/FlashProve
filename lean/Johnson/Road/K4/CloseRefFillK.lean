-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRefFillK.lean: `K04Law` (Johnson/Desc/Plain/K04Plain.lean) at the verifier's
state of the first chain (`seatS`), at the reference value and the filling of CloseFill.lean, in a
group that is not the first, WITH A PROMISE BEHIND THAT REMEMBERS THE ACCEPTING RUN. A definition,
a lemma and one theorem: a call of `RefSeat.k04Law_refFill`. No new argument.

OBJECT. `keptFrom on₀ p pc b`: b IS the statement behind an accept of K4's piece pc at a statement a
that meets on₀: there are a, a transcript τ and what the hearing returns (fo, o, G) with on₀ a,
`Yes seatS p pc a τ fo o G` and b = `behindOf seatS pc a τ o G`.
WHY. CloseRefFillS.lean fills the promise behind with `keptS p b` («some state s with
`KeptAtS p s b.1`»): of s nothing else is known. Whoever must show a line at b (the lines forms and
wo of `K4Lines`, CloseAtTable.lean) has then no accepting run and no promise in front in hand, while
every law that could pay such a line speaks of a state in front INSIDE the promise in front. The law
has both in hand where it shows the promise behind, so it can hand them on.
USER. `RefSeat.k4_own_refK` (CloseAtTableK.lean).
LETTERS. As in CloseRefFillS.lean; on' is `keptFrom on0 p pc`.

WHAT IT STILL TAKES: all that `RefSeat.k04Law_refS` takes, word for word, with `keptFrom on0 p pc`
in the place of `keptS p`.

Limits. K04_law IS NOT PROVED BY THIS: it is `K04Law` at letters chosen for this road, under the
premises named in CloseRefFillS.lean; every limit said there holds here. `keptFrom` is filled by
make: it says nothing of whether an accepting run exists. The reference sizes alone.
-/
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
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

/-- The promise behind, by make, WITH ITS RUN: b is the statement behind an accept of the piece at a
statement that meets on₀. -/
def keptFrom {Fr : Frame} {Cl Wt : Type} (on₀ : S × Fr.E.Str → Prop) (p : Par)
    (pc : Piece (ckP .two) Fr S Cl Wt) (b : S × Fr.E.Str) : Prop :=
  ∃ a τ fo o G, on₀ a ∧ Yes seatS p pc a τ fo o G ∧ b = behindOf seatS pc a τ o G

/-- It gives the weaker promise behind of CloseRefFillS.lean. -/
theorem keptS_of_from {Fr : Frame} {Cl Wt : Type} {on₀ : S × Fr.E.Str → Prop} {p : Par}
    {pc : Piece (ckP .two) Fr S Cl Wt} {b : S × Fr.E.Str} (h : keptFrom on₀ p pc b) :
    keptS p b := by
  obtain ⟨a, τ, fo, o, G, _, Y, rfl⟩ := h
  exact ⟨a.1, kept_of_yes Y⟩

variable [scl : Scl] {M Wt Cl : Type} {Fr : Frame} {pol KL : ByteArray}
  {X : Public} {p : Par} {tk : Array Nat}

/-- **`K04Law` at the first chain's state, the reference value and the filling whose promise behind
remembers the accepting run, in a group that is not the first**: from the premises of
`RefSeat.k04Law_refS`, with `keptFrom on0 p pc` in the place of `keptS p`. -/
theorem RefSeat.k04Law_refK (hscl : scl = sclX X p.g) (U : RefSeat M S) (hU : U.L = seatS)
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
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 (keptFrom on0 p pc) ctx0 dec).on x →
      SameRead pc.base x y → ctx0 y w → ctx0 x w)
    (hdec : ∀ x y : S × Fr.E.Str,
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 (keptFrom on0 p pc) ctx0 dec).on x →
      SameRead pc.base x y → dec y = dec x) :
    K04Law U.L ((U.atRec X p hg).semOf part p.hp.tl)
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3 on0 (keptFrom on0 p pc) ctx0 dec)
      p bk pc := by
  obtain ⟨y, nM, nR, nC, raw, maskAt, matAt, idxAt, L, n0, ns, nx, v7⟩ := U
  obtain rfl : L = seatS := hU
  exact RefSeat.k04Law_refFill hscl _ hg St B hP hG hg0 hy
    (fun _ _ hl => seatOk_S hl) Ex bk pc hds fe part hback hcap lw hn hQ
    (fun a _ _ _ _ w ha Y h => hctx a _ w ha (sameRead_of_yes Y) h)
    (fun a _ _ _ _ ha Y => hdec a _ ha (sameRead_of_yes Y))
    (fun a τ fo o G ha Y => ⟨a, τ, fo, o, G, ha.1, Y, rfl⟩)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.keptS_of_from
#print axioms OnBytes.Road.K4.RefSeat.k04Law_refK
