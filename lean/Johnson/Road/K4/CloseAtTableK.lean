-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseAtTableK.lean: K4's ROW AT THE TABLE OF JOINTS, in a group that is not the
first, WITH A PROMISE BEHIND THAT REMEMBERS THE ACCEPTING RUN. One lemma and one theorem: the text
of `RefSeat.k4_own_refS` (CloseAtTable.lean) with `keptFrom` (CloseRefFillK.lean) in the place of
`keptS`. No new argument.

OBJECT. `RefSeat.k4_own_refK`: `q.Own` between the table's promises at borders k and k + 1.
WHY. In `K4Lines` the lines forms and wo are asked at a statement b with `Lt.on' b` in hand. With
on' := `keptS p` that is «some state in front, of which nothing is known». With
on' := `keptFrom (tableOn0 …) p q` it is: b is the statement behind an accept of the piece at a
statement a that meets the table's promise at border k and bears no mark (`run_of_from`): so laws
of the form «inside the promise in front, at an accept: …» can be called as they lie.
USER. Meant: the lines forms and wo at the table's meaning. None yet.
LETTERS. As in CloseAtTable.lean.

Limits. K04_law IS NOT PROVED BY THIS. Every premise and every limit of CloseAtTable.lean's
`RefSeat.k4_own_refS` stands, `K4Lines` among them: the two lines only get one more fact in hand.
The reference sizes alone.
-/
import Johnson.Road.K4.CloseAtTable
import Johnson.Road.K4.CloseRefFillK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Fork Forest.elems)
open OnBytes.Model.Verify (Public)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.Sound (Frame Piece below onQ meansQ insQ outsQ strsOf)
open VerifiableInference.Desc.Plain.K04 (HearsAs FormsT frontRun)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable {P W : Type} {Fr : Frame}

/-- What the promise behind hands on at the table: the accepting run, inside the table's promise in
front, at a statement that bears no mark. -/
theorem run_of_from {Cl : Type} {N : Numbers} {Mg : Meaning P W} {Zt : P} {links : List ModelPart}
    {ps : List VerifiableInference.Desc.Place} {k : ℕ} {p : Par}
    {q : Piece (ckP .two) Fr S Cl W} {b : S × Fr.E.Str}
    (h : keptFrom (tableOn0 N Mg Zt links ps k) p q b) :
    ∃ a τ fo o G, onQ N Mg links ps (fun s => (Zt, s)) k a ∧ a.1.failed = none ∧
      Yes seatS p q a τ fo o G ∧ b = behindOf seatS q a τ o G := by
  obtain ⟨a, τ, fo, o, G, ha, Y, e⟩ := h
  exact ⟨a, τ, fo, o, G, ha.1, ha.2, Y, e⟩

variable [scl : Scl] {M Cl : Type}
variable {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **K4's row at the table, with a promise behind that remembers the accepting run**: from the
premises of `RefSeat.k4_own_refS`, `K4Lines` taken at `keptFrom (tableOn0 …) p q`. -/
theorem RefSeat.k4_own_refK (hscl : scl = sclX X p.g) (U : RefSeat M S) (hU : U.L = seatS)
    (hg : p.g < 12) (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hy : U.y = X.layers.y) (Ex : ExtSpec) (bk : Block S Cl)
    (q : Piece (ckP .two) Fr S Cl W) (hds : q.ds = dsLater p) (fe : S × Fr.E.Str → Ex.Str)
    (part : W → M) (hback : q.back = []) (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (lw : ℕ → LW Cb.Gl.E) {first : ℕ} {Q3 : Fork → Prop} {dec : S × Fr.E.Str → M}
    (hn : U.n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (hb : q.b = below bk) (hh : HearsAs seatS p bk)
    (hx : ∀ a τ b w, q.ior.red.out a τ = some b → q.ext a τ w = w) (N : Numbers)
    (Mg : Meaning P W) (Zt : P) {links : List ModelPart} {ps : List VerifiableInference.Desc.Place}
    {k m : ℕ} {pl pl' : VerifiableInference.Desc.Place}
    (H : AtK4 links ps k m pl) (Kf : K4Front Mg Zt links ps m p.P.y.fo p.P.y.h.lmb first Q3)
    (Kp : K4Keeps N Mg Zt links ps k m pl pl' q p)
    (Ln : K4Lines N Mg Zt m (U.atRec X p hg) part p
      ((U.atRec X p hg).lettersOf part p first p.P.y.fo Q3
        (tableOn0 N Mg Zt links ps k) (keptFrom (tableOn0 N Mg Zt links ps k) p q)
        (tableCtx0 N Mg Zt m) dec) dec q.base
      (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))) :
    q.Own (onQ N Mg links ps (fun s => (Zt, s)) k) (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))
      (meansQ N Mg (fun s => (Zt, s))) (insQ links ps k) (outsQ links ps k) := by
  have hlaw := RefSeat.k04Law_refK hscl U hU hg St B hP hG hg0 hy Ex bk q hds fe part hback hcap
    lw (on0 := tableOn0 N Mg Zt links ps k) hn hQ Ln.ctxRides Ln.decRides
  obtain ⟨y, nM, nR, nC, raw, maskAt, matAt, idxAt, L, n0, ns, nx, v7⟩ := U
  obtain rfl : L = seatS := hU
  exact k4_own_of_lines N Mg Zt H hlaw hb hh hback hx
    (fun a h1 h2 => ⟨⟨h1, h2⟩, k4_left_front N Mg Zt H Kf h1 h2⟩)
    (fun a τ b h1 h2 h3 _ => k4_promise_behind N Mg Zt H Kp hb hh hback a τ b h1 h2 h3)
    (k4Rel_fill _ part p Ln)
    (fun a τ b h3 hd => by
      obtain ⟨_, fo, o, G, yy, rfl⟩ := yes_of_out seatS hh hb hback a b τ h3
      exact Kp.dec a τ fo o G yy hd)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.run_of_from
#print axioms OnBytes.Road.K4.RefSeat.k4_own_refK
