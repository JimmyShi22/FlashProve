-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseAtTableKFirst.lean: K4's ROW AT THE TABLE OF JOINTS IN THE FIRST GROUP, WITH A
PROMISE BEHIND THAT REMEMBERS THE ACCEPTING RUN. The twin of Johnson/Road/K4/CloseAtTableK.lean's
theorem. One theorem: the text of `RefSeat.k4_own_refSF` (CloseAtTableFirst.lean) with `keptFrom`
(CloseRefFillK.lean) in the place of `keptS`. `run_of_from` (CloseAtTableK.lean) and `k4Rel_fillF`
(CloseAtTableFirst.lean: general in the promise behind) are taken as they stand. No new argument.

OBJECT: `RefSeat.k4_own_refKF`: `q.Own` between the table's promises at borders k and k + 1. WHY: as
in CloseAtTableK.lean: in `K4Lines` the lines forms and wo are asked at a statement b with `Lt.on'
b` in hand; with on' := `keptFrom (tableOn0 …) p q` that is: b is the statement behind an accept of
the piece at a statement that meets the table's promise at border k and bears no mark
(`run_of_from`). USER: none here; meant: the lines forms and wo at the table's meaning. LETTERS: as
in CloseAtTableFirst.lean.

Limits. K04_law IS NOT PROVED BY THIS. Every premise and every limit of CloseAtTableFirst.lean's
`RefSeat.k4_own_refSF` stands, `K4Lines` among them, and its open question on the line idn: the two
lines forms and wo only get one more fact in hand. The reference sizes alone. The first group alone.

-/
import Johnson.Road.K4.CloseAtTableFirst
import Johnson.Road.K4.CloseRefFillKFirst
import Johnson.Road.K4.CloseAtTableK

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
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.Sound (Frame Piece below onQ meansQ insQ outsQ strsOf)
open VerifiableInference.Desc.Plain.K04 (HearsAs)
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open Inst.Model.FFSeg (LW)

variable {P W : Type} {Fr : Frame} [scl : Scl] {M Cl : Type}

variable {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **K4's row at the table in the first group, with a promise behind that remembers the accepting
run**: from the premises of `RefSeat.k4_own_refSF`, `K4Lines` taken at `keptFrom (tableOn0 …) p q`.
-/
theorem RefSeat.k4_own_refKF (hscl : scl = sclX X p.g) (U : RefSeat M S) (hU : U.L = seatS)
    (St : PublicSteps pol KL X) (B : RefPub X p.g)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hla : (layerShape X.P).la = 16) (hy : U.y = X.layers.y)
    (Ex : ExtSpec) (bk : Block S Cl)
    (q : Piece (ckP .two) Fr S Cl W) (hds : q.ds = dsFirst p) (fe : S × Fr.E.Str → Ex.Str)
    (part : W → M) (hback : q.back = []) (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (lw : ℕ → LW Cb.Gl.E) {first : ℕ} {Q3 : Fork → Prop} {dec : S × Fr.E.Str → M}
    (hn : U.n0 = first + Forest.elems X.layers.y.fo) (hQ : ∀ F, Q3 F → F.ns ≤ U.ns + 1)
    (hV : p.P.V = ppref.V) (NE : EmbNums p.P.y)
    (hb : q.b = below bk) (hh : HearsAs seatS p bk)
    (hx : ∀ a τ b w, q.ior.red.out a τ = some b → q.ext a τ w = w) (N : Numbers)
    (Mg : Meaning P W) (Zt : P) {links : List ModelPart} {ps : List VerifiableInference.Desc.Place}
    {k m : ℕ} {pl pl' : VerifiableInference.Desc.Place}
    (H : AtK4 links ps k m pl) (Kf : K4Front Mg Zt links ps m p.P.y.fo p.P.y.h.lmb first Q3)
    (Kp : K4Keeps N Mg Zt links ps k m pl pl' q p)
    (Ln : K4Lines N Mg Zt m (U.atRecF X p).toPlan4K part p
      ((U.atRecF X p).lettersOfF part p first p.P.y.fo Q3
        (tableOn0 N Mg Zt links ps k) (keptFrom (tableOn0 N Mg Zt links ps k) p q)
        (tableCtx0 N Mg Zt m) dec) dec q.base
      (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))) :
    q.Own (onQ N Mg links ps (fun s => (Zt, s)) k) (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))
      (meansQ N Mg (fun s => (Zt, s))) (insQ links ps k) (outsQ links ps k) := by
  have hlaw := RefSeat.k04Law_refKF hscl U hU St B hP hG hg0 hla hy Ex bk q hds fe part hback hcap
    lw (on0 := tableOn0 N Mg Zt links ps k) hn hQ Ln.ctxRides Ln.decRides hV NE
  obtain ⟨y, nM, nR, nC, raw, maskAt, matAt, idxAt, L, n0, ns, nx, v7⟩ := U
  obtain rfl : L = seatS := hU
  exact k4_own_of_lines N Mg Zt H hlaw hb hh hback hx
    (fun a h1 h2 => ⟨⟨h1, h2⟩, k4_left_front N Mg Zt H Kf h1 h2⟩)
    (fun a τ b h1 h2 h3 _ => k4_promise_behind N Mg Zt H Kp hb hh hback a τ b h1 h2 h3)
    (k4Rel_fillF _ part p Ln)
    (fun a τ b h3 hd => by
      obtain ⟨_, fo, o, G, yy, rfl⟩ := yes_of_out seatS hh hb hback a b τ h3
      exact Kp.dec a τ fo o G yy hd)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.k4_own_refKF
