-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseAtTableFirst.lean: K4's ROW AT THE TABLE OF JOINTS, IN THE LAYERS' SEGMENT OF
THE FIRST GROUP: the piece that holds K4's block has `Own` at the table's own promises and relations
(`onQ` k, `onQ` (k + 1), `meansQ`, `insQ` k, `outsQ` k: Johnson/Desc/Sound/BordersQ.lean), UNDER
LINES ON THE TABLE's MEANING AND NUMBERS. The twin of Johnson/Road/K4/CloseAtTable.lean's two
theorems. Glue: `RefSeat.k04Law_refSF` (CloseRefFillSFirst.lean) laid into `k4_own_of_lines`
(K4AtTable.lean) with `k4_left_front` (K4PromiseFront.lean) and `k4_promise_behind`
(K4PromiseBehind.lean). No draw, no count. CloseAtTable.lean's `tableOn0`, `tableCtx0` and its
structure `K4Lines`, and the three theorems just named with their structures `AtK4`, `K4Rel`,
`K4Front`, `K4Keeps`, NAME NO GROUP (they take the place p and `K04Law seatS Sm Lt p bk q` as they
come; the table's row is `segRow .layers m 3` at every layers' segment m): they are taken as they
stand; `K4Lines` at the letters that the first group's value shares with a later group's.

  `k4Rel_fillF`: `K4Rel` (K4AtTable.lean) at the first group's filling (`Plan4KF.lettersOfF`,
    CloseFillFirst.lean), from `K4Lines`.
  `RefSeat.k4_own_refSF`: THE END.

WHAT `K4Lines` ASKS HERE THAT IT DOES NOT ASK IN A LATER GROUP, through the letters: its line idn:
under the promise in front and WITH ctx IN HAND, the 17 identities AND (J11) AT THE SEAT's TOKENS
give the table's item constr m idn; its line wo: AT A STATEMENT THAT MEETS THE FILLING's PROMISE
BEHIND AND THE TABLE's OWN (the letter onB, laid as `onQ` (k + 1)) AND BEARS NO MARK, the table's
item wo m gives the row's sentence `WoRowF` at the first group's value.

AN OPEN QUESTION ON THE LINE idn, THE FIRST GROUP's ALONE (by reading; no theorem): the line stands
at every state of the verifier under the promise in front and ctx, WITH NO YES IN HAND. Neither the
promise in front nor ctx ties the seat's tokens to the request of which the table's item constr m
idn is meant to speak; that the seat holds 2 ^ lt tokens, each below the vocabulary's size, is known
only behind a yes (`ClaimEnv.claimE` refuses otherwise). WHETHER ANY MEANING OF THE TABLE MEETS THE
LINE AS IT LIES IS NOT KNOWN.

OBJECT: the block bk is a letter with `HearsAs seatS p bk`; meant: the term that the description
seats at piece 3 of the first layers' segment. USER: none here; meant: whoever walks the table's
rows: `Own` is one clause of what a row's walk asks of a piece. LETTERS: as in CloseAtTable.lean.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE: `PublicSteps pol KL X`, `RefPub X p.g`,
la = 16, the plan's size of the vocabulary is ppref.V, `EmbNums` at the plan's layout (the last four
are paid at all public files in the goals' scope by `refPub_in_scope`, `scope_la`,
`emb_public_in_scope`: these calls are not made here) · the place holds the layers of the public
parameters X and the group's plan; g is 0 · the piece's rounds are K4's in the first group, it puts
no round behind them, its errors are the cap, it holds `below bk`, its extractor is the identity at
a yes · `HearsAs` · `AtK4` · n0; Q3's bound · EVERY LINE OF `K4Front` · EVERY LINE OF `K4Keeps` ·
EVERY LINE OF `K4Lines`. NO MEANING IS SHOWN TO MEET THESE LINES TOGETHER. That the promise in front
is met at a state of the verifier, and what the row opens at some yes, is shown by nothing here. The
reference sizes alone. The first group alone.
-/
import Johnson.Road.K4.CloseRefFillSFirst
import Johnson.Road.K4.CloseAtTable

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

/-- **`K4Rel` at the first group's filling**, from the nine lines. -/
theorem k4Rel_fillF {N : Numbers} {Mg : Meaning P W} {Zt : P} {m : ℕ} (QK : Plan4KF M S)
    (part : W → M) (p : Par) {first : ℕ} {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop}
    {dec : S × Fr.E.Str → M} {base : ℕ} {onB : S × Fr.E.Str → Prop}
    (Ln : K4Lines N Mg Zt m QK.toPlan4K part p
      (QK.lettersOfF part p first p.P.y.fo Q3 on0 on' (tableCtx0 N Mg Zt m) dec) dec base onB) :
    K4Rel N Mg Zt m (QK.toPlan4K.semOf part p.hp.tl)
      (QK.lettersOfF part p first p.P.y.fo Q3 on0 on' (tableCtx0 N Mg Zt m) dec) p onB where
  forms := Ln.forms
  wo := Ln.wo
  ctxIn := fun b w _ _ _ h1 h2 h3 h4 => ⟨⟨h1, h2, h3, h4⟩, Ln.pin b w ⟨h1, h2, h3, h4⟩⟩
  ctxOut := fun _ _ h => h.1
  idn := Ln.idn
  planes := Ln.planes
  keys := Ln.keys
  rider := Ln.rider

variable {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **K4's row at the table, in the first group**: from `PublicSteps`, `RefPub`, la = 16, the size
of the vocabulary, `EmbNums`, the premises on the table of scales, the place, the layout and the
seat, on the piece (rounds, back, errors, block, extractor), `HearsAs`, `AtK4`, n0, the bound on Q3,
`K4Front`, `K4Keeps` and `K4Lines`. -/
theorem RefSeat.k4_own_refSF (hscl : scl = sclX X p.g) (U : RefSeat M S) (hU : U.L = seatS)
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
        (tableOn0 N Mg Zt links ps k) (keptS p) (tableCtx0 N Mg Zt m) dec) dec q.base
      (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))) :
    q.Own (onQ N Mg links ps (fun s => (Zt, s)) k) (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))
      (meansQ N Mg (fun s => (Zt, s))) (insQ links ps k) (outsQ links ps k) := by
  have hlaw := RefSeat.k04Law_refSF hscl U hU St B hP hG hg0 hla hy Ex bk q hds fe part hback hcap
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

#print axioms OnBytes.Road.K4.k4Rel_fillF
#print axioms OnBytes.Road.K4.RefSeat.k4_own_refSF
