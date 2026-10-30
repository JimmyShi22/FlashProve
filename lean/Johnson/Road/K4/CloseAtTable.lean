-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseAtTable.lean: K4's ROW AT THE TABLE OF JOINTS, IN A LAYERS' SEGMENT OF A GROUP
THAT IS NOT THE FIRST: the piece that holds K4's block has `Own` at the table's own promises and
relations (`onQ` k, `onQ` (k + 1), `meansQ`, `insQ` k, `outsQ` k: Johnson/Desc/Sound/BordersQ.lean),
UNDER LINES ON THE TABLE's MEANING AND NUMBERS. Two definitions, a record and two theorems. Glue:
`RefSeat.k04Law_refS` (CloseRefFillS.lean) laid into `k4_own_of_lines` (K4AtTable.lean) with
`k4_left_front` (K4PromiseFront.lean) and `k4_promise_behind` (K4PromiseBehind.lean). No draw, no
count.

  `tableOn0`, `tableCtx0`: two letters of CloseFill.lean's filling, filled by the table's own terms:
  on0 a: the table's promise in front holds of a, and a bears no mark · ctx0 a w: the four items
  that K4's row reads and leaves open (pin m 0, pinW, constr m small, pinI) hold of (a, w).
  `K4Lines`: NINE LINES ON THE MEANING, at the reference value's own sentences: forms · wo (each at
  a statement that meets the filling's promise behind and the table's own) · pin (the four items
  give «part w is dec b») · idn · planes · keys · rider (each with ctx in hand) · ctxRides ·
  decRides (the four items and dec read of a statement only what a yes leaves: `SameRead`).
  `k4Rel_fill`: `K4Rel` (K4AtTable.lean) at the filling, from `K4Lines`.
  `RefSeat.k4_own_refS`: THE END. (`RefPub` is paid at all public files in the goals' scope by
  `refPub_in_scope`, RefInScope.lean: that call is not made here.)

OBJECT: the block bk is a letter with `HearsAs seatS p bk`; meant: the term that the description
seats at piece 3 of a layers' segment. USER: none yet; meant: whoever walks the table's rows.
LETTERS: by the caller's choice: the table of scales, the value's layout, seat and n0. Filled by
nobody: the table's Meaning and Numbers, its public part Zt, the lists of segments and places, M,
part, dec, the value's readers of a tuple of messages, first, Q3, fe, Ex, the piece.

Limits. K04_law IS NOT PROVED BY THIS. WHAT STAYS A PREMISE: `PublicSteps pol KL X` (the steps of
the public part that take no hash: paid at every o by `publicSteps_of_O`), `RefPub X p.g` · the
place holds the record's layers and the group's plan; g is not 0 and below 12 · the piece's rounds
are K4's, it puts no round behind them, its errors are the cap, it holds `below bk`, its extractor
is the identity at a yes · `HearsAs` · block number k stands at piece 3 of the layers' segment m
(`AtK4`) · n0; Q3's bound · EVERY LINE OF `K4Front` (four: the table's test on public items says
true; its item left m says `K3LeftAt` at the record's own readers and the plan's letters; its item
look m says that the two readers agree; `K3LeftOn` there gives its item leftOn m) · EVERY LINE OF
`K4Keeps` (thirteen; pub and pubP whole; four of them asked inside the promise in front alone,
«decodes rides» at every yes) · EVERY LINE OF `K4Lines` (nine). NO MEANING IS SHOWN TO MEET THESE
LINES TOGETHER. That the promise in front is met at a record, and what the row opens at some yes, is
shown by nothing here. The reference sizes alone.
-/
import Johnson.Road.K4.CloseRefFillS
import Johnson.Road.K4.K4PromiseFront

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

/-- The table's promise in front, at a statement that bears no mark. -/
def tableOn0 (N : Numbers) (Mg : Meaning P W) (Zt : P) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (k : ℕ) (a : S × Fr.E.Str) : Prop :=
  onQ N Mg links ps (fun s => (Zt, s)) k a ∧ a.1.failed = none

/-- The four items that K4's row reads and leaves open. -/
def tableCtx0 (N : Numbers) (Mg : Meaning P W) (Zt : P) (m : ℕ) (a : S × Fr.E.Str) (w : W) :
    Prop :=
  meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.pin m 0) a w ∧
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) .pinW a w ∧
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.constr m .small) a w ∧
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) .pinI a w

variable [scl : Scl] {M Cl : Type}

/-- **Nine lines on the table's meaning**, at a value QK that reads its letters off the first
chain's record. -/
structure K4Lines (N : Numbers) (Mg : Meaning P W) (Zt : P) (m : ℕ) (QK : Plan4K M S)
    (part : W → M) (p : Par) (Lt : VerifiableInference.Desc.Plain.K04.Letters S W Fr)
    (dec : S × Fr.E.Str → M) (base : ℕ) (onB : S × Fr.E.Str → Prop) : Prop where
  /-- formsT m 3 "own", at a statement that meets the filling's promise behind AND onB: meant: the
  table's own promise behind the block (there the public item hasRow m stands, without which the
  item wo m may hold of every witness), and bears no mark -/
  forms : ∀ b w, Lt.on' b → onB b → b.1.failed = none →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.formsT m 3 "own") b w →
    FormsT seatS (QK.semOf part p.hp.tl) (frontRun p) formsBack b.1 w
  /-- wo m, likewise -/
  wo : ∀ b w, Lt.on' b → onB b → b.1.failed = none →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.wo m) b w → Lt.wo b w
  /-- the four items give the pinned part -/
  pin : ∀ b w, tableCtx0 (Fr := Fr) N Mg Zt m b w → part w = dec b
  /-- constr m idn. WITH ctx IN HAND, as in the three lines that follow: the item is meant of the
  integers behind the committed symbols, which the value's cells meet only under the four read
  items -/
  idn : ∀ a w, Lt.on a → Lt.ctx a w → Lt.idn a w →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.constr m .idn) a w
  /-- worth m 2 "planes" -/
  planes : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthPlanes a w →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.worth m 2 "planes") a w
  /-- worth m 2 "keys" -/
  keys : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthKeys a w →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.worth m 2 "keys") a w
  /-- worth m 2 "rider" -/
  rider : ∀ a w, Lt.on a → Lt.ctx a w → Lt.worthRider a w →
    meansQ (Fr := Fr) N Mg (fun s => (Zt, s)) (.worth m 2 "rider") a w
  /-- the four items read only what a yes leaves: asked INSIDE THE PROMISE IN FRONT alone (outside a
  layers' link `SameRead` says too little) -/
  ctxRides : ∀ (x y : S × Fr.E.Str) w, Lt.on x → SameRead base x y →
    tableCtx0 (Fr := Fr) N Mg Zt m y w → tableCtx0 (Fr := Fr) N Mg Zt m x w
  /-- so does dec -/
  decRides : ∀ x y : S × Fr.E.Str, Lt.on x → SameRead base x y → dec y = dec x

/-- **`K4Rel` at the filling**, from the nine lines. -/
theorem k4Rel_fill {N : Numbers} {Mg : Meaning P W} {Zt : P} {m : ℕ} (QK : Plan4K M S)
    (part : W → M) (p : Par) {first : ℕ} {Q3 : Fork → Prop} {on0 on' : S × Fr.E.Str → Prop}
    {dec : S × Fr.E.Str → M} {base : ℕ} {onB : S × Fr.E.Str → Prop}
    (Ln : K4Lines N Mg Zt m QK part p
      (QK.lettersOf part p first p.P.y.fo Q3 on0 on' (tableCtx0 N Mg Zt m) dec) dec base onB) :
    K4Rel N Mg Zt m (QK.semOf part p.hp.tl)
      (QK.lettersOf part p first p.P.y.fo Q3 on0 on' (tableCtx0 N Mg Zt m) dec) p onB where
  forms := Ln.forms
  wo := Ln.wo
  ctxIn := fun b w _ _ _ h1 h2 h3 h4 => ⟨⟨h1, h2, h3, h4⟩, Ln.pin b w ⟨h1, h2, h3, h4⟩⟩
  ctxOut := fun _ _ h => h.1
  idn := Ln.idn
  planes := Ln.planes
  keys := Ln.keys
  rider := Ln.rider

variable {pol KL : ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **K4's row at the table**: from `PublicSteps`, `RefPub`, the premises on the table of
scales, the place, the layout and the seat, on the piece (rounds, back, errors, block, extractor),
`HearsAs`, `AtK4`, n0, the bound on Q3, `K4Front`, `K4Keeps` and `K4Lines`. -/
theorem RefSeat.k4_own_refS (hscl : scl = sclX X p.g) (U : RefSeat M S) (hU : U.L = seatS)
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
        (tableOn0 N Mg Zt links ps k) (keptS p) (tableCtx0 N Mg Zt m) dec) dec q.base
      (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))) :
    q.Own (onQ N Mg links ps (fun s => (Zt, s)) k) (onQ N Mg links ps (fun s => (Zt, s)) (k + 1))
      (meansQ N Mg (fun s => (Zt, s))) (insQ links ps k) (outsQ links ps k) := by
  have hlaw := RefSeat.k04Law_refS hscl U hU hg St B hP hG hg0 hy Ex bk q hds fe part hback hcap
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

#print axioms OnBytes.Road.K4.k4Rel_fill
#print axioms OnBytes.Road.K4.RefSeat.k4_own_refS
