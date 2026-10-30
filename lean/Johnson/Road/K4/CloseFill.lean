-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseFill.lean: A FILLING OF THE LETTERS OF K04's STATEMENT
(Johnson/Desc/Plain/K04Plain.lean: `Sem`, `Letters`), at a value that reads its letters off a seat
(`Plan4K`). BY MAKE THERE HOLD: six of the seven lines of `LettersAre` (CloseK.lean; the seventh,
ctx, from two premises), two of the four of `ReadsAre` (CloseReads.lean; one and cols stay premises)
and the promise's line of `FrontIs` (CloseK2.lean). `K04Law` is stated there too: THE PIN THAT IT
WANTS IS LAID INTO THE LETTER ctx BY MAKE: no step of soundness lies in that. Three definitions and
six theorems. Glue. No draw, no count.

  `Plan4K.semOf part tl`: the mask row of a world w is the value's at part w; the true value of an
  entry is `entryTrue tl o` at the value's own matrices of part w.
  `Plan4K.nuOf part iB`: the lookup's valuation: at a mask's place the value's mask row; at a cell
  of the planes' matrix the entry of matrix iB; 0 elsewhere, so at the keys' places: IT IS NOT THE
  LOOKUP's OWN VALUATION; by reading the keys' places are idle in `K3OutPlanes`; no lemma says so.
  `Plan4K.lettersOf`: on a: a letter on0, and `K3LeftAt` at the seat · idn: the value's `Idn` of
  part w · worthKeys: the value's `Keys` at the record and part w · worthPlanes: wherever the seat
  finds fo: `K3OutPlanes` at fo's shape, nuOf, fo and the ledger in hand · worthRider: wherever the
  seat finds fo: at the token part of fo's point every routed layer's selector sums to 1 · wo:
  wherever the seat finds the hearing's record o in b: the row's sentence `WoRow` (CloseK5.lean) at
  o and part w · ctx a w: a letter ctx0, and «part w is dec a», dec a letter that reads a tuple of
  messages off a statement · on': A LETTER STILL.
  `ctx_fill`: ctx rides back from behind a yes, if ctx0 does and dec reads the same behind as in
  front. `lettersAre_fill`, `readsAre_fill`, `frontIs_fill`: the three records at this filling.
  `Plan4K.k04LawAt_fill`: `K04LawAt` at this filling, at a piece whose errors are the cap.
  `Plan4K.k04Law_fill`: `K04Law` at this filling, at the same piece.

WHAT THE FILLING IS, AND IS NOT. The four letters idn, worthKeys, worthPlanes, worthRider are filled
by THE VERY SENTENCES THAT THE ROAD CONCLUDES. By reading (no theorem here says it): each other
filling that meets `LettersAre`'s four lines on these letters is implied by this one under the
promise in front, line by line: so the theorem's conclusion here is the most that this road gives.
It is no restatement of a premise: no premise of `k04LawAt_fill` speaks of `Idn`, `Keys`,
`K3OutPlanes` or the selectors. IT IS NOT SHOWN that the items of the table of joints (constr m idn;
worth m 2 "planes" | "keys" | "rider") ARE these sentences or follow from them: that is owed by
whoever fills the table. THE OWNERS OF THE ITEMS worth m 2 "keys" | "rider" AND wo m HAVE SENTENCES
OF THEIR OWN: ties owed, by nobody's theorem: the library's KF at call c is the extension of that
call's key vector at the call's point · the rider's arrays are d10 at the value's cells · the row's
own mask index is the value's. ctx HOLDS «part w is dec a» BY MAKE: over all dec `K04Law` here says
what `K04LawAt` says and no more; that the four items which K4's row reads give «part w is dec b» at
one dec is owed by whoever fills the table. The entries are true by make (EntryTrue.lean's limits):
AT A PLACE THAT NO TABLE OF o.funs OWNS THE ENTRY IS 0: that K4's forms name no such place:
Johnson/Road/K4/OwnedForms.lean (`back_owned`, `front_owned_bare`): at a hearing's return, under
four fields of the public lines and two premises on the lookup's record (its last claim and its
leaves' start name no entry): not called here.

Limits. K04_law IS NOT PROVED BY THIS: IT IS `K04Law` AT LETTERS CHOSEN HERE, UNDER PREMISES. WHAT
STAYS A PREMISE: ctx0 rides back from behind a yes to in front · dec reads the same behind a yes as
in front · kept · the two public numbers of `ReadsAre` (one, cols) · of `FrontIs` the lines fo, pub,
ok, n0 · `Meets`, `ValueIs`, `ValueMore`, pc.ds, pc.back, that the errors are the cap, C, hk, the
bound on Q3, the layout's line, the matrices' zeros, the seat's two laws, the public lines, the
rotary tables' fit. on0, on', ctx0, dec, part, fe, Ex, first, h3, Q3 and the letters of `Plan4K` are
not filled in this file: later files of this folder lay some of them (h3 and the value:
CloseRefFill.lean; on': CloseRefFillS.lean; ctx0: CloseAtTable.lean; first: K04Tied.lean). `WoRow`
says «there are» (CloseK5.lean's limits). That what the row opens is met at some yes is shown by
nothing here. That some record meets `K3LeftAt` is shown by nothing here. A group that is not the
first. USER: of the definitions, `ctx_fill`, `lettersAre_fill` and `readsAre_fill`:
CloseRefFill.lean; of `frontIs_fill`, `k04LawAt_fill` and `k04Law_fill`: nobody outside this file.

-/
import Johnson.Road.K4.CloseK5
import Johnson.Road.K4.ClosePin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2)
open OnBytes.Model.Layer (Own matIx)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (gl Tg7 aS7)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind K04Law K04LawAt frontRun)
open VerifiableInference.OnPublicFiles (K3LeftAt K3OutPlanes)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (LW d10)

variable [scl : Scl] {Mm T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- What the statement reads of a world, through part. -/
noncomputable def Plan4K.semOf (QK : Plan4K Mm T) (part : Wt → Mm) (tl : HTailF2) : Sem Wt where
  mask := fun w => QK.maskAt (part w)
  entryT := fun o w => entryTrue tl o (QK.mats (part w))

/-- The lookup's valuation, through part. -/
def Plan4K.nuOf (QK : Plan4K Mm T) (part : Wt → Mm) (iB : ℕ) (w : Wt) :
    _root_.Fo.Pl → Cb.Gl.E
  | .mask j => QK.maskAt (part w) j
  | .cell r c => QK.mats (part w) iB r c
  | _ => 0

/-- The letters: four filled by the sentences that the road concludes; wo by the row's sentence;
the promise in front holds the sharp promise of the lookup; ctx holds «part w is dec a»; on0, on',
ctx0, dec stay letters. -/
def Plan4K.lettersOf (QK : Plan4K Mm T) (part : Wt → Mm) (par : Par) (first : ℕ)
    (h3 : OnBytes.Model.Forest.Shape) (Q3 : Fork → Prop) (on0 on' : T × Fr.E.Str → Prop)
    (ctx0 : T × Fr.E.Str → Wt → Prop) (dec : T × Fr.E.Str → Mm) : Letters T Wt Fr where
  on := fun a => on0 a ∧
    K3LeftAt (fun s => some (QK.L.fork s)) QK.L.look h3 par.P.y.h.lmb first Q3 a.1
  on' := on'
  ctx := fun a w => ctx0 a w ∧ part w = dec a
  idn := fun _ w => QK.toL.plan.Idn (part w)
  worthPlanes := fun a w => ∀ fo, QK.L.look a.1 = some fo →
    K3OutPlanes fo.shape par.P.y.h.lmb first (QK.nuOf part (matIx par.P.y).iB w) gl fo
      (QK.L.fork a.1)
  worthKeys := fun a w => QK.toL.plan.Keys a.1 (part w)
  worthRider := fun a w => ∀ fo, QK.L.look a.1 = some fo →
    ∀ l, l < QK.toL.plan.full.D.ne → Blocks.ext QK.toL.plan.full.D.lT
      (d10 QK.toL.plan.full.D (QK.toL.plan.full.rd (QK.toL.plan.full.msg (part w))) l)
      (Inst.Model.FFSeg.zpos QK.toL.plan.full.D (zAt fo)) = 0
  wo := fun b w => ∀ o, QK.L.own b.1 = some o → QK.WoRow par o (part w)

variable (QK : Plan4K Mm T) (part : Wt → Mm) {first : ℕ} {h3 : OnBytes.Model.Forest.Shape}
  {Q3 : Fork → Prop} {on0 on' : T × Fr.E.Str → Prop} {ctx0 : T × Fr.E.Str → Wt → Prop}
  {dec : T × Fr.E.Str → Mm} {tl : HTailF2}

/-- **ctx rides back at the filling**, if ctx0 does and dec reads the same behind as in front. -/
theorem Plan4K.ctx_fill (pc : Piece (ckP .two) Fr T Cl Wt)
    (hc0 : ∀ a τ fo o G w, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → ctx0 (behindOf QK.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → dec (behindOf QK.L pc a τ o G) = dec a) :
    ∀ a τ fo o G w, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G →
      (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).ctx (behindOf QK.L pc a τ o G) w →
      (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).ctx a w :=
  fun a τ fo o G w ha Y hb =>
    ⟨hc0 a τ fo o G w ha Y hb.1, hb.2.trans (hd a τ fo o G ha Y)⟩

/-- **`LettersAre` at the filling**, from «ctx rides back». -/
theorem Plan4K.lettersAre_fill (A : QK.toL.plan.Meets par hS pcl) (Ex : ExtSpec)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater par) (fe : T × Fr.E.Str → Ex.Str)
    (hctx : ∀ a τ fo o G w, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G →
      (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).ctx (behindOf QK.L pc a τ o G) w →
      (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).ctx a w) :
    Plan4L.LettersAre A QK.L (QK.semOf part tl)
      (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec) Ex pc hds (fun a => (a.1, fe a)) part
      (QK.nuOf part (matIx par.P.y).iB) first where
  mask := fun _ => rfl
  maskNu := fun _ _ => rfl
  ctx := hctx
  idn := fun _ _ _ h => h
  keys := fun _ _ _ _ _ _ _ _ h => h
  planes := fun _ _ fo _ hl _ hP fo' hl' => by
    obtain rfl : fo = fo' := Option.some.inj (hl.symm.trans hl')
    exact hP
  rider := fun _ _ fo _ hl hR fo' hl' => by
    obtain rfl : fo = fo' := Option.some.inj (hl.symm.trans hl')
    exact hR

/-- **`ReadsAre` at the filling**, from the two public numbers. -/
theorem Plan4K.readsAre_fill
    (one : (tl.mats.getD (matIx par.P.y).iB {}).m / 2 ^ par.P.y.h.lmb = 1)
    (cols : _root_.Fo.planeCols h3 par.P.y.h.lmb ≤ (tl.mats.getD (matIx par.P.y).iB {}).k) :
    ReadsAre par (QK.semOf part tl) (QK.nuOf part (matIx par.P.y).iB) tl h3
      fun w => QK.mats (part w) where
  entry := fun _ _ => rfl
  one := one
  cols := cols
  cell := fun _ _ _ _ _ => rfl

/-- **`FrontIs` at the filling**, from its four public lines. -/
theorem Plan4K.frontIs_fill {s0 : OnBytes.Model.Forest.Shape} (fo : par.P.y.fo = h3)
    (pub : ∃ pb, h3 = { s0 with pub := pb }) (ok : FoNums.ok h3 = true)
    (n0 : QK.n0 = first + OnBytes.Model.Forest.elems h3) :
    Plan4L.FrontIs QK.toL par QK.L (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec) first s0 h3
      Q3 where
  on := fun _ ha => ha.2
  fo := fo
  pub := pub
  ok := ok
  n0 := n0

/-- **`K04LawAt` at the filling**, in a group that is not the first, at a piece whose errors are
the cap. -/
theorem Plan4K.k04LawAt_fill (A : QK.toL.plan.Meets par hS pcl) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block T Cl) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fe : T × Fr.E.Str → Ex.Str) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (C : QK.toL.plan.D.ChOK)
    (hk : ∀ l, l < QK.toL.plan.D.nl → (QK.toL.plan.D.Pl l).kq = (QK.toL.plan.D.Pl l).kk ∨
      (16 ≤ (QK.toL.plan.D.Pl l).kq ∧ 16 ≤ (QK.toL.plan.D.Pl l).kk))
    (V : Plan4L.ValueIs QK.toL par hS) (V2 : Plan4L.ValueMore QK.toL) (lw : ℕ → LW Cb.Gl.E)
    {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    (hQ : ∀ F, Q3 F → F.ns ≤ QK.ns + 1) (hy : QK.y = par.P.y)
    (hz : ∀ m a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats m a b c = 0)
    (hseat : ∀ x fo, QK.L.look x = some fo → SeatOk QK.L x)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toL.plan.full.D
      QK.toL.plan.full.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toL.plan.full.D QK.toL.plan.full.tb (par.g * par.P.y.Lam) lam)
    (fo : par.P.y.fo = h3) (pub : ∃ pb, h3 = { s0 with pub := pb }) (ok : FoNums.ok h3 = true)
    (n0 : QK.n0 = first + OnBytes.Model.Forest.elems h3)
    (one : (tl.mats.getD (matIx par.P.y).iB {}).m / 2 ^ par.P.y.h.lmb = 1)
    (cols : _root_.Fo.planeCols h3 par.P.y.h.lmb ≤ (tl.mats.getD (matIx par.P.y).iB {}).k)
    (hc0 : ∀ a τ fo o G w, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → ctx0 (behindOf QK.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → dec (behindOf QK.L pc a τ o G) = dec a)
    (kept : ∀ a τ fo o G, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → on' (behindOf QK.L pc a τ o G)) :
    K04LawAt QK.L (QK.semOf part tl) (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec) part par
      bk pc :=
  QK.k04LawAt_K5 A (QK.semOf part tl) (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec) Ex bk pc
    hds fe part hback hcap C hk V V2 lw hQ hy hz hseat hl hr
    (QK.lettersAre_fill part A Ex pc hds fe (QK.ctx_fill part pc hc0 hd))
    (QK.frontIs_fill part fo pub ok n0) (QK.readsAre_fill part one cols) kept
    (fun _ _ o h ho => h o ho)

/-- **`K04Law` at the filling**, under the same premises: the pin is laid into ctx by make. -/
theorem Plan4K.k04Law_fill (A : QK.toL.plan.Meets par hS pcl) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block T Cl) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fe : T × Fr.E.Str → Ex.Str) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (C : QK.toL.plan.D.ChOK)
    (hk : ∀ l, l < QK.toL.plan.D.nl → (QK.toL.plan.D.Pl l).kq = (QK.toL.plan.D.Pl l).kk ∨
      (16 ≤ (QK.toL.plan.D.Pl l).kq ∧ 16 ≤ (QK.toL.plan.D.Pl l).kk))
    (V : Plan4L.ValueIs QK.toL par hS) (V2 : Plan4L.ValueMore QK.toL) (lw : ℕ → LW Cb.Gl.E)
    {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    (hQ : ∀ F, Q3 F → F.ns ≤ QK.ns + 1) (hy : QK.y = par.P.y)
    (hz : ∀ m a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats m a b c = 0)
    (hseat : ∀ x fo, QK.L.look x = some fo → SeatOk QK.L x)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toL.plan.full.D
      QK.toL.plan.full.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toL.plan.full.D QK.toL.plan.full.tb (par.g * par.P.y.Lam) lam)
    (fo : par.P.y.fo = h3) (pub : ∃ pb, h3 = { s0 with pub := pb }) (ok : FoNums.ok h3 = true)
    (n0 : QK.n0 = first + OnBytes.Model.Forest.elems h3)
    (one : (tl.mats.getD (matIx par.P.y).iB {}).m / 2 ^ par.P.y.h.lmb = 1)
    (cols : _root_.Fo.planeCols h3 par.P.y.h.lmb ≤ (tl.mats.getD (matIx par.P.y).iB {}).k)
    (hc0 : ∀ a τ fo o G w, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → ctx0 (behindOf QK.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → dec (behindOf QK.L pc a τ o G) = dec a)
    (kept : ∀ a τ fo o G, (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → on' (behindOf QK.L pc a τ o G)) :
    K04Law QK.L (QK.semOf part tl) (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec) par bk pc :=
  k04Law_of_dec QK.L (QK.semOf part tl) (QK.lettersOf part par first h3 Q3 on0 on' ctx0 dec) part
    par bk pc hback
    (QK.k04LawAt_fill part A Ex bk pc hds fe hback hcap C hk V V2 lw hQ hy hz hseat hl hr fo pub ok
      n0 one cols hc0 hd kept)
    dec (fun _ _ h => h.2) hd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4K.ctx_fill
#print axioms OnBytes.Road.K4.Plan4K.lettersAre_fill
#print axioms OnBytes.Road.K4.Plan4K.readsAre_fill
#print axioms OnBytes.Road.K4.Plan4K.frontIs_fill
#print axioms OnBytes.Road.K4.Plan4K.k04LawAt_fill
#print axioms OnBytes.Road.K4.Plan4K.k04Law_fill
