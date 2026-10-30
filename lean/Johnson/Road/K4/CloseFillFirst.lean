-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseFillFirst.lean: A FILLING OF THE LETTERS OF K04's STATEMENT
(Johnson/Desc/Plain/K04Plain.lean: `Sem`, `Letters`) FOR THE FIRST GROUP, at the first group's value
that reads its letters off a seat (`Plan4KF`, ValueSeatFirst.lean). BY MAKE THERE HOLD: six of the
seven lines of `LettersAreF` (CloseKFirst.lean; the seventh, ctx, from two premises), two of the
four of `ReadsAre` (CloseReads.lean; one and cols stay premises) and the promise's line of `FrontIs`
(CloseK2.lean). `K04Law` is stated there too: THE PIN THAT IT WANTS IS LAID INTO THE LETTER ctx BY
MAKE: no step of soundness lies in that. The twin of Johnson/Road/K4/CloseFill.lean. A definition
and five theorems. Glue. No draw, no count. CloseFill.lean's `Plan4K.semOf`, `Plan4K.nuOf` and
`Plan4K.readsAre_fill` read the letters alone that the first group's value shares with a later
group's, and are taken as they stand.

  `Plan4KF.lettersOfF`: `Plan4K.lettersOf` (CloseFill.lean) at these letters, BUT TWO: idn a w: the
    value's `Idn` of part w AND (J11) (`Plan4F.J11`, ValueSaysFirst.lean) AT THE RECORD a.1 AND part
    w: every entry of the stream that comes in is the entry of the committed embedding's row of THE
    SEAT's TOKEN (L.tokv a.1).getD p 0 (`Plan4KF.tok_at`) · wo: wherever the seat finds the
    hearing's record o in b: `WoRowF` (CloseK5First.lean) at o and part w.
  `ctx_fillF`, `lettersAreF_fill`, `frontIs_fillF`: as in CloseFill.lean.
  `Plan4KF.k04LawAt_fillF`: `K04LawAt` at this filling, at a piece whose errors are the cap.
  `Plan4KF.k04Law_fillF`: `K04Law` at this filling, at the same piece.

WHAT THE FILLING IS, AND IS NOT: CloseFill.lean's paragraph of that name holds here, with (J11)
beside `Idn`: the four letters idn, worthKeys, worthPlanes, worthRider are filled by the very
sentences that the road concludes; IT IS NOT SHOWN that the items of the table of joints ARE these
sentences or follow from them: owed by whoever fills the table: IN THE FIRST GROUP ALSO THAT THE
ITEM constr m idn SPEAKS OF THE EMBEDDING AT THE REQUEST's OWN TOKENS, which (J11) reads off the
seat: NEITHER on NOR ctx TIES THE SEAT's TOKENS TO A REQUEST (CloseAtTableFirst.lean's head: an open
question). `Plan4K.nuOf` is not the lookup's own valuation (CloseFill.lean's head). ctx HOLDS «part
w is dec a» BY MAKE: over all dec `K04Law` here says what `K04LawAt` says and no more. The entries
are true by make (EntryTrue.lean's limits).

Limits. K04_law IS NOT PROVED BY THIS: IT IS `K04Law` AT LETTERS CHOSEN HERE, UNDER PREMISES. WHAT
STAYS A PREMISE: ctx0 rides back from behind a yes to in front · dec reads the same behind a yes as
in front · kept · the two public numbers of `ReadsAre` (one, cols) · of `FrontIs` the lines fo, pub,
ok, n0 · THE FOUR PREMISES ON SIZES OF CloseK5First.lean (D.P = ppref, kW = kRef, par.P.V = ppref.V,
`EmbNums`), which the later groups' file has not · `MeetsF`, `ValueIs`, `ValueMoreF`, pc.ds,
pc.back, that the errors are the cap, C, hk, the bound on Q3, the layout's line, the matrices'
zeros, the seat's two laws, the public lines, the rotary tables' fit. on0, on', ctx0, dec, part, fe,
Ex, first, h3, Q3 and the letters of `Plan4KF` are filled by nobody. `WoRowF` says «there are». That
what the row opens is met at some yes, and that some record meets `K3LeftAt`, is shown by nothing
here. The reference sizes alone. The first group alone. USER: of the definition:
CloseRefFillFirst.lean, CloseRefFillSFirst.lean, CloseAtTableFirst.lean, CloseScopeSFirst.lean [not
in this library]; of `ctx_fillF` and `lettersAreF_fill`: CloseRefFillFirst.lean; of `frontIs_fillF`,
`k04LawAt_fillF` and `k04Law_fillF`: nobody outside this file.
-/
import Johnson.Road.K4.CloseK5First
import Johnson.Road.K4.CloseFill

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
open Inst.Model (Scl Tables ppref)
open Inst.Model.Layout (kRef)
open Meaning.Emb (EmbNums)
open Inst.Model.FFSeg (LW d10)

variable [scl : Scl] {Mm T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The letters in the first group: four filled by the sentences that the road concludes, idn with
(J11) at the seat's tokens; wo by the row's sentence; the promise in front holds the sharp promise
of the lookup; ctx holds «part w is dec a»; on0, on', ctx0, dec stay letters. -/
def Plan4KF.lettersOfF (QK : Plan4KF Mm T) (part : Wt → Mm) (par : Par) (first : ℕ)
    (h3 : OnBytes.Model.Forest.Shape) (Q3 : Fork → Prop) (on0 on' : T × Fr.E.Str → Prop)
    (ctx0 : T × Fr.E.Str → Wt → Prop) (dec : T × Fr.E.Str → Mm) : Letters T Wt Fr where
  on := fun a => on0 a ∧
    K3LeftAt (fun s => some (QK.L.fork s)) QK.L.look h3 par.P.y.h.lmb first Q3 a.1
  on' := on'
  ctx := fun a w => ctx0 a w ∧ part w = dec a
  idn := fun a w => QK.toLF.planF.toPlan4.Idn (part w) ∧ QK.toLF.planF.J11 a.1 (part w)
  worthPlanes := fun a w => ∀ fo, QK.L.look a.1 = some fo →
    K3OutPlanes fo.shape par.P.y.h.lmb first (QK.toPlan4K.nuOf part (matIx par.P.y).iB w) gl fo
      (QK.L.fork a.1)
  worthKeys := fun a w => QK.toLF.planF.toPlan4.Keys a.1 (part w)
  worthRider := fun a w => ∀ fo, QK.L.look a.1 = some fo →
    ∀ l, l < QK.toLF.planF.fullF.D.ne → Blocks.ext QK.toLF.planF.fullF.D.lT
      (d10 QK.toLF.planF.fullF.D (QK.toLF.planF.fullF.rd (QK.toLF.planF.fullF.msg (part w))) l)
      (Inst.Model.FFSeg.zpos QK.toLF.planF.fullF.D (zAt fo)) = 0
  wo := fun b w => ∀ o, QK.L.own b.1 = some o → QK.WoRowF par o (part w)

variable (QK : Plan4KF Mm T) (part : Wt → Mm) {first : ℕ} {h3 : OnBytes.Model.Forest.Shape}
  {Q3 : Fork → Prop} {on0 on' : T × Fr.E.Str → Prop} {ctx0 : T × Fr.E.Str → Wt → Prop}
  {dec : T × Fr.E.Str → Mm} {tl : HTailF2}

/-- **ctx rides back at the filling**, if ctx0 does and dec reads the same behind as in front. -/
theorem Plan4KF.ctx_fillF (pc : Piece (ckP .two) Fr T Cl Wt)
    (hc0 : ∀ a τ fo o G w, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → ctx0 (behindOf QK.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → dec (behindOf QK.L pc a τ o G) = dec a) :
    ∀ a τ fo o G w, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G →
      (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).ctx (behindOf QK.L pc a τ o G) w →
      (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).ctx a w :=
  fun a τ fo o G w ha Y hb =>
    ⟨hc0 a τ fo o G w ha Y hb.1, hb.2.trans (hd a τ fo o G ha Y)⟩

/-- **`LettersAreF` at the filling**, from «ctx rides back». -/
theorem Plan4KF.lettersAreF_fill (A : QK.toLF.planF.MeetsF par hS pcl) (Ex : ExtSpec)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst par) (fe : T × Fr.E.Str → Ex.Str)
    (hctx : ∀ a τ fo o G w, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G →
      (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).ctx (behindOf QK.L pc a τ o G) w →
      (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).ctx a w) :
    Plan4LF.LettersAreF A QK.L (QK.toPlan4K.semOf part tl)
      (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec) Ex pc hds (fun a => (a.1, fe a)) part
      (QK.toPlan4K.nuOf part (matIx par.P.y).iB) first where
  mask := fun _ => rfl
  maskNu := fun _ _ => rfl
  ctx := hctx
  idn := fun _ _ _ h hJ => ⟨h, hJ⟩
  keys := fun _ _ _ _ _ _ _ _ h => h
  planes := fun _ _ fo _ hl _ hP fo' hl' => by
    obtain rfl : fo = fo' := Option.some.inj (hl.symm.trans hl')
    exact hP
  rider := fun _ _ fo _ hl hR fo' hl' => by
    obtain rfl : fo = fo' := Option.some.inj (hl.symm.trans hl')
    exact hR

/-- **`FrontIs` at the filling**, from its four public lines. -/
theorem Plan4KF.frontIs_fillF {s0 : OnBytes.Model.Forest.Shape} (fo : par.P.y.fo = h3)
    (pub : ∃ pb, h3 = { s0 with pub := pb }) (ok : FoNums.ok h3 = true)
    (n0 : QK.n0 = first + OnBytes.Model.Forest.elems h3) :
    Plan4L.FrontIs QK.toLF.toPlan4L par QK.L (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec)
      first s0 h3 Q3 where
  on := fun _ ha => ha.2
  fo := fo
  pub := pub
  ok := ok
  n0 := n0

/-- **`K04LawAt` at the filling, in the first group**, at a piece whose errors are the cap: from
`MeetsF`, the piece's rounds and back, that its errors are the cap, C, hk, `ValueIs`, `ValueMoreF`,
the bound on Q3, the layout's line, the matrices' zeros, the seat's two laws, the public lines, the
rotary tables' fit, the four public lines of `FrontIs`, the two public numbers of `ReadsAre`, «ctx0
rides back», «dec reads the same behind a yes», kept and the four premises on sizes. -/
theorem Plan4KF.k04LawAt_fillF (A : QK.toLF.planF.MeetsF par hS pcl) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block T Cl) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fe : T × Fr.E.Str → Ex.Str) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (C : QK.toLF.planF.D.ChOK)
    (hk : ∀ l, l < QK.toLF.planF.D.nl → (QK.toLF.planF.D.Pl l).kq = (QK.toLF.planF.D.Pl l).kk ∨
      (16 ≤ (QK.toLF.planF.D.Pl l).kq ∧ 16 ≤ (QK.toLF.planF.D.Pl l).kk))
    (V : Plan4L.ValueIs QK.toLF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QK.toLF)
    (lw : ℕ → LW Cb.Gl.E) {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    (hQ : ∀ F, Q3 F → F.ns ≤ QK.ns + 1) (hy : QK.y = par.P.y)
    (hz : ∀ m a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats m a b c = 0)
    (hseat : ∀ x fo, QK.L.look x = some fo → SeatOk QK.L x)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toLF.planF.fullF.D
      QK.toLF.planF.fullF.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toLF.planF.fullF.D QK.toLF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (fo : par.P.y.fo = h3) (pub : ∃ pb, h3 = { s0 with pub := pb }) (ok : FoNums.ok h3 = true)
    (n0 : QK.n0 = first + OnBytes.Model.Forest.elems h3)
    (one : (tl.mats.getD (matIx par.P.y).iB {}).m / 2 ^ par.P.y.h.lmb = 1)
    (cols : _root_.Fo.planeCols h3 par.P.y.h.lmb ≤ (tl.mats.getD (matIx par.P.y).iB {}).k)
    (hc0 : ∀ a τ fo o G w, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → ctx0 (behindOf QK.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → dec (behindOf QK.L pc a τ o G) = dec a)
    (kept : ∀ a τ fo o G, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → on' (behindOf QK.L pc a τ o G))
    (hP : QK.toLF.planF.fullF.D.P = ppref) (hkR : QK.toLF.planF.fullF.kW = kRef)
    (hV : par.P.V = ppref.V) (NE : EmbNums par.P.y) :
    K04LawAt QK.L (QK.toPlan4K.semOf part tl) (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec)
      part par bk pc :=
  QK.k04LawAt_K5F A (QK.toPlan4K.semOf part tl)
    (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec) Ex
    bk pc hds fe part hback hcap C hk V V2 lw hQ hy hz hseat hl hr
    (QK.lettersAreF_fill part A Ex pc hds fe (QK.ctx_fillF part pc hc0 hd))
    (QK.frontIs_fillF part fo pub ok n0) (QK.toPlan4K.readsAre_fill part one cols) hP hkR
    hV NE kept (fun _ _ o h ho => h o ho)

/-- **`K04Law` at the filling, in the first group**, at a piece whose errors are the cap: from
`MeetsF`, the piece's rounds and back, that its errors are the cap, C, hk, `ValueIs`, `ValueMoreF`,
the bound on Q3, the layout's line, the matrices' zeros, the seat's two laws, the public lines, the
rotary tables' fit, the four public lines of `FrontIs`, the two public numbers of `ReadsAre`, «ctx0
rides back», «dec reads the same behind a yes», kept and the four premises on sizes; the pin is had
from «part w is dec a», which ctx holds by make. -/
theorem Plan4KF.k04Law_fillF (A : QK.toLF.planF.MeetsF par hS pcl) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block T Cl) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fe : T × Fr.E.Str → Ex.Str) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (C : QK.toLF.planF.D.ChOK)
    (hk : ∀ l, l < QK.toLF.planF.D.nl → (QK.toLF.planF.D.Pl l).kq = (QK.toLF.planF.D.Pl l).kk ∨
      (16 ≤ (QK.toLF.planF.D.Pl l).kq ∧ 16 ≤ (QK.toLF.planF.D.Pl l).kk))
    (V : Plan4L.ValueIs QK.toLF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QK.toLF)
    (lw : ℕ → LW Cb.Gl.E) {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    (hQ : ∀ F, Q3 F → F.ns ≤ QK.ns + 1) (hy : QK.y = par.P.y)
    (hz : ∀ m a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats m a b c = 0)
    (hseat : ∀ x fo, QK.L.look x = some fo → SeatOk QK.L x)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toLF.planF.fullF.D
      QK.toLF.planF.fullF.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toLF.planF.fullF.D QK.toLF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (fo : par.P.y.fo = h3) (pub : ∃ pb, h3 = { s0 with pub := pb }) (ok : FoNums.ok h3 = true)
    (n0 : QK.n0 = first + OnBytes.Model.Forest.elems h3)
    (one : (tl.mats.getD (matIx par.P.y).iB {}).m / 2 ^ par.P.y.h.lmb = 1)
    (cols : _root_.Fo.planeCols h3 par.P.y.h.lmb ≤ (tl.mats.getD (matIx par.P.y).iB {}).k)
    (hc0 : ∀ a τ fo o G w, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → ctx0 (behindOf QK.L pc a τ o G) w → ctx0 a w)
    (hd : ∀ a τ fo o G, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → dec (behindOf QK.L pc a τ o G) = dec a)
    (kept : ∀ a τ fo o G, (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec).on a →
      Yes QK.L par pc a τ fo o G → on' (behindOf QK.L pc a τ o G))
    (hP : QK.toLF.planF.fullF.D.P = ppref) (hkR : QK.toLF.planF.fullF.kW = kRef)
    (hV : par.P.V = ppref.V) (NE : EmbNums par.P.y) :
    K04Law QK.L (QK.toPlan4K.semOf part tl)
      (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec) par bk pc :=
  k04Law_of_dec QK.L (QK.toPlan4K.semOf part tl)
    (QK.lettersOfF part par first h3 Q3 on0 on' ctx0 dec)
    part par bk pc hback
    (QK.k04LawAt_fillF part A Ex bk pc hds fe hback hcap C hk V V2 lw hQ hy hz hseat hl hr fo pub
      ok n0 one cols hc0 hd kept hP hkR hV NE)
    dec (fun _ _ h => h.2) hd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4KF.ctx_fillF
#print axioms OnBytes.Road.K4.Plan4KF.lettersAreF_fill
#print axioms OnBytes.Road.K4.Plan4KF.frontIs_fillF
#print axioms OnBytes.Road.K4.Plan4KF.k04LawAt_fillF
#print axioms OnBytes.Road.K4.Plan4KF.k04Law_fillF
