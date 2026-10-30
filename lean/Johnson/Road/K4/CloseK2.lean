-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseK2.lean: Johnson/Road/K4/CloseK.lean's TOP WITH SEVEN OF THE THIRTEEN FIELDS OF
`Plan4L.Owes` CONCLUDED, WHOLLY OR IN PART: TWO OF THEM PAID (rows, merge), THE OTHERS EXCHANGED FOR
ONE NAMED SENTENCE, which the promise in front is to give: `K3LeftAt`
(Johnson/Top/H/K3LeftStatement.lean): «the ledger in hand is the one that the lookup's hearing left,
and the heard record is its». Two records and two theorems. Glue: `front_of_leftAt`
(LookOfLeft.lean) and `Plan4L.rows_at` (CloseRows.lean) laid into the record `Owes`. No draw, no
count.

  `Plan4L.FrontIs`: FIVE LINES ON THE PROMISE AND ON PUBLIC NUMBERS: on: under the promise in front
  `K3LeftAt` holds of the record, at the seat's own readers, at a shape h3, the plan's lmb, the
  number first and a letter Q3 · fo: the plan's y.fo is h3 · pub: h3 is s0 with another public part
  · ok: h3 passes the lookup's test on numbers · n0: the value's n0 is first + the number of
  elements that the lookup hears.
  `Plan4L.Owes2`: WHAT IS STILL OWED: NINE FIELDS: kept · seat · ns (the ledger's number of slots is
  at most the value's ns + 1) · lines · ties (zOf, kTg, kIncS at the first statement are the
  lookup's return's) · rope · reads · planes (`K4ReadsTrue` alone) · wo.
  `Plan4L.owes_of2`: `Owes` from `FrontIs`, `Owes2`, `ValueIs`, `ValueMore` and the masks' line:
  CONCLUDED: sized · next · stands · rows · merge wholly; of look the lookup's five clauses and the
  filled slots; of planes the test on numbers.
  `Plan4L.k04LawAt_K2`: `K04LawAt L Sm Lt part par bk pc` at a piece whose errors are the cap.

Limits. K04_law IS NOT PROVED BY THIS. EVERY LINE OF `FrontIs`, EVERY FIELD OF `Owes2` AND EVERY
LINE OF `LettersAre` IS UNPAID HERE; so are `Meets`, `ValueIs`, `ValueMore`, pc.ds, pc.back, that
the errors are the cap, C and hk. THE LINE on ASKS `K3LeftAt` AT THE SEAT's OWN READERS (L.look,
L.fork) AND AT THE PLAN's LETTERS. The theorem that concludes `K3LeftAt` behind the lookup's piece
(`k3CallsKeepLeft`, Johnson/Desc/First/Look/K3LeftAll.lean) stands at other readers (the record's
lookHeard?, fork?) and at the lookup's own letters: the tie between the two is not here, and that
the piece in front of K4's is the lookup's is said by no theorem here. Of `K3LeftAt` this file and
CloseK3.lean spend: what was heard is the end values of a hearing; the shape; the points' and the
weights' make; the two clauses on the last claim; of what the hearing leaves in the ledger: next,
the sizes, the number of slots: NOT what it says of the free slots. `Owes2.lines` cannot be met at
the small shipped example. Nothing shows that all can be met together. The letters `Sem`, `Letters`,
part, fa, Ex, nu, first, h3, Q3 are not filled in this file: CloseFill.lean lays `Sem`, `Letters`
and nu from the others (`Plan4K.semOf`, `lettersOf`, `nuOf`), which it does not fill. USER:
`Plan4K.k04LawAt_K3` (CloseK3.lean). A group that is not the first.
-/
import Johnson.Road.K4.CloseK
import Johnson.Road.K4.CloseRows
import Johnson.Road.K4.LookOfLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (gl Tg7 aS7)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind K04LawAt frontRun)
open VerifiableInference.OnPublicFiles (K3Stands K4ReadsTrue K3LeftAt)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QL : Plan4L Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The promise in front, and four public lines.** -/
structure Plan4L.FrontIs (QL : Plan4L Cb.Gl.E Mm X) (par : Par) (L : Seat T)
    (Lt : Letters T Wt Fr) (first : ℕ) (s0 h3 : OnBytes.Model.Forest.Shape)
    (Q3 : Fork → Prop) : Prop where
  on : ∀ a, Lt.on a →
    K3LeftAt (fun s => some (L.fork s)) L.look h3 par.P.y.h.lmb first Q3 a.1
  fo : par.P.y.fo = h3
  pub : ∃ pb, h3 = { s0 with pub := pb }
  ok : FoNums.ok h3 = true
  n0 : QL.n0 = first + OnBytes.Model.Forest.elems h3

/-- **What is still owed.** -/
structure Plan4L.Owes2 (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (nu : Wt → _root_.Fo.Pl → Cb.Gl.E) (s : WsShape) (lk : ℕ)
    (s0 : OnBytes.Model.Forest.Shape) (tl : HTailF2) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G → Lt.on' (behindOf L pc a τ o G)
  /-- the seat's two laws -/
  seat : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G → SeatOk L a.1
  /-- the ledger's number of slots against the value's -/
  ns : ∀ a, Lt.on a → (L.fork a.1).ns ≤ QL.ns + 1
  /-- the plan's public lines -/
  lines : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QL.plan.full.D QL.plan.full.tb s
    lk s0 tl
  /-- the value's three letters at the first statement are the lookup's return's -/
  ties : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G →
    QL.plan.full.zOf (fa a).1 = zAt fo ∧
      QL.plan.full.kTg (fa a).1 = kTgAt fo (L.fork a.1) ∧
      ∀ s, QL.plan.kIncS (fa a).1 s = kIncAt fo (L.fork a.1) s
  /-- the rotary tables' fit at what was heard -/
  rope : ∀ a τ fo o G, Lt.on a → Yes L par pc a τ fo o G →
    ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QL.plan.full.D QL.plan.full.tb (par.g * par.P.y.Lam) lam
  /-- matrices whose reads are true, and whose cells are the message's -/
  reads : ∀ a τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w →
    ∃ Mt : Mats Cb.Gl.E, Plan4L.ReadsAt QL par hS L Sm part a.1 fo o G w Mt
  /-- the three planes' tables' reads are true in the world of the ledger behind the first run -/
  planes : ∀ a τ fo o G w fs₁ F₁, Lt.on a → Yes L par pc a τ fo o G →
    Behind L Sm Lt par (behindOf L pc a τ o G) w → frontRun par o G = some (fs₁, F₁) →
    K4ReadsTrue gl o.v fo F₁ (nu w) (Sm.entryT o w)
  /-- what the row opens on the committed weights gives the pending row at the merge's record -/
  wo : ∀ a τ fo o G w (g7 : Tg7) H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4, Lt.on a →
    Yes L par pc a τ fo o G →
    Led7 { par.P with tokv := L.tokv a.1 } par.hp par.g fo o (L.fork a.1) G (tapeAt par pc τ) []
      H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 →
    TgRec g7 { par.P with tokv := L.tokv a.1 } par.hp o (tapeAt par pc τ) H1 tT F4 G2 G3 G3' →
    Lt.wo (behindOf L pc a τ o G) w →
    WoSays QL.plan.full (aS7 (Plan4.tailMK A (numsK QL.plan.full))
      (ksOf { par.P with tokv := L.tokv a.1 } par.hp) ((tapeAt par pc τ).drop 1)
      (Plan4.nzAt A (L.tokv a.1) hds τ _) ((fa a).1, ptOf QL.plan (tapeAt par pc τ)) g7)
      o.wo (part w)

/-- **The thirteen fields from the nine, the promise's line and the value's choices.** -/
theorem Plan4L.owes_of2 (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ} {s : WsShape} {lk : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2} {Q3 : Fork → Prop}
    (V : Plan4L.ValueIs QL par hS) (V2 : Plan4L.ValueMore QL) (lw : ℕ → LW Cb.Gl.E)
    (hSm : ∀ w, Sm.mask w = QL.plan.maskAt (part w))
    (N : Plan4L.FrontIs QL par L Lt first s0 h3 Q3)
    (O : Plan4L.Owes2 A L Sm Lt Ex pc hds fa part nu s lk s0 tl) :
    Plan4L.Owes A L Sm Lt Ex pc hds fa part nu first s lk s0 tl := by
  have fr := fun (a : T × Fr.E.Str) (ha : Lt.on a) =>
    front_of_leftAt L (N.on a ha) (Pp := { par.P with tokv := L.tokv a.1 }) N.fo N.pub N.ok
  have nx : ∀ a, Lt.on a → QL.n0 = (L.fork a.1).next := fun a ha => by
    rw [(fr a ha).2.1]
    exact N.n0
  have rows : ∀ (a : T × Fr.E.Str) τ fo o G w, Lt.on a → Yes L par pc a τ fo o G →
      Behind L Sm Lt par (behindOf L pc a τ o G) w →
      RowsSay QL.plan.full (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)
        (lateAt QL.plan.full (lateOf (roomK QL.plan par hS))
          (fmOf QL.plan.full (ztS QL.plan.full) (par.P.y.lPd - par.P.y.ls) par.P.y.ls par.P.y.ls)
          (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) := by
    intro a τ fo o G w ha Y hB
    obtain ⟨K, hfil, he, hsl, _⟩ := (fr a ha).2.2 fo Y.look
    obtain ⟨hz0, hk0, hkS⟩ := O.ties a τ fo o G ha Y
    obtain ⟨Mt, hR, hcells⟩ := O.reads a τ fo o G w ha Y hB
    exact Plan4L.rows_at A L Sm Lt Ex hds fa part a τ Y w hB (O.seat a τ fo o G ha Y) (fr a ha).1
      (O.lines (L.tokv a.1)) K (O.rope a τ fo o G ha Y) lw hz0 hk0 hkS hfil he
      (fun y hy => Nat.lt_of_lt_of_le (hsl y hy) (O.ns a ha)) Mt hR hcells V V2 (nx a ha) (hSm w)
  refine
    { kept := O.kept
      seat := O.seat
      sized := fun a ha => (fr a ha).1
      next := nx
      lines := O.lines
      look := fun a τ fo o G ha Y => ?_
      rope := O.rope
      reads := O.reads
      stands := fun a τ fo o G ha Y => ?_
      planes := fun a τ fo o G w fs₁ F₁ ha Y hB h1 =>
        ⟨((fr a ha).2.2 fo Y.look).2.2.2.2, O.planes a τ fo o G w fs₁ F₁ ha Y hB h1⟩
      rows := fun a τ fo o G w ha Y hB =>
        ⟨(rows a τ fo o G w ha Y hB).1, (rows a τ fo o G w ha Y hB).2.1,
          (rows a τ fo o G w ha Y hB).2.2.1, (rows a τ fo o G w ha Y hB).2.2.2.1,
          (rows a τ fo o G w ha Y hB).2.2.2.2.1⟩
      wo := O.wo
      merge := fun a τ fo o G w ha Y hB => (rows a τ fo o G w ha Y hB).2.2.2.2.2 }
  · obtain ⟨K, hfil, _⟩ := (fr a ha).2.2 fo Y.look
    obtain ⟨hz0, hk0, hkS⟩ := O.ties a τ fo o G ha Y
    exact ⟨K, hz0, hk0, hkS, hfil⟩
  · obtain ⟨F, F', g, rs, _, hf, Lf, hg, hF'⟩ := N.on a ha
    have eg : g = fo := Option.some.inj (hg.symm.trans Y.look)
    have eF : L.fork a.1 = F' := Option.some.inj hF'
    subst eg
    rw [eF, Lf.shape, ← hf]
    exact ⟨rs, Lf.heardIs⟩

/-- **`K04LawAt` at a group that is not the first**, at a piece whose errors are the cap, from
`Meets`, the piece's rounds and back, C, hk, `ValueIs`, `ValueMore`, `LettersAre`, `FrontIs` and
`Owes2`. -/
theorem Plan4L.k04LawAt_K2 (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (C : QL.plan.D.ChOK)
    (hk : ∀ l, l < QL.plan.D.nl → (QL.plan.D.Pl l).kq = (QL.plan.D.Pl l).kk ∨
      (16 ≤ (QL.plan.D.Pl l).kq ∧ 16 ≤ (QL.plan.D.Pl l).kk))
    (V : Plan4L.ValueIs QL par hS) (V2 : Plan4L.ValueMore QL) (lw : ℕ → LW Cb.Gl.E)
    {s : WsShape} {lk : ℕ} {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ} {Q3 : Fork → Prop}
    (M : Plan4L.LettersAre A L Sm Lt Ex pc hds fa part nu first)
    (N : Plan4L.FrontIs QL par L Lt first s0 h3 Q3)
    (O : Plan4L.Owes2 A L Sm Lt Ex pc hds fa part nu s lk s0 tl) :
    K04LawAt L Sm Lt part par bk pc :=
  Plan4L.k04LawAt_cap A L Sm Lt Ex bk pc hds fa part hback hcap C hk V lw M
    (Plan4L.owes_of2 A L Sm Lt Ex pc hds fa part V V2 lw M.mask N O)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4L.owes_of2
#print axioms OnBytes.Road.K4.Plan4L.k04LawAt_K2
