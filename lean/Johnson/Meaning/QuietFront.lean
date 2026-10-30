-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/QuietFront.lean: the front road to three premises of the planes' row: behind a yes
of the step that closes the list of tables at a layers' link.

Johnson/Desc/K8/ReadsQuiet.lean's block `layers P` belongs to piece 4 of a layers' link, between the
layers' own rounds (piece 3) and the smallness test's draw (piece 5)
(Johnson/Desc/First/Driver/Chain.lean, kindsBeforeBatching; Johnson/Desc/K8/ReadsQuietAt.lean: blockAt; and
`behind own q`: it is laid BEHIND the block of that place's steps with rounds). Its text takes THE
PLAN's record P.tl, closes it with the tables that the carried record holds as heard by the layers'
own rounds, and lays it into the carried record, over whatever record lay there. So the record
behind its yes has: a link open; the closed list IS what is held as heard, weights too; and the
numbers, arrays and columns of P.tl. These are the premises ht, hfun, hp0 and hz (`SamePub`, both
halves) of the rows of Johnson/Meaning/PlanesTieK8.lean and PlanesTieK8CellsAt.lean.

Main theorems (namespace `Meaning.Reads`).
  `quiet_layers_yes`: a yes of `(layers P).decide` at s, taken apart: s stands in a layers' link a,
      a holds own as heard, and the record behind is s with { P.tl with funClosed := true, funs :=
      own.funs } laid in that link. By `layers_ok` and `closed_ok`
      (Johnson/Desc/K8/ReadsQuietLaws.lean).
  `quiet_keeps_own`: it keeps what is held as heard (DecideKeepsOwn, Johnson/Meaning/OwnKept.lean).
  `quiet_funs`: behind it: ht, hfun, and what is held as heard stays: from hown and hyes alone.
  `quiet_front`: with hP and a run of the hearing besides: at tl0 := the plan's record closed with
      the public shapes: `SamePub` at the record in the state (K8.recOf tl0 s') AND `SamePub tl tl0`
      at the open link's record tl itself: layout and numbers.
  `k4_host_planes_front`: `k4_host_planes_relA_cells` with that yes in the place of ht and hfun.
  `k4_host_planes_front_tie`: **`k4_host_planes_tie_cellN` with that yes in the place of hpub and
      hfun, from `TieAt` at the witness's cells**: the form in which `k08_row` has the tie in front
      of the smallness test's block (Johnson/Desc/First/K8/LawRow.lean).

Premises of `k4_host_planes_front`: hh · hq · hT · hG · hgp (as there) · hown (the record in front
of the step holds as heard THE o OF THAT RUN hh) · hyes (the step's yes) · h (relA AT THE RECORD
BEHIND THAT YES) · hu · h4; and the letters' own hs, hseat. `quiet_front` has besides hP: P.tl =
hp.tl: blockAt's text gives it at G[k.2], GIVEN that its G is the list of plans of which hp is
member number g and that kinds[l].2 is that g: not shown here.
Premises of `k4_host_planes_front_tie`: hh · hq · hT · hG · hgp · hP · hown · hyes · hE · htie (the
tie AT THE RECORD BEHIND THAT YES) · hW · h4. Twelve.
OBJECT · USER · LETTERS. Object: ReadsQuiet.lean's block `layers P` (its decide), State's S.here,
S.tl?, LayOwn; K8's files' `TieAt`, `SamePub`, `layReads ... .relA`; the layers' plain hearing. The
block is taken as the kind's text has it; no seated description is named. User: the planes' row at
the seated description. Letters: as in Johnson/Meaning/PlanesTieK8.lean; P, s, s', W, ν:
free, under "for all".

`closed_ok` is ReadsQuietLaws.lean's, called here.






Compiled with the whole library.
Limits. NOT TREATED: that the record behind this step's yes is the record in front of the smallness
test's block; that the record in front of it holds what the layers' own block has laid: BETWEEN THE
TWO STANDS PIECE 4's OWN BLOCK (the steps with rounds): that it keeps what is held as heard is
Johnson/Meaning/OwnKeptK1.lean's [not in this library]; that a yes of the joined block (own.andThen)
holds a yes of this
step at the record behind own's is shown at the seat (piece4_yes [not in this library]). The step is
taken as the kind's text has it, not as a lot joins it or a fold wraps it. Whether its yes can hold
(the plan's list open; one shape a matrix; the order's guard) is a run's matter. Nothing on
soundness.
-/
import Johnson.Meaning.PlanesTieK8CellsAt
import Johnson.Meaning.OwnKept
import Johnson.Desc.K8.ReadsQuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf planG plansG)
open OnBytes.K.Kc
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K8.ReadsQuiet (PG layers closed layers_ok closed_ok)
open Meaning.Planes

/-- **A yes of the block that closes the list at a layers' link, taken apart.** -/
theorem quiet_layers_yes {P : PG} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (layers P).decide s rs gs = .ok s') :
    ∃ (a : LayOwn) (own : Own), s.here = .lay a ∧ a.own = some own ∧
      s' = { s with here := .lay { a with
        tl := { P.tl with funClosed := true, funs := own.funs } } } := by
  obtain ⟨a, own, tl', ha, ho, hc, e⟩ := layers_ok h
  obtain ⟨_, e', _, _⟩ := closed_ok hc
  subst e'
  exact ⟨a, own, ha, ho, e⟩

/-- It keeps what is held as heard. -/
theorem quiet_keeps_own (P : PG) : DecideKeepsOwn (layers P) := by
  intro s rs gs s' h
  obtain ⟨a, own, ha, _, e⟩ := quiet_layers_yes h
  subst e
  unfold ownAt
  rw [ha]

section AtTheLetters
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.Sound OnBytes.Maker Johnson.Pack

/-- **Behind the step's yes**: a link is open; the closed list is what is held as heard; that stays.
-/
theorem quiet_funs {o : Own} {P : PG} {s s' : S} (hown : ownAt s = some o) {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hyes : (layers P).decide s rs gs = .ok s') :
    ∃ tl, s'.tl? = some tl ∧ tl.funs = o.funs ∧ ownAt s' = some o := by
  obtain ⟨a, own, ha, ho, e⟩ := quiet_layers_yes hyes
  have e1 : own = o := by
    unfold ownAt at hown
    rw [ha] at hown
    exact Option.some.inj (ho.symm.trans hown)
  subst e1
  subst e
  refine ⟨{ P.tl with funClosed := true, funs := own.funs }, rfl, rfl, ?_⟩
  show ({ a with tl := _ } : LayOwn).own = some own
  exact ho

/-- **Behind the step's yes**, where its parameter is the plan's record and o comes of a run of the
hearing: besides, the record has the numbers, arrays, columns and shapes of the plan's record closed
with the public shapes. -/
theorem quiet_front {Pb : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {Fk Fk' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl Pb hp g fo Fk t = some (o, Fk', t'))
    {P : PG} (hP : P.tl = hp.tl) {s s' : S} (hown : ownAt s = some o) {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hyes : (layers P).decide s rs gs = .ok s') :
    ∃ tl, s'.tl? = some tl ∧ tl.funs = o.funs ∧ ownAt s' = some o ∧
      SamePub (K8.recOf (Closed.closedAt hp.tl (Closed.layShapes Pb g)) s')
        (Closed.closedAt hp.tl (Closed.layShapes Pb g)) ∧
      SamePub tl (Closed.closedAt hp.tl (Closed.layShapes Pb g)) := by
  obtain ⟨a, own, ha, ho, e⟩ := quiet_layers_yes hyes
  have e1 : own = o := by
    unfold ownAt at hown
    rw [ha] at hown
    exact Option.some.inj (ho.symm.trans hown)
  subst e1
  subst e
  rw [hP]
  refine ⟨{ hp.tl with funClosed := true, funs := own.funs }, rfl, rfl, ?_, ?_, ?_⟩
  · show ({ a with tl := _ } : LayOwn).own = some own
    exact ho
  · exact { toSameSize := ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, (k4_hsh hh hp.tl).symm⟩
            toSameLay := ⟨rfl, rfl, rfl, rfl⟩ }
  · exact { toSameSize := ⟨rfl, fun _ => rfl, fun _ => rfl, rfl, (k4_hsh hh hp.tl).symm⟩
            toSameLay := ⟨rfl, rfl, rfl, rfl⟩ }

variable {J : Type} [Fintype J] (Y : Lay J) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → J → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → J → Cb.Gl.E)
  {Xi : Type} (G : FileDescription Xi) (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : K8.Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

/-- **The three clauses at the layers' forms, from the relation in front of the smallness test's
block at the record behind a yes of the block that closes the list.** -/
theorem k4_host_planes_front {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {Fk Fk' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo Fk t = some (o, Fk', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp)
    (hgp : Gp[g]? = some hp)
    {P : PG} {s s' : S} (hown : ownAt s = some o) {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hyes : (layers P).decide s rs gs = .ok s')
    (y : F.E.Str) (w : Wit Cells Tok MsgT)
    (h : (layReads Y (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)) cs l seat'
      arr entE entW G smpOf hs Cl F p base e hseat).relA (s', y) w)
    (W : World Cb.Gl.E)
    (hu : ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (hp.tl.mats.getD f.mat {}).k,
      ∀ sg < (hp.tl.mats.getD f.mat {}).m / f.len,
        Y.cellAt (entE (msgsOf cs l seat' arr w)) o.v.iU3 0
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val W.entry o.v.iU3 o.v.K3
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg))
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
        (thetaRec (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
          (sigOf cs l).Msg (Wit Cells Tok MsgT)
          (symL Y (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)) entE)
          (u3L Y (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)) entE)
          (digL Y (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)) entW))
        (msgsOf cs l seat' arr w) (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
        (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨tl, ht, hfun, _⟩ := quiet_funs hown hyes
  exact k4_host_planes_relA_cells Y _ cs l seat' arr entE entW G smpOf hs Cl F p base e hseat hh hq
    hT hG hgp rfl (s', y) w tl ht h hfun W hu ν h4

/-- **The three clauses at the layers' forms, from the smallness test's tie at the record behind a
yes of the block that closes the list**: the tie in the form in which `k08_row` has it in front
of the smallness test's block (`TieAt` at the witness's cells). The yes pays ht, hfun and all of
`SamePub`, numbers too. -/
theorem k4_host_planes_front_tie {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {Fk Fk' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo Fk t = some (o, Fk', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp)
    (hgp : Gp[g]? = some hp)
    {P : PG} (hP : P.tl = hp.tl) {s s' : S} (hown : ownAt s = some o) {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hyes : (layers P).decide s rs gs = .ok s')
    (hE : ∀ w j, early (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
      (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (w : Wit Cells Tok MsgT)
    (htie : TieAt (fun w a r c => Y.cellAt (entW w) a r c) s' w)
    (W : World Cb.Gl.E)
    (hW : ∀ pos < o.v.K3, W.entry o.v.iU3 0 pos = Y.cellAt (entW w) o.v.iU3 0 pos)
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
        (thetaRec (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
          (sigOf cs l).Msg (Wit Cells Tok MsgT)
          (symL Y (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)) entE)
          (u3L Y (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)) entE)
          (digL Y (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)) entW))
        (msgsOf cs l seat' arr w) (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
        (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨tl, ht, hfun, _, _, hpub⟩ := quiet_front hh hP hown hyes
  obtain ⟨tl', ht', htie'⟩ := htie
  obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
  exact k4_host_planes_tie_cellN Y _ cs l seat' arr entE entW hh hq hT hG hgp rfl hE w htie' hpub
    hfun W hW ν h4

end AtTheLetters

#print axioms quiet_layers_yes
#print axioms quiet_keeps_own
#print axioms quiet_funs
#print axioms quiet_front
#print axioms k4_host_planes_front
#print axioms k4_host_planes_front_tie

end Meaning.Reads
