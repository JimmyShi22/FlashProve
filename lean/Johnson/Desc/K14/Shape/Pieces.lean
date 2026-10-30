-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/Pieces.lean: the shared chain's shape (Johnson/Desc/K14/Shape/Lin.lean): THE
UPDATE at the six of the linear claim's eight sub-protocols in which the prover sends no oracle
message; and: WHEREVER SUCH A SUB-PROTOCOL's FUNCTION RETURNS, WHERE THE PLAN HAS TWO CODES AND THE
ROUND's CHALLENGES HAVE THE PLANNED NUMBER, THE SHAPE BEHIND IS THE UPDATE OF THE SHAPE IN FRONT.
Which of the six laws asks which of the two: «What is assumed», below. No premise on the state in
front. At a plan with one code pointUp, joinsUp and splitUp are not what the functions do
(Johnson/Desc/K14/Text.lean: linPoint, joins, split), and their three laws say nothing.

How. The functions' own texts (Johnson/Desc/K14/Text.lean) are compositions of five of the ground's
calls. Each of the five has a function on shapes with the law that it returns the shape behind
wherever the call returns, and the law that the call leaves what the kind notes
(Johnson/Desc/Ground/Shape/Ground.lean, More.lean). These functions return an Option. Here stands,
for each, what it returns where it returns, as a total function in closed form, with the law that
ties the two. WHERE THE GROUND's FUNCTION RETURNS NOTHING THE CLOSED FORM STILL GIVES A SHAPE: what
it does there is told at each definition, and no law ties it to the ground's function there. SO THE
SIX UPDATES ARE COMPOSITIONS OF THESE FIVE CLOSED FORMS, NOT OF THE GROUND's OWN FUNCTIONS ON
SHAPES. That the ground's own, composed in the same way, return at every shape that passes this
kind's test (under PlanFacts, the two sendings' test on the plan and Eight P), and that wherever
they return they return the same (no premise): Johnson/Desc/K14/Shape/Comp.lean.

Main names:
  modAt_same, modAt_congr   tools on a change of one entry of a list (modAt: Core.lean)
  groupUp, joinUp, rowsUp, ledNext, maskUp   the five updates in closed form; rowsUp_nil,
                      rowsUp_cons: no constraint more; one, then a list
  newGroupS_up, joinS_up, addRowS_up, addRowsS_up, takeMaskS_up   laws on shapes: what the routine
                      on shapes returns is the closed form; addRowsFromS_up: the like at the inner
                      loop of the adding of constraints
  sh2_group, sh2_join, sh2_row, sh2_rows, sh2_mask   from the call's return to the chain's shape
                      behind it
  kind_addLaid, kind_units, rec_kind, kinds_mapM   a constraint (rec_gamma) is of the kind plain.
                      That a constraint (loc_x) is of the kind generator is the library's
                      (Johnson/Desc/Key/Laid/Draws.lean: locX_kind). THE FIRST THREE HAVE LIKES IN
                      THE LIBRARY, in files that are not imported for a few lines: addLaid_kind
                      (Johnson/Desc/Third/Law/Sharp.lean), addLaid_kind', foldl_kind and
                      recRow_plain (Johnson/RunOne/KeyRow23.lean), foldl_kind
                      (Johnson/Top/H0/Tw/K2C/RowKinds.lean)
  rec_parts, loc_parts   what a return of "(rec_gamma)" and of "LOC" is made of: the ground's calls,
                      and the kinds of the constraints made, in the plan's numbers
  pointUp, recUp, locUp, joinsUp, zetaUp, splitUp   **the six updates**: functions with code of the
                      plan and the state's shape alone
  point_carries, rec_carries, loc_carries, joins_carries, zeta_carries, split_carries   **the
                      laws**, each under the premises named below. The numbers of constraints laid
                      are the plan's: one for each OOD seed of the key (index.answers); one for each
                      sampled location; one on each group

What is assumed, as premises: the plan has two codes (at "LIN point", the joinings and "SPLIT"); the
round's challenges have the planned number (at "LIN point", "LOC" and "LIN zeta").

What is not claimed. When a function returns. Nothing on what a constraint says. Nothing on
soundness, on completeness or on hiding.
-/
import Johnson.Desc.K14.Shape.Lin
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.K14.Law.LaysRL
import Johnson.Desc.K14.Blocks
import Johnson.Desc.Key.Laid.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.Ground (coreOf newGroupP joinP addRowP addRowsP takeMaskP ok)
open VerifiableInference.Desc.Ground.Sh
open Desc.K14.Law (laysRecW)

/-! ## Tools on lists -/

/-- A change of one entry that leaves it. -/
theorem modAt_same {α : Type} (l : List α) (i : Nat) (f : α → α) (h : ∀ x, f x = x) :
    modAt l i f = l := by
  refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
  simp only [modAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  split
  · exact h _
  · rfl

/-- Two changes that agree at the entry that is there. -/
theorem modAt_congr {α : Type} (l : List α) (i : Nat) (f g : α → α)
    (h : ∀ x, l[i]? = some x → f x = g x) : modAt l i f = modAt l i g := by
  refine List.ext_getElem (by simp [modAt]) fun j j1 j2 => ?_
  simp only [modAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  split
  · rename_i e
    subst e
    exact h _ (List.getElem?_eq_getElem _)
  · rfl

/-! ## The ground's calls: their updates on the shape, in closed form -/

/-- One more group, which has no member and no constraint. A total function: it lays the group
whether or not the two codes are there. The ground's newGroupS returns only where its clauses on the
two codes pass (groupL); elsewhere no law ties the two. -/
def groupUp (c : CoreSh) (code maskCode : Nat) : CoreSh :=
  { c with st := { c.st with groups := c.st.groups ++
      [{ code := code, maskCode := maskCode, members := [], kept := [], kinds := []
         inRun := false }] } }

/-- The message o joins the group g: o is laid among the group's members at the place whose number
is the count of the members below o, its mark kept at the same place, and the message notes g behind
the groups that it knows. A total function: none of the guards of the ground's joinS (joinG) is
asked. Where the group g is not there, no group changes (the place is counted on the empty list),
YET THE MESSAGE o STILL NOTES g; where the message o is not there, no message changes, yet the group
still takes o as a member. Where joinS does not return no law ties the two. -/
def joinUp (c : CoreSh) (g o : Nat) (kept : Bool) : CoreSh :=
  let pos := ((((c.st.groups[g]?).map (·.members)).getD []).filter (· < o)).length
  { c with st := { c.st with
      groups := modAt c.st.groups g fun G =>
        { G with members := insAt G.members pos o, kept := insAt G.kept pos kept }
      oracles := modAt c.st.oracles o fun x => { x with groups := x.groups ++ [g] } } }

/-- Constraints of these kinds more in the group g, in this order. A total function: where the group
g is not there nothing changes (modAt), and the guards of the ground's addRowS and addRowsS are not
asked. Where these do not return no law ties them to rowsUp. -/
def rowsUp (c : CoreSh) (g : Nat) (kinds : List RowKind) : CoreSh :=
  { c with st := { c.st with
      groups := modAt c.st.groups g fun G => { G with kinds := G.kinds ++ kinds } } }

/-- A ledger behind the taking of one free entry of a mask row. A total function: left - 1 is a
subtraction on Nat, so at 0 it stays 0. By its body it is the second half of the library's
stepLedger l (OnBytes/G4/Seat.lean); no law ties the two. -/
def ledNext (l : Ledger) : Ledger :=
  { l with next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 }

/-- One free entry of the message o's mask rows is taken. A total function: where the message o is
not there nothing changes (modAt), a message without a ledger stays as it is, and the guard of the
ground's takeMaskS (takeMaskG) is not asked. Where takeMaskS does not return no law ties the two. -/
def maskUp (c : CoreSh) (o : Nat) : CoreSh :=
  { c with st := { c.st with
      oracles := modAt c.st.oracles o fun x => { x with ledger := x.ledger.map ledNext } } }

/-- No constraint more. -/
theorem rowsUp_nil (c : CoreSh) (g : Nat) : rowsUp c g [] = c := by
  unfold rowsUp
  rw [modAt_same _ _ _ fun G => by rw [List.append_nil]]

/-- One constraint, then a list. -/
theorem rowsUp_cons (c : CoreSh) (g : Nat) (k : RowKind) (l : List RowKind) :
    rowsUp (rowsUp c g [k]) g l = rowsUp c g (k :: l) := by
  unfold rowsUp
  dsimp only
  rw [modAt_modAt]
  simp only [List.append_assoc, List.singleton_append]

/-! ## What the routines on shapes return is the closed form -/

/-- A new group. -/
theorem newGroupS_up {c : CoreSh} {a b : Nat} {y : Nat × CoreSh} (h : newGroupS c a b = some y) :
    y = (c.st.groups.length, groupUp c a b) := by
  unfold newGroupS at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- A joining. -/
theorem joinS_up {c y : CoreSh} {g o : Nat} {k : Bool} (h : joinS c g o k = some y) :
    y = joinUp c g o k := by
  unfold joinS at h
  split at h
  · obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    unfold joinUp
    rw [hG]
    rfl
  · cases h

/-- One constraint more. -/
theorem addRowS_up {c y : CoreSh} {g : Nat} {kind : RowKind} (h : addRowS c g kind = some y) :
    y = rowsUp c g [kind] := by
  unfold addRowS at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- Constraints one behind the other. -/
theorem addRowsFromS_up (g : Nat) : ∀ (l : List RowKind) (c y : CoreSh),
    addRowsFromS g l c = some y → y = rowsUp c g l
  | [], c, y, h => by
    rw [rowsUp_nil]
    exact (Option.some.inj h).symm
  | k :: l, c, y, h => by
    obtain ⟨e, he, h'⟩ := Option.bind_eq_some_iff.1 h
    rw [addRowsFromS_up g l e y h', addRowS_up he, rowsUp_cons]

/-- A list of constraints more. -/
theorem addRowsS_up {c y : CoreSh} {g : Nat} {l : List RowKind} (h : addRowsS c g l = some y) :
    y = rowsUp c g l := by
  unfold addRowsS at h
  split at h
  · exact addRowsFromS_up g l c y h
  · cases h

/-- A free entry of a mask row is taken. The law ties the core behind alone (y.2), not the number of
the entry taken (y.1). -/
theorem takeMaskS_up {c : CoreSh} {o : Nat} {y : Nat × CoreSh} (h : takeMaskS c o = some y) :
    y.2 = maskUp c o := by
  unfold takeMaskS at h
  split at h
  · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
    unfold maskUp
    dsimp only
    rw [modAt_congr c.st.oracles o _ (fun x => { x with ledger := x.ledger.map ledNext })
      fun x' hx' => by
        obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
        show _ = ({ x with ledger := x.ledger.map ledNext } : OrcSh)
        rw [hxl]
        rfl]
  · cases h

/-! ## From the return of a call of the ground's to the chain's shape behind it -/

/-- A new group. -/
theorem sh2_group (d d' : St) (a b n : Nat) (h : newGroupP d a b = some (n, d')) :
    n = (sh2 d).core.st.groups.length ∧
      sh2 d' = { sh2 d with core := groupUp (sh2 d).core a b } ∧ d'.loc = d.loc := by
  have e := newGroupS_up (newGroup_carries d d' a b n h)
  have l := (newGroup_frame d d' a b n h).1
  refine ⟨congrArg Prod.fst e, ?_, l⟩
  show Sh2.mk (coreSh (coreOf d')) (linSh d'.loc) = _
  rw [show coreSh (coreOf d') = _ from congrArg Prod.snd e, l]
  rfl

/-- A message joins a group. -/
theorem sh2_join (d d' : St) (g o : Nat) (k : Bool) (h : joinP d g o k = some d') :
    sh2 d' = { sh2 d with core := joinUp (sh2 d).core g o k } ∧ d'.loc = d.loc := by
  have e := joinS_up (join_carries d d' g o k h)
  have l := (join_frame d d' g o k h).1
  refine ⟨?_, l⟩
  show Sh2.mk (coreSh (coreOf d')) (linSh d'.loc) = _
  rw [show coreSh (coreOf d') = _ from e, l]
  rfl

/-- One constraint more: the shape keeps its kind. -/
theorem sh2_row (d d' : St) (g : Nat) (r : Row) (h : addRowP d g r = some d') :
    sh2 d' = { sh2 d with core := rowsUp (sh2 d).core g [r.kind] } ∧ d'.loc = d.loc := by
  have e := addRowS_up (addRow_carries d d' g r h)
  have l := (addRow_frame d d' g r h).1
  refine ⟨?_, l⟩
  show Sh2.mk (coreSh (coreOf d')) (linSh d'.loc) = _
  rw [show coreSh (coreOf d') = _ from e, l]
  rfl

/-- A list of constraints more: the shape keeps their kinds. -/
theorem sh2_rows (d d' : St) (g : Nat) (rows : List Row) (h : addRowsP d g rows = some d') :
    sh2 d' = { sh2 d with core := rowsUp (sh2 d).core g (rows.map (·.kind)) } ∧
      d'.loc = d.loc := by
  have e := addRowsS_up (addRows_carries d d' g rows h)
  have l := (addRows_frame d d' g rows h).1
  refine ⟨?_, l⟩
  show Sh2.mk (coreSh (coreOf d')) (linSh d'.loc) = _
  rw [show coreSh (coreOf d') = _ from e, l]
  rfl

/-- A free entry of a mask row is taken: one ledger turns. The number n of the entry taken is tied
to nothing. -/
theorem sh2_mask (d d' : St) (o n : Nat) (h : takeMaskP d o = some (n, d')) :
    sh2 d' = { sh2 d with core := maskUp (sh2 d).core o } ∧ d'.loc = d.loc := by
  have e := takeMaskS_up (takeMask_carries d d' o n h)
  have l := (takeMask_frame d d' o n h).1
  refine ⟨?_, l⟩
  show Sh2.mk (coreSh (coreOf d')) (linSh d'.loc) = _
  rw [show coreSh (coreOf d') = _ from e, l]
  rfl

/-! ## The kinds of the constraints that the kind makes -/

/-- Terms laid on a constraint leave its kind. -/
theorem kind_addLaid (o : Nat) (lay : VectorLay) : ∀ (l : List Tensor) (row : Row),
    (addLaid row o lay l).kind = row.kind
  | [], _ => rfl
  | t :: l, row => by
    show (addLaid (row.add o .main (lay.onTable t)) o lay l).kind = _
    rw [kind_addLaid o lay l]
    rfl

/-- A fold of steps that leave a constraint's kind leaves it. -/
theorem kind_units {α : Type} (f : Row → α → Row) (hf : ∀ r a, (f r a).kind = r.kind) :
    ∀ (l : List α) (row : Row), (l.foldl f row).kind = row.kind
  | [], _ => rfl
  | a :: l, row => by
    rw [List.foldl_cons, kind_units f hf l, hf]

/-- **A constraint (rec_gamma) is of the kind plain.** -/
theorem rec_kind {s : IndexShape} {seed : SampleSeed} {i : Nat} {w y : Array E} {u : FoldedRow}
    {row : Row} (h : recGamma s seed i w y u = some row) : row.kind = .plain := by
  unfold recGamma at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ts, _, sum, _, rfl⟩ := h
  have e := kind_units (fun (r : Row) (x : Nat × Nat) =>
      r.addUnit u.oracle .main (u.lay.index (s.padPlace x.1 x.2))
        (subE (if x.1 == i then mulE seed.beta (thetaE x.2) else zeroE)
          ((Tensor.eq seed.z).entry (s.padPlace x.1 x.2)))) (fun _ _ => rfl)
    ((List.range s.answers).flatMap fun a => (List.range 3).map fun t => (a, t)) (u.addAll {} ts)
  exact e.trans (kind_addLaid _ _ _ _)

/-- Where every constraint that f makes has the kind k, so has the list that mapM makes. -/
theorem kinds_mapM {α : Type} (f : α → Option Row) (k : RowKind)
    (hf : ∀ a r, f a = some r → r.kind = k) : ∀ (l : List α) (rows : List Row),
    l.mapM f = some rows → rows.map (·.kind) = List.replicate l.length k
  | [], rows, h => by
    obtain rfl : [] = rows := by simpa using h
    rfl
  | a :: l, rows, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs, hrs, rfl⟩ := h
    rw [List.map_cons, hf a r hr, kinds_mapM f k hf l rs hrs]
    rfl

/-! ## The six sub-protocols that send no oracle message: their updates on the shape -/

/-- "LIN point", at two codes: two groups; the point's length; the groups' numbers. -/
def pointUp (P : P14) (a : Sh2) : Sh2 :=
  { a with
    core := (groupUp (groupUp a.core P.par.S.fold.u.code P.par.S.sharedMaskCode)
      P.par.S.omega.code P.par.S.sharedMaskCode)
    lin := { a.lin with
      psi := P.par.S.kCol, gU := a.core.st.groups.length
      gOmega := a.core.st.groups.length + 1 } }

/-- "(rec_gamma)": o_u joins its group; one plain constraint for each OOD seed of the key, in the
plan's number (index.answers). -/
def recUp (P : P14) (a : Sh2) : Sh2 :=
  { a with core := (rowsUp (joinUp a.core a.lin.gU a.lin.oU false) a.lin.gU
      (List.replicate P.par.S.fold.index.answers .plain)) }

/-- "LOC": one constraint of the kind generator for each sampled location. -/
def locUp (P : P14) (a : Sh2) : Sh2 :=
  { a with core := rowsUp a.core a.lin.gU (List.replicate P.par.S.fold.columns .generator) }

/-- The joinings, at two codes. -/
def joinsUp (a : Sh2) : Sh2 :=
  { a with core := (joinUp (joinUp (joinUp a.core a.lin.gOmega a.lin.oOmega false) a.lin.gOmega
      a.lin.oSp false) a.lin.gU a.lin.oSp false) }

/-- "LIN zeta": the point's length. -/
def zetaUp (P : P14) (a : Sh2) : Sh2 := { a with lin := { a.lin with zFd := P.par.S.kRow } }

/-- "SPLIT", at two codes: one free entry of o_sp is taken; one plain constraint on each group. -/
def splitUp (a : Sh2) : Sh2 :=
  { a with core := (rowsUp (rowsUp (maskUp a.core a.lin.oSp) a.lin.gOmega [.plain]) a.lin.gU
      [.plain]) }

variable {P : P14}

/-- **"LIN point"**: wherever its function returns, where the plan has two codes (hS) and the round
holds as many sampled elements as the plan says (hpt: kCol), the shape behind is pointUp of the
shape in front. -/
theorem point_carries (hS : P.par.S.sharedSplitNeeded = true) (d d' : St) (r : Fmt.RoundView)
    (hpt : (drawn r).length = P.par.S.kCol) (h : linPoint P.par d [r] = some d') :
    sh2 d' = pointUp P (sh2 d) := by
  unfold linPoint at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, hS, if_true] at h
  obtain ⟨_, _, ⟨gU, d1⟩, h1, ⟨gO, d2⟩, h2, e⟩ := h
  obtain ⟨n1, e1, l1⟩ := sh2_group _ _ _ _ _ h1
  obtain ⟨n2, e2, l2⟩ := sh2_group _ _ _ _ _ h2
  obtain rfl := Option.some.inj e
  have n2' : gO = (sh2 d).core.st.groups.length + 1 := by
    rw [n2, e1]
    simp [groupUp]
  show Sh2.mk (sh2 d2).core (linSh { d2.loc with psiSh := drawn r, gU := gU, gOmega := gO }) = _
  rw [e2, e1, l2, l1, n1, n2']
  show Sh2.mk _ { linSh d.loc with
    psi := (drawn r).length, gU := (sh2 d).core.st.groups.length
    gOmega := (sh2 d).core.st.groups.length + 1 } = _
  rw [hpt]
  rfl

/-- **What a return of "(rec_gamma)" is made of**: one joining; one adding of constraints, which are
as many as the key has OOD seeds by the plan (index.answers), all of the kind plain. No premise but
the return. -/
theorem rec_parts (d d' : St) (rs : List Fmt.RoundView) (h : laysRec P.par d rs = some d') :
    ∃ (d1 : St) (rows : List Row), joinP d d.loc.gU d.loc.oU.oracle false = some d1 ∧
      addRowsP d1 d.loc.gU rows = some d' ∧
      rows.map (·.kind) = List.replicate P.par.S.fold.index.answers .plain := by
  have hok := (laysRecW P.par d d' rs h).1
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
  have hfit : d.loc.key.fits P.par.S.fold.index = true := hok.1
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, d1, hj, rows, hm, ha⟩ := h
  have hk := kinds_mapM _ .plain (fun _ _ hr => rec_kind hr) _ _ hm
  rw [List.length_zipIdx, hfit.1.2] at hk
  exact ⟨d1, rows, hj, ha, hk⟩

/-- **What a return of "LOC" is made of**, where the round holds as many sampled locations as the
plan says (hn: fold.columns): one adding of constraints, one for each sampled location, all of the
kind generator. -/
theorem loc_parts (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (hn : r.drawn.poss.length = P.par.S.fold.columns) (h : loc P.par d [r] [cols] = some d') :
    ∃ rows : List Row, addRowsP d d.loc.gU rows = some d' ∧
      rows.map (·.kind) = List.replicate P.par.S.fold.columns .generator := by
  unfold loc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rows, hm, ha⟩ := h
  have hk := kinds_mapM _ .generator (fun _ _ hr => by
    simp only [Option.bind_eq_some_iff] at hr
    obtain ⟨_, _, hr⟩ := hr
    exact VerifiableInference.Desc.Key.locX_kind _ _ _ _ _ _ hr) _ _ hm
  rw [List.length_map, hn] at hk
  exact ⟨rows, ha, hk⟩

/-- **"(rec_gamma)"**: wherever its function returns, the shape behind is recUp of the shape in
front. No premise but the return. -/
theorem rec_carries (d d' : St) (rs : List Fmt.RoundView) (h : laysRec P.par d rs = some d') :
    sh2 d' = recUp P (sh2 d) := by
  obtain ⟨d1, rows, hj, ha, hk⟩ := rec_parts d d' rs h
  rw [(sh2_rows _ _ _ _ ha).1, (sh2_join _ _ _ _ _ hj).1, hk]
  rfl

/-- **"LOC"**: wherever its function returns, where the round holds as many sampled locations as the
plan says (hn: fold.columns), the shape behind is locUp of the shape in front. -/
theorem loc_carries (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (hn : r.drawn.poss.length = P.par.S.fold.columns) (h : loc P.par d [r] [cols] = some d') :
    sh2 d' = locUp P (sh2 d) := by
  obtain ⟨rows, ha, hk⟩ := loc_parts d d' r cols hn h
  rw [(sh2_rows _ _ _ _ ha).1, hk]
  rfl

/-- **The joinings**: wherever their function returns, where the plan has two codes (hS), the shape
behind is joinsUp of the shape in front. -/
theorem joins_carries (hS : P.par.S.sharedSplitNeeded = true) (d d' : St) (rs : List Fmt.RoundView)
    (h : joins P.par d rs = some d') : sh2 d' = joinsUp (sh2 d) := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, hS, if_true] at h
  obtain ⟨_, _, d1, h1, d2, h2, h3⟩ := h
  rw [(sh2_join _ _ _ _ _ h3).1, (sh2_join _ _ _ _ _ h2).1, (sh2_join _ _ _ _ _ h1).1]
  rfl

/-- **"LIN zeta"**: wherever its function returns, where the round holds as many sampled elements as
the plan says (hz: kRow), the shape behind is zetaUp of the shape in front. -/
theorem zeta_carries (d d' : St) (r : Fmt.RoundView) (hz : (drawn r).length = P.par.S.kRow)
    (h : linZeta d [r] = some d') : sh2 d' = zetaUp P (sh2 d) := by
  obtain rfl : _ = d' := Option.some.inj h
  show Sh2.mk (coreSh (coreOf d)) { linSh d.loc with zFd := (drawn r).length } = _
  rw [hz]
  rfl

/-- **"SPLIT"**: wherever its function returns, where the plan has two codes (hS), the shape behind
is splitUp of the shape in front. -/
theorem split_carries (hS : P.par.S.sharedSplitNeeded = true) (d d' : St) (r : Fmt.RoundView)
    (h : split P.par d [r] = some d') : sh2 d' = splitUp (sh2 d) := by
  unfold split at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, hS] at h
  obtain ⟨row, _, h⟩ := h
  split at h
  · simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨GO, _, _, _, ⟨kappa, d1⟩, hk, d2, h2, h3⟩ := h
    rw [(sh2_row _ _ _ _ h3).1, (sh2_row _ _ _ _ h2).1, (sh2_mask _ _ _ _ hk).1]
    rfl
  · simp at h

end Desc.K14.Shape

#print axioms Desc.K14.Shape.modAt_same
#print axioms Desc.K14.Shape.modAt_congr
#print axioms Desc.K14.Shape.rowsUp_nil
#print axioms Desc.K14.Shape.rowsUp_cons
#print axioms Desc.K14.Shape.newGroupS_up
#print axioms Desc.K14.Shape.joinS_up
#print axioms Desc.K14.Shape.addRowS_up
#print axioms Desc.K14.Shape.addRowsFromS_up
#print axioms Desc.K14.Shape.addRowsS_up
#print axioms Desc.K14.Shape.takeMaskS_up
#print axioms Desc.K14.Shape.sh2_group
#print axioms Desc.K14.Shape.sh2_join
#print axioms Desc.K14.Shape.sh2_row
#print axioms Desc.K14.Shape.sh2_rows
#print axioms Desc.K14.Shape.sh2_mask
#print axioms Desc.K14.Shape.kind_addLaid
#print axioms Desc.K14.Shape.kind_units
#print axioms Desc.K14.Shape.rec_kind
#print axioms Desc.K14.Shape.kinds_mapM
#print axioms Desc.K14.Shape.point_carries
#print axioms Desc.K14.Shape.rec_parts
#print axioms Desc.K14.Shape.loc_parts
#print axioms Desc.K14.Shape.rec_carries
#print axioms Desc.K14.Shape.loc_carries
#print axioms Desc.K14.Shape.joins_carries
#print axioms Desc.K14.Shape.zeta_carries
#print axioms Desc.K14.Shape.split_carries
