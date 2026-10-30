-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyPile.lean: the rows on the committed matrix that a key file's lookups leave, and the one row
that the batching of these rows passes on. Of both, the weights on the matrix's rows and the column
point are shown to be functions of public parameters, of the points of the lookups' claims on their
keys, and of the batching's own challenges. The public parameters are the matrix's size m
(`Wf.Matrix`) and the lookups (`WfLookup`); a key's one-time chain has both in its parameter bytes
(`OneTime`, OnBytes/Params/Chains.lean: the fields `lin` and `ranges`). `wWeights`
(E2E/KeySendJobs.lean) is `handedWeights` at `pileOf`, and `wJob` there computes from it the vector
W that it sends. General in m, the lookups, the claims and the challenges. Definitions, statements
and proofs.

The setting. A row on the matrix (`TensorRow`, OnBytes/Iop/Batt.lean) has four fields: `g`, a list
of vectors whose sum is the weights on the matrix's rows; `psi`, the column point; `masks`, a mask
form; `target`. After the lookups, `tableRowsOf` (Johnson/Desc/Key/TableRows.lean) makes a row of
each part's claim on its keys (`Lkp.Keys`, OnBytes/Iop/Lkp.lean; a part is a `WfPart`) by the
verifier program's `Wf.pendingRow` (OnBytes/Iop/Wf.lean). Of the claim, `g` and `psi` read the field
`point` only; the row's mask form is the claim's, and its target reads the claim's target as well.
The pile is the list of these rows for all parts of all lookups. The batching (`Batt.verify`,
OnBytes/Iop/Batt.lean) draws an element x and runs the library's sumcheck, in which an element eps,
which joins the hiding polynomial to the claim, and one challenge for each column variable are
drawn. `Psc.run` (OnBytes/Iop/Psc.lean) computes what the sumcheck passes on, and `Batt.rowOf` makes
the one row of it. In the names, handed refers to that one row.

  `handed_same`: `handedWeights` at the flattened rows that `tableRowsOf` returns for all lookups is
    `handedWeights` at `pileOf m lookups` at the claims' points, at every x, eps and point. So these
    weights are a function of m, the lookups, the claims' points and the batching's challenges
  `pile_same`: these flattened rows have, row by row, the `g` and the `psi` of the rows of `pileOf`
    at the claims' points. Stated with `List.zip` where `handed_same` has `zipT`, and with the
    lookups numbered from any n, for the induction; `pileOf` is the case n = 0
  `rowOf_weights`: wherever `Psc.run` returns o at the batching's claim and summand for a pile and x
    (`Batt.claimOf`, `Batt.summandOf`), at every h (`Psc.Heard`: what was sent and drawn): in the
    row `Batt.rowOf pile o`, `g` is `handedWeights pile x h.eps o.point` and `psi` is `o.point`
  `run_rowMaps`: wherever `Psc.run` returns o, at any claim and summand: `o.rowMaps` is eps times
    the summand's coefficients without the first, and `o.point` is the challenges of the claim's
    variables
  `handedWeights_congr`: two piles whose rows have the same `g` and `psi` have the same
    `handedWeights`: mask forms and targets are not read
  `handedWeights_of`: `handedWeights` at a pile is `handedOf` at the list of the pairs of `g` and
    `psi` of its rows
  `tableRows_same`: where `tableRowsOf m l keys` returns rows, their `g` and `psi` are those of
    `rowOfPoint` at the claims' points, part by part
  `tableRows_by_number`: the same with the parts numbered from 0, the claim of part number f read
    from the list by `List.getD`
  `mapM_proj`, `zip_by_number`: two facts on lists: what `List.mapM` of a function into `Option`
    returns, seen through a projection; the zip of two lists of one length, written with the numbers
    of `List.zipIdx`
  `rowOfPoint m l p point`: a definition: `Wf.pendingRow` at a claim that has the point, `default`
    as its weights and as its mask form, and the target 0
  `pileOf m lookups points`: a definition: the rows `rowOfPoint` for all parts of all lookups, in
    the lookups' and the parts' order. `points i f` is the point of part number f of lookup number
    i, both counted from 0
  `handedCoeffs pile x eps point`: a definition: the coefficient of each row of the pile in the one
    row: for row number j it is eps · (x^j · eq(psi_j, point)), with `eqEval` for eq
  `handedWeights pile x eps point`: a definition: the `g` of the one row: every vector of every
    row's `g`, scaled by that row's coefficient
  `handedOf gs x eps point`: a definition: the same, from a list of pairs of `g` and `psi` in place
    of a pile

By what. `tableRows_same` unfolds `tableRowsOf` and applies `mapM_proj`; the two fields agree by
unfolding `Wf.pendingRow`, which gets `Wf.eqPlaces m` at the claim's point on both sides.
`tableRows_by_number` rewrites it by `zipT_eq` (OnBytes/Chain/Lists.lean) and `zip_by_number`.
`run_rowMaps` unfolds `Psc.run`. `rowOf_weights` follows from it by unfolding `Batt.rowOf`: the
coefficients of `Batt.summandOf` do not read the shown values. `handedWeights_of` unfolds
`Batt.summandOf` and `Batt.chiOf` and simplifies by `zipT_eq` and lemmas on lists;
`handedWeights_congr` rewrites by it on both sides. `pile_same` is an induction on the two lists by
`tableRows_by_number`. `handed_same` is `handedWeights_congr` at `pile_same` with n = 0. Further
definitions: `Psc.powers` (OnBytes/Iop/Psc.lean), `eqEval` (OnBytes/Field/Mle.lean), `Tensor.scale`
(OnBytes/Iop/Tensor.lean).

Hypotheses of `handed_same`; `pile_same` has the same two, without names. hn: there are as many
lists of claims as lookups. h: `tableRowsOf` returns rows for every lookup with its list of claims.
`layPile` (Johnson/Desc/Key/One.lean) tests the first, computes the rows by the expression of h, and
stores `rows.flatten` as the pile.

Limits.
- The points are a parameter: `points` in `pileOf`, the field `point` of the given claims in the
  theorems. How they are computed from the verifier's messages is not stated in Lean here.
- Only `g` and `psi` are compared. A row of `rowOfPoint` has the empty mask form, and its target is
  0 minus the lookup's offset times `Wf.coveredSum`. These are not those of the row that
  `tableRowsOf` returns, which has the claim's mask form and whose target reads the claim's.
- The value of a row's weights at a row of the matrix is not computed here: the equations are
  between lists of `Tensor`.
- `layPile` and `Batt.verify` are not called, and `layPile` is not imported: the theorems are stated
  of the expression and of the pure functions that these two call.
- Nothing on hiding follows from this file, also not from `handedWeights_congr`.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.Key.TableRows

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes
open OnBytes.Params (WfPart WfLookup)
open VerifiableInference.Desc.Key (tableRowsOf)

/-- The verifier program's row on the matrix (`Wf.pendingRow`) at a claim that has the given point,
`default` as its weights and as its mask form, and the target 0. -/
def rowOfPoint (m : Wf.Matrix) (l : WfLookup) (p : WfPart) (point : List E) : TensorRow :=
  Wf.pendingRow m l p { point := point, weights := default, masks := default, target := zeroE }
    (Wf.eqPlaces m point)

/-- The rows `rowOfPoint` of all parts of all lookups, in the lookups' and the parts' order.
`points i f` is the point of part number f of lookup number i. -/
def pileOf (m : Wf.Matrix) (lookups : List WfLookup) (points : Nat → Nat → List E) :
    List TensorRow :=
  lookups.zipIdx.flatMap fun x =>
    x.1.parts.zipIdx.map fun p => rowOfPoint m x.1 p.1 (points x.2 p.2)

/-- If pr of whatever f returns at a is g a, then, where `L.mapM f` returns R, R mapped by pr is L
mapped by g. -/
theorem mapM_proj {α β γ : Type} (f : α → Option β) (pr : β → γ) (g : α → γ)
    (h : ∀ a b, f a = some b → pr b = g a) :
    ∀ (L : List α) (R : List β), L.mapM f = some R → R.map pr = L.map g
  | [], R, e => by
    rw [List.mapM_nil] at e
    obtain rfl : [] = R := Option.some.inj e
    rfl
  | a :: L, R, e => by
    rw [List.mapM_cons] at e
    cases ha : f a with
    | none => rw [ha] at e; exact absurd e (by simp)
    | some b =>
      cases hL : L.mapM f with
      | none => rw [ha, hL] at e; exact absurd e (by simp)
      | some bs =>
        rw [ha, hL] at e
        obtain rfl : b :: bs = R := Option.some.inj e
        rw [List.map_cons, List.map_cons, h a b ha, mapM_proj f pr g h L bs hL]

/-- **The rows that `tableRowsOf` returns have the weights and the column points of `rowOfPoint`**
at the claims' points, part by part. -/
theorem tableRows_same (m : Wf.Matrix) (l : WfLookup) (keys : List Lkp.Keys)
    (rows : List TensorRow) (h : tableRowsOf m l keys = some rows) :
    rows.map (fun r => (r.g, r.psi)) = (zipT l.parts keys).map fun x =>
      ((rowOfPoint m l x.1 x.2.point).g, (rowOfPoint m l x.1 x.2.point).psi) := by
  unfold tableRowsOf at h
  split at h
  · refine mapM_proj _ _ _ (fun x r hx => ?_) _ _ h
    dsimp only at hx
    split at hx
    · obtain rfl := Option.some.inj hx
      rfl
    · exact absurd hx (by simp)
  · exact absurd h (by simp)

/-! ## The one row that the batching passes on -/

/-- The coefficients of the pile's rows in the row that the batching passes on: for row number j,
eps · (x^j · eq(psi_j, point)). In `Batt.verify` x is the element drawn in the batching's first
round, eps the element that joins the hiding polynomial to the claim, and point the challenges of
the column variables. Computed by the library's own summand (`Batt.summandOf`). -/
def handedCoeffs (pile : List TensorRow) (x eps : E) (point : List E) : List E :=
  (((Batt.summandOf pile x).coeffs point []).drop 1).map fun a => mulE eps a

/-- The weights on the matrix's rows in the row that the batching passes on, as a function of the
pile and of the challenges x, eps and point only. The vector W that a prover sends after the
batching is said to be these weights times the matrix (Johnson/Desc/K13/Law/Eval.lean); nothing on W
is stated in this file. -/
def handedWeights (pile : List TensorRow) (x eps : E) (point : List E) : List Tensor :=
  (zipT pile (handedCoeffs pile x eps point)).flatMap fun p => p.1.g.map fun t => t.scale p.2

/-- Wherever the library's sumcheck (`Psc.run`) returns: the coefficients that it passes on for the
rows (`rowMaps`) are eps times the summand's coefficients without the first, and its point is the
challenges of the claim's variables. -/
theorem run_rowMaps (c : Psc.Claim) (S : Psc.Summand) (fresh : List Slot) (h : Psc.Heard)
    (o : Psc.Out) (e : Psc.run c S fresh h = some o) :
    o.rowMaps = ((S.coeffs ((h.rounds.map (·.2)).take c.vars.length) h.values).drop 1).map
        (fun a => mulE h.eps a) ∧
      o.point = (h.rounds.map (·.2)).take c.vars.length := by
  unfold Psc.run at e
  dsimp only at e
  split at e
  · obtain rfl := Option.some.inj e
    exact ⟨rfl, rfl⟩
  · exact absurd e (by simp)

/-- **The row that `Batt.rowOf` makes has the weights `handedWeights` and the sumcheck's point as
its column point**: wherever `Psc.run` returns at the batching's claim and summand, whatever was
sent. -/
theorem rowOf_weights (pile : List TensorRow) (x : E) (fresh : List Slot) (h : Psc.Heard)
    (o : Psc.Out) (e : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o) :
    (Batt.rowOf pile o).g = handedWeights pile x h.eps o.point ∧
      (Batt.rowOf pile o).psi = o.point := by
  obtain ⟨e1, e2⟩ := run_rowMaps _ _ fresh h o e
  refine ⟨?_, rfl⟩
  unfold Batt.rowOf handedWeights handedCoeffs
  rw [e1, e2]
  rfl

/-! ## The weights passed on read the pile's weights and column points only -/

/-- The weights passed on, written from the rows' weights and column points only. -/
def handedOf (gs : List (List Tensor × List E)) (x eps : E) (point : List E) : List Tensor :=
  (gs.zip (((Psc.powers oneE x gs.length).zip gs).map fun p =>
    mulE eps (mulE p.1 (eqEval p.2.2 point)))).flatMap fun p => p.1.1.map fun t => t.scale p.2

theorem handedWeights_of (pile : List TensorRow) (x eps : E) (point : List E) :
    handedWeights pile x eps point = handedOf (pile.map fun r => (r.g, r.psi)) x eps point := by
  unfold handedWeights handedCoeffs handedOf Batt.summandOf Batt.chiOf
  simp only [zipT_eq, List.drop_succ_cons, List.drop_zero, List.map_map, List.length_map,
    List.zip_map_left, List.zip_map_right, List.flatMap_map]
  rfl

/-- **Two piles whose rows have the same weights and column points pass on the same weights**: the
rows' mask forms and targets, which `Wf.pendingRow` makes of the claim's fields `masks` and
`target`, are not read. -/
theorem handedWeights_congr (pile pile' : List TensorRow) (x eps : E) (point : List E)
    (h : pile.map (fun r => (r.g, r.psi)) = pile'.map fun r => (r.g, r.psi)) :
    handedWeights pile x eps point = handedWeights pile' x eps point := by
  rw [handedWeights_of, handedWeights_of, h]

/-! ## The pile over all lookups -/

/-- The zip of two lists of one length, mapped, is the first list with its numbers (`List.zipIdx`,
from any n), mapped, with the second list read by number (`List.getD`). -/
theorem zip_by_number {α β γ : Type} (F : α → β → γ) (d : β) :
    ∀ (as : List α) (bs : List β) (n : Nat), as.length = bs.length →
      (as.zip bs).map (fun x => F x.1 x.2) =
        (as.zipIdx n).map fun p => F p.1 (bs.getD (p.2 - n) d)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h => absurd h (by simp)
  | a :: as, b :: bs, n, h => by
    rw [List.zip_cons_cons, List.map_cons, List.zipIdx_cons, List.map_cons,
      zip_by_number F d as bs (n + 1) (by simpa using h)]
    rw [List.cons.injEq]
    refine ⟨by simp, List.map_congr_left fun p hp => ?_⟩
    have hp2 : n + 1 ≤ p.2 := (List.mem_zipIdx hp).1
    rw [show p.2 - n = (p.2 - (n + 1)) + 1 by omega, List.getD_cons_succ]

/-- One lookup's rows with the parts numbered from 0: `tableRows_same`, with the claim of part
number f read from the list of claims. -/
theorem tableRows_by_number (m : Wf.Matrix) (l : WfLookup) (keys : List Lkp.Keys)
    (rows : List TensorRow) (h : tableRowsOf m l keys = some rows) :
    rows.map (fun r => (r.g, r.psi)) = (l.parts.zipIdx.map fun p =>
      rowOfPoint m l p.1 (keys.getD p.2 default).point).map fun r => (r.g, r.psi) := by
  have hn : l.parts.length = keys.length := by
    unfold tableRowsOf at h
    split at h
    · rename_i hh
      exact beq_iff_eq.1 hh
    · exact absurd h (by simp)
  rw [tableRows_same m l keys rows h, zipT_eq, List.map_map,
    zip_by_number (fun (p : WfPart) (k : Lkp.Keys) =>
      ((rowOfPoint m l p k.point).g, (rowOfPoint m l p k.point).psi)) default l.parts keys 0 hn]
  rfl

/-- **The flattened rows of all lookups have the weights and the column points of `pileOf`** at the
claims' points: where `tableRowsOf` returns rows for every lookup with its claims. `layPile`
(Johnson/Desc/Key/One.lean) computes the rows in this way and stores the flattened list as the pile.
The lookups are numbered from any n; `pileOf` is the case n = 0. -/
theorem pile_same (m : Wf.Matrix) : ∀ (lookups : List WfLookup) (keys : List (List Lkp.Keys))
    (rows : List (List TensorRow)) (n : Nat), lookups.length = keys.length →
    (lookups.zip keys).mapM (fun x => tableRowsOf m x.1 x.2) = some rows →
    rows.flatten.map (fun r => (r.g, r.psi)) =
      ((lookups.zipIdx n).flatMap fun x => x.1.parts.zipIdx.map fun p =>
        rowOfPoint m x.1 p.1 ((keys.getD (x.2 - n) []).getD p.2 default).point).map
        fun r => (r.g, r.psi)
  | [], [], rows, _, _, e => by
    rw [List.zip_nil_left, List.mapM_nil] at e
    obtain rfl : [] = rows := Option.some.inj e
    rfl
  | [], _ :: _, _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, h, _ => absurd h (by simp)
  | l :: ls, k :: ks, rows, n, h, e => by
    rw [List.zip_cons_cons, List.mapM_cons] at e
    cases ha : tableRowsOf m l k with
    | none => rw [ha] at e; exact absurd e (by simp)
    | some r =>
      cases hL : (ls.zip ks).mapM (fun x => tableRowsOf m x.1 x.2) with
      | none => rw [ha, hL] at e; exact absurd e (by simp)
      | some rs =>
        rw [ha, hL] at e
        obtain rfl : r :: rs = rows := Option.some.inj e
        rw [List.flatten_cons, List.map_append, tableRows_by_number m l k r ha,
          pile_same m ls ks rs (n + 1) (by simpa using h) hL, List.zipIdx_cons, List.flatMap_cons,
          List.map_append]
        refine (congrArg (· ++ _) (by simp)).trans (congrArg (_ ++ ·) ?_)
        refine congrArg (List.map fun r : TensorRow => (r.g, r.psi)) ?_
        rw [List.flatMap_def, List.flatMap_def]
        refine congrArg List.flatten (List.map_congr_left fun x hx => ?_)
        have hx2 : n + 1 ≤ x.2 := (List.mem_zipIdx hx).1
        rw [show x.2 - n = (x.2 - (n + 1)) + 1 by omega, List.getD_cons_succ]

/-- **So the weights that the batching passes on are a function of public parameters, the claims'
points and the batching's own challenges only**: at the flattened rows that `tableRowsOf` returns
they are those at `pileOf`. -/
theorem handed_same (m : Wf.Matrix) (lookups : List WfLookup) (keys : List (List Lkp.Keys))
    (rows : List (List TensorRow)) (hn : lookups.length = keys.length)
    (h : (zipT lookups keys).mapM (fun x => tableRowsOf m x.1 x.2) = some rows) (x eps : E)
    (point : List E) :
    handedWeights rows.flatten x eps point =
      handedWeights (pileOf m lookups fun i f => ((keys.getD i []).getD f default).point) x eps
        point := by
  rw [zipT_eq] at h
  refine handedWeights_congr _ _ x eps point ?_
  rw [pile_same m lookups keys rows 0 hn h]
  rfl

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.mapM_proj
#print axioms AtPublicFiles.Key.tableRows_same
#print axioms AtPublicFiles.Key.run_rowMaps
#print axioms AtPublicFiles.Key.rowOf_weights
#print axioms AtPublicFiles.Key.handedWeights_of
#print axioms AtPublicFiles.Key.handedWeights_congr
#print axioms AtPublicFiles.Key.zip_by_number
#print axioms AtPublicFiles.Key.tableRows_by_number
#print axioms AtPublicFiles.Key.pile_same
#print axioms AtPublicFiles.Key.handed_same
#print axioms AtPublicFiles.Key.rowOfPoint
#print axioms AtPublicFiles.Key.pileOf
#print axioms AtPublicFiles.Key.handedCoeffs
#print axioms AtPublicFiles.Key.handedWeights
#print axioms AtPublicFiles.Key.handedOf
