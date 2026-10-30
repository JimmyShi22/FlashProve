-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/CoefWrites.lean: the step that lays the virtual rows' weights
(coefBody, Johnson/Desc/First/TailClaims/Coefficients.lean) as a list of writes "at virtual row r of
array t a vector of n weights is laid, with this product form", where the list is a function of
numbers, kinds and sizes alone. General laws; nothing is evaluated.

Why. The smallness test's guards on sizes (shapeT, Johnson/Desc/First/TailClaims/TestsCut.lean) are
asked behind that step, and of what they read the step turns the sizes of the rows' weights alone
(same_coefBody, CoefKeeps.lean). Which size stands at a place behind the step hangs on which write
came last. Here that is not argued: the writes are listed in the step's own order, so that whoever
keeps the sizes in a plain list can lay them one after the other.

  `LaysRow f n o a`: the change f of one virtual row leaves the row's weights L on its entries and
    their first column L0; lays weights coef of size n; marks the row as having a product form; lays
    the mark "1 on every row" as o and the first row of the equality polynomial as a.
  `Lays F ws G`: G comes of F by the writes ws = [(t, r, n, o, a), ..], in order.
  `Lays.same`: then Same F G (CoefKeeps.lean's ten clauses, no more). `Lays.append`.
  `Lays.reads`: **for every reader ρ of the ledger with a law "one such write turns ρ by w", ρ G is
    ρ F turned by the writes in order.**
  `coefWrites tl zb0 zb1 isTable rows`: the list: the tables' rows (one weight each) · the pieces'
    rows of the two calls (as many weights as the array has rows) · the reads' and the ties' row ·
    the three rows of the planes' array · one row for each matrix's symbols. zb0, zb1: the sizes of
    two points that the lookup on the digits heard; isTable, rows: each array's kind and number of
    rows.
  **`lays_coefBody`**: Lays F (coefWrites ..) (coefBody tl g F), at F's own kinds and numbers.

Limits. Nothing on the weights themselves, nor on the product form's point and factors (rowPoint,
rowLo, rowHi), which the step lays too. A write at a place that is not there changes nothing: the
list holds it all the same; a reader's law has to say the same. The program's own silent answers
stand in the list: an array beyond the arrays counts as a table; a matrix without an entry goes to
array 0, with no weight. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.CoefKeeps
import OnBytes.Tie.Pv.Lookup.Ends.FoSlEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims
open Fo (coefAll coefTables coefPieces coefPowers coefBZ coefMats coefPieces_eq coefMats_eq
  allPieces pieceF pieceW)

/-- One write: the array, the virtual row, the number of weights, "1 on every row", the first row of
the equality polynomial. -/
abbrev Write : Type := Nat × Nat × Nat × Bool × Nat

/-- What a change of one virtual row lays and leaves. -/
def LaysRow (f : HRow → HRow) (n : Nat) (o : Bool) (a : Nat) : Prop :=
  ∀ row, (f row).L = row.L ∧ (f row).L0 = row.L0 ∧ (f row).coef.size = n ∧
    (f row).rowForm = true ∧ (f row).rowOnes = o ∧ (f row).rowFirst = a

theorem LaysRow.keeps {f : HRow → HRow} {n : Nat} {o : Bool} {a : Nat} (h : LaysRow f n o a) :
    KeepsL f := fun row => ⟨(h row).1, (h row).2.1⟩

/-- **G comes of F by these writes, in order.** -/
inductive Lays : Fork → List Write → Fork → Prop
  | nil (F : Fork) : Lays F [] F
  | cons {F G : Fork} {t r n : Nat} {o : Bool} {a : Nat} {ws : List Write} {f : HRow → HRow} :
      LaysRow f n o a → Lays (onRow F t r f) ws G → Lays F ((t, r, n, o, a) :: ws) G

theorem Lays.same {F G : Fork} {ws : List Write} (h : Lays F ws G) : Same F G := by
  induction h with
  | nil F => exact Same.refl F
  | cons hf _ ih => exact (same_onRow _ _ _ hf.keeps).trans ih

theorem Lays.append {F G H : Fork} {ws vs : List Write} (h : Lays F ws G) (k : Lays G vs H) :
    Lays F (ws ++ vs) H := by
  induction h with
  | nil F => exact k
  | cons hf _ ih => exact Lays.cons hf (ih k)

theorem Lays.one (F : Fork) (t r n : Nat) (o : Bool) (a : Nat) {f : HRow → HRow}
    (hf : LaysRow f n o a) : Lays F [(t, r, n, o, a)] (onRow F t r f) :=
  Lays.cons hf (Lays.nil _)

/-- **A reader that has a law for one write goes along with all.** -/
theorem Lays.reads {σ : Type} (ρ : Fork → σ) (w : σ → Write → σ)
    (hw : ∀ (F : Fork) (t r n : Nat) (o : Bool) (a : Nat) (f : HRow → HRow), LaysRow f n o a →
      ρ (onRow F t r f) = w (ρ F) (t, r, n, o, a))
    {F G : Fork} {ws : List Write} (h : Lays F ws G) : ρ G = ws.foldl w (ρ F) := by
  induction h with
  | nil F => rfl
  | cons hf _ ih => rw [ih, hw _ _ _ _ _ _ _ hf]; rfl

/-! ## The list -/

/-- The tables' rows: one weight each. -/
def tabWrites (tl : HTailF2) (isTable : Nat → Bool) (l : List Nat) : List Write :=
  l.filterMap fun n => (tl.ix.U.getD n none).bind fun t =>
    if isTable t then some (t, 0, 1, true, 0) else none

/-- **The writes of the step that lays the weights, in its own order.** -/
def coefWrites (tl : HTailF2) (zb0 zb1 : Nat) (isTable : Nat → Bool) (rows : Nat → Nat) :
    List Write :=
  tabWrites tl isTable (List.range 4) ++
    (allPieces tl).map (fun a => (a.2.tree, a.2.row, rows a.2.tree, false, a.2.r0)) ++
    [(tl.ix.ZZ, tl.zzRowReads, tl.vt.size, false, 0),
      (tl.ix.ZZ, tl.zzRowTies, tl.vp.size, false, 0)] ++
    [(tl.ix.BZ, 0, 2 ^ min 5 zb0, false, 0), (tl.ix.BZ, 1, 2 ^ min 5 zb1, false, 0),
      (tl.ix.BZ, 2, 32, true, 0)] ++
    (List.range tl.NM).map fun mu =>
      (tl.gtTree.getD mu 0, 0, (tl.rowX.getD mu #[]).size, false, 0)

/-! ## The five stages -/

/-- One step of the first stage. -/
def tabStep (tl : HTailF2) (F : Fork) (n : Nat) : Fork :=
  match tl.ix.U.getD n none with
  | some t =>
    if (F.trees.getD t {}).kind == .table then
      onRow F t 0 fun row => formOnes { row with coef := #[oneE] }
    else F
  | none => F

theorem forIn_step {α σ : Type} (step : σ → α → σ) (f : α → σ → Id (ForInStep σ))
    (hf : ∀ a s, f a s = (pure (ForInStep.yield (step s a)) : Id (ForInStep σ))) :
    ∀ (l : List α) (s : σ), (forIn l s f : Id σ) = l.foldl step s
  | [], _ => rfl
  | a :: l, s => by
    rw [List.forIn_cons, hf]
    exact forIn_step step f hf l (step s a)

theorem coefTables_eq (tl : HTailF2) (F : Fork) :
    coefTables tl F = (List.range 4).foldl (tabStep tl) F := by
  unfold coefTables
  refine forIn_step (tabStep tl) _ (fun n s => ?_) _ _
  unfold tabStep
  cases tl.ix.U.getD n none with
  | none => rfl
  | some t =>
    by_cases hk : ((s.trees.getD t {}).kind == HKind.table) = true
    · simp only [hk, if_true]
      rfl
    · simp only [hk, Bool.false_eq_true, if_false]
      rfl

theorem lays_tables (tl : HTailF2) (F₀ : Fork) : ∀ (l : List Nat) (F : Fork), Same F₀ F →
    Lays F (tabWrites tl (fun t => (F₀.trees.getD t {}).kind == .table) l)
      (l.foldl (tabStep tl) F)
  | [], F, _ => Lays.nil F
  | n :: l, F, h => by
    show Lays F _ (l.foldl (tabStep tl) (tabStep tl F n))
    cases hU : tl.ix.U.getD n none with
    | none =>
      have s1 : tabStep tl F n = F := by
        unfold tabStep
        rw [hU]
      have w1 : tabWrites tl (fun t => (F₀.trees.getD t {}).kind == .table) (n :: l) =
          tabWrites tl (fun t => (F₀.trees.getD t {}).kind == .table) l := by
        unfold tabWrites
        rw [List.filterMap_cons, hU]
        rfl
      rw [s1, w1]
      exact lays_tables tl F₀ l F h
    | some t =>
      by_cases hk : ((F₀.trees.getD t {}).kind == HKind.table) = true
      · have s1 : tabStep tl F n =
            onRow F t 0 fun row => formOnes { row with coef := #[oneE] } := by
          unfold tabStep
          rw [hU]
          simp only [h.kind t, hk, if_true]
        have w1 : tabWrites tl (fun t => (F₀.trees.getD t {}).kind == .table) (n :: l) =
            (t, 0, 1, true, 0) ::
              tabWrites tl (fun t => (F₀.trees.getD t {}).kind == .table) l := by
          unfold tabWrites
          rw [List.filterMap_cons, hU]
          simp only [Option.bind_some, hk, if_true]
        rw [s1, w1]
        exact Lays.cons (f := fun row => formOnes { row with coef := #[oneE] })
          (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
          (lays_tables tl F₀ l _ (h.trans (same_onRow _ _ _ fun _ => ⟨rfl, rfl⟩)))
      · have s1 : tabStep tl F n = F := by
          unfold tabStep
          rw [hU]
          simp only [h.kind t, hk, Bool.false_eq_true, if_false]
        have w1 : tabWrites tl (fun t => (F₀.trees.getD t {}).kind == .table) (n :: l) =
            tabWrites tl (fun t => (F₀.trees.getD t {}).kind == .table) l := by
          unfold tabWrites
          rw [List.filterMap_cons, hU]
          simp only [Option.bind_some, hk, Bool.false_eq_true, if_false]
        rw [s1, w1]
        exact lays_tables tl F₀ l F h

theorem lays_foldl {α : Type} (tr ro sz : α → Nat) (on : α → Bool) (fi : α → Nat)
    (f : Fork → α → HRow → HRow) (I : Fork → Prop)
    (hI : ∀ F a, I F → I (onRow F (tr a) (ro a) (f F a)))
    (hn : ∀ F a, I F → LaysRow (f F a) (sz a) (on a) (fi a)) : ∀ (l : List α) (F : Fork), I F →
      Lays F (l.map fun a => (tr a, ro a, sz a, on a, fi a))
        (l.foldl (fun F a => onRow F (tr a) (ro a) (f F a)) F)
  | [], F, _ => Lays.nil F
  | a :: l, F, h => Lays.cons (hn F a h) (lays_foldl tr ro sz on fi f I hI hn l _ (hI F a h))

theorem lays_pieces (tl : HTailF2) (g : Forest.Heard) (F₀ F : Fork) (h : Same F₀ F) :
    Lays F ((allPieces tl).map fun a =>
      (a.2.tree, a.2.row, (F₀.trees.getD a.2.tree {}).R, false, a.2.r0))
      (coefPieces tl g F) := by
  rw [coefPieces_eq]
  exact lays_foldl (fun a : Nat × Piece => a.2.tree) (fun a => a.2.row)
    (fun a => (F₀.trees.getD a.2.tree {}).R) (fun _ => false) (fun a => a.2.r0) (pieceF tl g)
    (Same F₀) (fun F a hF => hF.trans (same_onRow _ _ _ fun _ => ⟨rfl, rfl⟩))
    (fun F a hF row => ⟨rfl, rfl, by
      show (pieceW _ _ _ (F.trees.getD a.2.tree {}).R).size = _
      unfold pieceW
      rw [Array.size_map, Array.size_range, hF.R], rfl, rfl, rfl⟩) _ _ h

theorem lays_powers (tl : HTailF2) (theta : E) (F : Fork) :
    Lays F [(tl.ix.ZZ, tl.zzRowReads, tl.vt.size, false, 0),
      (tl.ix.ZZ, tl.zzRowTies, tl.vp.size, false, 0)] (coefPowers tl theta F) :=
  Lays.cons (f := fun row => formPowers { row with coef := tl.vt } theta tl.tau)
    (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (Lays.one _ _ _ _ _ _ (f := fun row => formPowers { row with coef := tl.vp } theta tl.tau)
      (fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩))

theorem size_point (z : Array E) : (eqTab (z.extract 0 5)).size = 2 ^ min 5 z.size := by
  rw [Fo.eqTab_size, Array.size_extract]
  simp

theorem lays_bz (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    Lays F [(tl.ix.BZ, 0, 2 ^ min 5 (g.zb 0).size, false, 0),
      (tl.ix.BZ, 1, 2 ^ min 5 (g.zb 1).size, false, 0), (tl.ix.BZ, 2, 32, true, 0)]
      (coefBZ tl g F) :=
  Lays.cons (f := fun row => formPoint { row with coef := eqTab ((g.zb 0).extract 0 5) }
      ((g.zb 0).extract 0 5) 0) (fun _ => ⟨rfl, rfl, size_point _, rfl, rfl, rfl⟩)
    (Lays.cons (f := fun row => formPoint { row with coef := eqTab ((g.zb 1).extract 0 5) }
        ((g.zb 1).extract 0 5) 0) (fun _ => ⟨rfl, rfl, size_point _, rfl, rfl, rfl⟩)
      (Lays.one _ _ _ _ _ _
        (f := fun row => formOnes { row with coef := Array.replicate 32 oneE })
        (fun _ => ⟨rfl, rfl, Array.size_replicate .., rfl, rfl, rfl⟩)))

theorem lays_mats (tl : HTailF2) (theta : E) (F : Fork) :
    Lays F ((List.range tl.NM).map fun mu =>
      (tl.gtTree.getD mu 0, 0, (tl.rowX.getD mu #[]).size, false, 0)) (coefMats tl theta F) := by
  rw [coefMats_eq]
  exact lays_foldl (fun mu => tl.gtTree.getD mu 0) (fun _ => 0)
    (fun mu => (tl.rowX.getD mu #[]).size) (fun _ => false) (fun _ => 0)
    (fun _ mu row => formPowers { row with coef := tl.rowX.getD mu #[] } (powE theta tl.stepF)
      (tl.shp.getD mu {}).mS) (fun _ => True) (fun _ _ _ => trivial)
    (fun _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) _ _ trivial

/-- **THE STEP AS A LIST OF WRITES.** -/
theorem lays_coefBody (tl : HTailF2) (g : Forest.Heard) (F : Fork) :
    Lays F (coefWrites tl (g.zb 0).size (g.zb 1).size
      (fun t => (F.trees.getD t {}).kind == .table) (fun t => (F.trees.getD t {}).R))
      (coefBody tl g F) := by
  have a : Lays F (tabWrites tl (fun t => (F.trees.getD t {}).kind == .table) (List.range 4))
      (coefTables tl F) := by
    rw [coefTables_eq]
    exact lays_tables tl F _ F (Same.refl F)
  have b := lays_pieces tl g F _ a.same
  exact (((a.append b).append (lays_powers tl F.theta _)).append (lays_bz tl g _)).append
    (lays_mats tl F.theta _)

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Lays.same
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Lays.append
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Lays.reads
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.coefTables_eq
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lays_coefBody
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Write
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.LaysRow
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.LaysRow.keeps
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Lays
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.Lays.one
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tabWrites
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.coefWrites
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.tabStep
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.forIn_step
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lays_tables
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lays_foldl
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lays_pieces
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lays_powers
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.size_point
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lays_bz
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.lays_mats
