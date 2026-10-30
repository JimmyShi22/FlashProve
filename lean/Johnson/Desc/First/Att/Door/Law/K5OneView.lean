-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5OneView.lean: WHAT THE TEST `P5J.K03.oneB`
(Johnson/P5J/K03OneOwn.lean: the lookup argument's premise "one", as a test with code that walks
the entries of a link's list) READS, so that at written values it becomes closed. After the
pattern of Johnson/Top/H0/K2Ties/OffAt.lean. Definitions and laws; nothing is evaluated here.

  `callShapes D l`: the shapes of link l's calls' list. `sigListCalls_is`: that list is these
    shapes, each with its radius.
  `oneB_rad`: `oneB` is blind to the radii: it reads an entry's shape, and whether the place is
    there.
  `oneV V D num ps arr l`: the test at link l, read off the view V of the public parameters' shape
    (`PlanWritten.XShape`), at the place `idxAt D num l`, the seats `seatCallsT ps D l` and the
    identity for the witness's numbers.
  `oneB_view`: at the full size's shape and l < 25 the test reads the public parameters through the
    view alone.
  `oneV_sent`: it reads of "what the planner sends" the shape and the layout alone.
Limits. Laws on one test's text. Nothing on soundness. On hiding nothing.

-/
import Johnson.P5J.K03OneOwn
import Johnson.Desc.First.Look.K3IdxAt
import Johnson.P5T.SeatsAt
import Johnson.Goal.Meaning.NamedView
import Johnson.Goal.Meaning.NamedAskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.First.Look (Sent sigListCalls sigList keptAt messagesAt idxAt szOf)
open VerifiableInference.PlanWritten (XShape xShapeOf tailView)
open _root_.Meaning (labAt ownerK ownerA nameOf messageAt)
open _root_.Meaning.NamedAsk (tailV entryV tailV_at entryV_at tlK_eq fullShaped all_range_congr)
open P5J.K03 (oneB)
open P5T (PSeat)

/-- The shapes of link l's calls' list: the kept messages', then the link's own of moment 0. -/
def callShapes (D : Sent) (l : ℕ) : List OracleShape :=
  (keptAt D l).map (·.shape) ++
    ((messagesAt D l).takeWhile fun m => decide (m.moment ≤ 0)).map (·.shape)

/-- The calls' list is these shapes, each with its radius. -/
theorem sigListCalls_is (D : Sent) (rad : OracleShape → ℕ) (l : ℕ) :
    sigListCalls D rad l = (callShapes D l).map fun s => (s, rad s) := by
  unfold sigListCalls sigList callShapes
  rw [List.map_append, List.map_map, List.map_map]
  rfl

/-- **`oneB` is blind to the radii.** -/
theorem oneB_rad (X : Verify.Public) (D : Sent) (rad rad' : OracleShape → ℕ) (num : ℕ → ℕ → ℕ)
    (idx : ℕ → ℕ) (tls : ℕ → HTailF2) (k : ℕ) (st : ℕ → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (wn : ℕ → ℕ) :
    oneB X D rad num idx tls k st arr wn = oneB X D rad' num idx tls k st arr wn := by
  unfold oneB
  refine all_range_congr fun μ _ => ?_
  cases arrayOf D.layout (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ))) with
  | none => rfl
  | some A =>
    simp only [sigListCalls_is, List.getElem?_map]
    cases (callShapes D k)[idx (num (ownerK (labAt X k μ)) A.message)]? <;>
      cases messageAt D.shape (ownerK (labAt X k μ)) A.message <;> rfl

/-- **The test "one" at link l, read off the view of the public parameters' shape.** -/
def oneV (V : XShape) (D : Sent) (num : ℕ → ℕ → ℕ) (ps : List PSeat) (arr : ℕ → ℕ → ℕ) (l : ℕ) :
    Bool :=
  (List.range (tailV V l).1).all fun μ =>
    match arrayOf D.layout (ownerK (entryV (tailV V l) μ).1)
        (nameOf (ownerA (entryV (tailV V l) μ).1)) with
    | none => false
    | some A =>
      match (callShapes D l)[idxAt D num l (num (ownerK (entryV (tailV V l) μ).1) A.message)]?,
          messageAt D.shape (ownerK (entryV (tailV V l) μ).1) A.message with
      | some e, some m => e == m.shape &&
          arr (P6T.seatCallsT ps D l
              (idxAt D num l (num (ownerK (entryV (tailV V l) μ).1) A.message))).1
            (P6T.seatCallsT ps D l
              (idxAt D num l (num (ownerK (entryV (tailV V l) μ).1) A.message))).2 ==
            num (ownerK (entryV (tailV V l) μ).1) A.message
      | some _, none => false
      | none, _ => true

/-- **The test reads the public parameters through the view alone**, at the full size's shape. -/
theorem oneB_view {X : Verify.Public} (hF : fullShaped X = true) (D : Sent)
    (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ) (ps : List PSeat) (arr : ℕ → ℕ → ℕ) {l : ℕ}
    (hl : l < 25) :
    oneB X D rad num (idxAt D num l) (_root_.Meaning.tlAt X) l (fun j => P6T.seatCallsT ps D l j)
      arr id = oneV (xShapeOf X) D num ps arr l := by
  unfold oneB oneV
  rw [tailV_at X hl, tlK_eq hF hl]
  have e1 : (tailView (_root_.Meaning.tlAt X l)).1 = (szOf (_root_.Meaning.tlAt X l)).NM := rfl
  rw [e1]
  refine all_range_congr fun μ _ => ?_
  rw [entryV_at]
  simp only [labAt, _root_.Meaning.matsAt, sigListCalls_is, List.getElem?_map]
  generalize ((_root_.Meaning.tlAt X l).mats.getD μ {}).aId = lab
  cases arrayOf D.layout (ownerK lab) (nameOf (ownerA lab)) with
  | none => rfl
  | some A =>
    dsimp only
    cases (callShapes D l)[idxAt D num l (num (ownerK lab) A.message)]? <;>
      cases messageAt D.shape (ownerK lab) A.message <;> rfl

/-- **It reads of "what the planner sends" the shape and the layout alone.** -/
theorem oneV_sent (V : XShape) {D D' : Sent} (hs : D.shape = D'.shape)
    (hy : D.layout = D'.layout) (num : ℕ → ℕ → ℕ) (ps : List PSeat) (arr : ℕ → ℕ → ℕ) (l : ℕ) :
    oneV V D num ps arr l = oneV V D' num ps arr l := by
  obtain ⟨c, s, y, a⟩ := D
  obtain ⟨c', s', y', a'⟩ := D'
  obtain rfl : s = s' := hs
  obtain rfl : y = y' := hy
  rfl

end H2K5.Door

#print axioms H2K5.Door.sigListCalls_is
#print axioms H2K5.Door.oneB_rad
#print axioms H2K5.Door.oneB_view
#print axioms H2K5.Door.oneV_sent
