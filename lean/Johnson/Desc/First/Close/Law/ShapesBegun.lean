-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/ShapesBegun.lean: `ShapesAre` RIDES PAST THE BEGINNING OF THE GROUP's
TEST; SO THE TWO PUBLIC PREMISES OF `k10_rows_at_cube` (RowsAtCube.lean, beside this file) FOLLOW
FROM `ShapesAre` AT THE STATEMENT IN FRONT OF K10. Statements and proofs.

Why. `k10_rows_at_cube` draws every open item "row" of the segment from K10's law's end. Two of its
premises are public ties AT THE BEGUN STATEMENT: hC (`CubeFits` and `NamesFit`, at every group at
the frame's number and its layout) and hN (the slots' names lie within the tables).
CubeOfShapes.lean and NamesOfShapes.lean pay them at a statement with `ShapesAre`
(LayoutOfShapes.lean). What a walk along the chain can give is `ShapesAre` at the statement IN FRONT
of K10.
  `shapesAre_begun`: `ShapesAre T G lo kb no` gives `ShapesAre (begun T g G) (begunGroup G) lo kb
    no`: the beginning of the test turns no member, no flag and no shape (`closeLedgers_shape`,
    OnBytes/Slice/BlkStLaws.lean).
  `ties_of_shapes`: hC IN ITS OWN FORM, at the typed group `groupLayK` and the names `namesOf`:
    from: T's group at g has `ShapesAre`; `LayoutAgrees lo kb`; the numbering parts the members;
    `kLay lo kb` = s.h + s.g; s.h = 0; and the two codes' lengths at the layout (hc).
  `names_of_shapes`: hN in its own form: with "T is in order" (`InOrder`) besides.
Limits. `k10_rows_at_cube` is not called here. `ShapesAre` at a verifier's state, the numbering's
parting, `kLay lo kb` = s.h + s.g and the two equations on the codes' lengths stay premises. Nothing
on soundness.

-/
import Johnson.Desc.First.Close.Law.NamesOfShapes
import Johnson.Desc.First.Close.Law.OnOfOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Means Johnson.Pack Johnson.Top.H Johnson.G

section
variable {cs : Codes} {lo : List (OracleShape × ℕ)} {s : Sg} {e : ℕ} {kb : Fin lo.length → Bool}
  {hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = s.C}
  {hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = s.Z}
  {no : Fin lo.length → ℕ} {T : Statement} {G : Group}

/-- **The beginning of the group's test turns no member, no flag and no shape.** -/
theorem shapesAre_begun (g : ℕ) (H : ShapesAre T G lo kb no) :
    ShapesAre (begun T g G) (begunGroup G) lo kb no where
  members := H.members
  kept := H.kept
  shape := fun i hi => (closeLedgers_shape G.members.toList T (no i)).trans (H.shape i hi)

/-- **The public ties that k10_rows_at_cube asks (its hC), from ShapesAre in front.** -/
theorem ties_of_shapes (g : ℕ) (H : ∀ G, T.groups[g]? = some G → ShapesAre T G lo kb no)
    (hA : LayoutAgrees lo kb)
    (hinj : ∀ i ∈ membersOf lo, ∀ j ∈ membersOf lo, no i = no j → i = j)
    (hk : kLay lo kb = s.h + s.g) (hh : s.h = 0)
    (hc : ∀ G lay, T.groups[g]? = some G → (begun T g G).layout g = some lay →
      2 ^ lay.logEll = s.C.l ∧ 2 ^ lay.logEllZk = s.Z.l) :
    ∀ G lay, T.groups[g]? = some G → (begun T g G).layout g = some lay →
      CubeFits (groupLayK cs lo s e kb hM hZ) (begun T g G) lay (fun a => no a.1) ∧
        NamesFit (groupLayK cs lo s e kb hM hZ) (namesOf cs lo s e kb hM hZ no) (begun T g G) lay
          fun a => no a.1 := by
  intro G lay hG hL
  have hG' := begun_at g G hG
  have H' := shapesAre_begun g (H G hG)
  obtain ⟨L, h1, h2, -, -⟩ := layout_of_shapes hG' H' hA
  obtain rfl : L = lay := Option.some.inj (h1.symm.trans hL)
  obtain ⟨c1, c2⟩ := hc G L hG hL
  exact ⟨cubeFits_of_shapes hG' hL H' h2 hinj (h2.1.trans hk) hh c1 c2,
    namesFit_of_shapes hG' hL H' hinj⟩

/-- **The slots' names lie within the begun statement's tables (its hN).** -/
theorem names_of_shapes (g : ℕ) (hI : InOrder T)
    (H : ∀ G, T.groups[g]? = some G → ShapesAre T G lo kb no) (hA : LayoutAgrees lo kb)
    (hc : ∀ G lay, T.groups[g]? = some G → (begun T g G).layout g = some lay →
      2 ^ lay.logEll = s.C.l ∧ 2 ^ lay.logEllZk = s.Z.l) :
    ∀ G, T.groups[g]? = some G → ∀ (q : (groupLayK cs lo s e kb hM hZ).Kp)
      (x : (groupLayK cs lo s e kb hM hZ).s.cM.J),
      (namesOf cs lo s e kb hM hZ no).orc q < (begun T g G).oracles.size ∧
        (namesOf cs lo s e kb hM hZ no).idx q x <
          tableSize (begun T g G) ((namesOf cs lo s e kb hM hZ no).orc q) .main := by
  intro G hG q x
  have hG' := begun_at g G hG
  have H' := shapesAre_begun g (H G hG)
  obtain ⟨L, h1, -, -, -⟩ := layout_of_shapes hG' H' hA
  exact names_in (layFacts hG' h1 ((hI.begun g G hG).groups g _ hG')) H' (hc G L hG h1).1 q x

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.shapesAre_begun
#print axioms VerifiableInference.Desc.First.Close.ties_of_shapes
#print axioms VerifiableInference.Desc.First.Close.names_of_shapes
