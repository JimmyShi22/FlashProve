-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeFirstEnd.lean: WHAT IS READ OFF THE FIRST CHAIN's SHAPE AT ITS END
(E2E/KeyShapeFirstBack.lean's `Sh₁B`): the first chain's part of the file's last test; and the three
values that the third chain's start reads of the first chain. Definitions, statements and proofs.
Readers of the verifier's state: NOTHING IS SHOWN OF ANY PROVER.

  **`firstEndS`**, **`firstEndS_eq`**: the library's `firstEndOk` (Johnson/Desc/Key/Chain1.lean) IS
    A FUNCTION OF THE SHAPE: all five clauses.
  **`door_at`**: E2E/KeyShapeDoor.lean's `doorS` at the shape's core, its mark on the statement and
    its back part's `door` is `doorS` at the three values in the form in which `door_returns` and
    `door_carries` take them.
  `flat₂_tie`: at the key file's description: its shared chain's flat list is
    E2E/KeyShapeSharedChain.lean's `flat₂`.

Limits.
- `door_at` has a premise on public values: the shape of the test on the table at which the reader
  is taken is the one at which the start is read. It is paid nowhere here.
- No shape is exhibited here at which `firstEndS` accepts: E2E/KeyShapeAtFull.lean has one.


-/
import E2E.KeyShapeFirstBack
import E2E.KeyShapeDoor
import E2E.KeyShapeSharedChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (FirstState firstEndOk firstChainEnded lookupsOf)
open AtPublicFiles.KeyShape (Pub1)

variable (Q : Pub1) (cs : Codes)

/-- **The first chain's part of the file's last test, on the shape.** -/
def firstEndS (a : Sh₁B) : Bool :=
  (a.2.atEnd && a.2.back.lin.any fun l => l.own != noId && l.w != noId) &&
    a.2.look.led.isNone && a.2.look.keys.length == (lookupsOf Q.one).length &&
    decide (a.2.grp < a.1.st.groups.length) &&
    (((a.1.st.groups.drop a.2.grp).dropLast).all fun G => G.inRun && G.kinds.isEmpty)

/-- **It is the library's.** -/
theorem firstEndS_eq (s : FirstState) : firstEndS Q (sh₁B Q cs s) = firstEndOk Q.one s := by
  have e1 : ((sh₁B Q cs s).2.back.lin.any fun l => l.own != noId && l.w != noId) =
      s.lin.any fun l => l.own != noId && l.w != noId := by
    show ((s.lin.map VerifiableInference.Desc.K13.Honest.laidSh).any _) = _
    cases s.lin <;> rfl
  have e2 : (sh₁B Q cs s).2.look.led.isNone = s.base.fork.isNone := by
    show (s.base.fork.map _).isNone = _
    cases s.base.fork <;> rfl
  have e3 : (sh₁B Q cs s).2.look.keys.length = s.base.keys.length := by
    show (keysSlots s.base.keys).length = _
    unfold keysSlots
    rw [List.length_map]
  have e4 : (sh₁B Q cs s).1.st.groups.length = s.d.st.groups.size := by
    show (s.d.st.groups.toList.map grpSh).length = _
    rw [List.length_map, Array.length_toList]
  have e5 : ((((sh₁B Q cs s).1.st.groups.drop s.grp).dropLast).all fun G =>
      G.inRun && G.kinds.isEmpty) =
      (((s.d.st.groups.toList.drop s.grp).dropLast).all fun G => G.inRun && G.rows.isEmpty) := by
    show ((((s.d.st.groups.toList.map grpSh).drop s.grp).dropLast).all _) = _
    rw [← List.map_drop, ← List.map_dropLast, List.all_map]
    refine List.all_congr rfl fun G => ?_
    show (G.inRun && (G.rows.toList.map (·.kind)).isEmpty) = _
    cases h : G.rows.toList with
    | nil =>
      have : G.rows.isEmpty = true := by
        rw [← Array.isEmpty_toList, h]
        rfl
      rw [this]
      rfl
    | cons r l =>
      have : G.rows.isEmpty = false := by
        rw [← Array.isEmpty_toList, h]
        rfl
      rw [this]
      rfl
  unfold firstEndS firstEndOk firstChainEnded
  rw [e1, e2, e3, e4]
  show (_ && _ && _ && _ && ((((sh₁B Q cs s).1.st.groups.drop s.grp).dropLast).all _)) = _
  rw [e5]
  rfl

/-- **The start on shapes, at the first chain's shape.** -/
theorem door_at (S : LinShape) (hS : Q.one.lin = S) (s₁ : FirstState) (b : SharedSh) :
    doorS cs S (sh₁B Q cs s₁).1 (sh₁B Q cs s₁).2.tidy (sh₁B Q cs s₁).2.back.door b =
      doorS cs S (coreSh ⟨s₁.d.st, s₁.d.book, s₁.d.roots⟩) (stTidyB s₁.d.st)
        (s₁.lin.map (linSh S cs)) b := by
  subst hS
  have e : (sh₁B Q cs s₁).2.back.door = s₁.lin.map (linSh Q.one.lin cs) :=
    door_of_back Q.one.lin cs s₁
  rw [e]
  rfl

/-- **The description's shared chain's flat list is E2E/KeyShapeSharedChain.lean's.** -/
theorem flat₂_tie (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) :
    (keyFileDescription X N P).shared.blocksInOrder = flat₂ X.chains P := rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.firstEndS_eq
#print axioms AtPublicFiles.AtFiles.door_at
#print axioms AtPublicFiles.AtFiles.flat₂_tie
