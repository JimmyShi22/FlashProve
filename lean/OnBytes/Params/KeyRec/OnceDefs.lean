-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/OnceDefs.lean: the typed values of the sizing of the test on the table of a
key of full size: the lines, the three groups' shapes, the groups after each turn, the shape, the
record and the codes. Definitions, and one small evaluation in Lean's kernel.

Main names.
  keyLin, keyGroups, keyGroups_eq, keyX0 to keyZ1, keyOnceShape, keyOnceRec, keyCodes1.

Limits. The typed values were printed by Lean's evaluator; the files beside hold them against the
planner's routines. Nothing on soundness. What the whole leaves unsaid stands in the head of
OnBytes/Params/KeyRec/Once.lean.

-/
import OnBytes.Params.Fit.KeySizedParts
import OnBytes.Params.KeyRec.FoldedDefs
import OnBytes.Params.KeyRec.OmegaDefs
import OnBytes.Params.KeyRec.OwnDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

deriving instance DecidableEq for LinGroups

/-- The lines of a key's test on the table. -/
def keyLin : LinLines := linLines recordLines 3076096 1 true

/-- The record of the three groups. -/
def keyGroups : LinGroups :=
  ⟨true, .once, .once,
    ⟨⟨24, 4194304, 0, true⟩, ⟨13, 64, 0, true⟩, 7, 0, 1, .johnson, 0⟩,
    ⟨⟨22, 262144, 0, true⟩, ⟨13, 64, 0, true⟩, 4, 0, 1, .johnson, 0⟩,
    ⟨⟨22, 262144, 0, true⟩, ⟨13, 256, 0, true⟩, 5, 1, 1, .johnson, 0⟩, 66⟩

/-- It is the record that linSized's text forms. -/
theorem keyGroups_eq : linGroupsOf recordSet keyLin recordTable = keyGroups := by decide +kernel

/-- The folded row's group after turn 1. -/
def keyX0 : Sizing :=
  ⟨⟨⟨24, 4194304, 0, true⟩, ⟨13, 64, 0, true⟩, 7, 0, 1, .johnson, 182⟩, 97, true⟩

/-- Omega's group after turn 1. -/
def keyY0 : Sizing :=
  ⟨⟨⟨22, 262144, 0, true⟩, ⟨13, 64, 0, true⟩, 4, 0, 1, .johnson, 158⟩, 49, true⟩

/-- The own group after turn 1. -/
def keyZ0 : Sizing :=
  ⟨⟨⟨22, 262144, 0, true⟩, ⟨13, 256, 0, true⟩, 5, 1, 1, .johnson, 158⟩, 49, true⟩

/-- The folded row's group after turn 2. -/
def keyX1 : Sizing := ⟨keyU1, 97, true⟩

/-- Omega's group after turn 2. -/
def keyY1 : Sizing := ⟨keyO1, 49, true⟩

/-- The own group after turn 2. -/
def keyZ1 : Sizing := ⟨keyW1, 49, true⟩

/-- The shape of a key's test on the table. -/
def keyOnceShape : LinShape :=
  { fold :=
      { index := ⟨⟨32, 402653184, 44040191⟩, 11, 1, 40⟩
        u := { code := 0, mainRows := 107, mainDeg := 3, maskRows := 0, maskCode := noId,
               answers := 1 }
        rowsHigh := true, leafClass := 0, columns := 62 }
    kLo := 7
    matrixRows := 3076096
    omega := { code := 5, mainRows := 12, mainDeg := 3, maskRows := 0, maskCode := noId,
               answers := 1 }
    w := { code := 5, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 6, answers := 1 }
    omegaRowsHigh := true
    wRowsHigh := true
    sharedSplit := { code := noId, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 0,
                     answers := 1 }
    ownSplit := { code := noId, mainRows := 0, mainDeg := 1, maskRows := 0, maskCode := noId,
                  answers := 1 }
    omegaLeafClass := 1
    sharedSplitLeafClass := 2
    wLeafClass := 0
    ownSplitLeafClass := 3
    sharedMaskCode := 0
    ownMaskCode := 6
    masksAhead := true
    testU := [⟨0, 0, 7, 0⟩, ⟨1, 1, 5, 2⟩, ⟨2, 1, 4, 2⟩, ⟨3, 1, 4, 2⟩, ⟨4, 2, 0, 0⟩]
    testOmega := [⟨5, 0, 4, 0⟩, ⟨6, 3, 4, 3⟩, ⟨7, 4, 4, 3⟩, ⟨8, 5, 0, 0⟩]
    testOwn := [⟨5, 6, 5, 1⟩, ⟨6, 7, 4, 3⟩, ⟨9, 8, 3, 3⟩, ⟨10, 9, 3, 3⟩, ⟨11, 10, 0, 0⟩]
    testOwnOmega := []
    choice := ⟨true⟩ }

/-- The sizes of a key's test on the table. -/
def keyOnceRec : LinSized :=
  ⟨keyLin, keyOnceShape,
    ⟨{ code := noId, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 6, answers := 1 }, 0⟩,
    recordTable, ⟨keyU1, 97, keyUStages⟩, ⟨keyO1, 49, keyOStages⟩, ⟨keyW1, 49, keyWStages⟩, 710324⟩

/-- The codes that the test on the table hands on. -/
def keyCodes1 : Codes where
  base := #[⟨24, 4194304, 97⟩, ⟨21, 131072, 52⟩, ⟨17, 8192, 52⟩, ⟨13, 512, 52⟩, ⟨14, 512, 49⟩,
    ⟨22, 262144, 98⟩, ⟨18, 16384, 49⟩, ⟨14, 1024, 49⟩, ⟨15, 1024, 39⟩, ⟨15, 2048, 49⟩,
    ⟨13, 256, 41⟩, ⟨15, 256, 29⟩]
  mask := #[⟨13, 64, 146⟩, ⟨12, 256, 52⟩, ⟨14, 1024, 49⟩, ⟨14, 128, 49⟩, ⟨13, 64, 49⟩,
    ⟨15, 512, 39⟩, ⟨13, 256, 49⟩, ⟨15, 128, 49⟩, ⟨14, 64, 49⟩, ⟨13, 64, 41⟩, ⟨15, 256, 29⟩]

end OnBytes.Params

#print axioms OnBytes.Params.keyGroups_eq
