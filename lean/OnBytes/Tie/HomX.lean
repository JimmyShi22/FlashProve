-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/HomX.lean: the library's strict reader of a chain that opens stored tables, read through
a morphism of monads.

The library writes that reader once, over a variable monad m, with the hash h : .. → m ByteArray as
its first argument (Fmt/Rules8X.lean: `Fmt.readStored`, `Fmt.roundX`, `Fmt.foldRoundsX`,
`Fmt.readChainX`, `Fmt.wholeChainX`, `Fmt.verifyXW`). For the reader without stored tables the
library proves that a morphism of monads passes through each function (Run/HomFmtProofs.lean). This
file proves the same for the six functions with stored tables, by the same steps.

Main theorems, for every morphism φ : Run.Hom m n and every hash h over m.
 `app_readStored`    φ.app (Fmt.readStored h ..) = Fmt.readStored (φ.on h) ..
 `app_roundX`, `app_foldRoundsX`, `app_readChainX`, `app_wholeChainX`, `app_verifyXW`   the like.

What is not claimed. Nothing on soundness, and no probability. Nothing on what the six functions
compute, and nothing on how often they call the hash. No monad, morphism or hash is fixed here. The
program does not call any function that is named in this file: "the program" is the Lean port that
is built from OnBytes/, not the C++ verifier, and its reader is another text.

-/
import Run.HomFmtProofs
import Fmt.Rules8X

set_option autoImplicit false

namespace OnBytes.Tie.HomX

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Run.Hom m n)
  (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- A morphism of monads passes through the reader of one round's openings of stored trees: φ
applied to the reader at the hash h is the reader at the hash `φ.on h`, which is h with φ applied to
each call. -/
theorem app_readStored (cfg statement : ByteArray) (P : Fmt.Plan) (poss : List Nat)
    (b : ByteArray) :
    ∀ (ts : List Fmt.Stored) (sn : Fmt.Seen) (i : Nat),
      φ.app (Fmt.readStored h cfg statement P poss b ts sn i) =
        Fmt.readStored (φ.on h) cfg statement P poss b ts sn i
  | [], _, _ => φ.app_pure _
  | t :: ts, sn, i => by
    unfold Fmt.readStored
    simp only [φ.app_bind, Run.Hom.readOpeningW]
    refine congrArg _ (funext fun r => ?_)
    cases r with
    | none => exact φ.app_pure _
    | some o =>
      simp only []
      split
      · split
        · exact φ.app_pure _
        · simp only [φ.app_bind, app_readStored cfg statement P poss b ts]
          refine congrArg _ (funext fun r => ?_)
          cases r <;> exact φ.app_pure _
      · exact φ.app_pure _

/-- A morphism of monads passes through the reader of one round of a chain that opens stored
trees. -/
theorem app_roundX (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored) :
    φ.app (Fmt.roundX h cfg statement P run b s r ts) =
      Fmt.roundX (φ.on h) cfg statement P run b s r ts := by
  unfold Fmt.roundX
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · simp only [φ.app_bind, Run.Hom.queryW]
        refine congrArg _ (funext fun q => ?_)
        cases q with
        | none => exact φ.app_pure _
        | some cv =>
          simp only []
          split
          · exact φ.app_pure _
          · simp only [φ.app_bind, app_readStored]
            refine congrArg _ (funext fun q => ?_)
            cases q with
            | none => exact φ.app_pure _
            | some x =>
              simp only [φ.app_bind, Run.Hom.readOpens]
              refine congrArg _ (funext fun q => ?_)
              cases q <;> exact φ.app_pure _

/-- A morphism of monads passes through the fold over the rounds, each with its stored trees. -/
theorem app_foldRoundsX (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s : Fmt.St),
      φ.app (Fmt.foldRoundsX h cfg statement P run b rs s) =
        Fmt.foldRoundsX (φ.on h) cfg statement P run b rs s
  | [], _ => φ.app_pure _
  | r :: rs, s => by
    simp only [Fmt.foldRoundsX, φ.app_bind, app_roundX]
    refine congrArg _ (funext fun q => ?_)
    cases q with
    | none => exact φ.app_pure _
    | some s' => exact app_foldRoundsX cfg statement P run b rs s'

/-- **A morphism of monads passes through the reader of a chain that opens stored tables**, from
any place i of any byte string b, for any description S and any record of met vertices. -/
theorem app_readChainX (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat) :
    φ.app (Fmt.readChainX h S seen b i) = Fmt.readChainX (φ.on h) S seen b i := by
  unfold Fmt.readChainX
  split
  · exact φ.app_pure _
  · simp only []
    split
    · exact φ.app_pure _
    · simp only [φ.app_bind, Run.Hom.startChainW]
      refine congrArg _ (funext fun pd => ?_)
      refine congrArg _ (funext fun q => ?_)
      cases q with
      | none => exact φ.app_pure _
      | some hd =>
        simp only [φ.app_bind, app_foldRoundsX]
        refine congrArg _ (funext fun q => ?_)
        cases q <;> exact φ.app_pure _

/-- A morphism of monads passes through the reader that also asks that nothing stands behind the
chain. -/
theorem app_wholeChainX (S : Fmt.SpecX) (b : ByteArray) :
    φ.app (Fmt.wholeChainX h S b) = Fmt.wholeChainX (φ.on h) S b := by
  simp only [Fmt.wholeChainX, φ.app_bind, app_readChainX]
  refine congrArg _ (funext fun q => ?_)
  cases q <;> exact φ.app_pure _

/-- A morphism of monads passes through the reader followed by a decision on the view. -/
theorem app_verifyXW {Y : Type} (S : Fmt.SpecX) (dec : Y → Fmt.View → Bool) (y : Y)
    (file : ByteArray) :
    φ.app (Fmt.verifyXW h S dec y file) = Fmt.verifyXW (φ.on h) S dec y file := by
  simp only [Fmt.verifyXW, φ.app_bind, app_wholeChainX]
  refine congrArg _ (funext fun q => ?_)
  cases q <;> exact φ.app_pure _

end OnBytes.Tie.HomX
