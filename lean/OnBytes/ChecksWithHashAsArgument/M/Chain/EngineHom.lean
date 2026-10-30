-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/EngineHom.lean: a morphism of monads passes through the engine over m.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import Run.HomFmtProofs

set_option autoImplicit false

namespace OnBytes.TwoPort.M.EngineHom

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Run.Hom m n)

section walk
variable {α σ : Type} (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ))

theorem app_loneM (d i : Nat) (x : α) (s : σ) :
    φ.app (loneM comb give d i x s) = loneM (fun a b c e => φ.app (comb a b c e)) give d i x s := by
  unfold loneM
  split
  · exact φ.app_pure _
  · split <;> simp only [φ.app_bind, φ.app_pure]

theorem app_levelLoopM (d : Nat) :
    ∀ (l : List (Nat × α)) (s : σ) (acc : Array (Nat × α)),
      φ.app (levelLoopM comb give d l s acc) =
        levelLoopM (fun a b c e => φ.app (comb a b c e)) give d l s acc
  | [], s, acc => φ.app_pure _
  | [(i, x)], s, acc => by
    simp only [levelLoopM, φ.app_bind, app_loneM]
    refine congrArg _ (funext fun r => ?_)
    cases r <;> exact φ.app_pure _
  | (i, x) :: (i', x') :: rest, s, acc => by
    unfold levelLoopM
    split
    · simp only [φ.app_bind, app_levelLoopM d rest]
    · simp only [φ.app_bind, app_loneM]
      refine congrArg _ (funext fun r => ?_)
      cases r with
      | none => exact φ.app_pure _
      | some p => exact app_levelLoopM d ((i', x') :: rest) _ _

theorem app_walkM :
    ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
      φ.app (walkM comb give d now s met) =
        walkM (fun a b c e => φ.app (comb a b c e)) give d now s met
  | 0, now, s, met => by
    unfold walkM
    split <;> first | exact φ.app_pure _ | simp_all
  | d + 1, now, s, met => by
    simp only [walkM, φ.app_bind, app_levelLoopM]
    refine congrArg _ (funext fun r => ?_)
    cases r with
    | none => exact φ.app_pure _
    | some p => exact app_walkM d _ _ _

end walk

variable (h : HashM m)

theorem app_leavesLoopM (sh : Shape) (start : ByteArray) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)) (acc : Array (Nat × ByteArray)),
      φ.app (leavesLoopM h sh start xs cs acc) = leavesLoopM (φ.on h) sh start xs cs acc
  | x :: xs, (col, salt) :: cs, acc => by
    simp only [leavesLoopM, φ.app_bind, app_leavesLoopM sh start xs cs]
    rfl
  | [], _, acc => by simp only [leavesLoopM, φ.app_pure]
  | _ :: _, [], acc => by simp only [leavesLoopM, φ.app_pure]

theorem app_openingM (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) :
    φ.app (openingM h cfg f salt sh start xs b i) =
      openingM (φ.on h) cfg f salt sh start xs b i := by
  unfold openingM
  split
  · split
    · exact φ.app_pure _
    · simp only [φ.app_bind, φ.app_pure, app_leavesLoopM, app_walkM]
      rfl
  · exact φ.app_pure _

theorem app_storedLoopM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
      φ.app (storedLoopM K h cfg statement P poss b ts sn i acc) =
        storedLoopM K (φ.on h) cfg statement P poss b ts sn i acc
  | [], _, _, _ => φ.app_pure _
  | t :: ts, sn, i, acc => by
    unfold storedLoopM
    simp only [φ.app_bind, app_openingM]
    refine congrArg _ (funext fun r => ?_)
    cases r with
    | none => exact φ.app_pure _
    | some o =>
      simp only []
      split
      · split
        · exact φ.app_pure _
        · exact app_storedLoopM K cfg statement P poss b ts _ _ _
      · exact φ.app_pure _

theorem app_opensLoopM {R : Type} (K : Keeper R) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
      φ.app (opensLoopM K h cfg P run roots poss b os sn i acc) =
        opensLoopM K (φ.on h) cfg P run roots poss b os sn i acc
  | [], _, _, _ => φ.app_pure _
  | (sh, src) :: os, sn, i, acc => by
    unfold opensLoopM
    split
    · exact φ.app_pure _
    · simp only [φ.app_bind, app_openingM]
      refine congrArg _ (funext fun r => ?_)
      cases r with
      | none => exact φ.app_pure _
      | some o =>
        simp only []
        split
        · split
          · exact φ.app_pure _
          · exact app_opensLoopM K cfg P run roots poss b os _ _ _
        · exact φ.app_pure _

theorem app_roundM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s : StK R) (r : Round) (ts : List Stored) :
    φ.app (roundM K h cfg statement P run b s r ts) =
      roundM K (φ.on h) cfg statement P run b s r ts := by
  unfold roundM
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
          · simp only [φ.app_bind, app_storedLoopM]
            refine congrArg _ (funext fun q => ?_)
            cases q with
            | none => exact φ.app_pure _
            | some x =>
              simp only [φ.app_bind, app_opensLoopM]
              refine congrArg _ (funext fun q => ?_)
              cases q <;> exact φ.app_pure _

theorem app_foldRoundsM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK R),
      φ.app (foldRoundsM K h cfg statement P run b rs s) =
        foldRoundsM K (φ.on h) cfg statement P run b rs s
  | [], _ => φ.app_pure _
  | r :: rs, s => by
    simp only [foldRoundsM, φ.app_bind, app_roundM]
    refine congrArg _ (funext fun q => ?_)
    cases q with
    | none => exact φ.app_pure _
    | some s' => exact app_foldRoundsM K cfg statement P run b rs s'

theorem app_restM {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) :
    φ.app (restM K h S seen b x i0) = restM K (φ.on h) S seen b x i0 := by
  unfold restM
  simp only [φ.app_bind, Run.Hom.startChainW]
  refine congrArg _ (funext fun pd => ?_)
  refine congrArg _ (funext fun q => ?_)
  cases q with
  | none => exact φ.app_pure _
  | some hd =>
    simp only [φ.app_bind, app_foldRoundsM]
    refine congrArg _ (funext fun q => ?_)
    cases q <;> exact φ.app_pure _

theorem app_readChainM {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (i : Nat) : φ.app (readChainM K h S seen b i) = readChainM K (φ.on h) S seen b i := by
  unfold readChainM
  split
  · exact φ.app_pure _
  · split
    · split
      · exact φ.app_pure _
      · exact app_restM φ h K S seen b _ _
    · exact app_restM φ h K S seen b _ _
    · exact app_restM φ h K S seen b _ _

end OnBytes.TwoPort.M.EngineHom
