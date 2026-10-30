-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/EngineKeepsAt.lean: a property of computations that pure and bind keep
passes through the engine over m, if every call of the hash under a number other than 169 has it,
and the only call under 169 that a chain's reader makes: the digest of the chain's own parameter
bytes.

After OnBytes/ChecksWithHashAsArgument/M/Chain/EngineKeeps.lean, whose premise speaks of every call. There the proofs
use the premise at seven places: the calls under 160 and 172 with which a chain starts, the calls
under 162 of a round, a leaf (164 or 174), a vertex (166), and the parameters' digest (169). Here
the first six are met by the narrower premise, and the seventh is a premise by itself (`hpd`). So
these theorems also say which numbers the engine's calls have.

Limits: a frame over letters: nothing is said of any property or hash. "Other than 169" is said
modulo 65536, as a call's string holds its number (`Tie.oStr_number`, OnBytes/Tie/DigestPoint.lean).
For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineKeeps

set_option autoImplicit false

namespace OnBytes.TwoPort.M

namespace EngineKeepsAt

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)
open OnBytes.TwoPort.M.EngineKeeps (ok_walkM)

/-- A leaf's call number is not 169. -/
theorem leafNo_ne (stored : Bool) : Fmt.leafNo stored % 65536 ≠ 169 := by
  cases stored <;> decide

variable {m : Type → Type} [Monad m] (k : Keeps m)

variable (h : HashM m) (hh : ∀ n t i s b, n % 65536 ≠ 169 → k.ok (h n t i s b))
include hh

/-- The property passes through `startChainW`. -/
theorem ok_startChainW (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray) :
    k.ok (Fmt.startChainW h lab pd statement rnd) := by
  unfold Fmt.startChainW
  split
  · split
    · exact k.ok_bind _ _ (hh _ _ _ _ _ (by decide)) fun _ => k.ok_pure _
    · split
      · refine k.ok_bind _ _ (hh _ _ _ _ _ (by decide)) fun run => ?_
        split
        · exact k.ok_bind _ _ (hh _ _ _ _ _ (by decide)) fun _ => k.ok_pure _
        · exact k.ok_pure _
      · exact k.ok_pure _
  · exact k.ok_pure _

/-- The property passes through `fetchFrom`. -/
theorem ok_fetchFrom (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Fmt.Kind)
    (w nonce : Nat) :
    ∀ (c j : Nat) (acc : Array ByteArray), k.ok (Fmt.fetchFrom h lab rho i msg kind w nonce c j acc)
  | 0, _, _ => k.ok_pure _
  | c + 1, j, acc => by
    unfold Fmt.fetchFrom
    exact k.ok_bind _ _ (hh _ _ _ _ _ (by decide)) fun _ =>
      ok_fetchFrom lab rho i msg kind w nonce c _ _

/-- The property passes through `queryW`. -/
theorem ok_queryW (c : Fmt.Chain) (msg : ByteArray) (kind : Fmt.Kind) (work nonce K : Nat) :
    k.ok (Fmt.Chain.queryW h c msg kind work nonce K) := by
  unfold Fmt.Chain.queryW Fmt.fetchW
  split
  · refine k.ok_bind _ _ ?_ fun _ => k.ok_pure _
    exact k.ok_bind _ _ (ok_fetchFrom k h hh _ _ _ _ _ _ _ _ _ _) fun _ => k.ok_pure _
  · exact k.ok_pure _

/-- The property passes through `leavesLoopM`. -/
theorem ok_leavesLoopM (sh : Shape) (start : ByteArray) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)) (acc : Array (Nat × ByteArray)),
      k.ok (leavesLoopM h sh start xs cs acc)
  | x :: xs, (col, salt) :: cs, acc => by
    unfold leavesLoopM
    exact k.ok_bind _ _ (hh _ _ _ _ _ (leafNo_ne _)) fun _ => ok_leavesLoopM sh start xs cs _
  | [], _, acc => by
    unfold leavesLoopM
    exact k.ok_pure _
  | _ :: _, [], acc => by
    unfold leavesLoopM
    exact k.ok_pure _

/-- The property passes through `openingM`. -/
theorem ok_openingM (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) : k.ok (openingM h cfg f salt sh start xs b i) := by
  unfold openingM
  split
  · split
    · exact k.ok_pure _
    · refine k.ok_bind _ _ (ok_leavesLoopM k h hh _ _ _ _ _) fun ls => ?_
      exact k.ok_bind _ _
        (ok_walkM k _ _ (fun _ _ _ _ => hh _ _ _ _ _ (by decide)) _ _ _ _) fun _ =>
        k.ok_pure _
  · exact k.ok_pure _

/-- The property passes through `storedLoopM`. -/
theorem ok_storedLoopM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
      k.ok (storedLoopM K h cfg statement P poss b ts sn i acc)
  | [], _, _, _ => k.ok_pure _
  | t :: ts, sn, i, acc => by
    unfold storedLoopM
    refine k.ok_bind _ _ (ok_openingM k h hh _ _ _ _ _ _ _ _) fun r => ?_
    cases r with
    | none => exact k.ok_pure _
    | some o =>
      simp only []
      split
      · split
        · exact k.ok_pure _
        · exact ok_storedLoopM K cfg statement P poss b ts _ _ _
      · exact k.ok_pure _

/-- The property passes through `opensLoopM`. -/
theorem ok_opensLoopM {R : Type} (K : Keeper R) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
      k.ok (opensLoopM K h cfg P run roots poss b os sn i acc)
  | [], _, _, _ => k.ok_pure _
  | (sh, src) :: os, sn, i, acc => by
    unfold opensLoopM
    split
    · exact k.ok_pure _
    · refine k.ok_bind _ _ (ok_openingM k h hh _ _ _ _ _ _ _ _) fun r => ?_
      cases r with
      | none => exact k.ok_pure _
      | some o =>
        simp only []
        split
        · split
          · exact k.ok_pure _
          · exact ok_opensLoopM K cfg P run roots poss b os _ _ _
        · exact k.ok_pure _

/-- The property passes through `roundM`. -/
theorem ok_roundM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s : StK R) (r : Round) (ts : List Stored) :
    k.ok (roundM K h cfg statement P run b s r ts) := by
  unfold roundM
  split
  · exact k.ok_pure _
  · split
    · exact k.ok_pure _
    · split
      · exact k.ok_pure _
      · refine k.ok_bind _ _ (ok_queryW k h hh _ _ _ _ _ _) fun q => ?_
        cases q with
        | none => exact k.ok_pure _
        | some cv =>
          simp only []
          split
          · exact k.ok_pure _
          · refine k.ok_bind _ _ (ok_storedLoopM k h hh K _ _ _ _ _ _ _ _ _) fun q => ?_
            cases q with
            | none => exact k.ok_pure _
            | some x =>
              refine k.ok_bind _ _ (ok_opensLoopM k h hh K _ _ _ _ _ _ _ _ _ _) fun q => ?_
              cases q <;> exact k.ok_pure _

/-- The property passes through `foldRoundsM`. -/
theorem ok_foldRoundsM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK R),
      k.ok (foldRoundsM K h cfg statement P run b rs s)
  | [], _ => k.ok_pure _
  | r :: rs, s => by
    unfold foldRoundsM
    refine k.ok_bind _ _ (ok_roundM k h hh K _ _ _ _ _ _ _ _) fun q => ?_
    cases q with
    | none => exact k.ok_pure _
    | some s' => exact ok_foldRoundsM K cfg statement P run b rs s'

/-- The property passes through `restM`. -/
theorem ok_restM {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) (hpd : k.ok (h 169 0 1 Fmt.zero32 S.base.params)) :
    k.ok (restM K h S seen b x i0) := by
  unfold restM
  refine k.ok_bind _ _ hpd fun pd => ?_
  refine k.ok_bind _ _ (ok_startChainW k h hh _ _ _ _) fun q => ?_
  cases q with
  | none => exact k.ok_pure _
  | some hd =>
    refine k.ok_bind _ _ (ok_foldRoundsM k h hh K _ _ _ _ _ _ _) fun q => ?_
    cases q <;> exact k.ok_pure _

/-- The property passes through `readChainM`. -/
theorem ok_readChainM {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (i : Nat) (hpd : k.ok (h 169 0 1 Fmt.zero32 S.base.params)) :
    k.ok (readChainM K h S seen b i) := by
  unfold readChainM
  split
  · exact k.ok_pure _
  · split
    · split
      · exact k.ok_pure _
      · exact ok_restM k h hh K S seen b _ _ hpd
    · exact ok_restM k h hh K S seen b _ _ hpd
    · exact ok_restM k h hh K S seen b _ _ hpd

end EngineKeepsAt

end OnBytes.TwoPort.M
