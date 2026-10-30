-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/EngineKeeps.lean: a property of computations that pure and bind keep passes
through the engine over m, if every call of the hash has it. NoCoin is such a property.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM

set_option autoImplicit false

namespace OnBytes.TwoPort.M

/-- A property of computations in m that `pure` has and `bind` keeps. -/
structure Keeps (m : Type → Type) [Monad m] where
  ok : {α : Type} → m α → Prop
  ok_pure : ∀ {α : Type} (a : α), ok (pure a : m α)
  ok_bind : ∀ {α β : Type} (x : m α) (g : α → m β), ok x → (∀ a, ok (g a)) → ok (x >>= g)

namespace EngineKeeps

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)

variable {m : Type → Type} [Monad m] (k : Keeps m)

section walk
variable {α σ : Type} (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ))
  (hc : ∀ a b c e, k.ok (comb a b c e))
include hc

theorem ok_loneM (d i : Nat) (x : α) (s : σ) : k.ok (loneM comb give d i x s) := by
  unfold loneM
  split
  · exact k.ok_pure _
  · dsimp only
    split <;> exact k.ok_bind _ _ (hc _ _ _ _) fun _ => k.ok_pure _

theorem ok_levelLoopM (d : Nat) :
    ∀ (l : List (Nat × α)) (s : σ) (acc : Array (Nat × α)), k.ok (levelLoopM comb give d l s acc)
  | [], s, acc => k.ok_pure _
  | [(i, x)], s, acc => by
    unfold levelLoopM
    refine k.ok_bind _ _ (ok_loneM k comb give hc d i x s) fun r => ?_
    cases r <;> exact k.ok_pure _
  | (i, x) :: (i', x') :: rest, s, acc => by
    unfold levelLoopM
    split
    · exact k.ok_bind _ _ (hc _ _ _ _) fun _ => ok_levelLoopM d rest _ _
    · refine k.ok_bind _ _ (ok_loneM k comb give hc d i x s) fun r => ?_
      cases r with
      | none => exact k.ok_pure _
      | some p => exact ok_levelLoopM d ((i', x') :: rest) _ _

theorem ok_walkM :
    ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
      k.ok (walkM comb give d now s met)
  | 0, now, s, met => by
    unfold walkM
    split <;> first | exact k.ok_pure _ | simp_all
  | d + 1, now, s, met => by
    unfold walkM
    refine k.ok_bind _ _ (ok_levelLoopM k comb give hc (d + 1) now s #[]) fun r => ?_
    cases r with
    | none => exact k.ok_pure _
    | some p => exact ok_walkM d _ _ _

end walk

variable (h : HashM m) (hh : ∀ n t i s b, k.ok (h n t i s b))
include hh

theorem ok_startChainW (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray) :
    k.ok (Fmt.startChainW h lab pd statement rnd) := by
  unfold Fmt.startChainW
  split
  · split
    · exact k.ok_bind _ _ (hh _ _ _ _ _) fun _ => k.ok_pure _
    · split
      · refine k.ok_bind _ _ (hh _ _ _ _ _) fun run => ?_
        split
        · exact k.ok_bind _ _ (hh _ _ _ _ _) fun _ => k.ok_pure _
        · exact k.ok_pure _
      · exact k.ok_pure _
  · exact k.ok_pure _

theorem ok_fetchFrom (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Fmt.Kind)
    (w nonce : Nat) :
    ∀ (c j : Nat) (acc : Array ByteArray), k.ok (Fmt.fetchFrom h lab rho i msg kind w nonce c j acc)
  | 0, _, _ => k.ok_pure _
  | c + 1, j, acc => by
    unfold Fmt.fetchFrom
    exact k.ok_bind _ _ (hh _ _ _ _ _) fun _ => ok_fetchFrom lab rho i msg kind w nonce c _ _

theorem ok_queryW (c : Fmt.Chain) (msg : ByteArray) (kind : Fmt.Kind) (work nonce K : Nat) :
    k.ok (Fmt.Chain.queryW h c msg kind work nonce K) := by
  unfold Fmt.Chain.queryW Fmt.fetchW
  split
  · refine k.ok_bind _ _ ?_ fun _ => k.ok_pure _
    exact k.ok_bind _ _ (ok_fetchFrom k h hh _ _ _ _ _ _ _ _ _ _) fun _ => k.ok_pure _
  · exact k.ok_pure _

theorem ok_leavesLoopM (sh : Shape) (start : ByteArray) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)) (acc : Array (Nat × ByteArray)),
      k.ok (leavesLoopM h sh start xs cs acc)
  | x :: xs, (col, salt) :: cs, acc => by
    unfold leavesLoopM
    exact k.ok_bind _ _ (hh _ _ _ _ _) fun _ => ok_leavesLoopM sh start xs cs _
  | [], _, acc => by
    unfold leavesLoopM
    exact k.ok_pure _
  | _ :: _, [], acc => by
    unfold leavesLoopM
    exact k.ok_pure _

theorem ok_openingM (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) : k.ok (openingM h cfg f salt sh start xs b i) := by
  unfold openingM
  split
  · split
    · exact k.ok_pure _
    · refine k.ok_bind _ _ (ok_leavesLoopM k h hh _ _ _ _ _) fun ls => ?_
      exact k.ok_bind _ _ (ok_walkM k _ _ (fun _ _ _ _ => hh _ _ _ _ _) _ _ _ _) fun _ =>
        k.ok_pure _
  · exact k.ok_pure _

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

theorem ok_restM {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) : k.ok (restM K h S seen b x i0) := by
  unfold restM
  refine k.ok_bind _ _ (hh _ _ _ _ _) fun pd => ?_
  refine k.ok_bind _ _ (ok_startChainW k h hh _ _ _ _) fun q => ?_
  cases q with
  | none => exact k.ok_pure _
  | some hd =>
    refine k.ok_bind _ _ (ok_foldRoundsM k h hh K _ _ _ _ _ _ _) fun q => ?_
    cases q <;> exact k.ok_pure _

theorem ok_readChainM {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (i : Nat) : k.ok (readChainM K h S seen b i) := by
  unfold readChainM
  split
  · exact k.ok_pure _
  · split
    · split
      · exact k.ok_pure _
      · exact ok_restM k h hh K S seen b _ _
    · exact ok_restM k h hh K S seen b _ _
    · exact ok_restM k h hh K S seen b _ _

end EngineKeeps

end OnBytes.TwoPort.M
