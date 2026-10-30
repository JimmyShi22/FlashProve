-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Chain/EngineCost.lean: how many questions the engine over m asks at most: the
library's count with a condition on what comes out (Run.CostP), at the numbers of
OnBytes/Tie/CostX.lean.
MADE BY A PROGRAM from a file of the same name that this project's authors wrote over an earlier
arrangement of these definitions, which is not in this tree: the program turned names, imports,
opens and the spelling of calls alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.Chain.Draws
import OnBytes.Chain.Lists
import OnBytes.Tie.CostX

set_option autoImplicit false

namespace OnBytes.TwoPort.M.EngineCost

open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)
open OnBytes.Tie.CostX

variable {m : Type → Type} [Monad m] (c : Run.CostP m) (k : Nat)

section walk
variable {α σ : Type} (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ))
  (hc : ∀ a b x y, c.le (comb a b x y) k fun _ => True)
include hc

theorem le_loneM (d i : Nat) (x : α) (s : σ) :
    c.le (loneM comb give d i x s) k fun _ => True := by
  unfold loneM
  split
  · exact c.pureLe _ _ _ trivial
  · dsimp only
    split <;> exact c.bindPure _ _ _ _ _ (hc _ _ _ _) fun _ _ => trivial

theorem le_levelLoopM (d : Nat) :
    ∀ (l : List (Nat × α)) (s : σ) (acc : Array (Nat × α)),
      c.le (levelLoopM comb give d l s acc) (l.length * k)
        fun r => ∀ p, r = some p → p.1.length ≤ acc.size + l.length
  | [], s, acc => c.pureLe _ _ _ fun p e => by cases e; simp
  | [(i, x)], s, acc => by
    unfold levelLoopM
    refine c.le_mono _ (k + 0) _ _ _
      (c.le_bind _ _ k 0 _ _ (le_loneM c k comb give hc d i x s) fun r _ => ?_) (by simp)
      fun _ h => h
    cases r with
    | none => exact c.le_pure _ _ fun p e => by cases e
    | some q => exact c.le_pure _ _ fun p e => by cases e; simp
  | (i, x) :: (i', x') :: rest, s, acc => by
    unfold levelLoopM
    split
    · refine c.le_mono _ (k + rest.length * k) _
        (fun r => ∀ p, r = some p → p.1.length ≤ acc.size + 1 + rest.length) _
        (c.le_bind _ _ k _ _ _ (hc _ _ _ _) fun v _ =>
          c.le_mono _ _ _ _ _ (le_levelLoopM d rest s (acc.push (i / 2, v))) (Nat.le_refl _)
            fun r hr p e => by
              have := hr p e
              simp only [Array.size_push] at this
              exact this)
        (by simp only [List.length_cons, Nat.succ_mul]; omega) fun r hr p e => ?_
      have := hr p e
      simp only [List.length_cons] at this ⊢
      omega
    · refine c.le_mono _ (k + ((i', x') :: rest).length * k) _
        (fun r => ∀ p, r = some p → p.1.length ≤ acc.size + 1 + ((i', x') :: rest).length) _
        (c.le_bind _ _ k _ _ _ (le_loneM c k comb give hc d i x s) fun r _ => ?_)
        (by simp only [List.length_cons, Nat.succ_mul]; omega) fun r hr p e => ?_
      · cases r with
        | none => exact c.pureLe _ _ _ fun p e => by cases e
        | some q =>
          refine c.le_mono _ _ _ _ _ (le_levelLoopM d ((i', x') :: rest) q.2 (acc.push q.1))
            (Nat.le_refl _) fun r hr p e => ?_
          have := hr p e
          simp only [Array.size_push] at this
          exact this
      · have := hr p e
        simp only [List.length_cons] at this ⊢
        omega

theorem le_walkM :
    ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
      c.le (walkM comb give d now s met) (d * (now.length * k)) fun _ => True
  | 0, now, s, met => by
    unfold walkM
    split <;> first | exact c.pureLe _ _ _ trivial | simp_all
  | d + 1, now, s, met => by
    unfold walkM
    refine c.le_mono _ (now.length * k + d * (now.length * k)) _ _ _
      (c.le_bind _ _ _ _ _ _ (le_levelLoopM c k comb give hc (d + 1) now s #[]) fun r hr => ?_)
      (by rw [Nat.succ_mul]; omega) fun _ h => h
    cases r with
    | none => exact c.pureLe _ _ _ trivial
    | some p =>
      have hp : p.1.length ≤ now.length := by
        have := hr p rfl
        simpa using this
      exact c.le_mono _ _ _ _ _ (le_walkM d p.1 p.2 _)
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hp)) fun _ h => h

end walk

variable (h : HashM m)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

theorem le_leavesLoopM (sh : Shape) (start : ByteArray) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)) (acc : Array (Nat × ByteArray)),
      c.le (leavesLoopM h sh start xs cs acc) (xs.length * k)
        fun r => r.length ≤ acc.size + xs.length
  | x :: xs, (col, salt) :: cs, acc => by
    unfold leavesLoopM
    refine c.le_mono _ (k + xs.length * k) _ (fun r => r.length ≤ acc.size + 1 + xs.length) _
      (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun v _ =>
        c.le_mono _ _ _ _ _ (le_leavesLoopM sh start xs cs (acc.push (x, v))) (Nat.le_refl _)
          fun r hr => by
            simp only [Array.size_push] at hr
            exact hr)
      (by simp only [List.length_cons, Nat.succ_mul]; omega) fun r hr => ?_
    simp only [List.length_cons] at hr ⊢
    omega
  | [], _, acc => by
    unfold leavesLoopM
    exact c.pureLe _ _ _ (by simp)
  | _ :: _, [], acc => by
    unfold leavesLoopM
    exact c.pureLe _ _ _ (by simp)

theorem le_openingM (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) :
    c.le (openingM h cfg f salt sh start xs b i) ((sh.a + 1) * (xs.length * k)) fun _ => True := by
  unfold openingM
  split
  · split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _ (xs.length * k + (sh.a * (xs.length * k) + 0)) _ _ _
        (c.le_bind _ _ _ _ _ _ (le_leavesLoopM c k h hk sh start xs _ #[]) fun now hn =>
          c.le_bind _ _ _ 0 _ _
            (c.le_mono _ _ _ _ _
              (le_walkM c k (fun _ _ l r => Fmt.vertexW h cfg l r) Fmt.takeGiven
                (fun _ _ _ _ => hk _ _ _ _ _) sh.a now _ _)
              (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by simpa using hn))) fun _ h => h)
            fun _ _ => c.le_pure _ _ trivial)
        (by rw [Nat.succ_mul]; omega) fun _ h => h
  · exact c.pureLe _ _ _ trivial

theorem le_storedLoopM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (poss : List Nat) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
      c.le (storedLoopM K h cfg statement P poss b ts sn i acc) (storedN ts * k) fun _ => True
  | [], _, _, _ => c.pureLe _ _ _ trivial
  | t :: ts, sn, i, acc => by
    unfold storedLoopM
    have hl : (listOfT ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))).length ≤ t.count := by
      rw [listOfT_eq]
      refine Nat.le_trans (Run.CostP.listOf_len _) ?_
      unfold Fmt.partOf
      rw [List.length_map, List.length_take]
      exact Nat.min_le_left _ _
    refine c.le_mono _ ((t.sh.a + 1) * (t.count * k) + storedN ts * k) _ _ _
      (c.le_bind _ _ _ _ _ _
        (c.le_mono _ _ _ _ _ (le_openingM c k h hk cfg P.field t.salt t.sh _ _ b i)
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hl)) fun _ h => h) fun r _ => ?_)
      (by simp only [storedN, Nat.add_mul, Nat.mul_assoc]; exact Nat.le_refl _) fun _ h => h
    cases r with
    | none => exact c.pureLe _ _ _ trivial
    | some o =>
      simp only []
      split
      · split
        · exact c.pureLe _ _ _ trivial
        · exact le_storedLoopM K cfg statement P poss b ts _ _ _
      · exact c.pureLe _ _ _ trivial

theorem le_opensLoopM {R : Type} (K : Keeper R) (cfg : ByteArray) (P : Plan)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : R) (i : Nat) (acc : Array (Shape × List Nat × OpenOut)),
      c.le (opensLoopM K h cfg P run roots poss b os sn i acc) (Run.opensN poss.length os * k)
        fun _ => True
  | [], _, _, _ => c.pureLe _ _ _ trivial
  | (sh, src) :: os, sn, i, acc => by
    unfold opensLoopM
    have hl : (listOfT (poss.map (· % 2 ^ sh.a))).length ≤ poss.length := by
      rw [listOfT_eq]
      refine Nat.le_trans (Run.CostP.listOf_len _) ?_
      rw [List.length_map]
      exact Nat.le_refl _
    split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _ ((sh.a + 1) * (poss.length * k) + Run.opensN poss.length os * k) _ _ _
        (c.le_bind _ _ _ _ _ _
          (c.le_mono _ _ _ _ _ (le_openingM c k h hk cfg P.field P.salt sh _ _ b i)
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hl)) fun _ h => h) fun r _ => ?_)
        (by simp only [Run.opensN, Nat.add_mul, Nat.mul_assoc]; exact Nat.le_refl _) fun _ h => h
      cases r with
      | none => exact c.pureLe _ _ _ trivial
      | some o =>
        simp only []
        split
        · split
          · exact c.pureLe _ _ _ trivial
          · exact le_opensLoopM K cfg P run roots poss b os _ _ _
        · exact c.pureLe _ _ _ trivial

theorem le_roundM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s : StK R) (r : Round) (ts : List Stored) :
    c.le (roundM K h cfg statement P run b s r ts) (roundNX r ts * k) fun _ => True := by
  unfold roundM
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · exact c.pureLe _ _ _ trivial
    · split
      · exact c.pureLe _ _ _ trivial
      · refine c.le_mono _
          ((Fmt.firstBlock r.entry.work + (Fmt.wordsAtMost r.entry r.kind + 3) / 4 + 1) / 2 * k +
            (storedN ts * k + (Run.opensN r.entry.poss r.opens * k + 0)))
          _ _ _ (c.le_bind _ _ _ _ _ _ (c.queryW h k hk _ _ _ _ _ _) fun q _ => ?_)
          (by simp only [roundNX, Run.roundN, Nat.add_mul]; omega) fun _ h => h
        cases q with
        | none => exact c.pureLe _ _ _ trivial
        | some cv =>
          simp only []
          split
          · exact c.pureLe _ _ _ trivial
          · refine c.le_bind _ _ _ _ (fun _ => True) _
              (le_storedLoopM c k h hk K cfg statement P _ b ts _ _ _) fun q _ => ?_
            cases q with
            | none => exact c.pureLe _ _ _ trivial
            | some x =>
              refine c.le_bind _ _ _ 0 (fun _ => True) _ ?_ fun q _ => ?_
              · have key : ∀ (roots : Array ByteArray) (sn : R) (i : Nat)
                    (acc : Array (Shape × List Nat × OpenOut)),
                    c.le (opensLoopM K h cfg P run roots
                        (drawRoundT P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b
                            r.opens sn i acc)
                      (Run.opensN r.entry.poss r.opens * k) fun _ => True :=
                          fun roots sn i acc => by
                  have := le_opensLoopM c k h hk K cfg P run roots
                    (drawRoundT P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b r.opens sn i acc
                  rw [drawRoundT_eq, Run.CostP.drawRound_poss] at this
                  rw [drawRoundT_eq]
                  exact this
                exact key _ _ _ _
              · cases q <;> exact c.le_pure _ _ trivial

theorem le_foldRoundsM {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK R),
      c.le (foldRoundsM K h cfg statement P run b rs s) (roundsNX rs * k) fun _ => True
  | [], _ => c.pureLe _ _ _ trivial
  | r :: rs, s => by
    unfold foldRoundsM
    refine c.le_mono _ (roundNX r.1 r.2 * k + roundsNX rs * k) _ _ _
      (c.le_bind _ _ _ _ _ _ (le_roundM c k h hk K cfg statement P run b s r.1 r.2) fun q _ => ?_)
      (by simp only [roundsNX, Nat.add_mul]; exact Nat.le_refl _) fun _ h => h
    cases q with
    | none => exact c.pureLe _ _ _ trivial
    | some s' => exact le_foldRoundsM K cfg statement P run b rs s'

theorem le_restM {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) :
    c.le (restM K h S seen b x i0) (fileNX S * k) fun _ => True := by
  unfold restM
  refine c.le_mono _ (k + (2 * k + (roundsNX (S.base.rounds.zip S.stored) * k + 0))) _ _ _
    (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun pd _ =>
      c.le_bind _ _ _ _ (fun _ => True) _ (c.startChainW h k hk _ _ _ _) fun q _ => ?_)
    (by simp only [fileNX, Nat.add_mul]; omega) fun _ h => h
  cases q with
  | none => exact c.pureLe _ _ _ trivial
  | some hd =>
    refine c.le_bind _ _ _ 0 (fun _ => True) _ ?_ fun q _ => ?_
    · rw [zipT_eq]
      exact le_foldRoundsM c k h hk K _ _ _ _ _ _ _
    · cases q <;> exact c.le_pure _ _ trivial

theorem le_readChainM {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (i : Nat) : c.le (readChainM K h S seen b i) (fileNX S * k) fun _ => True := by
  unfold readChainM
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · split
      · exact c.pureLe _ _ _ trivial
      · exact le_restM c k h hk K S seen b _ _
    · exact le_restM c k h hk K S seen b _ _
    · exact le_restM c k h hk K S seen b _ _

end OnBytes.TwoPort.M.EngineCost
