-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/CountsSent.lean: the program's reader of a chain over a monad, at any hash, asks at
most its description's number of calls, and a chain that it returns has sent as many roots as the
description's rounds say.

OnBytes/ChecksWithHashAsArgument/M/Chain/EngineCost.lean bounds the calls of that reader (le_roundM, le_foldRoundsM,
le_restM, le_readChainM) in the library's count with a condition (Run.CostP: "x asks at most t, and
whatever it puts out has P"), at the condition that always holds. Here the same four walks carry a
condition: how many roots stand in the messages that were read. A round's message is read by a plain
reader that goes by the round's items, so it holds one root for each item "root", whatever the hash
answers.

Main definitions: sent (the roots in the messages read so far), itemsRoots (the items "root" of a
list of rounds).
Main theorems: readItems_roots, whole_roots (the plain reader); le_roundM_sent, le_foldRoundsM_sent,
le_restM_sent, le_readChainM_sent; le_readChain_sent (at the keeper that the program's reader has).

Limits. What a bound says depends on the count at which it is used. Nothing on which roots were
sent.


-/
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineCost
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK.Counts

open OnBytes.Tie.CostX OnBytes.TwoPort OnBytes.TwoPort.M OnBytes.TwoPort.M.EngineCost
open Fmt (Plan Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src Fld)

/-! ## The plain reader of a message -/

/-- What was read of one item is a root exactly if the item is one. -/
theorem readItem_roots (f : Fmt.Fld) (t : Fmt.Item) (b : ByteArray) (i : Nat) (x : Fmt.ItemValue)
    (j : Nat) (h : Fmt.readItem f t b i = some (x, j)) (l : List Fmt.ItemValue) :
    (Fmt.rootsOf (x :: l)).length = Fmt.countItem .root [t] + (Fmt.rootsOf l).length := by
  cases t <;> unfold Fmt.readItem at h <;> obtain ⟨y, -, e⟩ := Option.map_eq_some_iff.1 h <;>
    cases e
  · show (Fmt.rootsOf l).length = 0 + _
    rw [Nat.zero_add]
  · show (Fmt.rootsOf l).length = 0 + _
    rw [Nat.zero_add]
  · show (Fmt.rootsOf l).length = 0 + _
    rw [Nat.zero_add]
  · show (y.1 :: Fmt.rootsOf l).length = 1 + _
    rw [List.length_cons, Nat.add_comm]
  · show (Fmt.rootsOf l).length = 0 + _
    rw [Nat.zero_add]

theorem countItem_cons (t : Fmt.Item) (ts : List Fmt.Item) :
    Fmt.countItem .root (t :: ts) = Fmt.countItem .root [t] + Fmt.countItem .root ts := by
  unfold Fmt.countItem
  rw [← List.length_append, ← List.filter_append]
  rfl

/-- A message that was read by its items holds one root for each item "root". -/
theorem readItems_roots (f : Fmt.Fld) :
    ∀ (ts : List Fmt.Item) (b : ByteArray) (i : Nat) (vals : List Fmt.ItemValue) (j : Nat),
      Fmt.readItems f ts b i = some (vals, j) →
      (Fmt.rootsOf vals).length = Fmt.countItem .root ts
  | [], _, _, _, _, h => by
    cases h
    rfl
  | t :: ts, b, i, vals, j, h => by
    unfold Fmt.readItems at h
    split at h
    · rename_i x j1 h1
      split at h
      · rename_i l k1 h2
        cases h
        rw [readItem_roots f t b i x j1 h1 l, readItems_roots f ts b j1 l _ h2]
        exact (countItem_cons t ts).symm
      · cases h
    · cases h

theorem whole_roots (f : Fmt.Fld) (ts : List Fmt.Item) (msg : ByteArray) (vals : List Fmt.ItemValue)
    (h : Fmt.whole (Fmt.readItems f ts) msg = some vals) :
    (Fmt.rootsOf vals).length = Fmt.countItem .root ts := by
  unfold Fmt.whole at h
  split at h
  · rename_i x j hx
    split at h
    · cases h
      exact readItems_roots f ts msg 0 _ j hx
    · cases h
  · cases h

/-! ## The roots in what was read -/

/-- The number of roots in the messages of the rounds that were read. -/
def sent (out : Array Fmt.RoundOut) : Nat :=
  (out.toList.flatMap fun x => Fmt.rootsOf x.vals).length

theorem sent_push (out : Array Fmt.RoundOut) (ro : Fmt.RoundOut) :
    sent (out.push ro) = sent out + (Fmt.rootsOf ro.vals).length := by
  unfold sent
  rw [Array.toList_push, List.flatMap_append, List.length_append]
  simp

/-- The number of items "root" in a list of rounds. -/
def itemsRoots : List (Fmt.Round × List Fmt.Stored) → Nat
  | [] => 0
  | r :: rs => Fmt.countItem .root r.1.items + itemsRoots rs

/-! ## The four walks, with the condition -/

variable {m : Type → Type} [Monad m] (c : Run.CostP m) (k : Nat) (h : HashM m)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

/-- One round: at most roundNX r ts * k; the state that it returns has the round's roots more. -/
theorem le_roundM_sent {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s : StK R) (r : Round) (ts : List Stored) :
    c.le (roundM K h cfg statement P run b s r ts) (roundNX r ts * k) fun q =>
      ∀ s', q = some s' → sent s'.out = sent s.out + Fmt.countItem .root r.items := by
  unfold roundM
  split
  · exact c.pureLe _ _ _ fun _ e => by cases e
  · split
    · exact c.pureLe _ _ _ fun _ e => by cases e
    · rename_i vals hv
      rw [readItemsT_eq] at hv
      split
      · exact c.pureLe _ _ _ fun _ e => by cases e
      · refine c.le_mono _
          ((Fmt.firstBlock r.entry.work + (Fmt.wordsAtMost r.entry r.kind + 3) / 4 + 1) / 2 * k +
            (storedN ts * k + (Run.opensN r.entry.poss r.opens * k + 0)))
          _ _ _ (c.le_bind _ _ _ _ _ _ (c.queryW h k hk _ _ _ _ _ _) fun q _ => ?_)
          (by simp only [roundNX, Run.roundN, Nat.add_mul]; omega) fun _ h => h
        cases q with
        | none => exact c.pureLe _ _ _ fun _ e => by cases e
        | some cv =>
          simp only []
          split
          · exact c.pureLe _ _ _ fun _ e => by cases e
          · refine c.le_bind _ _ _ _ (fun _ => True) _
              (le_storedLoopM c k h hk K cfg statement P _ b ts _ _ _) fun q _ => ?_
            cases q with
            | none => exact c.pureLe _ _ _ fun _ e => by cases e
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
              · cases q with
                | none => exact c.le_pure _ _ fun _ e => by cases e
                | some y =>
                  refine c.le_pure _ _ fun s' e => ?_
                  cases e
                  show sent (s.out.push _) = _
                  rw [sent_push]
                  exact congrArg _ (whole_roots P.field r.items _ vals hv)

/-- The fold over the rounds. -/
theorem le_foldRoundsM_sent {R : Type} (K : Keeper R) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s : StK R),
      c.le (foldRoundsM K h cfg statement P run b rs s) (roundsNX rs * k) fun q =>
        ∀ s', q = some s' → sent s'.out = sent s.out + itemsRoots rs
  | [], s => c.pureLe _ _ _ fun _ e => by
      cases e
      rfl
  | r :: rs, s => by
    unfold foldRoundsM
    refine c.le_mono _ (roundNX r.1 r.2 * k + roundsNX rs * k) _ _ _
      (c.le_bind _ _ _ _ _ _ (le_roundM_sent c k h hk K cfg statement P run b s r.1 r.2)
        fun q hq => ?_)
      (by simp only [roundsNX, Nat.add_mul]; exact Nat.le_refl _) fun _ h => h
    cases q with
    | none => exact c.pureLe _ _ _ fun _ e => by cases e
    | some s1 =>
      refine c.le_mono _ _ _ _ _ (le_foldRoundsM_sent K cfg statement P run b rs s1)
        (Nat.le_refl _) fun q h2 s' e => ?_
      rw [h2 s' e, hq s1 rfl]
      show _ = _ + (_ + _)
      rw [Nat.add_assoc]

/-- What follows the chain's random bytes. -/
theorem le_restM_sent {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (x : Option ByteArray) (i0 : Nat) :
    c.le (restM K h S seen b x i0) (fileNX S * k) fun r =>
      ∀ o j, r = some (o, j) → sent o.rounds = itemsRoots (S.base.rounds.zip S.stored) := by
  unfold restM
  refine c.le_mono _ (k + (2 * k + (roundsNX (S.base.rounds.zip S.stored) * k + 0))) _ _ _
    (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun pd _ =>
      c.le_bind _ _ _ _ (fun _ => True) _ (c.startChainW h k hk _ _ _ _) fun q _ => ?_)
    (by simp only [fileNX, Nat.add_mul]; omega) fun _ h => h
  cases q with
  | none => exact c.pureLe _ _ _ fun _ _ e => by cases e
  | some hd =>
    rw [zipT_eq]
    refine c.le_bind _ _ _ 0 _ _ (le_foldRoundsM_sent c k h hk K _ _ _ _ _ _ _) fun q hq => ?_
    cases q with
    | none => exact c.le_pure _ _ fun _ _ e => by cases e
    | some s =>
      refine c.le_pure _ _ fun o j e => ?_
      cases e
      have e2 := hq s rfl
      show sent s.out = _
      rw [e2]
      show 0 + _ = _
      rw [Nat.zero_add]

/-- **The reader of a chain over a monad asks at most fileNX S * k, and a chain that it returns has
sent as many roots as the description's rounds have items "root".** -/
theorem le_readChainM_sent {R : Type} (K : Keeper R) (S : SpecX) (seen : Seen) (b : ByteArray)
    (i : Nat) :
    c.le (readChainM K h S seen b i) (fileNX S * k) fun r =>
      ∀ o j, r = some (o, j) → sent o.rounds = itemsRoots (S.base.rounds.zip S.stored) := by
  unfold readChainM
  split
  · exact c.pureLe _ _ _ fun _ _ e => by cases e
  · split
    · split
      · exact c.pureLe _ _ _ fun _ _ e => by cases e
      · exact le_restM_sent c k h hk K S seen b _ _
    · exact le_restM_sent c k h hk K S seen b _ _
    · exact le_restM_sent c k h hk K S seen b _ _

/-- The same at the keeper that the program's reader has. -/
theorem le_readChain_sent (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) :
    c.le (M.readChain h S seen b i) (fileNX S * k) fun r =>
      ∀ o j, r = some (o, j) → sent o.rounds = itemsRoots (S.base.rounds.zip S.stored) :=
  le_readChainM_sent c k h hk Keeper.indexed S seen b i

end OnBytes.TieK.Counts
