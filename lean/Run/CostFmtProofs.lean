-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CostFmtProofs.lean: the proofs of the statements of Run/CostFmt.lean.

The statements bound the number of questions asked by the functions of the format that hash (those
named in Run/CostFmt.lean, the head, 3), for any count `c : CostP m` (Run/CostP.lean) and any hash
h of which each call asks at most k. The numbers are upper bounds; this limit and what they do not
count are told in Run/CostFmt.lean, the head, 3 and 4.

One lemma for each function (`Run.CostP.HM` to `Run.CostP.wholeChain`: for use by name).

Notation:
  `c.le x t P`: the count's predicate, of `x` and a number `t` of questions (`CostP`,
    Run/CostP.lean);
  `P` there: its condition on what comes out (Run/CostP.lean);
  `opensN`, `roundN`, `roundsN`, `fileN`: the numbers for the openings, a round, the rounds, a file
    (Run/CostFmt.lean);
  `firstBlock work`: the first block of the verifier's message, at `work` bits of work
    (Fmt/Rules5.lean);
  `K`: the number of blocks of the verifier's message (`Chain.queryW`, Fmt/Rules5.lean);
  `S`: a description (`Fmt.Spec`, Fmt/Rules8.lean), the data under which a file is read.
-/
import Run.CostFmt

set_option autoImplicit false

namespace Run

namespace CostP
variable {m : Type → Type} [Monad m] (c : CostP m)
open _root_.Fmt

/-- A value asks nothing: any number is a bound. The value must have P. -/
theorem pureLe {α : Type} (a : α) (t : Nat) (P : α → Prop) (h : P a) : c.le (pure a : m α) t P :=
  c.le_mono _ 0 t P P (c.le_pure a P h) (Nat.zero_le _) fun _ h => h

/-- A step, then a value computed from its result: under the hypotheses below, the step's bound s
is a bound. -/
theorem bindPure {α β : Type} (x : m α) (g : α → β) (s : Nat) (P : α → Prop) (Q : β → Prop)
    (hx : c.le x s P) (hg : ∀ a, P a → Q (g a)) :
    c.le (x >>= fun a => pure (g a)) s Q :=
  c.le_bind x _ s 0 P Q hx fun a ha => c.le_pure _ Q (hg a ha)

theorem HM (ask : ByteArray → m ByteArray) (k : Nat) (hk : ∀ s, c.le (ask s) k fun _ => True)
    (number tree index : Nat) (start bytes : ByteArray) :
    c.le (Fmt.HM ask number tree index start bytes) (2 * k) fun _ => True := by
  unfold Fmt.HM
  split
  · refine c.le_mono _ (k + (k + 0)) _ _ _
      (c.le_bind _ _ k (k + 0) _ _ (hk _) fun a _ =>
        c.le_bind _ _ k 0 _ _ (hk _) fun b _ => c.le_pure _ _ trivial)
      (by omega) fun _ h => h
  · exact c.le_mono _ k _ _ _ (hk _) (by omega) fun _ h => h

variable (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

theorem startChainW (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray) :
    c.le (Fmt.startChainW h lab pd statement rnd) (2 * k) fun _ => True := by
  unfold Fmt.startChainW
  split
  · split
    · exact c.le_mono _ (k + 0) _ _ _
        (c.le_bind _ _ k 0 _ _ (hk _ _ _ _ _) fun _ _ => c.le_pure _ _ trivial) (by omega)
        fun _ h => h
    · split
      · refine c.le_mono _ (k + k) _ _ _
          (c.le_bind _ _ k k _ _ (hk _ _ _ _ _) fun run _ => ?_) (by omega) fun _ h => h
        split
        · exact c.le_mono _ (k + 0) _ _ _
            (c.le_bind _ _ k 0 _ _ (hk _ _ _ _ _) fun _ _ => c.le_pure _ _ trivial) (by omega)
            fun _ h => h
        · exact c.pureLe _ _ _ trivial
      · exact c.pureLe _ _ _ trivial
  · exact c.pureLe _ _ _ trivial

theorem fetchFrom (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce : Nat) :
    ∀ (n j : Nat) (acc : Array ByteArray),
      c.le (Fmt.fetchFrom h lab rho i msg kind w nonce n j acc) (n * k) fun _ => True
  | 0, _, _ => c.pureLe _ _ _ trivial
  | n + 1, j, acc => by
    simp only [Fmt.fetchFrom]
    exact c.le_mono _ (k + n * k) _ _ _
      (c.le_bind _ _ k (n * k) _ _ (hk _ _ _ _ _) fun _ _ =>
        fetchFrom lab rho i msg kind w nonce n _ _)
      (by rw [Nat.succ_mul]; omega) fun _ h => h

theorem fetchW (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray)
    (kind : Kind) (w nonce n : Nat) :
    c.le (Fmt.fetchW h lab rho i msg kind w nonce n) ((n + 1) / 2 * k) fun _ => True := by
  simp only [Fmt.fetchW]
  exact c.bindPure _ _ _ _ _
    (c.fetchFrom h k hk lab rho i msg kind w nonce _ _ _) fun _ _ => trivial

theorem queryW (ch : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat) :
    c.le (ch.queryW h msg kind work nonce K) ((firstBlock work + K + 1) / 2 * k) fun _ => True := by
  unfold Chain.queryW
  split
  · exact c.bindPure _ _ _ _ _ (c.fetchW h k hk _ _ _ _ _ _ _ _) fun _ _ => trivial
  · exact c.pureLe _ _ _ trivial

omit hk

section
variable {α σ : Type} (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ))
  (hc : ∀ a b x y, c.le (comb a b x y) k fun _ => True)
include hc

theorem walkLoneW (d i : Nat) (x : α) (s : σ) :
    c.le (Fmt.walkLoneW comb give d i x s) k fun _ => True := by
  unfold Fmt.walkLoneW
  split
  · exact c.pureLe _ _ _ trivial
  · split <;> exact c.bindPure _ _ _ _ _ (hc _ _ _ _) fun _ _ => trivial

/-- Assumes hc (the `variable` line above): each call of comb asks at most k. One depth: at most k
questions for each vertex of the list; the list that comes out is no longer. -/
theorem walkLevelW (d : Nat) :
    ∀ (l : List (Nat × α)) (s : σ), c.le (Fmt.walkLevelW comb give d l s) (l.length * k)
      fun r => ∀ p, r = some p → p.1.length ≤ l.length
  | [], s => c.pureLe _ _ _ fun p e => by cases e; exact Nat.le_refl _
  | [(i, x)], s => by
    simp only [Fmt.walkLevelW]
    refine c.le_mono _ k _ _ _
      (c.bindPure _ _ _ _ _ (c.walkLoneW k comb give hc d i x s) fun r _ p e => ?_) (by simp)
      fun _ h => h
    cases r with
    | none => cases e
    | some r => cases e; exact Nat.le_refl _
  | (i, x) :: (i', x') :: rest, s => by
    unfold Fmt.walkLevelW
    split
    · refine c.le_mono _ (k + (rest.length * k + 0)) _ _ _
        (c.le_bind _ _ k _ _ _ (hc _ _ _ _) fun v _ =>
          c.le_bind _ _ _ 0 _ _ (walkLevelW d rest s) fun r hr => c.le_pure _ _ fun p e => ?_)
        (by simp only [List.length_cons, Nat.succ_mul]; omega) fun _ h => h
      cases r with
      | none => cases e
      | some r =>
        cases e
        have := hr r rfl
        simp only [List.length_cons]
        omega
    · refine c.le_mono _ (k + ((i', x') :: rest).length * k) _ _ _
        (c.le_bind _ _ k _ _ _ (c.walkLoneW k comb give hc d i x s) fun r _ => ?_)
        (by simp only [List.length_cons, Nat.succ_mul]; omega) fun _ h => h
      cases r with
      | none => exact c.pureLe _ _ _ fun p e => by cases e
      | some q =>
        refine c.bindPure _ _ _ _ _ (walkLevelW d ((i', x') :: rest) q.2) fun r hr p e => ?_
        cases r with
        | none => cases e
        | some r =>
          cases e
          have := hr r rfl
          simp only [List.length_cons] at this ⊢
          omega

/-- Assumes hc. From depth d to the root: at most d · (the length of the list) · k questions. -/
theorem walkW :
    ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
      c.le (Fmt.walkW comb give d now s met) (d * (now.length * k)) fun _ => True
  | 0, now, s, met => by
    unfold Fmt.walkW
    split <;> first | exact c.pureLe _ _ _ trivial | simp_all
  | d + 1, now, s, met => by
    simp only [Fmt.walkW]
    refine c.le_mono _ (now.length * k + d * (now.length * k)) _ _ _
      (c.le_bind _ _ _ _ _ _ (c.walkLevelW k comb give hc (d + 1) now s) fun r hr => ?_)
      (by rw [Nat.succ_mul]; omega) fun _ h => h
    cases r with
    | none => exact c.pureLe _ _ _ trivial
    | some p =>
      exact c.le_mono _ _ _ _ _ (walkW d p.1 p.2 _)
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (hr p rfl))) fun _ h => h

end

include hk

/-- Assumes hk: each call of h asks at most k. The opened leaves: at most k questions for each
position; the list that comes out is no longer than the list of positions. -/
theorem leavesW (sh : Shape) (start : ByteArray) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)),
      c.le (Fmt.leavesW h sh start xs cs) (xs.length * k) fun r => r.length ≤ xs.length
  | x :: xs, (col, salt) :: cs => by
    simp only [Fmt.leavesW]
    refine c.le_mono _ (k + (xs.length * k + 0)) _ _ _
      (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun v _ =>
        c.le_bind _ _ _ 0 _ _ (leavesW sh start xs cs) fun r hr => c.le_pure _ _ ?_)
      (by simp only [List.length_cons, Nat.succ_mul]; omega) fun _ h => h
    simp only [List.length_cons]
    omega
  | [], _ => by simp only [Fmt.leavesW]; exact c.pureLe _ _ _ (Nat.le_refl _)
  | _ :: _, [] => by simp only [Fmt.leavesW]; exact c.pureLe _ _ _ (Nat.zero_le _)

theorem readOpeningW (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) :
    c.le (Fmt.readOpeningW h cfg f salt sh start xs b i)
      ((sh.a + 1) * (xs.length * k)) fun _ => True := by
  unfold Fmt.readOpeningW
  split
  · split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _ (xs.length * k + (sh.a * (xs.length * k) + 0)) _ _ _
        (c.le_bind _ _ _ _ _ _ (c.leavesW h k hk sh start xs _) fun now hn =>
          c.le_bind _ _ _ 0 _ _
            (c.le_mono _ _ _ _ _
              (c.walkW k (fun _ _ l r => vertexW h cfg l r) takeGiven
                (fun _ _ _ _ => hk _ _ _ _ _) sh.a now _ _)
              (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hn)) fun _ h => h)
            fun _ _ => c.le_pure _ _ trivial)
        (by rw [Nat.succ_mul]; omega) fun _ h => h
  · exact c.pureLe _ _ _ trivial

omit hk

/-! ### Pure facts on lists and draws -/

theorem insertN_len (x : Nat) : ∀ l : List Nat, (insertIntoIncreasingList x l).length ≤ l.length + 1
  | [] => Nat.le_refl _
  | y :: l => by
    unfold insertIntoIncreasingList
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_succ _
      · have := insertN_len x l
        simp only [List.length_cons]
        omega

theorem listOf_len : ∀ l : List Nat, (listOf l).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: l => Nat.le_trans (insertN_len x (listOf l)) (Nat.succ_le_succ (listOf_len l))

theorem times_len {α : Type} (x : Dr α) :
    ∀ (n : Nat) (r : Row) (p : Nat), (x.times n r p).1.length = n
  | 0, _, _ => rfl
  | n + 1, r, _ => congrArg Nat.succ (times_len x n r _)

theorem drawRound_poss (f : Fld) (e : Entry) (kd : Kind) (row : Row) :
    (drawRound f e kd row).poss.length = e.poss :=
  times_len _ _ _ _

/-! ### A chain in a file -/

include hk

theorem readOpens (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (roots : Array ByteArray)
    (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : Seen) (i : Nat),
      c.le (Fmt.readOpens h cfg P run roots poss b os sn i)
        (opensN poss.length os * k) fun _ => True
  | [], _, _ => c.pureLe _ _ _ trivial
  | (sh, src) :: os, sn, i => by
    unfold Fmt.readOpens
    simp only []
    split
    · exact c.pureLe _ _ _ trivial
    · have hl : (listOf (poss.map (· % 2 ^ sh.a))).length ≤ poss.length :=
        Nat.le_trans (listOf_len _) (Nat.le_of_eq (List.length_map _))
      refine c.le_mono _ ((sh.a + 1) * (poss.length * k) + opensN poss.length os * k) _ _ _
        (c.le_bind _ _ _ _ _ _
          (c.le_mono _ _ _ _ _ (c.readOpeningW h k hk cfg P.field P.salt sh _ _ b i)
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hl)) fun _ h => h) fun r _ => ?_)
        (by simp only [opensN, Nat.add_mul, Nat.mul_assoc]; exact Nat.le_refl _) fun _ h => h
      cases r with
      | none => exact c.pureLe _ _ _ trivial
      | some o =>
        simp only []
        split
        · split
          · exact c.pureLe _ _ _ trivial
          · refine c.le_mono _ (opensN poss.length os * k + 0) _ _ _
              (c.le_bind _ _ _ 0 _ _ (readOpens cfg P run roots poss b os _ _) fun r _ => ?_)
              (Nat.le_refl _) fun _ h => h
            cases r <;> exact c.le_pure _ _ trivial
        · exact c.pureLe _ _ _ trivial

theorem step (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : St) (r : Round) :
    c.le (Fmt.step h cfg P run b s r) (roundN r * k) fun _ => True := by
  unfold Fmt.step
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · exact c.pureLe _ _ _ trivial
    · split
      · exact c.pureLe _ _ _ trivial
      · refine c.le_mono _
          ((firstBlock r.entry.work + (wordsAtMost r.entry r.kind + 3) / 4 + 1) / 2 * k +
            opensN r.entry.poss r.opens * k)
          _ _ _ (c.le_bind _ _ _ _ _ _ (c.queryW h k hk _ _ _ _ _ _) fun q _ => ?_)
          (by simp only [roundN, Nat.add_mul]; exact Nat.le_refl _) fun _ h => h
        cases q with
        | none => exact c.pureLe _ _ _ trivial
        | some cv =>
          simp only []
          split
          · exact c.pureLe _ _ _ trivial
          · refine c.le_mono _ (opensN r.entry.poss r.opens * k + 0) _ _ _
              (c.le_bind _ _ _ 0 (fun _ => True) _ ?_ fun q _ => ?_) (Nat.le_refl _) fun _ h => h
            · have key : ∀ (roots : Array ByteArray) (i : Nat),
                  c.le (Fmt.readOpens h cfg P run roots
                      (drawRound P.field r.entry r.kind (rowOf cv.2)).poss b r.opens s.seen i)
                    (opensN r.entry.poss r.opens * k) fun _ => True := fun roots i => by
                have := c.readOpens h k hk cfg P run roots
                  (drawRound P.field r.entry r.kind (rowOf cv.2)).poss b r.opens s.seen i
                rw [drawRound_poss] at this
                exact this
              exact key _ _
            · cases q <;> exact c.le_pure _ _ trivial

theorem foldRounds (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List Round) (s : St),
      c.le (Fmt.foldRounds h cfg P run b rs s) (roundsN rs * k) fun _ => True
  | [], _ => c.pureLe _ _ _ trivial
  | r :: rs, s => by
    simp only [Fmt.foldRounds]
    refine c.le_mono _ (roundN r * k + roundsN rs * k) _ _ _
      (c.le_bind _ _ _ _ _ _ (c.step h k hk cfg P run b s r) fun q _ => ?_)
      (by simp only [roundsN, Nat.add_mul]; exact Nat.le_refl _) fun _ h => h
    cases q with
    | none => exact c.pureLe _ _ _ trivial
    | some s' => exact foldRounds cfg P run b rs s'

theorem readChain (S : Fmt.Spec) (seen : Seen) (b : ByteArray) (i : Nat) :
    c.le (Fmt.readChain h S seen b i) (fileN S * k) fun _ => True := by
  unfold Fmt.readChain
  split
  · exact c.pureLe _ _ _ trivial
  · simp only []
    split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _ (k + (2 * k + (roundsN S.rounds * k + 0))) _ _ _
        (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun pd _ =>
          c.le_bind _ _ _ _ _ _ (c.startChainW h k hk _ _ _ _) fun q _ => ?_)
        (by simp only [fileN, Nat.add_mul]; omega) fun _ h => h
      cases q with
      | none => exact c.pureLe _ _ _ trivial
      | some hd =>
        refine c.le_bind _ _ _ 0 _ _ (c.foldRounds h k hk _ _ _ _ _ _) fun q _ => ?_
        cases q <;> exact c.le_pure _ _ trivial

theorem wholeChain (S : Fmt.Spec) (b : ByteArray) :
    c.le (Fmt.wholeChain h S b) (fileN S * k) fun _ => True := by
  simp only [Fmt.wholeChain]
  refine c.le_bind _ _ _ 0 _ _ (c.readChain h k hk S [] b 0) fun q _ => ?_
  cases q <;> exact c.le_pure _ _ trivial

end CostP

theorem cost_pure : Spec.cost_pure := ⟨CostP.listOf_len, CostP.drawRound_poss⟩

theorem cost_HM : Spec.cost_HM := fun _ _ c ask k hk => c.HM ask k hk

theorem cost_first : Spec.cost_first := fun _ _ c h k hk => c.startChainW h k hk

theorem cost_round : Spec.cost_round := fun _ _ c h k hk =>
  ⟨c.fetchFrom h k hk, c.fetchW h k hk, c.queryW h k hk⟩

theorem cost_tree : Spec.cost_tree := fun _ _ c k =>
  ⟨fun _ _ comb give hc =>
      ⟨c.walkLoneW k comb give hc, c.walkLevelW k comb give hc, c.walkW k comb give hc⟩,
    fun h hk => ⟨c.leavesW h k hk, c.readOpeningW h k hk⟩⟩

theorem cost_file : Spec.cost_file := fun _ _ c h k hk =>
  ⟨c.readOpens h k hk, c.step h k hk, c.foldRounds h k hk, c.readChain h k hk, c.wholeChain h k hk⟩

end Run
