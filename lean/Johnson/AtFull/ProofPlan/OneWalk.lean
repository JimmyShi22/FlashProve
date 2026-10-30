-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/OneWalk.lean: TWO OF THE TESTS ON THE PLAN, `FileDescription.beforeOk`
(Johnson/Desc/Block.lean) AND THE CLAUSE `BookPlan.inTime` (Johnson/Desc/BookPlan.lean), OVER SHORT
TABLES THAT ARE EACH MADE IN ONE PASS ALONG A CHAIN's ROUNDS. General in the rounds, the told trees,
the blocks and the description. Definitions, statements and proofs.

Why. Both tests ask, message by message, for the number of a tree's sending round (`sendRound`,
`BookPlan.roundOfRoot`) and look into the list of told trees. Each such look walks a list from its
head. At a long written description Lean's kernel is to be asked these tests; each field of a table
takes one pass along its list, however many messages are named.

  `sentFrom`, `ansFrom`, `Tab`, `tabOf`: the tables. `beforeAtL`, `inTimeL`: the two tests' texts
    with look-ups in the walks' places.
  `sent_is`, `send_is`, `root_is`, `ans_is`, `smp_is`, `len_is`, `pick_tab`: what each look-up is.
  `beforeAt_tab`, `beforeOk_tab`, `inTime_tab`: MAIN: each tabled test IS the test.

What the tables do not spare. A look-up still walks a list from its head: a short one (as many
members as the chain sends trees). `beforeAtL` walks all the rounds with answers at each named
message that is sampled. `inTimeL` still walks the rounds themselves, once. Each block's own rounds
are still read (`findIdx`, `length`).

Limits. Bookkeeping: equations between Bools. No description is named. That the kernel gets through
a given description is seen where a theorem is checked. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Block
import Johnson.G.Eager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.OneWalk

open VerifiableInference.Desc
open Johnson.G (force force_eq lenE length_of_lenE)

/-! ### the tables -/

/-- For each root that the rounds send, in order, the number of its sending round; the rounds count
from k. The counter is made a numeral at each step (`force`). -/
def sentFrom : Nat → List Fmt.DeclaredRound → List Nat
  | _, [] => []
  | k, r :: l => List.replicate r.entry.roots k ++ force (k + 1) fun k' => sentFrom k' l

/-- The numbers of the rounds whose message holds answers; the rounds count from k. -/
def ansFrom : Nat → List Fmt.DeclaredRound → List Nat
  | _, [] => []
  | k, r :: l =>
    if r.entry.answers != 0 then k :: force (k + 1) fun k' => ansFrom k' l
    else force (k + 1) fun k' => ansFrom k' l

/-- What the two tests read of one chain, beside its rounds' openings: sent: for each tree that it
sends the number of the sending round · ans: the numbers of the rounds with answers · smp: for each
tree whether a tenant is sampled · len: how many rounds. `beforeAtL` reads all four; `inTimeL`
reads sent and smp alone. -/
structure Tab where
  sent : List Nat
  ans : List Nat
  smp : List Bool
  len : Nat
  deriving DecidableEq

/-- The table of a chain's rounds and told trees. -/
def tabOf (ds : List Fmt.DeclaredRound) (os : List Oracle) : Tab :=
  ⟨sentFrom 0 ds, ansFrom 0 ds, os.map fun o => o.tenants.any (·.sampled), lenE 0 ds⟩

/-! ### what each look-up is -/

theorem sent_is (l : List Fmt.DeclaredRound) :
    ∀ k n, (sentFrom k l)[n]? = (sendRound l n).map (· + k) := by
  induction l with
  | nil => intro k n; simp [sentFrom, sendRound]
  | cons r l ih =>
    intro k n
    rw [sentFrom, force_eq, sendRound]
    by_cases h : n < r.entry.roots
    · rw [if_pos h, List.getElem?_append_left (by rw [List.length_replicate]; exact h),
        List.getElem?_replicate, if_pos h]
      simp
    · rw [if_neg h,
        List.getElem?_append_right (by rw [List.length_replicate]; exact Nat.le_of_not_lt h),
        List.length_replicate, ih, Option.map_map]
      refine congrArg (fun f => Option.map f (sendRound l (n - r.entry.roots))) (funext fun x => ?_)
      simp only [Function.comp_apply]
      omega

theorem send_is (l : List Fmt.DeclaredRound) (n : Nat) : sendRound l n = (sentFrom 0 l)[n]? := by
  rw [sent_is]
  cases sendRound l n <;> rfl

theorem root_send (l : List Fmt.DeclaredRound) : ∀ n, BookPlan.roundOfRoot l n = sendRound l n := by
  induction l with
  | nil => intro n; rfl
  | cons d l ih => intro n; rw [BookPlan.roundOfRoot, sendRound, ih]

theorem root_is (l : List Fmt.DeclaredRound) (n : Nat) :
    BookPlan.roundOfRoot l n = (sentFrom 0 l)[n]? := by
  rw [root_send, send_is]

theorem ans_is (i last : Nat) (l : List Fmt.DeclaredRound) : ∀ k,
    ((l.zipIdx k).any fun r =>
      r.1.entry.answers != 0 && decide (i < r.2) && decide (r.2 ≤ last)) =
      (ansFrom k l).any fun j => decide (i < j) && decide (j ≤ last) := by
  induction l with
  | nil => intro k; simp [ansFrom]
  | cons r l ih =>
    intro k
    simp only [List.zipIdx_cons, List.any_cons, ansFrom, force_eq]
    rw [ih (k + 1)]
    by_cases h : (r.entry.answers != 0) = true
    · simp [h]
    · simp [h]

theorem smp_is (f : Oracle → Bool) (os : List Oracle) (n : Nat) :
    ((os.map f)[n]?).getD false = (os[n]?).any f := by
  rw [List.getElem?_map]
  cases os[n]? <;> rfl

theorem len_is (l : List Fmt.DeclaredRound) : lenE 0 l = l.length := (length_of_lenE rfl).symm

/-- The pick of a chain's table is the table of the picks. -/
theorem pick_tab (p q : Prop) [Decidable p] [Decidable q] (a b c : List Fmt.DeclaredRound)
    (x y z : List Oracle) :
    (if p then tabOf a x else if q then tabOf b y else tabOf c z) =
      tabOf (if p then a else if q then b else c) (if p then x else if q then y else z) := by
  by_cases hp : p
  · simp only [if_pos hp]
  · by_cases hq : q
    · simp only [if_neg hp, if_pos hq]
    · simp only [if_neg hp, if_neg hq]

/-! ### beforeOk -/

/-- `beforeAt` (Johnson/Desc/Block.lean), its text, but for five places: one pick t of the chain's
table for the two picks ds and os · `t.len` for `ds.length` · `t.sent[m.2]?` for
`sendRound ds m.2` · `(t.smp[m.2]?).getD false` for the look into os · `t.ans.any` for the walk
along `ds.zipIdx`. -/
def beforeAtL {S Cl : Type} (T : Tab × Tab × Tab) (c : Nat) : Nat → List (Block S Cl) → Bool
  | _, [] => true
  | from', b :: l =>
    (b.before.all fun m =>
      let t := if m.1 == 1 then T.1 else if m.1 == 2 then T.2.1 else T.2.2
      let last := if m.1 == c + 1 then from' + b.rounds.findIdx drawsAny else t.len
      match t.sent[m.2]? with
      | none => false
      | some i =>
        decide (1 ≤ m.1) && decide (m.1 ≤ c + 1) && decide (i ≤ last) &&
          (!((t.smp[m.2]?).getD false) ||
            t.ans.any fun j => decide (i < j) && decide (j ≤ last))) &&
    beforeAtL T c (from' + b.rounds.length) l

theorem beforeAt_tab {S Cl : Type}
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) :
    ∀ (l : List (Block S Cl)) (f : Nat), beforeAt D O c f l =
      beforeAtL (tabOf D.1 O.1, tabOf D.2.1 O.2.1, tabOf D.2.2 O.2.2) c f l
  | [], _ => by simp only [beforeAt, beforeAtL]
  | b :: l, f => by
    simp only [beforeAt, beforeAtL, beforeAt_tab D O c l, pick_tab]
    simp only [tabOf, send_is, ans_is, smp_is, len_is]
    rfl

/-- **beforeOk over three tables.** -/
theorem beforeOk_tab {Xi : Type} (F : FileDescription Xi) {T₁ T₂ T₃ : Tab}
    (h₁ : tabOf F.roundsDeclaredByBlocks.1 (oraclesOf F.first.blocksInOrder) = T₁)
    (h₂ : tabOf F.roundsDeclaredByBlocks.2.1 (oraclesOf F.shared.blocksInOrder) = T₂)
    (h₃ : tabOf F.roundsDeclaredByBlocks.2.2 (oraclesOf F.second.blocksInOrder) = T₃) :
    F.beforeOk = (beforeAtL (T₁, T₂, T₃) 0 0 F.first.blocksInOrder &&
      beforeAtL (T₁, T₂, T₃) 1 0 F.shared.blocksInOrder && beforeAtL (T₁, T₂, T₃) 2 0 F.second.blocksInOrder) := by
  subst h₁ h₂ h₃
  unfold FileDescription.beforeOk
  simp only [beforeAt_tab]

/-! ### inTime -/

/-- `BookPlan.inTime` (Johnson/Desc/BookPlan.lean), its text, with each chain's rounds paired with
its table, and look-ups for `roundOfRoot` and `holdsSampled`. -/
def inTimeL (D : BookPlan.DeclaredRoundsByChain) (T : Tab × Tab × Tab) : Bool :=
  [(D.1, T.1), (D.2.1, T.2.1), (D.2.2, T.2.2)].zipIdx.all fun c => c.1.1.zipIdx.all fun d =>
    d.1.opens.all fun o =>
      match o.2 with
      | .own n => (c.1.2.sent[n]?).any fun i =>
          decide (i + (if (c.1.2.smp[n]?).getD false then 1 else 0) ≤ d.2)
      | .taken chain sent => c.2 == 2 && decide (chain < 2) &&
          ((([T.1, T.2.1, T.2.2][chain]?).map (·.sent)).getD [])[sent]?.isSome

theorem holds₀ (O₁ O₂ O₃ : List Oracle) (n : Nat) : BookPlan.holdsSampled [O₁, O₂, O₃] 0 n =
    ((O₁.map fun o => o.tenants.any (·.sampled))[n]?).getD false := by
  rw [smp_is]; rfl

theorem holds₁ (O₁ O₂ O₃ : List Oracle) (n : Nat) : BookPlan.holdsSampled [O₁, O₂, O₃] 1 n =
    ((O₂.map fun o => o.tenants.any (·.sampled))[n]?).getD false := by
  rw [smp_is]; rfl

theorem holds₂ (O₁ O₂ O₃ : List Oracle) (n : Nat) : BookPlan.holdsSampled [O₁, O₂, O₃] 2 n =
    ((O₃.map fun o => o.tenants.any (·.sampled))[n]?).getD false := by
  rw [smp_is]; rfl

theorem taken_is (a b c : List Fmt.DeclaredRound) (x y z : List Oracle) : ∀ chain : Nat,
    sentFrom 0 (([a, b, c][chain]?).getD []) =
      (([tabOf a x, tabOf b y, tabOf c z][chain]?).map (·.sent)).getD []
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- **inTime over three tables.** -/
theorem inTime_tab (D : BookPlan.DeclaredRoundsByChain) (O₁ O₂ O₃ : List Oracle) {T₁ T₂ T₃ : Tab}
    (h₁ : tabOf D.1 O₁ = T₁) (h₂ : tabOf D.2.1 O₂ = T₂) (h₃ : tabOf D.2.2 O₃ = T₃) :
    BookPlan.inTime D [O₁, O₂, O₃] = inTimeL D (T₁, T₂, T₃) := by
  subst h₁ h₂ h₃
  unfold BookPlan.inTime inTimeL
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.all_cons, List.all_nil, Nat.zero_add,
    Nat.reduceAdd, root_is, holds₀, holds₁, holds₂, taken_is D.1 D.2.1 D.2.2 O₁ O₂ O₃]
  rfl

end P2Law.OneWalk

#print axioms P2Law.OneWalk.sent_is
#print axioms P2Law.OneWalk.send_is
#print axioms P2Law.OneWalk.root_send
#print axioms P2Law.OneWalk.root_is
#print axioms P2Law.OneWalk.ans_is
#print axioms P2Law.OneWalk.smp_is
#print axioms P2Law.OneWalk.len_is
#print axioms P2Law.OneWalk.pick_tab
#print axioms P2Law.OneWalk.beforeAt_tab
#print axioms P2Law.OneWalk.beforeOk_tab
#print axioms P2Law.OneWalk.holds₀
#print axioms P2Law.OneWalk.holds₁
#print axioms P2Law.OneWalk.holds₂
#print axioms P2Law.OneWalk.taken_is
#print axioms P2Law.OneWalk.inTime_tab
