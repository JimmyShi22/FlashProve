-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyThreadBase.lean: A FIRST FILLING OF THE KEY FILE's THREE THREADS, as far as the tests with
code on a thread's letters read them (`Thread.fits`, Johnson/Desc/ProofFile/Honest/Thread/Thr.lean).
That these tests accept, in scope: E2E/KeyThreadFits.lean. A thread is a family of sentences, one at
each border between two sub-protocols of a chain, over which the rule for a file's acceptance is
stated (Johnson/Desc/ProofFile/Honest/Thread/File.lean). Definitions with code, statements and
proofs. NOTHING IS SHOWN OF ANY PROVER: no completeness, nothing on what a view shows.

WHAT THE TESTS ASK. n: how many sub-protocols' rows are looked at.
  1  whatever one of the first n rows of the table of joints asks or shuts is open in front of it
  2  every sub-protocol states a list of oracle messages for each round, one message for each root
  3  no tree that is taken over has an own tree's source
  4  at every border up to n, for every tree that is at hand there: the letter `fixed` says no more
     challenges than are heard there. (A comparison of two numbers: no tree's table is read.)
  5  the stops read no more challenges in front of the chain than there are
They read the items with their rows and what is open at the start; the list of sub-protocols; the
rounds in front of the chain; `near`, `taken`, `fixed`. THEY READ NO OTHER LETTER: not what an item
says, not the witness, not a tree's table, not the form.

WHAT IS LAID.
  the items and rows   THE LIBRARY's OWN TABLE OF JOINTS OF THE KEY FILE
    (Johnson/Desc/Key/KeyBorders.lean, KeyBorders23.lean: `KItem`, `rows₁ 2`, `rows₂`, `rows₃`,
    `start₁ 2`, `end₂`), each row read forward (`FwdRow.of`): as the threads of the proof file are
    laid off that file's table. ONE ROW IS TURNED (`rowsFirst`): the sending of the message that the
    format calls W owes the claim "Eval" too: the honest run has that row behind the sending, while
    the table opens the claim where the way back spends another. The shared chain's thread bears THE
    SHARED ITEMS ALONE (`sharedItem`): by type its parts are handed no instance and no state of the
    first chain: an item stays if it reads none of the first chain's messages and is neither the
    claim that the batching leaves nor the one on the carried mark.
  `ahead`, `near`   nothing in front of the first and of the shared chain; in front of the last
    chain the rounds of the two others, of which the stops may read the first chain's.
  `taken`   the sources of other chains' trees that the last chain's declared rounds open, in order.
  `fixed`   an own tree: the challenges in front of the chain, and the chain's own IN FRONT OF THE
    ROUND THAT SENDS IT (`sendRound`, Johnson/Desc/Block.lean). No challenge of a round is among the
    arguments of that round's message (Johnson/Desc/ProofFile/Honest/Frame.lean, `Step.tell`). A
    tree that is taken over: the like in its own chain, counted in the last chain's order of
    hearing.
  `Rest`   ALL OTHER LETTERS, in one structure, typed at these items: they stay letters.
  `keyBase₁`, `keyBase₂`, `keyBase₃`   the three threads, general in the description F.

What is shown.
  `sendRound_lt`, `sendRound_some`, `sendRound_append`, `sentIn_le`, `sentIn_front`   on the round
    that sends a tree. `trees_roots`, `treesTo_roots`: as many oracle messages are stated as roots
    are counted.
  **`fits_of`**: GENERAL IN THE THREAD: the five tests from five plain facts.
  `lists_of_shaped`: test 2 from the description's own test on a sub-protocol's shape.
  `table₁`, `table₂`, `table₃`: test 1 at 19, 12 and 4 rows: closed tests, evaluated. `table_no`: a
    negative test: with nothing open at the first chain's start test 1 rejects.
  `shared_ends`, `ends_table`: what is open at the ends: the shared chain's thread begins at the
    item on the stored table alone and ends at the two on Omega's message; the first chain's forward
    open set ends as the table's own, with "Eval" behind it; the last chain's as the table's own.
    `turned_one`: the turning turns the row number 17 alone.

Limits.
- `Thread.fits` = true SHOWS NO CHOICE RIGHT. It would hold at a table without any item. That the
  table's rows are the right ones, that the shared chain's thread bears the right items, that a
  tree's table is fixed where `fixed` says:
  none of these is shown.
- What weighs is not here: what an item says, the witness, the trees' tables, and the debts at every
  sub-protocol over them.
- An item that the shared chain's thread does not bear and that the table opens or shuts in the
  shared chain (the claim that the batching leaves; two claims that read the first chain's message
  V) stands in no thread between the first chain's end and the last chain's start. Of these the
  claim "DotOm" is open at the last chain's start: it is owed at the seam in front of that chain.


-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.Key.KeyBorders23

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (FileDescription Block Place Strs sendRound)
open VerifiableInference.Desc.Key (KItem KRow names₁ rows₁ rows₂ rows₃ start₁ end₂ readsMsg)
open ProofFile.Honest

/-! ## 1 The round that sends a tree -/

/-- How many roots a list of rounds counts. -/
def rootsOf (l : List Fmt.DeclaredRound) : Nat := (l.map (·.entry.roots)).sum

theorem rootsOf_cons (r : Fmt.DeclaredRound) (l : List Fmt.DeclaredRound) :
    rootsOf (r :: l) = r.entry.roots + rootsOf l := by
  unfold rootsOf
  rw [List.map_cons, List.sum_cons]

theorem rootsOf_append (l₁ l₂ : List Fmt.DeclaredRound) :
    rootsOf (l₁ ++ l₂) = rootsOf l₁ + rootsOf l₂ := by
  unfold rootsOf
  rw [List.map_append, List.sum_append]

theorem sendRound_lt : ∀ (l : List Fmt.DeclaredRound) (j i : Nat), sendRound l j = some i → i < l.length
  | [], _, _, h => by cases h
  | r :: l, j, i, h => by
    unfold sendRound at h
    by_cases hj : j < r.entry.roots
    · rw [if_pos hj] at h
      cases h
      exact Nat.succ_pos _
    · rw [if_neg hj] at h
      obtain ⟨i', h', rfl⟩ := Option.map_eq_some_iff.1 h
      exact Nat.succ_lt_succ (sendRound_lt l _ _ h')

theorem sendRound_some : ∀ (l : List Fmt.DeclaredRound) (j : Nat), j < rootsOf l →
    ∃ i, sendRound l j = some i
  | [], _, h => by cases h
  | r :: l, j, h => by
    unfold sendRound
    by_cases hj : j < r.entry.roots
    · exact ⟨0, if_pos hj⟩
    · rw [if_neg hj]
      rw [rootsOf_cons] at h
      obtain ⟨i, hi⟩ := sendRound_some l (j - r.entry.roots) (by omega)
      exact ⟨i + 1, by rw [hi]; rfl⟩

theorem sendRound_append : ∀ (l₁ l₂ : List Fmt.DeclaredRound) (j : Nat), j < rootsOf l₁ →
    sendRound (l₁ ++ l₂) j = sendRound l₁ j
  | [], _, _, h => by cases h
  | r :: l₁, l₂, j, h => by
    rw [List.cons_append]
    unfold sendRound
    by_cases hj : j < r.entry.roots
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj]
      rw [rootsOf_cons] at h
      rw [sendRound_append l₁ l₂ (j - r.entry.roots) (by omega)]

/-- The number, from 0, of the round that sends the tree number j of a chain; 0 where none does. -/
def sentIn (l : List Fmt.DeclaredRound) (j : Nat) : Nat := (sendRound l j).getD 0

theorem sentIn_le (l : List Fmt.DeclaredRound) (j : Nat) : sentIn l j ≤ l.length := by
  unfold sentIn
  cases h : sendRound l j with
  | none => exact Nat.zero_le _
  | some i => exact Nat.le_of_lt (sendRound_lt l j i h)

/-- A tree that the first of two lists of rounds counts is sent in a round of that list. -/
theorem sentIn_front (l₁ l₂ : List Fmt.DeclaredRound) (j : Nat) (h : j < rootsOf l₁) :
    sentIn (l₁ ++ l₂) j ≤ l₁.length := by
  unfold sentIn
  rw [sendRound_append l₁ l₂ j h]
  exact sentIn_le l₁ j

section Lists
variable {S Cl : Type}

/-- A sub-protocol states a list of oracle messages for each round, one message for each root. -/
def Listed (x : Block S Cl) : Prop :=
  x.rounds.length = x.oracles.length ∧ x.rounds.map (·.entry.roots) = x.oracles.map (·.length)

theorem map_of_zip {α β : Type} (f : α → Nat) (g : β → Nat) : ∀ (a : List α) (b : List β),
    a.length = b.length → (∀ x ∈ a.zip b, g x.2 = f x.1) → a.map f = b.map g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | x :: a, y :: b, h, hz => by
    rw [List.map_cons, List.map_cons, (hz (x, y) List.mem_cons_self : g y = f x),
      map_of_zip f g a b (Nat.succ.inj h) fun z hz' => hz z (List.mem_cons_of_mem _ hz')]

/-- From the description's own test on a sub-protocol's shape. -/
theorem lists_of_shaped {x : Block S Cl} (h : x.shaped = true) : Listed x := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1.symm, map_of_zip _ _ _ _ h.1.symm fun z hz => ?_⟩
  have hz' := h.2 z hz
  rw [Bool.and_eq_true, beq_iff_eq] at hz'
  exact hz'.1

theorem trees_roots : ∀ l : List (Block S Cl), (∀ x ∈ l, Listed x) →
    (l.flatMap fun x => x.oracles.flatMap id).length = rootsOf (l.flatMap (·.rounds))
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, rootsOf_append,
      trees_roots l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    congr 1
    rw [List.length_flatMap]
    unfold rootsOf
    rw [(h x List.mem_cons_self).2]
    rfl

/-- As many oracle messages are stated in front of a border as roots are counted there. -/
theorem treesTo_roots (bs : List (Block S Cl)) (h : ∀ x ∈ bs, Listed x) (b : Nat) :
    treesTo bs b = rootsOf (declsTo bs b) :=
  trees_roots _ fun x hx => h x (List.mem_of_mem_take hx)

theorem decls_split (bs : List (Block S Cl)) (b : Nat) :
    bs.flatMap (·.rounds) = declsTo bs b ++ (bs.drop b).flatMap (·.rounds) := by
  unfold declsTo
  rw [← List.flatMap_append, List.take_append_drop]

end Lists

/-! ## 2 The five tests from five plain facts -/

section General
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **The tests with code accept**, general in the thread. -/
theorem fits_of (n : Nat) (h1 : fwdFit T.start T.row n = true) (h2 : ∀ x ∈ T.bs, Listed x)
    (h3 : ∀ σ ∈ T.taken, ∃ c m, σ = .taken c m) (h4 : ∀ σ ∈ T.taken, T.fixed σ ≤ T.front)
    (h4' : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j)
    (h5 : T.near ≤ T.front) : T.fits n = true := by
  unfold Thread.fits
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨h1, ?_⟩, ?_⟩, ?_⟩, decide_eq_true h5⟩
  · rw [List.all_eq_true]
    intro x hx
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
    exact h2 x hx
  · rw [List.all_eq_true]
    intro σ hσ
    obtain ⟨c, m, rfl⟩ := h3 σ hσ
    rfl
  · rw [List.all_eq_true]
    intro b _
    rw [List.all_eq_true]
    intro σ hσ
    refine decide_eq_true ?_
    unfold Thread.hand at hσ
    rcases List.mem_append.1 hσ with hσ | hσ
    · exact Nat.le_trans (h4 σ hσ) (Nat.le_add_right _ _)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hσ
      rw [h4', decls_split T.bs b]
      refine Nat.add_le_add_left (sentIn_front _ _ j ?_) _
      rw [← treesTo_roots T.bs h2 b]
      exact List.mem_range.1 hj

end General

/-! ## 3 The table of joints, read forward -/

/-- A row of the library's table, read forward. -/
def fwd (r : KRow) : FwdRow KItem := FwdRow.of r.ins r.outs r.ctx

/-- The forward row behind the border number b of a list of rows; an empty row beyond the list. -/
def rowsAt (rs : List KRow) (b : Nat) : FwdRow KItem := ((rs[b]?).map fwd).getD {}

/-- **The first chain's forward rows, with ONE TURNING**: the sending of the message that the format
calls W owes the claim "Eval" too. The table, which was written for the way back, opens that claim
at the shared point, where it spends the claim that the batching leaves. Read forward, the honest
run has the row behind that sending. -/
def rowsFirst (b : Nat) : FwdRow KItem :=
  let f := rowsAt (rows₁ 2) b
  if (names₁ 2)[b]? == some "w.1.send" then { f with owes := f.owes ++ [.claim 1 "Eval"] } else f

/-- **The items that the shared chain's thread bears.** -/
def sharedItem (i : KItem) : Bool :=
  (readsMsg i).all (fun k => decide (3 ≤ k)) && i != .pile && i != .unmarked

/-- A row without the other items. -/
def sharedRow (r : KRow) : KRow :=
  { r with ins := r.ins.filter sharedItem, outs := r.outs.filter sharedItem
           ctx := r.ctx.filter sharedItem }

/-- What is open at the shared chain's start. -/
def startShared : List KItem := VerifiableInference.Desc.Key.seam.filter sharedItem

theorem table₁ : fwdFit (start₁ 2) rowsFirst 19 = true := by decide

theorem table₂ : fwdFit startShared (rowsAt (rows₂.map sharedRow)) 12 = true := by decide

theorem table₃ : fwdFit end₂ (rowsAt rows₃) 4 = true := by decide

/-- A negative test: with nothing open at the first chain's start the test rejects. -/
theorem table_no : fwdFit [] rowsFirst 19 = false := by decide

/-- What the shared chain's thread has open at its start, and at its end. -/
theorem shared_ends : startShared = [.pinT] ∧
    fwdOpen startShared (rowsAt (rows₂.map sharedRow)) 12 = [.pin 4, .srow 4] := by decide

/-- The first chain's forward open set ends as the table's own does, with the claim "Eval" behind
it; the last chain's as the table's own. -/
theorem ends_table :
    fwdOpen (start₁ 2) rowsFirst 19 = VerifiableInference.Desc.Key.end₁ ++ [.claim 1 "Eval"] ∧
      fwdOpen end₂ (rowsAt rows₃) 4 = [.unmarked] := by decide

/-- The turning turns one row: number 17. -/
theorem turned_one :
    (List.range 19).filter (fun b => (rowsFirst b).owes != (rowsAt (rows₁ 2) b).owes) = [17] := by
  decide

/-! ## 4 The three threads -/

/-- **All letters of a thread that the tests with code do not read**, typed at the table's items. -/
structure Rest (Bk : ProverCoinCounts) (S W : Type) where
  table : Fmt.TreeSource → Coins Bk → W → List Fmt.Drawn → Place × Table
  stored : W → Nat → Nat → Option (List UInt64)
  valid : W → Prop
  P : Type
  handed : Coins Bk → W → List Fmt.Drawn → P
  Wt : Type
  form : Nat → P × S → Bool
  formP : Nat → P × S → Prop
  means : W → KItem → P × S → Strs → Wt → Prop
  wit : Coins Bk → W → List Fmt.Drawn → Wt
  strs : Env → Strs
  begun : Coins Bk → W → List Fmt.Drawn → S → Prop
  rides : Nat → W → S → Prop
  keeps : Nat → S → S → Prop

/-- The sources of other chains' trees that a list of rounds opens, in order. -/
def takenIn (l : List Fmt.DeclaredRound) : List Fmt.TreeSource :=
  (l.flatMap (·.opens)).filterMap fun o =>
    match o.2 with
    | .own _ => none
    | .taken c n => some (.taken c n)

theorem takenIn_taken (l : List Fmt.DeclaredRound) : ∀ σ ∈ takenIn l, ∃ c m, σ = .taken c m := by
  intro σ hσ
  obtain ⟨o, -, ho⟩ := List.mem_filterMap.1 hσ
  cases h : o.2 with
  | own n =>
    rw [h] at ho
    cases ho
  | taken c n =>
    rw [h] at ho
    exact ⟨c, n, (Option.some.inj ho).symm⟩

section Threads
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)

/-- A chain's declared rounds. -/
abbrev decl₁ : List Fmt.DeclaredRound := F.first.blocksInOrder.flatMap (·.rounds)
abbrev decl₂ : List Fmt.DeclaredRound := F.shared.blocksInOrder.flatMap (·.rounds)
abbrev decl₃ : List Fmt.DeclaredRound := F.second.blocksInOrder.flatMap (·.rounds)

/-- After how many challenges a tree is fixed, in a chain in front of which nothing is heard. -/
def fixedOwn (l : List Fmt.DeclaredRound) : Fmt.TreeSource → Nat
  | .own j => sentIn l j
  | .taken _ _ => 0

/-- The like in the last chain, which has heard the first chain's challenges, then the shared
chain's. -/
def fixedLast : Fmt.TreeSource → Nat
  | .own j => ((decl₁ F).length + (decl₂ F).length) + sentIn (decl₃ F) j
  | .taken c n => if c == 0 then sentIn (decl₁ F) n else (decl₁ F).length + sentIn (decl₂ F) n

/-- **The first chain's thread.** Its halves are laid by `seat₁` (E2E/KeyLaid.lean). -/
def keyBase₁ (R : Rest Bk F.S₁ (Local W₀ Rc Xi Tr)) :
    Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { φ := .own, chain := 0, ft := 0, bs := F.first.blocksInOrder, hs := [], ahead := [], near := 0
    taken := []
    fixed := fixedOwn (decl₁ F), table := R.table, stored := R.stored, valid := R.valid
    ι := KItem, dec := inferInstance, start := start₁ 2, row := rowsFirst
    P := R.P, handed := R.handed, Wt := R.Wt, form := R.form, formP := R.formP, means := R.means
    wit := R.wit, strs := R.strs, begun := R.begun, rides := R.rides, keeps := R.keeps }

/-- **The shared chain's thread.** -/
def keyBase₂ (R : Rest Bk F.S₂ (Common W₀ Rc Ky)) :
    Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky :=
  { φ := .shared, chain := 1, ft := 0, bs := F.shared.blocksInOrder, hs := [], ahead := [], near := 0
    taken := []
    fixed := fixedOwn (decl₂ F), table := R.table, stored := R.stored, valid := R.valid
    ι := KItem, dec := inferInstance, start := startShared, row := rowsAt (rows₂.map sharedRow)
    P := R.P, handed := R.handed, Wt := R.Wt, form := R.form, formP := R.formP, means := R.means
    wit := R.wit, strs := R.strs, begun := R.begun, rides := R.rides, keeps := R.keeps }

/-- **The last chain's thread.** -/
def keyBase₃ (R : Rest Bk F.S₃ (Local W₀ Rc Xi Tr)) :
    Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { φ := .own, chain := 2, ft := F.lastChainFirstTreeNumber, bs := F.second.blocksInOrder, hs := []
    ahead := decl₁ F ++ decl₂ F, near := (decl₁ F).length, taken := takenIn (decl₃ F)
    fixed := fixedLast F, table := R.table, stored := R.stored, valid := R.valid
    ι := KItem, dec := inferInstance, start := end₂, row := rowsAt rows₃
    P := R.P, handed := R.handed, Wt := R.Wt, form := R.form, formP := R.formP, means := R.means
    wit := R.wit, strs := R.strs, begun := R.begun, rides := R.rides, keeps := R.keeps }

end Threads

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.fits_of
#print axioms AtPublicFiles.KeyThread.lists_of_shaped
#print axioms AtPublicFiles.KeyThread.takenIn_taken
#print axioms AtPublicFiles.KeyThread.table₁
#print axioms AtPublicFiles.KeyThread.table₂
#print axioms AtPublicFiles.KeyThread.table₃
#print axioms AtPublicFiles.KeyThread.table_no
#print axioms AtPublicFiles.KeyThread.shared_ends
#print axioms AtPublicFiles.KeyThread.ends_table
#print axioms AtPublicFiles.KeyThread.turned_one
