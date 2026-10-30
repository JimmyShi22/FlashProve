-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkSendRun.lean: a run of the program's sending block, taken apart.

In the sending block (OnBytes/Iop/Send.lean: `sendVerify`) the verifier receives the roots of the
oracle messages of one prover's message, enters the messages into the statement and their trees into
the book, draws the seed of a sample, and receives one or more answers for each sampled message. The
block has loops. This file first says what a run of a loop is, and then what a run of the block's
two parts is, for any number of oracle messages and answers.

Main definitions.
 `RunFold`      the runs of a loop's body on the entries of a list, one after the other.
 `treesSent`, `partsLaid`, `bookSent`, `stSent`
                the book of trees and the statement after the receiving, as functions of what was
                held before.
 `todoOf`       the oracle messages that are sampled.
 `answerStep`, `sampleStep`
                one turn of the loop over a message's answers, and of the loop over the messages.
Main theorems.
 `forIn_inv`, `forIn_inv_array`   a run of a loop whose body never breaks off.
 `pureSteps`                     all turns of a loop that changes its value alone.
 `receiveOracles_inv`            a run of the receiving.
 `verify_inv`                    a run of the seed and the answers.
 `sendVerify_inv`                a run of the block: a run of the receiving, then one of the rest.
Not claimed. What a sample row's coefficients are. Nothing on the dry run. Nothing on soundness.
-/
import OnBytes.Iop.Send
import OnBytes.Slice.BlkBegin

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## Loops -/

/-- The runs of a loop's body on the entries of a list, one after the other. step a b c b' c' says
that the body, at the entry a, from the loop's value b and the context c, goes on with b' and c'. -/
def RunFold {α β : Type} (step : α → β → Ctx → β → Ctx → Prop) :
    List α → β → Ctx → β → Ctx → Prop
  | [], b, c, b', c' => b' = b ∧ c' = c
  | a :: l, b, c, b', c' => ∃ b1 c1, step a b c b1 c1 ∧ RunFold step l b1 c1 b' c'

/-- A run of a loop over a list whose body never breaks off is the runs of the body, in the
entries' order. -/
theorem forIn_inv {α β : Type} (f : α → β → Blk (ForInStep β))
    (step : α → β → Ctx → β → Ctx → Prop)
    (hf : ∀ a b c r c1, (f a b).Yields c r c1 → ∃ b1, r = .yield b1 ∧ step a b c b1 c1) :
    ∀ (l : List α) (b : β) (c : Ctx) (b' : β) (c' : Ctx),
      (forIn l b f).Yields c b' c' → RunFold step l b c b' c'
  | [], b, c, b', c', h => by
    rw [List.forIn_nil] at h
    exact (Blk.yields_pure _ _ _ _).1 h
  | a :: l, b, c, b', c', h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨b1, rfl, hs⟩ := hf a b c r c1 h1
    exact ⟨b1, c1, hs, forIn_inv f step hf l b1 c1 b' c' h2⟩

/-- The same for a loop over an array. -/
theorem forIn_inv_array {α β : Type} (f : α → β → Blk (ForInStep β))
    (step : α → β → Ctx → β → Ctx → Prop)
    (hf : ∀ a b c r c1, (f a b).Yields c r c1 → ∃ b1, r = .yield b1 ∧ step a b c b1 c1)
    (as : Array α) (b : β) (c : Ctx) (b' : β) (c' : Ctx) (h : (forIn as b f).Yields c b' c') :
    RunFold step as.toList b c b' c' := by
  rw [← Array.forIn_toList] at h
  exact forIn_inv f step hf _ _ _ _ _ h

/-! ## Single calls -/

/-- Reading the number of the chain's first tree returns it and changes nothing. -/
theorem yields_firstTree (n : Nat) (c c' : Ctx) :
    Blk.firstTree.Yields c n c' ↔ n = c.ch.firstTree ∧ c' = c := by
  show (some (c.ch.firstTree, c) : Option (Nat × Ctx)) = some (n, c') ↔ _
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Putting a statement in the place of the present one changes the statement alone. -/
theorem yields_setStatement (S : Statement) (c c' : Ctx) :
    (Blk.setStatement S).Yields c () c' ↔ c' = { c with st := S } := by
  show (some ((), { c with st := S }) : Option (Unit × Ctx)) = some ((), c') ↔ _
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    rfl

/-- On a view, receiving a root returns its number on the chain and counts it. -/
theorem yields_recvRoot (n : Nat) (c c' : Ctx) (hd : c.ch.dry = false) :
    Blk.recvRoot.Yields c n c' ↔
      n = c.ch.roots ∧ c' = { c with ch := { c.ch with roots := c.ch.roots + 1 } } := by
  unfold Blk.Yields Blk.outcome Blk.recvRoot
  simp only [hd, Bool.false_eq_true, if_false, Except.toOption, Option.some.injEq, Prod.mk.injEq]
  exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

/-! ## Receiving oracle messages -/

/-- The trees of a prover's message, appended to those that the book has. first: the number of
the chain's first tree; roots: the number of roots received before. -/
def treesSent (first : Nat) : List TreeShape → Nat → Array Tree → Array Tree
  | [], _, trees => trees
  | s :: l, roots, trees =>
    treesSent first l (roots + 1)
      (trees.push { shape := s, number := first + roots, src := .own roots })

/-- The oracle messages of a prover's message, entered as parts of their trees. n0: the number of
the first of them; base: the number of the first of the trees. -/
def partsLaid (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat) (trees : Array Tree) :
    Array Tree :=
  (List.range sent.size).foldl (fun trees i =>
    trees.modify (base + lay.tree.getD i 0) fun x => { x with
      parts := x.parts.push (n0 + i)
      oneList := x.oneList || (sent.getD i default).shape.answers == 0 }) trees

/-- The book after a prover's message with oracle messages. -/
def bookSent (c : Ctx) (sent : Array OracleNotice) (lay : TreeLay) : TreeBook :=
  { trees := partsLaid sent lay c.st.oracles.size c.book.trees.size
      (treesSent c.ch.firstTree lay.shapes.toList c.ch.roots c.book.trees)
    place := c.book.place ++ (Array.range sent.size).map fun i =>
      (c.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0) }

/-- The statement after a prover's message with oracle messages. -/
def stSent (S : Statement) (sent : Array OracleNotice) : Statement :=
  { S with oracles := S.oracles ++ sent.map fun n => { shape := n.shape } }

/-- One turn of the loop that receives the roots, on a view. -/
def rootStep (first : Nat) (s : TreeShape) (trees : Array Tree) (c : Ctx) (trees' : Array Tree)
    (c' : Ctx) : Prop :=
  c.ch.dry = false →
    trees' = trees.push { shape := s, number := first + c.ch.roots, src := .own c.ch.roots } ∧
    c' = { c with ch := { c.ch with roots := c.ch.roots + 1 } }

/-- All turns of the loop that receives the roots. -/
theorem rootSteps (first : Nat) : ∀ (l : List TreeShape) (trees : Array Tree) (c : Ctx)
    (trees' : Array Tree) (c' : Ctx), c.ch.dry = false →
    RunFold (rootStep first) l trees c trees' c' →
    trees' = treesSent first l c.ch.roots trees ∧
      c' = { c with ch := { c.ch with roots := c.ch.roots + l.length } }
  | [], _, _, _, _, _, h => h
  | s :: l, trees, c, trees', c', hd, h => by
    obtain ⟨t1, c1, h1, h2⟩ := h
    obtain ⟨rfl, rfl⟩ := h1 hd
    obtain ⟨e1, e2⟩ := rootSteps first l _ _ trees' c' (by exact hd) h2
    refine ⟨e1, ?_⟩
    rw [e2, List.length_cons]
    show _ = { c with ch := { c.ch with roots := c.ch.roots + (l.length + 1) } }
    rw [Nat.add_assoc, Nat.add_comm 1]

/-- All turns of a loop that changes its value alone. -/
theorem pureSteps {α β : Type} (g : β → α → β) : ∀ (l : List α) (b : β) (c : Ctx) (b' : β)
    (c' : Ctx), RunFold (fun a b c b' c' => b' = g b a ∧ c' = c) l b c b' c' →
    b' = l.foldl g b ∧ c' = c
  | [], _, _, _, _, h => h
  | a :: l, b, c, b', c', h => by
    obtain ⟨b1, c1, ⟨rfl, rfl⟩, h2⟩ := h
    exact pureSteps g l _ _ b' c' h2

/-- A run of the call that receives the oracle messages of a prover's message, on a view. -/
theorem receiveOracles_inv (sent : Array OracleNotice) (ids : Array Nat) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (Blk.receiveOracles sent).Yields c ids c') :
    ∃ lay, layTrees c.st.codes sent = some lay ∧ c.st.oracles.size = c.book.place.size ∧
      ids = (Array.range sent.size).map (· + c.st.oracles.size) ∧
      c' = { c with
        ch := { c.ch with roots := c.ch.roots + lay.shapes.size }
        st := stSent c.st sent
        book := bookSent c sent lay } := by
  unfold Blk.receiveOracles at h
  obtain ⟨S, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨eS, e1⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨B, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨eB, e2⟩ := (Blk.yields_theBook _ _ _).1 h2
  obtain ⟨first, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨eF, e3⟩ := (yields_firstTree _ _ _).1 h3
  obtain ⟨_, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨_, e4⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨_, c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨kpl, e5⟩ := (Blk.yields_must _ _ _).1 h5
  obtain ⟨lay, c6, h6, a6⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
  obtain ⟨hlay, e6⟩ := (Blk.yields_get _ _ _ _).1 h6
  obtain ⟨t1, c7, h7, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 a6
  obtain ⟨t2, c8, h8, a8⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
  obtain ⟨_, c9, h9, a9⟩ := (Blk.yields_bind _ _ _ _ _).1 a8
  obtain ⟨_, c10, h10, a10⟩ := (Blk.yields_bind _ _ _ _ _).1 a9
  have e9 := (yields_setStatement _ _ _).1 h9
  have e10 := (Blk.yields_setBook _ _ _).1 h10
  obtain ⟨ei, e11⟩ := (Blk.yields_pure _ _ _ _).1 a10
  -- nothing has changed before the roots are received
  have e2' : c2 = c := e2.trans e1
  have e3' : c3 = c := e3.trans e2'
  have e6' : c6 = c := e6.trans (e5.trans (e4.trans e3'))
  rw [e1] at eB
  rw [e2'] at eF
  -- the roots
  have k7 : RunFold (rootStep first) lay.shapes.toList B.trees c6 t1 c7 := by
    refine forIn_inv_array _ _ ?_ _ _ _ _ _ h7
    intro s r d x d1 hy
    obtain ⟨n, d2, y1, y2⟩ := (Blk.yields_bind _ _ _ _ _).1 hy
    obtain ⟨_, d3, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 y2
    obtain ⟨_, f3⟩ := (Blk.yields_pure _ _ _ _).1 y3
    obtain ⟨f4, f5⟩ := (Blk.yields_pure _ _ _ _).1 y4
    refine ⟨_, f4, fun hdd => ?_⟩
    obtain ⟨rfl, f1⟩ := (yields_recvRoot _ _ _ hdd).1 y1
    exact ⟨rfl, f5.trans (f3.trans f1)⟩
  rw [e6'] at k7
  obtain ⟨et1, e7⟩ := rootSteps first _ _ _ _ _ hd k7
  -- the parts
  have k8 := forIn_inv _ (fun i (b : Array Tree) (d : Ctx) b' d' =>
      b' = (fun (trees : Array Tree) i =>
        trees.modify (B.trees.size + lay.tree.getD i 0) fun x => { x with
          parts := x.parts.push (S.oracles.size + i)
          oneList := x.oneList || (sent.getD i default).shape.answers == 0 }) b i ∧ d' = d)
    (by
      intro i r d x d1 hy
      obtain ⟨_, d3, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 hy
      obtain ⟨_, f3⟩ := (Blk.yields_pure _ _ _ _).1 y3
      obtain ⟨f4, f5⟩ := (Blk.yields_pure _ _ _ _).1 y4
      exact ⟨_, f4, rfl, f5.trans f3⟩) _ _ _ _ _ h8
  obtain ⟨et2, e8⟩ := pureSteps _ _ _ _ _ _ k8
  refine ⟨lay, ?_, ?_, ?_, ?_⟩
  · rw [← eS]
    exact hlay
  · rw [← eS, ← eB]
    exact beq_iff_eq.1 kpl
  · rw [ei, eS]
  · rw [e11, e10, e9, e8, e7, et2, et1, eS, eB, eF, Array.length_toList]
    rfl

/-! ## The seed and the answers -/

/-- The oracle messages among ids that are sampled: those whose shape has answers. -/
def todoOf (S : Statement) (ids : Array Nat) : List Nat :=
  ids.toList.filter fun o => ((S.oracles[o]?).map (·.shape.answers)).getD 0 != 0

/-- One turn of the loop over the answers of the oracle message o of the shape s: the answer number
i is received, and the sample row with that target joins the rows. -/
def answerStep (S : Statement) (seeds : List SampleSeed) (o : Nat) (s : OracleShape) (i : Nat)
    (rows : Array Row) (c : Ctx) (rows' : Array Row) (c' : Ctx) : Prop :=
  ∃ seed row y, seeds[i]? = some seed ∧ Send.form S.codes s o seed i = some row ∧
    Blk.recvAnswer.Yields c y c' ∧ rows' = rows.push { row with target := y }

/-- One turn of the loop over the sampled oracle messages: all answers of one of them are received,
and it is admitted with its sample rows. -/
def sampleStep (S : Statement) (seeds : List SampleSeed) (x : Nat × OracleShape) (_ : PUnit)
    (c : Ctx) (_ : PUnit) (c' : Ctx) : Prop :=
  ∃ rows c1, RunFold (answerStep S seeds x.1 x.2) (List.range x.2.answers) #[] c rows c1 ∧
    (Send.admit x.1 rows).Yields c1 () c'

/-- A run of the seed and the answers, on a view. shapes: the shapes of the sampled oracle
messages; drawn: what the round of the seed drew; seeds: the seeds cut out of it; c1: the context
after that round; c2: the context after the last answer. -/
theorem verify_inv (ids : Array Nat) (own : Bool) (c c' : Ctx) (hd : c.ch.dry = false)
    (h : (Send.verify ids own).Yields c () c') :
    ∃ shapes drawn seeds c1 c2,
      (todoOf c.st ids).mapM (fun o => (c.st.oracles[o]?).map (·.shape)) = some shapes ∧
      (Blk.close "SEND seed" .seeds (shapes.foldl (fun a s => max a s.answers) 0)).Yields
        c drawn c1 ∧
      Send.seedsOf (shapes.foldl (fun b s => max b (Send.cube c.st.codes s).bits) 0)
        (shapes.foldl (fun a s => max a s.answers) 0) (drawn.elems.map E.ofTriple) = some seeds ∧
      (seeds.all fun s => !isZeroE s.beta) = true ∧
      RunFold (sampleStep c.st seeds) ((todoOf c.st ids).zip shapes) PUnit.unit c1 PUnit.unit c2 ∧
      (if own = true then (Blk.closeEmpty "SEND answer").Yields c2 () c' else c' = c2) := by
  unfold Send.verify at h
  obtain ⟨S, d1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨eS, e1⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨_, d2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, e2⟩ := (Blk.yields_must _ _ _).1 h2
  obtain ⟨_, d3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨_, e3⟩ := (Blk.yields_must _ _ _).1 h3
  obtain ⟨shapes, d4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨hsh, e4⟩ := (Blk.yields_get _ _ _ _).1 h4
  obtain ⟨drawn, d5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨seeds, d6, h6, a6⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
  obtain ⟨hse, e6⟩ := (Blk.yields_get _ _ _ _).1 h6
  obtain ⟨_, d7, h7, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 a6
  obtain ⟨u, d8, h8, a8⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
  have e4' : d4 = c := e4.trans (e3.trans (e2.trans e1))
  rw [e4'] at h5
  have hd5 : d5.ch.dry = false := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k, _⟩ :=
      Blk.close_inv _ _ _ _ _ _ hd h5
    exact k
  have hd6 : d6.ch.dry = false := by rw [e6]; exact hd5
  obtain ⟨hne, e7⟩ := (Blk.yields_test _ _ _ hd6).1 h7
  have e7' : d7 = d5 := e7.trans e6
  rw [e7', zipT_eq] at h8
  have k8 : RunFold (sampleStep S seeds) ((todoOf S ids).zip shapes) PUnit.unit d5 u d8 := by
    refine forIn_inv _ _ ?_ _ _ _ _ _ h8
    rintro ⟨o, s⟩ r d x d' hy
    obtain ⟨rows, f1, y1, y2⟩ := (Blk.yields_bind _ _ _ _ _).1 hy
    obtain ⟨_, f2, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 y2
    obtain ⟨g1, g2⟩ := (Blk.yields_pure _ _ _ _).1 y4
    refine ⟨PUnit.unit, g1, rows, f1, ?_, ?_⟩
    · refine forIn_inv _ _ ?_ _ _ _ _ _ y1
      intro i rw' q x' q' hz
      obtain ⟨seed, q1, z1, z2⟩ := (Blk.yields_bind _ _ _ _ _).1 hz
      obtain ⟨m1, n1⟩ := (Blk.yields_get _ _ _ _).1 z1
      obtain ⟨row, q2, z3, z4⟩ := (Blk.yields_bind _ _ _ _ _).1 z2
      obtain ⟨m2, n2⟩ := (Blk.yields_get _ _ _ _).1 z3
      obtain ⟨y, q3, z5, z6⟩ := (Blk.yields_bind _ _ _ _ _).1 z4
      obtain ⟨_, q4, z7, z8⟩ := (Blk.yields_bind _ _ _ _ _).1 z6
      obtain ⟨_, n4⟩ := (Blk.yields_pure _ _ _ _).1 z7
      obtain ⟨m5, n5⟩ := (Blk.yields_pure _ _ _ _).1 z8
      rw [n2, n1] at z5
      rw [n5, n4]
      exact ⟨_, m5, seed, row, y, m1, m2, z5, rfl⟩
    · rw [g2]
      exact y3
  rw [eS] at hsh hse k8
  refine ⟨shapes, drawn, seeds, d5, d8, hsh, h5, hse, hne, k8, ?_⟩
  cases own
  · exact ((Blk.yields_pure _ _ _ _).1 a8).2
  · exact a8

/-- A run of the sending block: the oracle messages are received, then sampled. -/
theorem sendVerify_inv (notices : Array OracleNotice) (own : Bool) (ids : Array Nat) (c c' : Ctx)
    (h : (sendVerify notices own).Yields c ids c') :
    ∃ c1, (Blk.receiveOracles notices).Yields c ids c1 ∧ (Send.verify ids own).Yields c1 () c' := by
  unfold sendVerify at h
  obtain ⟨ids', c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a2
  exact ⟨c1, h1, h2⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.forIn_inv
#print axioms OnBytes.Slice.forIn_inv_array
#print axioms OnBytes.Slice.yields_firstTree
#print axioms OnBytes.Slice.yields_setStatement
#print axioms OnBytes.Slice.yields_recvRoot
#print axioms OnBytes.Slice.rootSteps
#print axioms OnBytes.Slice.pureSteps
#print axioms OnBytes.Slice.receiveOracles_inv
#print axioms OnBytes.Slice.verify_inv
#print axioms OnBytes.Slice.sendVerify_inv
