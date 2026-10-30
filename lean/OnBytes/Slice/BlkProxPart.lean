-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxPart.lean: the public part of a verifier's context, and how the calls that send
oracle messages, make groups and join them change it.

The hypotheses under which a run of the program is followed are of two kinds: what a view holds, and
what is public. Public facts are asked of the context at which a run on a view stands. They can be
evaluated only on a context that is at hand. This file names the part of a context on which such
facts hang (pub): the codes; the oracle messages' shapes; the groups' codes, members and marks
"kept"; the book's places and trees, but for the count of a tree's openings and where its root comes
from; the number of the chain's first tree, of roots received and of answers to a sample. It is a
context again, so that all functions on contexts apply to it. The file then has functions on
contexts (sentP, groupP, joinP, csP) and shows that the program's calls change the public part by
them. All are computable, so the public part behind a stretch of a run is a term that is made of the
public part before it.

Main definitions.
  pubTree, pubBook, pubOracle, pubGroup, pubSt, pub   the public part.
  sentP      oracle messages are received.
  groupP     a group is made.
  joinP      an oracle message joins a group.
  csP        a code switch: its message is received and the new tables join their group.
Main theorems.
  map_modify_same, map_modify_comm   an array that is changed at one place, and mapped.
  pubSt_*    what the changes of a statement do to its public part.
  pubBook_kept, pubBook_bookSent   a reading keeps the book's public part; a prover's message.
  pub_mk, pub_same   the public part from its five parts.
  pub_sent, pub_group   the public part after oracle messages are received, after a group is made.
  pub_pub    the public part of a public part is itself.

Not claimed. Nothing on a run: the laws on the program's blocks are in
OnBytes/Slice/BlkProxKeeps.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun

/-! ## The public part -/

/-- A tree without the count of its openings and without the word on where its root comes from: for
a tree that is taken over from another chain that word holds values of a proof. -/
def pubTree (T : Tree) : Tree := { T with lists := 0, src := .own 0 }

/-- The book with such trees. -/
def pubBook (B : TreeBook) : TreeBook := ⟨B.trees.map pubTree, B.place⟩

/-- An oracle message's shape alone. -/
def pubOracle (x : Oracle) : Oracle := { shape := x.shape }

/-- A group's codes, members and marks "kept" alone. -/
def pubGroup (G : Group) : Group :=
  { code := G.code, maskCode := G.maskCode, members := G.members, kept := G.kept }

/-- The public part of a statement. -/
def pubSt (S : Statement) : Statement :=
  ⟨S.codes, S.oracles.map pubOracle, S.groups.map pubGroup⟩

/-- The public part of a context. -/
def pub (c : Ctx) : Ctx where
  ch := { dry := false, entries := [], firstTree := c.ch.firstTree, samples := c.ch.samples,
          roots := c.ch.roots }
  st := pubSt c.st
  book := pubBook c.book

/-- The public part from its five parts. -/
theorem pub_mk (c : Ctx) (F s r : ℕ) (S : Statement) (B : TreeBook) (h1 : c.ch.firstTree = F)
    (h2 : c.ch.samples = s) (h3 : c.ch.roots = r) (h4 : pubSt c.st = S) (h5 : pubBook c.book = B) :
    pub c = { ch := { dry := false, entries := [], firstTree := F, samples := s, roots := r },
              st := S, book := B } := by
  unfold pub
  rw [h1, h2, h3, h4, h5]

/-! ## Arrays -/

/-- An array is changed at one place in a way that a map does not see. -/
theorem map_modify_same {α β : Type} (a : Array α) (i : ℕ) (f : α → α) (h : α → β)
    (hc : ∀ x, h (f x) = h x) : (a.modify i f).map h = a.map h := by
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_map, Array.getElem?_map, Array.getElem?_modify]
  split
  · cases a[j]? with
    | none => rfl
    | some x => exact congrArg some (hc x)
  · rfl

/-- An array is changed at one place in a way that goes through a map, at the member that stands
there. -/
theorem map_modify_comm {α β : Type} (a : Array α) (i : ℕ) (f : α → α) (h : α → β) (f' : β → β)
    (hc : ∀ x, a[i]? = some x → h (f x) = f' (h x)) :
    (a.modify i f).map h = (a.map h).modify i f' := by
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_map, Array.getElem?_modify, Array.getElem?_modify, Array.getElem?_map]
  split
  · rename_i e
    subst e
    cases hx : a[i]? with
    | none => rfl
    | some x => exact congrArg some (hc x hx)
  · rfl

/-! ## Statements -/

/-- Changing an oracle message but for its shape changes nothing public. -/
theorem pubSt_oracle (S : Statement) (o : ℕ) (f : Oracle → Oracle)
    (hf : ∀ x, (f x).shape = x.shape) :
    pubSt { S with oracles := S.oracles.modify o f } = pubSt S := by
  unfold pubSt
  rw [show ({ S with oracles := S.oracles.modify o f } : Statement).oracles.map pubOracle =
    S.oracles.map pubOracle from map_modify_same _ _ _ _ fun x => by
      unfold pubOracle
      rw [hf]]

/-- Changing a group's open rows and the mark that its test has begun changes nothing public. -/
theorem pubSt_group (S : Statement) (g : ℕ) (f : Group → Group)
    (hf : ∀ G, pubGroup (f G) = pubGroup G) :
    pubSt { S with groups := S.groups.modify g f } = pubSt S := by
  unfold pubSt
  rw [show ({ S with groups := S.groups.modify g f } : Statement).groups.map pubGroup =
    S.groups.map pubGroup from map_modify_same _ _ _ _ hf]

/-- Closing ledgers changes nothing public. -/
theorem pubSt_closeLedgers : ∀ (l : List ℕ) (S : Statement), pubSt (closeLedgers S l) = pubSt S
  | [], _ => rfl
  | o :: l, S => by
    show pubSt (closeLedgers _ l) = _
    rw [pubSt_closeLedgers l]
    exact pubSt_oracle S o _ fun _ => rfl

/-- The beginning of a test changes nothing public. -/
theorem pubSt_begun (S : Statement) (g : ℕ) (G : Group) : pubSt (begun S g G) = pubSt S :=
  (pubSt_group (closeLedgers S G.members.toList) g
    (fun G => { G with inRun := true, rows := #[] }) fun _ => rfl).trans (pubSt_closeLedgers _ _)

/-- Open rows that are added change nothing public. -/
theorem pubSt_withRows (g : ℕ) : ∀ (l : List Row) (S : Statement),
    pubSt (withRows S g l) = pubSt S
  | [], _ => rfl
  | r :: l, S => by
    show pubSt (withRows (withRow S g r) g l) = _
    rw [pubSt_withRows g l]
    exact pubSt_group S g _ fun _ => rfl

/-- Entering an oracle message's sample rows changes nothing public. -/
theorem pubSt_admitted (S : Statement) (o : ℕ) (s : OracleShape) (places : List PadPlace)
    (rows : Array Row) : pubSt (admitted S o s places rows) = pubSt S :=
  pubSt_oracle S o _ fun _ => rfl

/-- Closing the new oracle message's ledger changes nothing public. -/
theorem pubSt_ledgerShut (S : Statement) (T : SwitchTarget) (g : ℕ) :
    pubSt (ledgerShut S T g) = pubSt S := by
  unfold ledgerShut
  split
  · exact pubSt_closeLedgers _ _
  · rfl

/-- Oracle messages are received: their shapes are appended. -/
theorem pubSt_stSent (S : Statement) (sent : Array OracleNotice) :
    pubSt (stSent S sent) = stSent (pubSt S) sent := by
  unfold pubSt stSent
  simp only [Array.map_append, Array.map_map]
  rfl

/-- A group is made: it is appended. -/
theorem pubSt_withGroup (S : Statement) (a b : ℕ) :
    pubSt (withGroup S a b) = withGroup (pubSt S) a b := by
  unfold pubSt withGroup
  simp only [Array.map_push]
  rfl

/-- An oracle message joins a group, on a statement: the group's members stay in the order of their
numbers. -/
def joinP (g o : ℕ) (kept : Bool) (S : Statement) : Statement :=
  { S with groups := S.groups.modify g fun G => { G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept } }

/-- An oracle message joins a group. -/
theorem pubSt_joined (S : Statement) (g o : ℕ) (kept : Bool) (G : Group)
    (hG : S.groups[g]? = some G) : pubSt (withMessageInGroup S g o kept G) = joinP g o kept (pubSt S) := by
  unfold pubSt withMessageInGroup joinP
  have e1 : (S.oracles.modify o fun x => { x with groups := x.groups ++ [g] }).map pubOracle =
      S.oracles.map pubOracle := map_modify_same _ _ _ _ fun _ => rfl
  have e2 := map_modify_comm S.groups g (fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept }) pubGroup
    (fun G => { G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })
    (fun x hx => by
      obtain rfl := Option.some.inj (hG.symm.trans hx)
      rfl)
  simp only [e1, e2]

/-! ## The book -/

/-- A reading keeps the book's public part. -/
theorem pubBook_kept {B B' : TreeBook} (h : Blk.BookKept B B') : pubBook B' = pubBook B := by
  unfold pubBook
  rw [h.place]
  congr 1
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_map, Array.getElem?_map]
  cases hj : B.trees[j]? with
  | none =>
    have hs : B.trees.size ≤ j := Array.getElem?_eq_none_iff.1 hj
    rw [Array.getElem?_eq_none (by rw [h.size]; exact hs)]
  | some T =>
    obtain ⟨T', e1, e2, e3, e4, e5, e6⟩ := h.trees j T hj
    rw [e1]
    show some (pubTree T') = some (pubTree T)
    unfold pubTree
    cases T
    cases T'
    simp only at e2 e3 e4 e5 e6
    subst e2 e3 e4 e5 e6
    rfl

/-- The trees of a prover's message are appended: their public part hangs on the public part of the
trees before them alone. -/
theorem treesSent_map (first : ℕ) : ∀ (l : List TreeShape) (roots : ℕ) (trees : Array Tree),
    (treesSent first l roots trees).map pubTree =
      (treesSent first l roots (trees.map pubTree)).map pubTree
  | [], _, trees => by
    show trees.map pubTree = (trees.map pubTree).map pubTree
    rw [Array.map_map]
    rfl
  | s :: l, roots, trees => by
    show (treesSent first l (roots + 1) (trees.push _)).map pubTree =
      (treesSent first l (roots + 1) ((trees.map pubTree).push _)).map pubTree
    rw [treesSent_map first l, treesSent_map first l _ ((trees.map pubTree).push _),
      Array.map_push, Array.map_push, Array.map_map]
    rfl

/-- Entering the oracle messages as parts of their trees goes through the public part. -/
theorem partsLaid_map (sent : Array OracleNotice) (lay : TreeLay) (n0 base : ℕ)
    (trees : Array Tree) : (partsLaid sent lay n0 base trees).map pubTree =
      partsLaid sent lay n0 base (trees.map pubTree) := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    exact map_modify_comm _ _ _ _ _ fun _ _ => rfl

/-- The book after a prover's message, on the public part. -/
theorem pubBook_bookSent (c : Ctx) (sent : Array OracleNotice) (lay : TreeLay) :
    pubBook (bookSent c sent lay) = pubBook (bookSent (pub c) sent lay) := by
  unfold pubBook bookSent
  rw [partsLaid_map, treesSent_map]
  show _ = (⟨(partsLaid sent lay (c.st.oracles.map pubOracle).size (c.book.trees.map pubTree).size
    (treesSent c.ch.firstTree lay.shapes.toList c.ch.roots (c.book.trees.map pubTree))).map pubTree,
    c.book.place ++ (Array.range sent.size).map fun i =>
      ((c.book.trees.map pubTree).size + lay.tree.getD i 0, lay.part.getD i 0)⟩ : TreeBook)
  rw [Array.size_map, Array.size_map, partsLaid_map]

/-! ## The functions on contexts -/

/-- Oracle messages are received: the program's own placing in trees; the shapes; the book; the
roots. -/
def sentP (sent : Array OracleNotice) (P : Ctx) : Ctx :=
  { P with
    ch := { P.ch with roots := P.ch.roots + ((layTrees P.st.codes sent).getD {}).shapes.size }
    st := stSent P.st sent
    book := pubBook (bookSent P sent ((layTrees P.st.codes sent).getD {})) }

/-- A group is made. -/
def groupP (a b : ℕ) (P : Ctx) : Ctx := { P with st := withGroup P.st a b }

/-- A code switch into the group gp: its message is received, and the new tables, the first oracle
message of it, join the group. -/
def csP (T : SwitchTarget) (gp : ℕ) (others : Array OracleNotice) (P : Ctx) : Ctx :=
  { sentP (sentOf T others) P with
    st := joinP gp P.st.oracles.size false (stSent P.st (sentOf T others)) }

/-- Two contexts with the same five parts have the same public part. -/
theorem pub_same {c c' : Ctx} (h1 : c'.ch.firstTree = c.ch.firstTree)
    (h2 : c'.ch.samples = c.ch.samples) (h3 : c'.ch.roots = c.ch.roots)
    (h4 : pubSt c'.st = pubSt c.st) (h5 : pubBook c'.book = pubBook c.book) : pub c' = pub c :=
  pub_mk c' _ _ _ _ _ h1 h2 h3 h4 h5

/-- Oracle messages are received, on the public part. lay: the program's placing. -/
theorem pub_sent (c : Ctx) (sent : Array OracleNotice) (lay : TreeLay)
    (hl : layTrees c.st.codes sent = some lay) :
    pub { c with
      ch := { c.ch with roots := c.ch.roots + lay.shapes.size }
      st := stSent c.st sent
      book := bookSent c sent lay } = sentP sent (pub c) := by
  have e : (layTrees (pub c).st.codes sent).getD {} = lay := by
    show (layTrees c.st.codes sent).getD {} = lay
    rw [hl]
    rfl
  unfold sentP
  rw [e]
  exact pub_mk _ _ _ _ _ _ rfl rfl rfl (pubSt_stSent _ _) (pubBook_bookSent _ _ _)

/-- A group is made, on the public part. -/
theorem pub_group (c : Ctx) (a b : ℕ) :
    pub { c with st := withGroup c.st a b } = groupP a b (pub c) :=
  pub_mk _ _ _ _ _ _ rfl rfl rfl (pubSt_withGroup _ _ _) rfl

/-- The public part of a public part is itself. -/
theorem pub_pub (c : Ctx) : pub (pub c) = pub c := by
  unfold pub pubSt pubBook
  simp only [Array.map_map]
  rfl

end OnBytes.Slice.ProxRun
