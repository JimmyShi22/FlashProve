-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxKeeps.lean: what a whole proximity test leaves of the verifier's context.

In a key's chains a proximity test (OnBytes/Iop/Prox.lean: ioppVerify) stands in the middle of a
chain, or two tests stand in a row. Whoever follows a run of the program past such a test needs to
know what the test has left as it was. This file says so, for a run on a view, with no hypothesis on
what the view's rounds hold.

Main definitions.
  Closed     a property of statements lasts through each way in which a test changes the statement.
  ExtG, Ext     what a stretch of a run that has closed k rounds has left, and how many oracle
                messages and groups it has made (Ext: none): of the statement what
                OnBytes/Slice/BlkProxEarlierMessagesAndGroups.lean names (Old); what is public of the book; the channel's
                settings; the rounds and entries but the first k; an end piece of the opened
                columns.
                If no named test is recorded as failed after it, none was before it.
  Calm          what a stretch of a run within one round has left.
  stagesRounds, testRounds   the number of rounds that the stages, and a whole test, close.
  newOracles    the number of oracle messages that the stages make.
  foldP, stagesP, testP   what a fold, the stages, and a whole test do to the context's public
                part.
  TestKept      what a whole test on the group g has left.
Main theorems.
  Ext.refl, Ext.trans, Calm.refl, Calm.trans, Calm.close
  foldVerify_ext, csVerify_ext, baseVerify_ext, stages_ext   the blocks of a test.
  baseVerify_cut    the base case's one reading, with nothing asked of its two named tests.
  ioppVerify_kept   a whole test.

Not claimed. Nothing on what the test has shown. Nothing on the new oracle messages, groups and
trees but their numbers, their public part, and that they come after the older ones. The number of
roots received is said only through the public part, as the outcome of the program's own placing of
oracle messages in trees; that it is one for each code switch is shown where that placing is a
public fact (OnBytes/Slice/BlkProxChain.lean). Nothing on a tree's count of openings. Nothing on the
dry run. Two hypotheses stand under all numbers of this file: a sample has one answer, and masks
ride; without riding masks a test makes other numbers of oracle messages and trees. That testRounds
is the length of a list of written rounds is not shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups
import OnBytes.Slice.BlkProxPart
import OnBytes.Slice.BlkJointCs
import OnBytes.Slice.BlkTop
import OnBytes.Slice.BlkBat
import OnBytes.Slice.BaseYields

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun
open Params (IoppStage IoppChoice)

/-! ## Properties of a statement that a test keeps -/

/-- A property of statements lasts through each way in which a proximity test changes the
statement: an oracle message is marked as spent; oracle messages are received; a group is made; a
group's test begins; a code switch into a group that was made for it. -/
structure Closed (Inv : Statement → Prop) : Prop where
  spent : ∀ (S : Statement) (o : Nat), Inv S →
    Inv { S with oracles := S.oracles.modify o fun x => { x with spentAsMask := true } }
  sent : ∀ (S : Statement) (sent : Array OracleNotice), Inv S → Inv (stSent S sent)
  group : ∀ (S : Statement) (a b : Nat), Inv S → Inv (withGroup S a b)
  begun : ∀ (S : Statement) (g : Nat) (G : Group), S.groups[g]? = some G → Inv S →
    Inv (begun S g G)
  switch : ∀ (old : SingleRows) (T : SwitchTarget) (gp : Nat) (others : Array OracleNotice)
    (c c' : Ctx) (out : Switched) (row : GroupRow) (lay : GroupLayout) (theta : E) (D : CsTaken),
    CsRan old T gp others c c' out row lay theta D →
    c.st.groups[gp]? = some { code := T.shape.code, maskCode := T.shape.maskCode } →
    Inv c.st → Inv c'.st

/-! ## Two relations between contexts -/

/-- What a stretch of a run on a view that has closed k rounds has left, and how much is new: a
oracle messages, b groups; f: what it has done to the context's public part
(OnBytes/Slice/BlkProxPart.lean). n0, g0, sp: see Old. -/
structure ExtG (n0 g0 : Nat) (sp : Nat → Prop) (k a b : Nat) (f : Ctx → Ctx) (c c' : Ctx) :
    Prop where
  /-- the statement's codes, older oracle messages and older groups -/
  st : Old n0 g0 sp c.st c'.st
  /-- what is public of the book -/
  book : BookKeeps c.book c'.book
  /-- if no named test is recorded as failed at the end, none was at the start -/
  failed : c'.failed = none → c.failed = none
  /-- it is no dry run -/
  dry : c'.ch.dry = false
  /-- the opened columns that are left to be read are an end piece of those that were -/
  opened : ∃ l, c.ch.opened = l ++ c'.ch.opened
  /-- no fewer roots have been received -/
  roots : c.ch.roots ≤ c'.ch.roots
  /-- the number of the first tree that this chain sends -/
  firstTree : c'.ch.firstTree = c.ch.firstTree
  /-- the number of answers to a sample -/
  samples : c'.ch.samples = c.ch.samples
  /-- of the view's rounds that were not closed the first k are gone -/
  pending : c'.ch.pending = c.ch.pending.drop k
  /-- of the plan's entries the first k are gone -/
  entries : c'.ch.entries = c.ch.entries.drop k
  /-- each property that a test keeps has lasted -/
  inv : ∀ Inv : Statement → Prop, Closed Inv → Inv c.st → Inv c'.st
  /-- a oracle messages and b groups are new -/
  osz : c'.st.oracles.size = c.st.oracles.size + a
  gsz : c'.st.groups.size = c.st.groups.size + b
  /-- the book has as many new trees as roots were received, and a new places -/
  trees : c'.book.trees.size + c.ch.roots = c.book.trees.size + c'.ch.roots
  places : c'.book.place.size = c.book.place.size + a
  /-- if no oracle message is new, no root was received -/
  still : a = 0 → c'.ch.roots = c.ch.roots
  /-- the public part -/
  part : pub c' = f (pub c)

/-- A stretch in which no oracle message and no group is made. -/
abbrev Ext (n0 g0 : Nat) (sp : Nat → Prop) (k : Nat) (c c' : Ctx) : Prop :=
  ExtG n0 g0 sp k 0 0 id c c'

variable {n0 g0 : Nat} {sp : Nat → Prop}

/-- Nothing was done. -/
theorem Ext.refl {c : Ctx} (hd : c.ch.dry = false) : Ext n0 g0 sp 0 c c :=
  ⟨Old.refl _ _ _ _, BookKeeps.refl _, fun h => h, hd, ⟨[], rfl⟩, Nat.le_refl _, rfl, rfl, rfl, rfl,
    fun _ _ h => h, rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩

/-- Two stretches in a row. -/
theorem ExtG.trans {k1 k2 a1 a2 b1 b2 : Nat} {f1 f2 : Ctx → Ctx} {a b c : Ctx}
    (h1 : ExtG n0 g0 sp k1 a1 b1 f1 a b) (h2 : ExtG n0 g0 sp k2 a2 b2 f2 b c) :
    ExtG n0 g0 sp (k1 + k2) (a1 + a2) (b1 + b2) (f2 ∘ f1) a c := by
  obtain ⟨l1, e1⟩ := h1.opened
  obtain ⟨l2, e2⟩ := h2.opened
  refine ⟨h1.st.trans h2.st, h1.book.trans h2.book, fun h => h1.failed (h2.failed h), h2.dry,
    ⟨l1 ++ l2, by rw [e1, e2, List.append_assoc]⟩, h1.roots.trans h2.roots,
    h2.firstTree.trans h1.firstTree, h2.samples.trans h1.samples, ?_, ?_,
    fun I hI h => h2.inv I hI (h1.inv I hI h), ?_, ?_, ?_, ?_,
    fun e0 => (h2.still (by omega)).trans (h1.still (by omega)),
    by rw [h2.part, h1.part]; rfl⟩
  · rw [h2.pending, h1.pending, List.drop_drop]
  · rw [h2.entries, h1.entries, List.drop_drop]
  · rw [h2.osz, h1.osz, Nat.add_assoc]
  · rw [h2.gsz, h1.gsz, Nat.add_assoc]
  · have t1 := h1.trees
    have t2 := h2.trees
    omega
  · rw [h2.places, h1.places, Nat.add_assoc]

/-- Two stretches in a row in which nothing is made. -/
theorem Ext.trans {k1 k2 : Nat} {a b c : Ctx} (h1 : Ext n0 g0 sp k1 a b)
    (h2 : Ext n0 g0 sp k2 b c) : Ext n0 g0 sp (k1 + k2) a c := ExtG.trans h1 h2

/-- The numbers, rewritten. -/
theorem ExtG.cast {k k' a a' b b' : Nat} {f : Ctx → Ctx} {c c' : Ctx}
    (h : ExtG n0 g0 sp k a b f c c') (e : k = k') (ea : a = a') (eb : b = b') :
    ExtG n0 g0 sp k' a' b' f c c' := e ▸ ea ▸ eb ▸ h

/-- What was done to the public part, written otherwise. -/
theorem ExtG.castP {k a b : Nat} {f f' : Ctx → Ctx} {c c' : Ctx}
    (h : ExtG n0 g0 sp k a b f c c') (e : f (pub c) = f' (pub c)) :
    ExtG n0 g0 sp k a b f' c c' :=
  ⟨h.st, h.book, h.failed, h.dry, h.opened, h.roots, h.firstTree, h.samples, h.pending, h.entries,
    h.inv, h.osz, h.gsz, h.trees, h.places, h.still, h.part.trans e⟩

/-- The number of rounds, rewritten. -/
theorem Ext.cast {k k' : Nat} {c c' : Ctx} (h : Ext n0 g0 sp k c c') (e : k = k') :
    Ext n0 g0 sp k' c c' := e ▸ h

/-- An equal context. -/
theorem Ext.of_eq {c c' : Ctx} (hd : c.ch.dry = false) (h : c' = c) : Ext n0 g0 sp 0 c c' := by
  rw [h]
  exact Ext.refl hd

/-- Only the statement has changed. -/
theorem Ext.of_st {c : Ctx} (hd : c.ch.dry = false) {S : Statement} (h : Old n0 g0 sp c.st S)
    (hi : ∀ Inv : Statement → Prop, Closed Inv → Inv c.st → Inv S) {b : Nat}
    (ho : S.oracles.size = c.st.oracles.size) (hg : S.groups.size = c.st.groups.size + b)
    {f : Ctx → Ctx} (hp : pub { c with st := S } = f (pub c)) :
    ExtG n0 g0 sp 0 0 b f c { c with st := S } :=
  ⟨h, BookKeeps.refl _, fun h => h, hd, ⟨[], rfl⟩, Nat.le_refl _, rfl, rfl, rfl, rfl, hi, ho, hg,
    rfl, rfl, fun _ => rfl, hp⟩

/-- Only intermediate values were kept. -/
theorem Ext.of_notes {c c' : Ctx} (hd : c.ch.dry = false) (h : Blk.SameButNotes c c') :
    Ext n0 g0 sp 0 c c' := by
  refine ⟨by rw [h.st]; exact Old.refl _ _ _ _, BookKeeps.of_eq h.book,
    fun hf => by rw [← h.failed]; exact hf, by rw [h.ch]; exact hd, ⟨[], by rw [h.ch]; rfl⟩,
    Nat.le_of_eq (by rw [h.ch]), by rw [h.ch], by rw [h.ch], by rw [h.ch]; rfl,
    by rw [h.ch]; rfl, fun _ _ hI => by rw [h.st]; exact hI, by rw [h.st]; rfl, by rw [h.st]; rfl,
    by rw [h.book, h.ch], by rw [h.book]; rfl, fun _ => by rw [h.ch],
    pub_same (by rw [h.ch]) (by rw [h.ch]) (by rw [h.ch]) (by rw [h.st]) (by rw [h.book])⟩

/-- What a stretch of a run within one round has left: items of the open message were taken, values
were kept, named tests were made. The rounds after the first one that is not closed are as they
were. -/
structure Calm (c c' : Ctx) : Prop where
  /-- the statement -/
  st : c'.st = c.st
  /-- the book -/
  book : c'.book = c.book
  /-- if no named test is recorded as failed at the end, none was at the start -/
  failed : c'.failed = none → c.failed = none
  /-- whether it is a dry run -/
  dry : c'.ch.dry = c.ch.dry
  /-- the opened columns that are left to be read -/
  opened : c'.ch.opened = c.ch.opened
  /-- the number of roots received -/
  roots : c'.ch.roots = c.ch.roots
  /-- the number of the first tree that this chain sends -/
  firstTree : c'.ch.firstTree = c.ch.firstTree
  /-- the number of answers to a sample -/
  samples : c'.ch.samples = c.ch.samples
  /-- the plan's entries -/
  entries : c'.ch.entries = c.ch.entries
  /-- the rounds after the first one that is not closed -/
  tail : c'.ch.pending.tail = c.ch.pending.tail
  /-- what the first round that is not closed has drawn -/
  drawn : c'.ch.pending.head?.map (·.drawn) = c.ch.pending.head?.map (·.drawn)

/-- Nothing was done. -/
theorem Calm.refl (c : Ctx) : Calm c c :=
  ⟨rfl, rfl, fun h => h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two stretches in a row. -/
theorem Calm.trans {a b c : Ctx} (h1 : Calm a b) (h2 : Calm b c) : Calm a c :=
  ⟨h2.st.trans h1.st, h2.book.trans h1.book, fun h => h1.failed (h2.failed h),
    h2.dry.trans h1.dry, h2.opened.trans h1.opened, h2.roots.trans h1.roots,
    h2.firstTree.trans h1.firstTree, h2.samples.trans h1.samples, h2.entries.trans h1.entries,
    h2.tail.trans h1.tail, h2.drawn.trans h1.drawn⟩

/-- An equal context. -/
theorem Calm.of_eq {c c' : Ctx} (h : c' = c) : Calm c c' := by
  rw [h]
  exact Calm.refl c

/-- The channel, the statement and the book are as they were. -/
theorem Calm.of_ch {c c' : Ctx} (h1 : c'.ch = c.ch) (h2 : c'.st = c.st) (h3 : c'.book = c.book)
    (h4 : c'.failed = none → c.failed = none) : Calm c c' :=
  ⟨h2, h3, h4, by rw [h1], by rw [h1], by rw [h1], by rw [h1], by rw [h1], by rw [h1], by rw [h1],
    by rw [h1]⟩

/-- Only intermediate values were kept. -/
theorem Calm.of_notes {c c' : Ctx} (h : Blk.SameButNotes c c') : Calm c c' :=
  Calm.of_ch h.ch h.st h.book fun hf => by rw [← h.failed]; exact hf

/-- A stretch within a round in which no item was taken. -/
theorem Calm.ext {c c' : Ctx} (h : Calm c c') (hd : c.ch.dry = false)
    (hp : c'.ch.pending = c.ch.pending) : Ext n0 g0 sp 0 c c' :=
  ⟨by rw [h.st]; exact Old.refl _ _ _ _, BookKeeps.of_eq h.book, h.failed, h.dry.trans hd,
    ⟨[], by rw [h.opened]; rfl⟩, Nat.le_of_eq h.roots.symm, h.firstTree, h.samples, hp, h.entries,
    fun _ _ hI => by rw [h.st]; exact hI, by rw [h.st]; rfl, by rw [h.st]; rfl,
    by rw [h.book, h.roots], by rw [h.book]; rfl, fun _ => h.roots,
    pub_same h.firstTree h.samples h.roots (by rw [h.st]) (by rw [h.book])⟩

/-- An element was received. -/
theorem recvE_calm (x : E) (c c' : Ctx) (hd : c.ch.dry = false) (h : Blk.recvE.Yields c x c') :
    Calm c c' := by
  obtain ⟨r, rest, vs, h1, _, h3, s⟩ := Blk.recvE_inv x c c' hd h
  exact ⟨s.st, s.book, fun hf => by rw [← s.failed]; exact hf, s.dry, s.opened, s.roots,
    s.firstTree, s.samples, s.entries, by rw [h1, h3]; rfl, by rw [h1, h3]; rfl⟩

/-- Several elements were received. -/
theorem recvEsInto_calm : ∀ (n : Nat) (acc out : Array E) (c c' : Ctx), c.ch.dry = false →
    (Blk.recvEsInto n acc).Yields c out c' → Calm c c'
  | 0, _, _, _, _, _, h => Calm.of_eq ((Blk.yields_pure _ _ _ _).1 h).2
  | n + 1, acc, out, c, c', hd, h => by
    rw [recvEsInto_succ_fun] at h
    obtain ⟨x, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    have k1 := recvE_calm x c c1 hd h1
    exact k1.trans (recvEsInto_calm n _ out c1 c' (k1.dry.trans hd) h2)

/-- Several vectors were received. -/
theorem recvVectors_calm : ∀ (ns : List Nat) (out : List (Array E)) (c c' : Ctx),
    c.ch.dry = false → (recvVectors ns).Yields c out c' → Calm c c'
  | [], _, _, _, _, h => Calm.of_eq ((Blk.yields_pure _ _ _ _).1 h).2
  | n :: ns, out, c, c', hd, h => by
    have h0 : (Blk.recvEsInto n #[] >>= fun v => recvVectors ns >>= fun vs =>
        (pure (v :: vs) : Blk (List (Array E)))).Yields c out c' := h
    obtain ⟨v, c1, h1, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
    obtain ⟨vs, c2, h2, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
    obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h0
    have k1 := recvEsInto_calm n _ v c c1 hd h1
    exact k1.trans (recvVectors_calm ns vs c1 _ (k1.dry.trans hd) h2)

/-- A named test. -/
theorem check_calm (name : String) (b : Bool) (c c' : Ctx)
    (h : (Blk.check name b).Yields c () c') : Calm c c' := by
  obtain ⟨h1, h2, h3⟩ := check_frame name b c c' h
  refine Calm.of_ch h1 h2 h3 fun hf => ?_
  unfold Blk.Yields Blk.outcome Blk.check at h
  split at h
  · cases Option.some.inj h
    exact hf
  · cases Option.some.inj h
    cases hf

/-- A named test on what only a run on a view computes. -/
theorem checkOnView_calm (name : String) (f : Unit → Bool) (c c' : Ctx)
    (h : (Blk.checkOnView name f).Yields c () c') : Calm c c' := by
  unfold Blk.Yields Blk.outcome Blk.checkOnView at h
  split at h
  · cases Option.some.inj h
    exact Calm.refl c
  · cases Option.some.inj h
    exact Calm.of_ch rfl rfl rfl fun hf => by cases hf

/-- A round is closed after a stretch within it. -/
theorem Calm.close {c c1 c' : Ctx} (h : Calm c c1) (hd : c.ch.dry = false) (name : String)
    (kind : Fmt.Kind) (nz : Nat) (d : Fmt.Drawn) (hc : (Blk.close name kind nz).Yields c1 d c') :
    Ext n0 g0 sp 1 c c' := by
  obtain ⟨e, es, r, rest, e1, _, _, e4, _, _, _, _, _, e10, e11, _, e13, e14, e15, e16, e17, e18,
    e19, e20⟩ := Blk.close_inv name kind nz d c1 c' (h.dry.trans hd) hc
  refine ⟨by rw [e13, h.st]; exact Old.refl _ _ _ _, BookKeeps.of_eq (e14.trans h.book),
    fun hf => h.failed (by rw [← e15]; exact hf), e16, ⟨[], by rw [e17, h.opened]; rfl⟩,
    Nat.le_of_eq (e18.trans h.roots).symm, e19.trans h.firstTree, e20.trans h.samples, ?_, ?_,
    fun _ _ hI => by rw [e13, h.st]; exact hI, by rw [e13, h.st]; rfl, by rw [e13, h.st]; rfl,
    by rw [e14, h.book, e18, h.roots], by rw [e14, h.book]; rfl, fun _ => e18.trans h.roots,
    pub_same (e19.trans h.firstTree) (e20.trans h.samples) (e18.trans h.roots)
      (by rw [e13, h.st]) (by rw [e14, h.book])⟩
  · rw [e10, List.drop_one, ← h.tail, e4]
    rfl
  · rw [e11, ← h.entries, e1]
    rfl

/-- A round in which one element is drawn is closed. -/
theorem Calm.closeOne {c c1 c' : Ctx} (h : Calm c c1) (hd : c.ch.dry = false) (name : String)
    (kind : Fmt.Kind) (nz : Nat) (x : E) (hc : (Blk.closeOne name kind nz).Yields c1 x c') :
    Ext n0 g0 sp 1 c c' := by
  obtain ⟨d, h1, _⟩ := Blk.closeOne_inv name kind nz x c1 c' hc
  exact h.close hd name kind nz d h1

/-- A round is closed after a stretch within it: what is as it was, and what was drawn. -/
theorem Calm.close_same {c c1 c' : Ctx} (h : Calm c c1) (hd : c.ch.dry = false) (name : String)
    (kind : Fmt.Kind) (nz : Nat) (d : Fmt.Drawn) (hc : (Blk.close name kind nz).Yields c1 d c') :
    c'.st = c.st ∧ c'.book = c.book ∧ c'.ch.opened = c.ch.opened ∧
      c'.ch.firstTree = c.ch.firstTree ∧ c.ch.pending.head?.map (·.drawn) = some d := by
  obtain ⟨e, es, r, rest, _, _, _, e4, _, e6, _, _, _, _, _, _, e13, e14, _, _, e17, _, e19, _⟩ :=
    Blk.close_inv name kind nz d c1 c' (h.dry.trans hd) hc
  refine ⟨e13.trans h.st, e14.trans h.book, e17.trans h.opened, e19.trans h.firstTree, ?_⟩
  rw [← h.drawn, e4, e6]
  rfl

/-! ## The calls of a test -/

/-- An oracle message is marked as spent: an older one that may be, or a new one. -/
theorem spend_ext (o : Nat) (c c' : Ctx) (hd : c.ch.dry = false) (ho : sp o ∨ n0 ≤ o)
    (h : (Blk.spendAsMask o).Yields c () c') : Ext n0 g0 sp 0 c c' := by
  rw [Blk.spendAsMask_inv o c c' h]
  exact Ext.of_st hd (old_spent n0 g0 sp c.st o ho) (fun _ hI h => hI.spent _ o h)
    (Array.size_modify ..) rfl
    (pub_same rfl rfl rfl (pubSt_oracle c.st o _ fun _ => rfl) rfl)

/-- The trees of a prover's message are appended. -/
theorem treesSent_size (first : Nat) : ∀ (l : List TreeShape) (roots : Nat) (trees : Array Tree),
    (treesSent first l roots trees).size = trees.size + l.length
  | [], _, _ => rfl
  | s :: l, roots, trees => by
    show (treesSent first l (roots + 1) (trees.push _)).size = _
    rw [treesSent_size first l, Array.size_push, List.length_cons]
    omega

/-- Entering the oracle messages as parts of their trees makes no tree. -/
theorem partsLaid_size (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (trees : Array Tree) : (partsLaid sent lay n0 base trees).size = trees.size := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih, Array.size_modify]

/-- The book after a prover's message: as many new trees as the message has, and a new place for
each of its oracle messages. -/
theorem bookSent_sizes (c : Ctx) (sent : Array OracleNotice) (lay : TreeLay) :
    (bookSent c sent lay).trees.size = c.book.trees.size + lay.shapes.size ∧
      (bookSent c sent lay).place.size = c.book.place.size + sent.size := by
  constructor
  · show (partsLaid _ _ _ _ _).size = _
    rw [partsLaid_size, treesSent_size, Array.length_toList]
  · show (c.book.place ++ (Array.range sent.size).map _).size = _
    rw [Array.size_append, Array.size_map, Array.size_range]

/-- The statement after a prover's message has its oracle messages more. -/
theorem stSent_size (S : Statement) (sent : Array OracleNotice) :
    (stSent S sent).oracles.size = S.oracles.size + sent.size := by
  show (S.oracles ++ sent.map _).size = _
  rw [Array.size_append, Array.size_map]

/-- Oracle messages are received. Their numbers are those after the statement's. -/
theorem receive_ext (sent : Array OracleNotice) (ids : Array Nat) (c c' : Ctx)
    (hd : c.ch.dry = false) (hn : n0 ≤ c.st.oracles.size) (hpos : 0 < sent.size)
    (h : (Blk.receiveOracles sent).Yields c ids c') :
    ExtG n0 g0 sp 0 sent.size 0 (sentP sent) c c' ∧
      ids = (Array.range sent.size).map (· + c.st.oracles.size) := by
  obtain ⟨lay, hlay, _, hi, rfl⟩ := receiveOracles_inv sent ids c c' hd h
  exact ⟨⟨old_stSent n0 g0 sp c.st sent hn, bookSent_keeps c sent lay, fun h => h, hd, ⟨[], rfl⟩,
    Nat.le_add_right _ _, rfl, rfl, rfl, rfl, fun _ hI h => hI.sent _ sent h, stSent_size _ _, rfl,
    by
      show (bookSent c sent lay).trees.size + c.ch.roots =
        c.book.trees.size + (c.ch.roots + lay.shapes.size)
      rw [(bookSent_sizes c sent lay).1]
      omega, (bookSent_sizes c sent lay).2, fun e0 => absurd e0 (by omega),
    pub_sent c sent lay hlay⟩, hi⟩

/-- Opened columns are read. -/
theorem readOpened_ext (ids : Array Nat) (pos : Positions) (out : Array (Array Column))
    (c c' : Ctx) (hd : c.ch.dry = false) (h : (Blk.readOpened ids pos).Yields c out c') :
    Ext n0 g0 sp 0 c c' := by
  obtain ⟨_, cols, _, hop, _, _, _, hf, hb⟩ := Blk.readOpened_inv ids pos out c c' hd h
  exact ⟨by rw [hf.st]; exact Old.refl _ _ _ _, BookKeeps.of_kept hb,
    fun h => by rw [← hf.failed]; exact h, hf.dry.trans hd, ⟨_, hop⟩, Nat.le_of_eq hf.roots.symm,
    hf.firstTree, hf.samples, hf.pending, hf.entries, fun _ _ hI => by rw [hf.st]; exact hI,
    by rw [hf.st]; rfl, by rw [hf.st]; rfl, by rw [hb.size, hf.roots], by rw [hb.place]; rfl,
    fun _ => hf.roots,
    pub_same hf.firstTree hf.samples hf.roots (by rw [hf.st]) (pubBook_kept hb)⟩

/-- The rows of a complex of single rows are read. -/
theorem singleRowsRead_ext (s : SingleRows) (pos : Positions) (y : Array E) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (singleRowsRead s pos).Yields c y c') :
    Ext n0 g0 sp 0 c c' := by
  unfold singleRowsRead at h
  obtain ⟨opened, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_get _ _ _ _).1 h2
  exact readOpened_ext _ pos opened c _ hd h1

/-! ## FOLD -/

/-- The rounds of a fold. -/
theorem foldRounds_ext : ∀ (n : Nat) (claim : E) (c c' : Ctx) (r : List E × E),
    c.ch.dry = false → (foldRounds n claim).Yields c r c' → Ext n0 g0 sp n c c'
  | 0, _, _, _, _, hd, h => Ext.of_eq hd ((Blk.yields_pure _ _ _ _).1 h).2
  | n + 1, claim, c, c', r, hd, h => by
    have h0 : (Blk.recvE >>= fun c0 => Blk.recvE >>= fun c2 =>
        Blk.closeOne "FOLD round" >>= fun g =>
        foldRounds n (foldClaimRound claim c0 c2 g) >>= fun r =>
        (pure (g :: r.1, r.2) : Blk (List E × E))).Yields c r c' := h
    obtain ⟨c0, x1, h1, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
    obtain ⟨c2, x2, h2, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
    obtain ⟨g, x3, h3, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
    obtain ⟨r', x4, h4, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
    obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h0
    have k1 := recvE_calm c0 c x1 hd h1
    have k2 := recvE_calm c2 x1 x2 (k1.dry.trans hd) h2
    have k3 : Ext n0 g0 sp 1 c x3 := (k1.trans k2).closeOne hd _ _ _ g h3
    exact (k3.trans (foldRounds_ext n _ x3 _ r' k3.dry h4)).cast (Nat.add_comm 1 n)

/-- The end of a fold's first message: the mask is marked as spent (up to c1), and the sum is
received. -/
theorem foldStart_tail (F : FoldShape) (id : Nat) (s : FoldStart) (c c' : Ctx)
    (hd : c.ch.dry = false) (ho : sp id ∨ n0 ≤ id)
    (h : (Blk.statement >>= fun S => Blk.must (foldMaskOk S F id) >>= fun _ =>
      Blk.spendAsMask id >>= fun _ => Blk.recvE >>= fun sum =>
      (pure { shape := F, mask := id, sum := sum } : Blk FoldStart)).Yields c s c') :
    ∃ c1, Ext n0 g0 sp 0 c c1 ∧ Calm c1 c' := by
  obtain ⟨S1, y3, a6, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, hy3⟩ := (Blk.yields_statement _ _ _).1 a6
  rw [hy3] at a7
  obtain ⟨_, y4, a8, a9⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
  obtain ⟨_, hy4⟩ := (Blk.yields_must _ _ _).1 a8
  rw [hy4] at a9
  obtain ⟨_, c1, a10, a11⟩ := (Blk.yields_bind _ _ _ _ _).1 a9
  obtain ⟨sum, y5, a12, a13⟩ := (Blk.yields_bind _ _ _ _ _).1 a11
  obtain ⟨_, hy5⟩ := (Blk.yields_pure _ _ _ _).1 a13
  rw [← hy5] at a12
  have e3 : Ext n0 g0 sp 0 c c1 := spend_ext id c c1 hd ho a10
  exact ⟨c1, e3, recvE_calm sum c1 c' e3.dry a12⟩

/-- A fold's first message: up to c1 no item is taken; then the sum is received. -/
theorem foldStart_ext (F : FoldShape) (mask : Option Nat) (s : FoldStart) (c c' : Ctx)
    (hd : c.ch.dry = false) (hn : n0 ≤ c.st.oracles.size)
    (hm : ∀ o, mask = some o → sp o ∨ n0 ≤ o) (h : (foldStartVerify F mask).Yields c s c') :
    ∃ c1, ExtG n0 g0 sp 0 (if mask.isSome then 0 else 1) 0
      (if mask.isSome then id else sentP #[foldMaskNotice F]) c c1 ∧ Calm c1 c' := by
  unfold foldStartVerify at h
  obtain ⟨S0, y0, a0, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, hy0⟩ := (Blk.yields_statement _ _ _).1 a0
  rw [hy0] at a1
  obtain ⟨_, y1, a2, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, hy1⟩ := (Blk.yields_must _ _ _).1 a2
  rw [hy1] at a3
  cases mask with
  | some id =>
    obtain ⟨o, y2, a4, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
    obtain ⟨ho, hy2⟩ := (Blk.yields_pure _ _ _ _).1 a4
    rw [ho, hy2] at a5
    exact foldStart_tail F id s c c' hd (hm id rfl) a5
  | none =>
    obtain ⟨ids, z1, b1, b2⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
    obtain ⟨o, z2, b3, b4⟩ := (Blk.yields_bind _ _ _ _ _).1 b2
    obtain ⟨hi, hz⟩ := (Blk.yields_get _ _ _ _).1 b3
    rw [hz] at b4
    obtain ⟨e, hids⟩ := receive_ext (n0 := n0) (g0 := g0) (sp := sp) #[foldMaskNotice F] ids c z1
      hd hn Nat.one_pos b1
    have ho : n0 ≤ o := by
      rw [hids] at hi
      simp at hi
      omega
    obtain ⟨c1, e1, m1⟩ := foldStart_tail F o s z1 c' e.dry (Or.inr ho) b4
    exact ⟨c1, ExtG.trans e e1, m1⟩

/-- FOLD. The mask is an older oracle message that may be spent, a new one, or is received. -/
theorem foldVerify_ext (F : FoldShape) (row : GroupRow) (mask : Option Nat) (out : SingleRows)
    (c c' : Ctx) (hd : c.ch.dry = false) (hn : n0 ≤ c.st.oracles.size)
    (hm : ∀ o, mask = some o → sp o ∨ n0 ≤ o) (h : (foldVerify F row mask).Yields c out c') :
    ExtG n0 g0 sp (F.layout.k + 1) (if mask.isSome then 0 else 1) 0
      (if mask.isSome then id else sentP #[foldMaskNotice F]) c c' := by
  unfold foldVerify at h
  obtain ⟨s1, x1, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨s2, x2, k3, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
  obtain ⟨c1, e3, m1⟩ := foldStart_ext (n0 := n0) (g0 := g0) (sp := sp) F mask s1 c x1 hd hn hm k1
  -- the coefficient
  unfold foldEpsilon at k3
  obtain ⟨_, z1, d1, d2⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
  obtain ⟨_, hz1⟩ := (Blk.yields_must _ _ _).1 d1
  rw [hz1] at d2
  obtain ⟨eps, z2, d3, d4⟩ := (Blk.yields_bind _ _ _ _ _).1 d2
  obtain ⟨_, hz2⟩ := (Blk.yields_pure _ _ _ _).1 d4
  rw [← hz2] at d3
  have e4 : Ext n0 g0 sp 1 c1 x2 := m1.closeOne e3.dry _ _ _ eps d3
  -- the rounds
  unfold foldRoundsVerify at k4
  obtain ⟨_, w1, f1, f2⟩ := (Blk.yields_bind _ _ _ _ _).1 k4
  obtain ⟨_, hw1⟩ := (Blk.yields_get _ _ _ _).1 f1
  rw [hw1] at f2
  obtain ⟨_, w2, f3, f4⟩ := (Blk.yields_bind _ _ _ _ _).1 f2
  obtain ⟨_, hw2⟩ := (Blk.yields_must _ _ _).1 f3
  rw [hw2] at f4
  obtain ⟨_, w3, f5, f6⟩ := (Blk.yields_bind _ _ _ _ _).1 f4
  obtain ⟨_, hw3⟩ := (Blk.yields_statement _ _ _).1 f5
  rw [hw3] at f6
  obtain ⟨_, w4, f7, f8⟩ := (Blk.yields_bind _ _ _ _ _).1 f6
  obtain ⟨_, hw4⟩ := (Blk.yields_testOnView _ _ _ e4.dry).1 f7
  rw [hw4] at f8
  obtain ⟨r, w5, f9, f10⟩ := (Blk.yields_bind _ _ _ _ _).1 f8
  obtain ⟨_, hw5⟩ := (Blk.yields_pure _ _ _ _).1 f10
  rw [← hw5] at f9
  have e5 : Ext n0 g0 sp F.layout.k x2 c' := foldRounds_ext _ _ x2 c' r e4.dry f9
  exact (ExtG.trans (ExtG.trans e3 e4) e5).cast (by omega) rfl rfl

/-! ## CS -/

/-- The sending of one sampled oracle message keeps the number of answers to a sample. -/
theorem sendOne_samples (N : OracleNotice) (others : Array OracleNotice) (ids : Array Nat)
    (c c' : Ctx) (hd : c.ch.dry = false) (h1 : N.shape.answers = 1)
    (ho : ∀ n ∈ others, n.shape.answers = 0)
    (h : (sendVerify (#[N] ++ others) false).Yields c ids c') :
    c'.ch.samples = c.ch.samples := by
  obtain ⟨cR, hR, hV⟩ := sendVerify_inv _ _ _ _ _ h
  obtain ⟨lay, _, _, hids, hcR⟩ := receiveOracles_inv _ _ _ _ hd hR
  have hdR : cR.ch.dry = false := by rw [hcR]; exact hd
  have hstR : cR.st = stSent c.st (#[N] ++ others) := by rw [hcR]
  obtain ⟨shapes, drawn, seeds, c1, c2, hsh, hclose, _, _, hrun, hend⟩ :=
    verify_inv ids false cR c' hdR hV
  have htodo : todoOf cR.st ids = [c.st.oracles.size] := by
    rw [hstR, hids]
    exact todo_one c.st N others (by omega) ho
  have hshapes : shapes = [N.shape] := by
    rw [htodo, hstR] at hsh
    simp only [List.mapM_cons, List.mapM_nil, sent_first] at hsh
    exact (Option.some.inj hsh).symm
  subst hshapes
  obtain ⟨e, es, r1, rest1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, k15, _, _, _, k19⟩ :=
    Blk.close_inv _ _ _ _ _ _ hdR hclose
  rw [htodo] at hrun
  obtain ⟨_, c3, ⟨rows, c4, hans, hadm⟩, _, rfl⟩ := hrun
  rw [show (c.st.oracles.size, N.shape).2.answers = 1 from h1] at hans
  obtain ⟨_, c5, ⟨seed, row, alpha, _, _, hrecv, rfl⟩, rfl, rfl⟩ := hans
  obtain ⟨r2, rest, vs, _, _, _, q4⟩ := Blk.recvAnswer_inv _ _ _ k15 hrecv
  obtain ⟨x, places, _, _, _, _, _, a6⟩ := admit_inv _ _ _ _ hadm
  have hc' : c' = c2 := by simpa using hend
  rw [hc', a6]
  refine (q4.samples.trans k19).trans ?_
  rw [hcR]

/-- A code switch keeps the number of answers to a sample. -/
theorem csVerify_samples (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (out : Switched) (row : GroupRow) (lay : GroupLayout)
    (c c' : Ctx) (hd : c.ch.dry = false) (hk : T.kept = #[]) (h1 : T.shape.answers = 1)
    (ho : ∀ n ∈ others, n.shape.answers = 0)
    (h : (csVerify old T gp others).Yields c (out, row, lay) c') :
    c'.ch.samples = c.ch.samples := by
  unfold csVerify at h
  obtain ⟨⟨out', theta⟩, c1, hsw, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨input, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨S, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨row', c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨_, e5⟩ := (Blk.yields_pure _ _ _ _).1 a5
  obtain ⟨ids, cA, code, d, e, cB, y, cC, cD, _, hsend, _, hclose, _, _, _, _, _, hread, hnotes,
    hadm⟩ := switchVerify_inv old T gp others out' theta c c1 hk hsw
  have sA := sendOne_samples ⟨T.shape, T.leafClass⟩ others ids c cA hd h1 ho hsend
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, dA, _⟩ :=
    sendOne_inv ⟨T.shape, T.leafClass⟩ others ids c cA hd h1 ho hsend
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, dB, _, _, _, sB⟩ :=
    Blk.close_inv _ _ _ _ _ _ dA hclose
  have kC := singleRowsRead_ext (n0 := 0) (g0 := 0) (sp := fun _ => False) old _ y cB cC dB hread
  have dD : cD.ch.dry = false := by rw [hnotes.ch]; exact kC.dry
  obtain ⟨_, _, _, _, _, _, e1⟩ := switchAdmit_inv old T gp out' y cD c1 dD hk hadm
  obtain ⟨_, _, _, _, _, _, _, e2⟩ := beginRun_inv _ _ _ _ h2
  have d2 : c2.ch.dry = false := by rw [e2, e1]; exact dD
  obtain ⟨_, _, _, e3⟩ := requireRows_inv _ _ _ d2 h3
  obtain ⟨_, e4⟩ := (Blk.yields_statement _ _ _).1 h4
  have d4 : c4.ch.dry = false := by rw [e4, e3]; exact d2
  obtain ⟨_, e5'⟩ := (Blk.yields_getOnView _ _ _ _ _ d4).1 h5
  rw [e5, e5', e4, e3, e2, e1]
  show cD.ch.samples = _
  rw [hnotes.ch, kC.samples, sB, sA]

/-- Open rows that are added make no oracle message and no group. -/
theorem withRows_sizes (g : Nat) : ∀ (l : List Row) (S : Statement),
    (withRows S g l).oracles.size = S.oracles.size ∧ (withRows S g l).groups.size = S.groups.size
  | [], _ => ⟨rfl, rfl⟩
  | r :: l, S => by
    obtain ⟨a, b⟩ := withRows_sizes g l (withRow S g r)
    exact ⟨a, b.trans (Array.size_modify ..)⟩

/-- The beginning of a test makes no oracle message and no group. -/
theorem begun_sizes (S : Statement) (g : Nat) (G : Group) :
    (begun S g G).oracles.size = S.oracles.size ∧ (begun S g G).groups.size = S.groups.size := by
  constructor
  · exact closeLedgers_size _ _
  · show (Array.modify _ _ _).size = _
    rw [Array.size_modify, closeLedgers_groups]

/-- Closing the new oracle message's ledger makes no oracle message and no group. -/
theorem ledgerShut_sizes (S : Statement) (T : SwitchTarget) (g : Nat) :
    (ledgerShut S T g).oracles.size = S.oracles.size ∧
      (ledgerShut S T g).groups.size = S.groups.size := by
  unfold ledgerShut
  split
  · exact ⟨closeLedgers_size _ _, by rw [closeLedgers_groups]⟩
  · exact ⟨rfl, rfl⟩

/-- A code switch makes the oracle messages that it sends, and no group. -/
theorem CsRan.sizes {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice}
    {c c' : Ctx} {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}
    (r : CsRan old T gp others c c' out row lay theta D) :
    c'.st.oracles.size = c.st.oracles.size + (1 + others.size) ∧
      c'.st.groups.size = c.st.groups.size := by
  rw [r.st]
  constructor
  · rw [(begun_sizes _ _ _).1]
    unfold CsTaken.stR
    rw [(withRows_sizes _ _ _).1]
    unfold CsTaken.stJ
    show (Array.modify _ _ _).size = _
    rw [Array.size_modify, (ledgerShut_sizes _ _ _).1]
    unfold CsTaken.stA
    show (Array.modify _ _ _).size = _
    rw [Array.size_modify, stSent_size]
    show _ + (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others).size = _
    rw [Array.size_append]
    rfl
  · rw [(begun_sizes _ _ _).2]
    unfold CsTaken.stR
    rw [(withRows_sizes _ _ _).2]
    unfold CsTaken.stJ
    show (Array.modify _ _ _).size = _
    rw [Array.size_modify, (ledgerShut_sizes _ _ _).2]
    rfl

/-- Reading the rows of a complex of single rows makes no tree and no place of the book. -/
theorem singleRowsRead_book (s : SingleRows) (pos : Positions) (y : Array E) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (singleRowsRead s pos).Yields c y c') :
    Blk.BookKept c.book c'.book := by
  unfold singleRowsRead at h
  obtain ⟨opened, c1, h1, h2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_get _ _ _ _).1 h2
  obtain ⟨_, _, _, _, _, _, _, _, hb⟩ := Blk.readOpened_inv _ pos opened c _ hd h1
  exact hb

/-- A code switch, on the public part. hs: the number of answers to a sample is as it was. -/
theorem CsRan.part {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice}
    {c c' : Ctx} {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : CsTaken}
    (r : CsRan old T gp others c c' out row lay theta D) (hs : c'.ch.samples = c.ch.samples) :
    pub c' = csP T gp others (pub c) := by
  have e : (layTrees (pub c).st.codes (sentOf T others)).getD {} = D.lay := by
    show (layTrees c.st.codes (sentOf T others)).getD {} = D.lay
    rw [r.trees]
    rfl
  have hst : pubSt c'.st =
      joinP gp (pub c).st.oracles.size false (stSent (pub c).st (sentOf T others)) := by
    rw [r.st, pubSt_begun]
    unfold CsTaken.stR
    rw [pubSt_withRows]
    unfold CsTaken.stJ
    rw [pubSt_joined _ _ _ _ _ r.group, pubSt_ledgerShut]
    unfold CsTaken.stA
    rw [pubSt_admitted, pubSt_stSent]
    show _ = joinP gp (c.st.oracles.map pubOracle).size false _
    rw [Array.size_map]
    rfl
  have hbk : pubBook c'.book = pubBook (bookSent (pub c) (sentOf T others) D.lay) := by
    rw [r.book, pubBook_kept (singleRowsRead_book old _ D.y D.cB D.cC r.dryB r.read), r.bookB,
      pubBook_bookSent]
  unfold csP sentP
  rw [e]
  exact pub_mk c' _ _ _ _ _ r.firstTree hs r.roots hst hbk

/-- CS into a group that was made for it. The oracle messages that ride in the switch's message
have the numbers after the new oracle message's. -/
theorem csVerify_ext (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) (out : Switched) (row : GroupRow) (lay : GroupLayout)
    (c c' : Ctx) (hd : c.ch.dry = false) (hk : T.kept = #[]) (h1 : T.shape.answers = 1)
    (ho : ∀ n ∈ others, n.shape.answers = 0) (hn : n0 ≤ c.st.oracles.size) (hg : g0 ≤ gp)
    (a b : Nat) (ha : a = T.shape.code) (hb : b = T.shape.maskCode)
    (hG : c.st.groups[gp]? = some { code := a, maskCode := b })
    (h : (csVerify old T gp others).Yields c (out, row, lay) c') :
    ExtG n0 g0 sp 2 (1 + others.size) 0 (csP T gp others) c c' ∧
      out.others = (Array.range others.size).map (· + (c.st.oracles.size + 1)) := by
  have hs := csVerify_samples old T gp others out row lay c c' hd hk h1 ho h
  obtain ⟨theta, D, r⟩ := csVerify_inv old T gp others out row lay c c' hd hk h1 ho h
  have eG : D.G = { code := a, maskCode := b } := Option.some.inj (r.group0.symm.trans hG)
  have hmem : ∀ o ∈ (D.grown c).members.toList, n0 ≤ o := by
    intro o hm
    have e : (D.grown c).members = #[c.st.oracles.size] := by
      unfold CsTaken.grown
      rw [eG]
      simp
    rw [e] at hm
    rw [List.mem_singleton.1 hm]
    exact hn
  have hst : Old n0 g0 sp c.st c'.st := by
    rw [r.st]
    exact (((((old_stSent n0 g0 sp c.st (sentOf T others) hn).trans
      (old_admitted n0 g0 sp _ c.st.oracles.size T.shape D.places #[D.sample] hn)).trans
      (old_ledgerShut n0 g0 sp _ T c.st.oracles.size hn)).trans
      (old_joined n0 g0 sp _ gp c.st.oracles.size false D.G hn hg)).trans
      (old_withRows n0 g0 sp gp hg D.rows _)).trans
      (old_begun n0 g0 sp _ gp (D.grown c) hmem hg)
  obtain ⟨l, hl⟩ :=
    (singleRowsRead_ext (n0 := n0) (g0 := g0) (sp := sp) old _ D.y D.cB D.cC r.dryB r.read).opened
  refine ⟨⟨hst, r.bookKeeps, fun hf => by rw [← r.failed]; exact hf, r.dry,
    ⟨l, by rw [r.opened, ← hl, r.openedB]⟩, by rw [r.roots]; exact Nat.le_add_right _ _,
    r.firstTree, hs, ?_, ?_, fun _ hI hS => hI.switch _ _ _ _ _ _ _ _ _ _ _ r
      (by rw [hG, ha, hb]) hS, (CsRan.sizes r).1, (CsRan.sizes r).2, ?_, ?_,
      fun e0 => absurd e0 (by omega), CsRan.part r hs⟩, r.riders⟩
  · rw [r.pending', r.pending]
    rfl
  · rw [r.entries', r.entries]
    rfl
  · rw [r.book, (singleRowsRead_book old _ D.y D.cB D.cC r.dryB r.read).size, r.bookB,
      (bookSent_sizes c _ D.lay).1, r.roots]
    omega
  · rw [r.book, (singleRowsRead_book old _ D.y D.cB D.cC r.dryB r.read).place, r.bookB,
      (bookSent_sizes c _ D.lay).2]
    show _ + (#[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++ others).size = _
    rw [Array.size_append]
    rfl

/-! ## BASE -/

/-- BASE, with a masking oracle that came in an earlier message: an older oracle message that
may be spent, or a new one. What it leaves; and its one reading: the mask is marked as spent (c1);
the columns are read (from a to a') at the list of the positions d that the second of its two rounds
has drawn; up to there no column was read, and none is read after it. Nothing is asked of the two
named tests. -/
theorem baseVerify_cut (R : SingleRows) (star lc : Nat) (c c' : Ctx) (hd : c.ch.dry = false)
    (ho : sp star ∨ n0 ≤ star) (h : (baseVerify R (some star) lc).Yields c () c') :
    Ext n0 g0 sp 2 c c' ∧
    ∃ (code : Code) (c1 a a' : Ctx) (d : Fmt.Drawn) (opened : Array (Array Column)),
      c.st.codes.base[R.code]? = some code ∧ (Blk.spendAsMask star).Yields c () c1 ∧
      (c.ch.pending.drop 1).head?.map (·.drawn) = some d ∧
      (Blk.readOpened ((singleRowsOracles R).push star)
        (Positions.ofDraws code.logN d.poss)).Yields a opened a' ∧
      a.ch.dry = false ∧ a.ch.opened = c.ch.opened ∧ a.book = c.book ∧
      a.ch.firstTree = c.ch.firstTree ∧ a.st = c1.st ∧ c'.ch.opened = a'.ch.opened := by
  unfold baseVerify at h
  obtain ⟨S0, x1, h1, g1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨code, x2, h2, g2⟩ := (Blk.yields_bind _ _ _ _ _).1 g1
  obtain ⟨star', x3, h3, g3⟩ := (Blk.yields_bind _ _ _ _ _).1 g2
  obtain ⟨S, x4, h4, g4⟩ := (Blk.yields_bind _ _ _ _ _).1 g3
  obtain ⟨u5, x5, h5, g5⟩ := (Blk.yields_bind _ _ _ _ _).1 g4
  obtain ⟨u6, x6, h6, g6⟩ := (Blk.yields_bind _ _ _ _ _).1 g5
  obtain ⟨tauS, x7, h7, g7⟩ := (Blk.yields_bind _ _ _ _ _).1 g6
  obtain ⟨lam, x8, h8, g8⟩ := (Blk.yields_bind _ _ _ _ _).1 g7
  obtain ⟨u9, x9, h9, g9⟩ := (Blk.yields_bind _ _ _ _ _).1 g8
  obtain ⟨m, x10, h10, g10⟩ := (Blk.yields_bind _ _ _ _ _).1 g9
  obtain ⟨r, x11, h11, g11⟩ := (Blk.yields_bind _ _ _ _ _).1 g10
  obtain ⟨u12, x12, h12, g12⟩ := (Blk.yields_bind _ _ _ _ _).1 g11
  obtain ⟨left, x13, h13, g13⟩ := (Blk.yields_bind _ _ _ _ _).1 g12
  obtain ⟨u14, x14, h14, g14⟩ := (Blk.yields_bind _ _ _ _ _).1 g13
  obtain ⟨u15, x15, h15, g15⟩ := (Blk.yields_bind _ _ _ _ _).1 g14
  obtain ⟨u16, x16, h16, g16⟩ := (Blk.yields_bind _ _ _ _ _).1 g15
  obtain ⟨⟨pos, more⟩, x17, h17, g17⟩ := (Blk.yields_bind _ _ _ _ _).1 g16
  obtain ⟨u18, x18, h18, g18⟩ := (Blk.yields_bind _ _ _ _ _).1 g17
  obtain ⟨opened, x19, h19, g19⟩ := (Blk.yields_bind _ _ _ _ _).1 g18
  obtain ⟨y, x20, h20, g20⟩ := (Blk.yields_bind _ _ _ _ _).1 g19
  obtain ⟨stars, x21, h21, h22⟩ := (Blk.yields_bind _ _ _ _ _).1 g20
  clear h g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20
  -- the public head
  obtain ⟨eS0, ex1⟩ := (Blk.yields_statement _ _ _).1 h1
  subst x1
  obtain ⟨hcode, ex2⟩ := (Blk.yields_get _ _ _ _).1 h2
  subst x2
  rw [eS0] at hcode
  obtain ⟨est, ex3⟩ := (Blk.yields_pure _ _ _ _).1 h3
  subst x3 star'
  obtain ⟨_, ex4⟩ := (Blk.yields_statement _ _ _).1 h4
  subst x4
  obtain ⟨_, ex5⟩ := (Blk.yields_must _ _ _).1 h5
  subst x5
  have e6 : Ext n0 g0 sp 0 c x6 := spend_ext star c x6 hd ho h6
  -- the first round
  have e8 : Ext n0 g0 sp 1 x6 x8 := (recvE_calm tauS x6 x7 e6.dry h7).closeOne e6.dry _ _ _ lam h8
  obtain ⟨d8, h8', _⟩ := Blk.closeOne_inv _ _ _ lam x7 x8 h8
  obtain ⟨s1, s2, s3, s4, _⟩ := (recvE_calm tauS x6 x7 e6.dry h7).close_same e6.dry _ _ _ d8 h8'
  -- the second round
  obtain ⟨_, ex9⟩ := (Blk.yields_must _ _ _).1 h9
  subst x9
  have m10 := recvVectors_calm _ m x8 x10 e8.dry h10
  have d10 : x10.ch.dry = false := m10.dry.trans e8.dry
  have m11 := recvVectors_calm _ r x10 x11 d10 h11
  have d11 : x11.ch.dry = false := m11.dry.trans d10
  obtain ⟨_, ex12⟩ := (Blk.yields_testOnView _ _ _ d11).1 h12
  subst x12
  obtain ⟨_, ex13⟩ := (Blk.yields_onView _ _ _ _ _ d11).1 h13
  subst x13
  have m14 := Calm.of_notes (Blk.yields_note _ _ _ _ h14)
  have m15 := Calm.of_notes (Blk.yields_note _ _ _ _ h15)
  have m16 := check_calm _ _ _ _ h16
  obtain ⟨d, _, hcl, _, _, _, hpm⟩ := closePositions_inv _ _ _ _ _ h17
  have e17 : Ext n0 g0 sp 1 x8 x17 :=
    ((((m10.trans m11).trans m14).trans m15).trans m16).close e8.dry _ _ _ d hcl
  obtain ⟨t1, t2, t3, t4, t5⟩ :=
    ((((m10.trans m11).trans m14).trans m15).trans m16).close_same e8.dry _ _ _ d hcl
  have hpos : pos = Positions.ofDraws code.logN d.poss := (Prod.mk.inj hpm).1
  -- the reading
  obtain ⟨_, ex18⟩ := (Blk.yields_must _ _ _).1 h18
  subst x18
  have e19 : Ext n0 g0 sp 0 x17 x19 := readOpened_ext _ pos opened x17 x19 e17.dry h19
  obtain ⟨_, ex20⟩ := (Blk.yields_get _ _ _ _).1 h20
  subst x20
  obtain ⟨_, ex21⟩ := (Blk.yields_get _ _ _ _).1 h21
  subst x21
  have m22 := checkOnView_calm _ _ _ _ h22
  have p22 : c'.ch.pending = x19.ch.pending := by
    unfold Blk.Yields Blk.outcome Blk.checkOnView at h22
    split at h22 <;> cases Option.some.inj h22 <;> rfl
  have ex6 := Blk.spendAsMask_inv star c x6 h6
  refine ⟨((((e6.trans e8).trans e17).trans e19).trans (m22.ext e19.dry p22)).cast rfl,
    code, x6, x17, x19, d, opened, hcode, h6, ?_, hpos ▸ h19, e17.dry, ?_, ?_, ?_, t1.trans s1,
    m22.opened⟩
  · have hp8 : x8.ch.pending = c.ch.pending.drop 1 := by
      rw [e8.pending, ex6]
    rw [← hp8]
    exact t5
  · rw [t3, s3, ex6]
  · rw [t2, s2, ex6]
  · rw [t4, s4, ex6]

/-- What BASE leaves. -/
theorem baseVerify_ext (R : SingleRows) (star lc : Nat) (c c' : Ctx) (hd : c.ch.dry = false)
    (ho : sp star ∨ n0 ≤ star) (h : (baseVerify R (some star) lc).Yields c () c') :
    Ext n0 g0 sp 2 c c' := (baseVerify_cut R star lc c c' hd ho h).1

/-! ## The stages, and the whole test -/

/-- The number of rounds that the stages from cur on close: a fold's coefficient and one round for
each row variable, two rounds of a code switch, and two of the base case. -/
def stagesRounds : IoppStage → List IoppStage → Nat
  | _, [] => 2
  | cur, next :: rest => cur.k + 1 + 2 + stagesRounds next rest

/-- The number of rounds that a proximity test closes: the batching's, and the stages'. -/
def testRounds : List IoppStage → Nat
  | [] => 0
  | first :: rest => 1 + stagesRounds first rest

/-- The number of oracle messages that the stages from a stage on make: two for each code switch,
the new tables and what rides with them; one more if the first fold receives its own mask. rest: the
stages after the first of them. -/
def newOracles (mask : Option Nat) (rest : List IoppStage) : Nat :=
  (if mask.isSome then 0 else 1) + 2 * rest.length

/-- What a fold does to the public part: its mask is received, if it has not come. -/
def foldP (mask : Option Nat) (cur : IoppStage) : Ctx → Ctx :=
  if mask.isSome then id else sentP #[foldMaskNotice (ioppFoldShape cur {})]

/-- What the stages from cur on do to the public part, where a sample has one answer and masks
ride: the 1 and the mark true in the text stand where the program has its number of answers and
its mark "ride". mask: the mask of the first fold, if it has come. For each stage but the last: the
fold; a group is made; the code switch into it. -/
def stagesP : Option Nat → IoppStage → List IoppStage → Ctx → Ctx
  | _, _, [] => id
  | mask, cur, next :: rest => fun P =>
    stagesP (some 0) next rest
      (csP (switchTargetStage next.code next.maskCode next.k next.h 1)
        (foldP mask cur P).st.groups.size (stageOthers true next rest)
        (groupP next.code next.maskCode (foldP mask cur P)))

/-- What a whole proximity test does to the public part, where a sample has one answer and masks
ride (stagesP). At other settings it is the term of no run. -/
def testP (fm : Option Nat) : List IoppStage → Ctx → Ctx
  | [] => id
  | first :: rest => stagesP fm first rest

/-- Only whether the mask has come matters. -/
theorem stagesP_some (o : Nat) (cur : IoppStage) (rest : List IoppStage) :
    stagesP (some o) cur rest = stagesP (some 0) cur rest := by
  cases rest <;> rfl

/-- If masks ride, one oracle message rides in a code switch's message. -/
theorem stageOthers_size (next : IoppStage) (rest : List IoppStage) :
    (stageOthers true next rest).size = 1 := by
  unfold stageOthers
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  split <;> rfl

/-- The stages, if masks ride and a sample has one answer. The mask of the first of them is an
older oracle message that may be spent, a new one, or (before a fold) is still to come. -/
theorem stages_ext : ∀ (rest : List IoppStage) (cur : IoppStage) (row : GroupRow)
    (L : GroupLayout) (mask : Option Nat) (c c' : Ctx), c.ch.dry = false →
    n0 ≤ c.st.oracles.size → g0 ≤ c.st.groups.size → (∀ o, mask = some o → sp o ∨ n0 ≤ o) →
    (rest = [] → mask.isSome = true) →
    (ioppStagesVerify 1 true cur rest row L mask).Yields c () c' →
    ExtG n0 g0 sp (stagesRounds cur rest) (newOracles mask rest) rest.length
      (stagesP mask cur rest) c c'
  | [], cur, row, L, mask, c, c', hd, _, _, hm, hl, h => by
    obtain ⟨R, _, hb⟩ := ioppStages_last_inv _ _ _ _ _ _ _ _ h
    obtain ⟨star, rfl⟩ := Option.isSome_iff_exists.1 (hl rfl)
    exact ExtG.cast (baseVerify_ext R star 0 c c' hd (hm star rfl) hb) rfl rfl rfl
  | next :: rest, cur, row, L, mask, c, c', hd, hn, hg, hm, _, h => by
    obtain ⟨rows1, a1, a2, to1, a3, s1, row1, L1, a4, a5, a6, a7, a8, mask1, f1, n1, g1, w1, n2, n3,
      n4, n5, hm1, r1⟩ := ioppStages_step_inv _ _ _ _ _ _ _ _ _ _ h
    have e1 : ExtG n0 g0 sp (cur.k + 1) (if mask.isSome then 0 else 1) 0
        (if mask.isSome then id else sentP #[foldMaskNotice (ioppFoldShape cur L)]) c a1 :=
      foldVerify_ext (ioppFoldShape cur L) row mask rows1 c a1 hd hn hm f1
    have e2 : Ext n0 g0 sp 0 a1 a2 := Ext.of_notes e1.dry (Blk.yields_note _ _ _ _ n1)
    obtain ⟨hto, ea3⟩ := newGroup_inv _ _ _ _ _ g1
    have hg2 : g0 ≤ a2.st.groups.size := hg.trans (ExtG.trans e1 e2).st.gsize
    have hn2 : n0 ≤ a2.st.oracles.size := hn.trans (ExtG.trans e1 e2).st.osize
    have e3 : ExtG n0 g0 sp 0 0 1 (groupP next.code next.maskCode) a2 a3 := by
      rw [ea3]
      exact Ext.of_st e2.dry (old_withGroup n0 g0 sp a2.st _ _ hg2)
        (fun _ hI h => hI.group _ _ _ h) rfl (Array.size_push ..) (pub_group _ _ _)
    have hG3 : a3.st.groups[to1]? = some { code := next.code, maskCode := next.maskCode } := by
      rw [ea3, hto]
      exact withGroup_group _ _ _
    have hn3 : n0 ≤ a3.st.oracles.size := hn2.trans e3.st.osize
    obtain ⟨e4, hrid⟩ := csVerify_ext (n0 := n0) (g0 := g0) (sp := sp) rows1 _ to1 _ s1 row1 L1 a3
      a4 e3.dry rfl rfl (stageOthers_plain true next rest) hn3 (hto ▸ hg2) _ _ rfl rfl hG3 w1
    have e5 : Ext n0 g0 sp 0 a4 a5 := Ext.of_notes e4.dry (Blk.yields_note _ _ _ _ n2)
    have e6 : Ext n0 g0 sp 0 a5 a6 := Ext.of_notes e5.dry (Blk.yields_noteBy _ _ _ _ n3)
    have e7 : Ext n0 g0 sp 0 a6 a7 := Ext.of_notes e6.dry (Blk.yields_note _ _ _ _ n4)
    have e8 : Ext n0 g0 sp 0 a7 a8 := Ext.of_notes e7.dry (Blk.yields_note _ _ _ _ n5)
    have e38 := ExtG.trans (ExtG.trans (ExtG.trans (ExtG.trans e4 e5) e6) e7) e8
    have hmask : mask1.isSome = true ∧ ∀ o, mask1 = some o → sp o ∨ n0 ≤ o := by
      rcases hm1 with ⟨_, hx, hs⟩ | ⟨hf, _⟩
      · refine ⟨hs, fun o ho => Or.inr ?_⟩
        rw [← hx, hrid] at ho
        simp at ho
        omega
      · cases hf
    have e9 := stages_ext rest next row1 L1 mask1 a8 c' e8.dry (hn3.trans e38.st.osize)
      ((hg2.trans e3.st.gsize).trans e38.st.gsize) hmask.2 (fun _ => hmask.1) r1
    obtain ⟨om, hom⟩ := Option.isSome_iff_exists.1 hmask.1
    have hto' : to1 = (foldP mask cur (pub c)).st.groups.size := by
      have e12 := (ExtG.trans e1 e2).part
      have : (pub a2).st.groups.size = a2.st.groups.size := Array.size_map ..
      rw [hto, ← this, e12]
      rfl
    refine ((ExtG.trans (ExtG.trans (ExtG.trans (ExtG.trans e1 e2) e3) e38) e9).castP (by
      show stagesP mask1 next rest (csP _ to1 _ (groupP _ _ _)) = stagesP mask cur (next :: rest) _
      rw [hom, stagesP_some, hto']
      rfl)).cast (by
      show cur.k + 1 + 0 + 0 + (2 + 0 + 0 + 0 + 0) + stagesRounds next rest = _
      rfl) ?_ ?_
    · unfold newOracles
      rw [stageOthers_size, if_pos hmask.1, List.length_cons]
      omega
    · rw [List.length_cons]
      omega

/-- What a whole proximity test on the group g, which was G, has left, and how much it has made. fm:
the mask of its first fold, if it had come. stages: the test's stages. -/
structure TestKept (g : Nat) (G : Group) (fm : Option Nat) (stages : List IoppStage)
    (c c' : Ctx) : Prop where
  /-- the statement's codes -/
  codes : c'.st.codes = c.st.codes
  /-- each older oracle message is as it was, but that a member's ledger is closed; of the mark
  "spent" of the first fold's mask nothing is said -/
  oracle : ∀ o x, c.st.oracles[o]? = some x → ∃ x', c'.st.oracles[o]? = some x' ∧
    SameOracle (fm = some o) (if o ∈ G.members.toList then shut x else x) x'
  /-- each other older group is as it was -/
  group : ∀ g', g' ≠ g → g' < c.st.groups.size → c'.st.groups[g']? = c.st.groups[g']?
  /-- the group that was tested is marked and holds no open row -/
  tested : c'.st.groups[g]? = some { G with inRun := true, rows := #[] }
  /-- what is public of the book -/
  book : BookKeeps c.book c'.book
  /-- if no named test is recorded as failed at the end, none was at the start -/
  failed : c'.failed = none → c.failed = none
  /-- it is no dry run -/
  dry : c'.ch.dry = false
  /-- the opened columns that are left to be read are an end piece of those that were -/
  opened : ∃ l, c.ch.opened = l ++ c'.ch.opened
  /-- no fewer roots have been received -/
  roots : c.ch.roots ≤ c'.ch.roots
  /-- the number of the first tree that this chain sends -/
  firstTree : c'.ch.firstTree = c.ch.firstTree
  /-- the number of answers to a sample -/
  samples : c'.ch.samples = c.ch.samples
  /-- of the view's rounds that were not closed those of the test are gone -/
  pending : c'.ch.pending = c.ch.pending.drop (testRounds stages)
  /-- of the plan's entries those of the test's rounds are gone -/
  entries : c'.ch.entries = c.ch.entries.drop (testRounds stages)
  /-- each property that a test keeps has lasted -/
  inv : ∀ Inv : Statement → Prop, Closed Inv → Inv c.st → Inv c'.st
  /-- the new oracle messages: two for each code switch, and the first fold's mask if it had not
  come; the new groups: one for each code switch -/
  oracles : c'.st.oracles.size = c.st.oracles.size + newOracles fm stages.tail
  groups : c'.st.groups.size = c.st.groups.size + stages.tail.length
  /-- the book has as many new trees as roots were received, and a new place for each new oracle
  message -/
  trees : c'.book.trees.size + c.ch.roots = c.book.trees.size + c'.ch.roots
  places : c'.book.place.size = c.book.place.size + newOracles fm stages.tail
  /-- the public part -/
  part : pub c' = testP fm stages (pub c)

/-- A whole proximity test, on a view, if masks ride and a sample has one answer. -/
theorem ioppVerify_kept (g : Nat) (stages : List IoppStage) (choice : IoppChoice)
    (fm : Option Nat) (c c' : Ctx) (hd : c.ch.dry = false) (hs : c.ch.samples = 1)
    (hr : choice.masksRide = true) (h : (ioppVerify g stages choice fm).Yields c () c') :
    ∃ G, c.st.groups[g]? = some G ∧ G.inRun = false ∧
      TestKept g G fm stages c c' := by
  cases stages with
  | nil =>
    exfalso
    unfold ioppVerify at h
    obtain ⟨answers, ca, _, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨S, cb, _, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
    obtain ⟨_, cc, m3, _⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
    have h3 := ((Blk.yields_must _ _ _).1 m3).1
    simp [ioppOk] at h3
  | cons first rest =>
    obtain ⟨answers, ca, S, cb, row, L, cd, ce, G', cf, k1, k2, k3, k4, k5, k6, _, k8⟩ :=
      ioppVerify_inv g first rest choice fm c c' h
    have ha : answers = c.ch.samples ∧ ca = c := by
      have k1' : (some (c.ch.samples, c) : Option (Nat × Ctx)) = some (answers, ca) := k1
      cases k1'
      exact ⟨rfl, rfl⟩
    obtain ⟨hans, hca⟩ := ha
    obtain ⟨_, hcb⟩ := (Blk.yields_statement _ _ _).1 k2
    rw [hcb, hca] at k4
    obtain ⟨G, x, e, es, r, rs, hb, b1, _, _, b4, _, _, b7, b8, _⟩ :=
      batVerify_inv g row L c cd hd k4
    have nce := Blk.yields_note _ _ _ _ k5
    obtain ⟨_, hcf⟩ := (yields_group _ _ _ _).1 k6
    rw [hcf, hans] at k8
    have hrest : rest ≠ [] := by
      intro e0
      rw [e0] at k3
      simp [ioppOk] at k3
    rw [hs, hr] at k8
    have dce : ce.ch.dry = false := by rw [nce.ch]; exact hb.dry
    have hsz : ce.st = begun c.st g G := nce.st.trans hb.st
    have ho : c.st.oracles.size ≤ ce.st.oracles.size := by
      rw [hsz]
      exact Nat.le_of_eq (closeLedgers_size _ _).symm
    have hgz : c.st.groups.size ≤ ce.st.groups.size := by
      rw [hsz]
      show _ ≤ (Array.modify _ _ _).size
      rw [Array.size_modify, closeLedgers_groups]
    have E := stages_ext (n0 := c.st.oracles.size) (g0 := c.st.groups.size)
      (sp := fun o => fm = some o) rest first row L fm ce c' dce ho hgz
      (fun o h => Or.inl h) (fun h => absurd h hrest) k8
    have hg : g < c.st.groups.size := by
      have := hb.group
      exact (Array.getElem?_eq_some_iff.1 this).1
    obtain ⟨l, hl⟩ := E.opened
    refine ⟨G, hb.group, hb.fresh, ⟨?_, ?_, ?_, ?_, ?_, ?_, E.dry, ⟨l, ?_⟩, ?_, ?_, ?_, ?_, ?_,
      fun I hI hS => E.inv I hI (by rw [hsz]; exact hI.begun _ g G hb.group hS), ?_, ?_, ?_, ?_,
      ?_⟩⟩
    · rw [E.st.codes, hsz]
      exact closeLedgers_codes _ _
    · intro o x hx
      have hlt : o < c.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
      have h1 : ce.st.oracles[o]? = some (if o ∈ G.members.toList then shut x else x) := by
        rw [hsz]
        show (closeLedgers c.st G.members.toList).oracles[o]? = _
        rw [closeLedgers_get, hx]
        rfl
      exact E.st.oracle o _ hlt h1
    · intro g' hne hlt
      rw [E.st.group g' hlt, hsz]
      show (Array.modify _ _ _)[g']? = _
      rw [Array.getElem?_modify, if_neg (fun e => hne e.symm), closeLedgers_groups]
    · rw [E.st.group g hg, hsz]
      show (Array.modify _ _ _)[g]? = _
      rw [Array.getElem?_modify, if_pos rfl, closeLedgers_groups, hb.group]
      rfl
    · exact (BookKeeps.of_eq (nce.book.trans hb.book)).trans E.book
    · intro hf
      have := E.failed hf
      rw [nce.failed, hb.failed] at this
      exact this
    · rw [← hl, nce.ch, hb.opened]
    · have := E.roots
      rw [nce.ch, hb.roots] at this
      exact this
    · rw [E.firstTree, nce.ch, hb.firstTree]
    · rw [E.samples, nce.ch, hb.samples]
    · rw [E.pending, nce.ch, b7, b4]
      show _ = (r :: rs).drop (1 + stagesRounds first rest)
      rw [Nat.add_comm, List.drop_succ_cons]
    · rw [E.entries, nce.ch, b8, b1]
      show _ = (e :: es).drop (1 + stagesRounds first rest)
      rw [Nat.add_comm, List.drop_succ_cons]
    · rw [E.osz, hsz, (begun_sizes _ _ _).1]
      rfl
    · rw [E.gsz, hsz, (begun_sizes _ _ _).2]
      rfl
    · have t := E.trees
      rw [nce.book, hb.book, nce.ch, hb.roots] at t
      exact t
    · rw [E.places, nce.book, hb.book]
      rfl
    · rw [E.part, pub_same (c := c) (c' := ce) (by rw [nce.ch, hb.firstTree])
        (by rw [nce.ch, hb.samples]) (by rw [nce.ch, hb.roots]) (by rw [hsz, pubSt_begun])
        (by rw [nce.book, hb.book])]
      rfl

end OnBytes.Slice.ProxRun
