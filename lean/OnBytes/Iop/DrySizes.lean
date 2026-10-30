-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/DrySizes.lean: the dry run of a block that reads a stored table hangs on the table key's
item and sizes, not on its values.

Why. A chain's description is made from a dry run of the chain's block (`Blk.dryRun`,
OnBytes/Iop/Ground.lean). The block of an entry's chain (`linkVerify`) and the shared part of a
key's and a proof's tail (`linSharedVerify`) take a `TableKey` (OnBytes/Iop/Foldeq.lean): the number
of the statement's item that holds the table, the answers of the table's record, and the record's
seeds. At `record = #[]`, `seeds = []` a key is its item's number alone. Else it holds values that
come from a file and from a hash. This file shows that these values have no part in a dry run.

How. A key is used at four places: the public test `key.fits`, which is a function of the sizes; a
test on the seeds' factors (`Blk.test`), which does nothing in a dry run; the record's rows and a
note, which a dry run does not compute; and the item's number in the stored opening. The piece that
reads the item reads nothing else of a key, so with one item it is one function
(`foldeqColumnsVerify_item`). For the other three: `Ctx.Dry c` says that the run is dry and keeps no
intermediate values. `Blk.Keeps b` says that b leaves these two flags as they are; it is shown of
the blocks that run before the last of these three places. `Blk.DryEq b b'` says that b and b' give
the same result at every dry context: the same value and the same context left, or the same failure.
 - `Blk.Keeps`, with `keeps_pure`, `keeps_bind`, `keeps_ite`, the loops (`keeps_forIn`,
   `keeps_forInA`, `keeps_forM`) and one lemma for each block that is met;
 - `TableKey.Alike k k'`: one item; as many answers; as many seeds, and seed by seed a point of as
   many coordinates. `TableKey.Alike.fits`; `TableKey.alike_of_fits`: two keys that fit one shape
   and name one item are alike;
 - `Ctx.Dry`, `Blk.DryEq`, with `dryEq_bind`, `dryEq_bind2`, `dryEq_bind_left`;
   `dryEq_foldeqRequire`, `dryEq_foldeqJoined`, `foldeqColumnsVerify_item`, `dryEq_foldeqVerify`,
   `dryEq_linSharedVerify`, `dryEq_linkStepsVerify`;
 - `Blk.DryEq.dryRunNamed`: such blocks have one dry run; `linkVerify_dry_alike`: an entry's block
   at two pairs of keys that are alike: the whole dry run, the failure's name and all;
   `linkVerify_rounds_sizes`: so the rounds with their stored openings are the same at all keys that
   fit the shape's table and name the same items.

Main definitions: `Blk.Keeps`, `TableKey.Alike`, `Ctx.Dry`, `Blk.DryEq`.
Main theorems: `TableKey.alike_of_fits`, `dryEq_foldeqVerify`, `dryEq_linSharedVerify`,
`dryEq_linkStepsVerify`, `Blk.DryEq.dryRunNamed`, `linkVerify_dry_alike`, `linkVerify_rounds_sizes`.

Not claimed. NOTHING ON A RUN ON A VIEW: there the decision hangs on the answers and on the seeds.
THAT A CHAIN's DESCRIPTION IS FREE OF THE TABLE: a description is made of the dry run's rounds AND
of the chain's statement, which holds the table's root and answers. That a dry run returns a value
at any shape. At a shape with a record a key without one does not fit, so it is no stand-in for a
key that does. Nothing on where a key's values come from. Nothing on the second chain of a tail,
whose description names trees taken over by root and start. `Blk.Keeps` is shown of the blocks that
are met here, not of every block. `TableKey.Alike` asks more than the proofs use of the seeds. The
laws hold at every start. OnBytes/Proof/TailDry.lean [not in this library] has the law for the
shared chain's whole block; so here read: not proved in this library.

-/
import OnBytes.Iop.Link
import OnBytes.Iop.Lin

set_option autoImplicit false

namespace OnBytes

open Params (IndexShape FoldeqShape LinkShape LinShape)

namespace Blk

/-! ## Blocks that leave the two flags as they are -/

/-- The block leaves the context's two flags as they are: whether the run is dry, and whether
intermediate values are kept. -/
def Keeps {α : Type} (b : Blk α) : Prop :=
  ∀ c a c', b c = .ok (a, c') → c'.ch.dry = c.ch.dry ∧ c'.keepNotes = c.keepNotes

/-- A block that only returns a value keeps the two flags. -/
theorem keeps_pure {α : Type} (a : α) : Keeps (pure a : Blk α) := by
  intro c x c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- A bind whose first block fails, fails so. -/
theorem bind_error {α β : Type} {b : Blk α} {f : α → Blk β} {c : Ctx} {e : Failure}
    (h : b c = .error e) : (b >>= f) c = .error e := by
  show StateT.bind b f c = _
  unfold StateT.bind
  rw [h]
  rfl

/-- A bind whose first block succeeds goes on from its value and context. -/
theorem bind_ok {α β : Type} {b : Blk α} {f : α → Blk β} {c c1 : Ctx} {a : α}
    (h : b c = .ok (a, c1)) : (b >>= f) c = f a c1 := by
  show StateT.bind b f c = _
  unfold StateT.bind
  rw [h]
  rfl

/-- One block after another keeps the two flags, if the first does and the second does at every
value of the first. -/
theorem keeps_bind {α β : Type} {b : Blk α} {f : α → Blk β} (hb : Keeps b)
    (hf : ∀ a, Keeps (f a)) : Keeps (b >>= f) := by
  intro c x c' h
  cases hbc : b c with
  | error e =>
      rw [bind_error hbc] at h
      cases h
  | ok r =>
      obtain ⟨a, c1⟩ := r
      rw [bind_ok hbc] at h
      have h1 := hb c a c1 hbc
      have h2 := hf a c1 x c' h
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- A choice between two blocks that keep the two flags keeps them. -/
theorem keeps_ite {α : Type} {p : Prop} [Decidable p] {x y : Blk α} (hx : Keeps x)
    (hy : Keeps y) : Keeps (if p then x else y) := by
  split
  · exact hx
  · exact hy

/-- A block that always fails keeps the two flags: it leaves no context. -/
theorem keeps_fail {α : Type} (name : String) : Keeps (fail name : Blk α) := by
  intro c a c' h
  cases h

/-- `must` keeps the two flags. -/
theorem keeps_must (b : Bool) (name : String) : Keeps (must b name) := by
  intro c a c' h
  unfold must at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- `test` keeps the two flags. -/
theorem keeps_test (b : Bool) (name : String) : Keeps (test b name) := by
  intro c a c' h
  unfold test at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- `get` keeps the two flags. -/
theorem keeps_get {α : Type} (x : Option α) (name : String) : Keeps (get x name) := by
  intro c a c' h
  unfold get at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- `onView` keeps the two flags. -/
theorem keeps_onView {α : Type} (d : α) (f : Unit → α) : Keeps (onView d f) := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- `getOnView` keeps the two flags. -/
theorem keeps_getOnView {α : Type} (d : α) (f : Unit → Option α) (name : String) :
    Keeps (getOnView d f name) := by
  intro c a c' h
  unfold getOnView at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h

/-- `isDry` keeps the two flags. -/
theorem keeps_isDry : Keeps isDry := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- `samples` keeps the two flags. -/
theorem keeps_samples : Keeps samples := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- `firstTree` keeps the two flags. -/
theorem keeps_firstTree : Keeps firstTree := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- `statement` keeps the two flags. -/
theorem keeps_statement : Keeps statement := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- `setStatement` keeps the two flags. -/
theorem keeps_setStatement (S : Statement) : Keeps (setStatement S) := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- `theBook` keeps the two flags. -/
theorem keeps_theBook : Keeps theBook := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- `setBook` keeps the two flags. -/
theorem keeps_setBook (B : TreeBook) : Keeps (setBook B) := by
  intro c a c' h
  cases h
  exact ⟨rfl, rfl⟩

/-- `note` keeps the two flags. -/
theorem keeps_note (w : String) (v : E) : Keeps (note w v) := by
  intro c a c' h
  unfold note at h
  cases h
  split <;> exact ⟨rfl, rfl⟩

/-- `noteBy` keeps the two flags. -/
theorem keeps_noteBy (w : String) (v : Unit → E) : Keeps (noteBy w v) := by
  intro c a c' h
  unfold noteBy at h
  cases h
  split <;> exact ⟨rfl, rfl⟩

/-- `item` keeps the two flags. -/
theorem keeps_item (i : Fmt.Item) (d : Fmt.ItemValue) : Keeps (item i d) := by
  intro c a c' h
  unfold item at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact ⟨rfl, rfl⟩

/-- `recvRoot` keeps the two flags. -/
theorem keeps_recvRoot : Keeps recvRoot := by
  intro c a c' h
  unfold recvRoot at h
  cases h
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- `close` keeps the two flags. -/
theorem keeps_close (name : String) (kind : Fmt.Kind) (nz : Nat) : Keeps (close name kind nz) := by
  intro c a c' h
  unfold close at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h; exact ⟨rfl, rfl⟩
          · cases h

/-- `onOracle` keeps the two flags. -/
theorem keeps_onOracle (o : Nat) (f : Oracle → Oracle) : Keeps (onOracle o f) := by
  intro c a c' h
  unfold onOracle at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-- `onGroup` keeps the two flags. -/
theorem keeps_onGroup (g : Nat) (f : Group → Group) : Keeps (onGroup g f) := by
  intro c a c' h
  unfold onGroup at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-! ## Loops -/

/-- A loop over a list keeps the two flags, if its body does at every member and every state. -/
theorem keeps_forIn {α β : Type} (f : α → β → Blk (ForInStep β)) (hf : ∀ a s, Keeps (f a s)) :
    ∀ (l : List α) (init : β), Keeps (forIn l init f)
  | [], init => by
      rw [List.forIn_nil]
      exact keeps_pure init
  | a :: l, init => by
      rw [List.forIn_cons]
      refine keeps_bind (hf a init) fun r => ?_
      cases r with
      | done s => exact keeps_pure s
      | yield s => exact keeps_forIn f hf l s

/-- A loop over an array keeps the two flags, if its body does at every member and every state. -/
theorem keeps_forInA {α β : Type} (f : α → β → Blk (ForInStep β)) (hf : ∀ a s, Keeps (f a s))
    (l : Array α) (init : β) : Keeps (forIn l init f) := by
  rw [← Array.forIn_toList]
  exact keeps_forIn f hf l.toList init

/-- `List.forM` keeps the two flags, if the block does at every member. -/
theorem keeps_forM {α : Type} (f : α → Blk PUnit) (hf : ∀ a, Keeps (f a)) :
    ∀ l : List α, Keeps (l.forM f)
  | [] => keeps_pure PUnit.unit
  | a :: l => keeps_bind (hf a) fun _ => keeps_forM f hf l

/-! ## Blocks made of these -/

/-- `oracle` keeps the two flags. -/
theorem keeps_oracle (o : Nat) : Keeps (oracle o) :=
  keeps_bind keeps_statement fun _ => keeps_get _ _

/-- `group` keeps the two flags. -/
theorem keeps_group (g : Nat) : Keeps (group g) :=
  keeps_bind keeps_statement fun _ => keeps_get _ _

/-- `closeEmpty` keeps the two flags. -/
theorem keeps_closeEmpty (name : String) : Keeps (closeEmpty name) :=
  keeps_bind (keeps_close _ _ _) fun _ => keeps_pure _

/-- `closeElems` keeps the two flags. -/
theorem keeps_closeElems (name : String) (nz : Nat) : Keeps (closeElems name nz) :=
  keeps_bind (keeps_close _ _ _) fun _ => keeps_pure _

/-- `recvAnswer` keeps the two flags. -/
theorem keeps_recvAnswer : Keeps recvAnswer := by
  refine keeps_bind (keeps_item _ _) fun g => ?_
  split
  · exact keeps_pure _
  · exact keeps_fail _

/-- `newGroup` keeps the two flags. -/
theorem keeps_newGroup (code maskCode : Nat) : Keeps (newGroup code maskCode) :=
  keeps_bind keeps_statement fun _ => keeps_bind (keeps_get _ _) fun _ =>
    keeps_bind (keeps_get _ _) fun _ => keeps_bind (keeps_must _ _) fun _ =>
      keeps_bind (keeps_setStatement _) fun _ => keeps_pure _

/-- `join` keeps the two flags. -/
theorem keeps_join (g o : Nat) (kept : Bool) : Keeps (join g o kept) :=
  keeps_bind (keeps_group _) fun _ => keeps_bind (keeps_oracle _) fun _ =>
    keeps_bind (keeps_must _ _) fun _ => keeps_bind (keeps_must _ _) fun _ =>
      keeps_bind (keeps_must _ _) fun _ => keeps_bind (keeps_must _ _) fun _ =>
        keeps_bind (keeps_must _ _) fun _ => keeps_bind (keeps_onGroup _ _) fun _ =>
          keeps_onOracle _ _

/-- `addRow` keeps the two flags. -/
theorem keeps_addRow (g : Nat) (row : Row) : Keeps (addRow g row) := by
  unfold addRow
  refine keeps_bind keeps_statement fun _ => keeps_bind (keeps_group _) fun _ =>
    keeps_bind (keeps_must _ _) fun _ => keeps_bind keeps_isDry fun d => ?_
  split
  · exact keeps_pure _
  · exact keeps_bind (keeps_pure _) fun _ => keeps_bind (keeps_must _ _) fun _ =>
      keeps_bind (keeps_must _ _) fun _ => keeps_bind (keeps_must _ _) fun _ =>
        keeps_bind (keeps_must _ _) fun _ => keeps_bind (keeps_test _ _) fun _ =>
          keeps_onGroup _ _

/-- `addRowsOnView` keeps the two flags. -/
theorem keeps_addRowsOnView (g : Nat) (rows : Unit → Option (List Row)) :
    Keeps (addRowsOnView g rows) :=
  keeps_bind (keeps_group _) fun _ => keeps_bind (keeps_must _ _) fun _ =>
    keeps_bind (keeps_getOnView _ _ _) fun _ => keeps_forM _ (keeps_addRow g) _

/-- `receiveOracles` keeps the two flags. -/
theorem keeps_receiveOracles (sent : Array OracleNotice) : Keeps (receiveOracles sent) := by
  unfold receiveOracles
  refine keeps_bind keeps_statement fun _ => keeps_bind keeps_theBook fun _ =>
    keeps_bind keeps_firstTree fun _ => keeps_bind (keeps_must _ _) fun _ =>
      keeps_bind (keeps_must _ _) fun _ => keeps_bind (keeps_get _ _) fun _ => ?_
  refine keeps_bind (keeps_forInA _ (fun _ _ => keeps_bind keeps_recvRoot fun _ =>
    keeps_bind (keeps_pure _) fun _ => keeps_pure _) _ _) fun _ => ?_
  refine keeps_bind (keeps_forIn _ (fun _ _ => keeps_bind (keeps_pure _) fun _ =>
    keeps_pure _) _ _) fun _ => ?_
  exact keeps_bind (keeps_setStatement _) fun _ => keeps_bind (keeps_setBook _) fun _ =>
    keeps_pure _

end Blk

open Blk in
/-- `Send.admit` keeps the two flags. -/
theorem Send.keeps_admit (o : Nat) (rows : Array Row) : Keeps (Send.admit o rows) :=
  keeps_bind keeps_statement fun _ => keeps_bind (keeps_oracle _) fun _ =>
    keeps_bind (keeps_get _ _) fun _ => keeps_bind (keeps_must _ _) fun _ => keeps_onOracle _ _

open Blk in
/-- `Send.verify`, with its two loops, keeps the two flags. -/
theorem Send.keeps_verify (ids : Array Nat) (own : Bool) : Keeps (Send.verify ids own) := by
  unfold Send.verify
  refine keeps_bind keeps_statement fun _ => keeps_bind (keeps_must _ _) fun _ =>
    keeps_bind (keeps_must _ _) fun _ => keeps_bind (keeps_get _ _) fun _ =>
      keeps_bind (keeps_close _ _ _) fun _ => keeps_bind (keeps_get _ _) fun _ =>
        keeps_bind (keeps_test _ _) fun _ => ?_
  refine keeps_bind (keeps_forIn _ (fun x _ => ?_) _ _) fun _ =>
    keeps_ite (keeps_closeEmpty _) (keeps_pure _)
  obtain ⟨o, s⟩ := x
  refine keeps_bind (keeps_forIn _ (fun _ _ => keeps_bind (keeps_get _ _) fun _ =>
    keeps_bind (keeps_get _ _) fun _ => keeps_bind keeps_recvAnswer fun _ =>
      keeps_bind (keeps_pure _) fun _ => keeps_pure _) _ _) fun _ => ?_
  exact keeps_bind (Send.keeps_admit _ _) fun _ => keeps_pure _

open Blk in
/-- `sendVerify` keeps the two flags. -/
theorem keeps_sendVerify (n : Array OracleNotice) (own : Bool) : Keeps (sendVerify n own) :=
  keeps_bind (keeps_receiveOracles _) fun _ => keeps_bind (Send.keeps_verify _ _) fun _ =>
    keeps_pure _

open Blk in
/-- `drawPoint` keeps the two flags. -/
theorem keeps_drawPoint (round : String) (count : Nat) : Keeps (drawPoint round count) :=
  keeps_bind (keeps_closeElems _ _) fun _ => keeps_bind (keeps_must _ _) fun _ => keeps_pure _

open Blk in
/-- `foldeqRequire` keeps the two flags. -/
theorem keeps_foldeqRequire (key : TableKey) (S : FoldeqShape) : Keeps (foldeqRequire key S) :=
  keeps_bind keeps_statement fun _ => keeps_bind (keeps_must _ _) fun _ =>
    keeps_bind (keeps_must _ _) fun _ => keeps_test _ _

open Blk in
/-- `foldeqJoined` keeps the two flags. -/
theorem keeps_foldeqJoined (S : FoldeqShape) (key : TableKey) (e : Array E) (o g : Nat) :
    Keeps (foldeqJoined S key e o g) :=
  keeps_bind keeps_statement fun _ => keeps_bind (keeps_join _ _ _) fun _ =>
    keeps_bind (keeps_addRowsOnView _ _) fun _ => keeps_pure _

/-! ## Two keys of one item and the same sizes -/

/-- Two keys name one item and have the same sizes: as many answers in the record, as many seeds,
and seed by seed a point of as many coordinates. -/
def TableKey.Alike (k k' : TableKey) : Prop :=
  k.item = k'.item ∧ k.record.size = k'.record.size ∧
    k.seeds.map (·.z.length) = k'.seeds.map (·.z.length)

/-- Whether a list's members all have a property of one number each hangs on the list of these
numbers. -/
private theorem all_of_map {α : Type} (f : α → Nat) (p : Nat → Bool) :
    ∀ l : List α, (l.all fun x => p (f x)) = (l.map f).all p
  | [] => rfl
  | a :: l => by
      rw [List.all_cons, List.map_cons, List.all_cons, all_of_map f p l]

/-- Whether a key fits a shape hangs on its sizes alone. -/
theorem TableKey.Alike.fits {k k' : TableKey} (a : k.Alike k') (s : IndexShape) :
    k.fits s = k'.fits s := by
  have hl : k.seeds.length = k'.seeds.length := by
    have := congrArg List.length a.2.2
    rwa [List.length_map, List.length_map] at this
  unfold TableKey.fits
  rw [a.2.1, hl, all_of_map (·.z.length) (· == s.cubeBits) k.seeds,
    all_of_map (·.z.length) (· == s.cubeBits) k'.seeds, a.2.2]

/-- Two lists of one length whose members all have one number. -/
private theorem map_eq_of_all {α : Type} (f : α → Nat) (n : Nat) :
    ∀ l l' : List α, l.length = l'.length → (l.all fun x => f x == n) = true →
      (l'.all fun x => f x == n) = true → l.map f = l'.map f
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | a :: l, b :: l', h, h1, h2 => by
      rw [List.all_cons, Bool.and_eq_true] at h1 h2
      rw [List.map_cons, List.map_cons, map_eq_of_all f n l l' (Nat.succ.inj h) h1.2 h2.2,
        eq_of_beq h1.1, eq_of_beq h2.1]

/-- Two keys that fit one shape and name one item are alike. -/
theorem TableKey.alike_of_fits {k k' : TableKey} {s : IndexShape} (h : k.fits s = true)
    (h' : k'.fits s = true) (hi : k.item = k'.item) : k.Alike k' := by
  unfold TableKey.fits at h h'
  rw [Bool.and_eq_true, Bool.and_eq_true] at h h'
  refine ⟨hi, (eq_of_beq h.1.1).trans (eq_of_beq h'.1.1).symm, ?_⟩
  exact map_eq_of_all (·.z.length) s.cubeBits k.seeds k'.seeds
    ((eq_of_beq h.1.2).trans (eq_of_beq h'.1.2).symm) h.2 h'.2

/-! ## At a dry context the pieces that see a key give the same result -/

/-- The run is dry and keeps no intermediate values. -/
def Ctx.Dry (c : Ctx) : Prop := c.ch.dry = true ∧ c.keepNotes = false

namespace Blk

/-- Two blocks give the same result at every dry context: the same value and the same context left,
or the same failure. -/
def DryEq {α : Type} (b b' : Blk α) : Prop := ∀ c, c.Dry → b c = b' c

/-- A block gives the same result as itself. -/
theorem DryEq.refl {α : Type} (b : Blk α) : DryEq b b := fun _ _ => rfl

/-- After one block that keeps the flags: two continuations that agree at dry contexts. -/
theorem dryEq_bind {α β : Type} {b : Blk α} {f f' : α → Blk β} (hb : Keeps b)
    (hf : ∀ a, DryEq (f a) (f' a)) : DryEq (b >>= f) (b >>= f') := by
  intro c hc
  cases hbc : b c with
  | error e => rw [bind_error hbc, bind_error hbc]
  | ok r =>
      obtain ⟨a, c1⟩ := r
      rw [bind_ok hbc, bind_ok hbc]
      have h1 := hb c a c1 hbc
      exact hf a c1 ⟨h1.1.trans hc.1, h1.2.trans hc.2⟩

/-- Two first blocks that agree at dry contexts, of which the first keeps the flags. -/
theorem dryEq_bind2 {α β : Type} {b b' : Blk α} {f f' : α → Blk β} (hb : Keeps b)
    (hbb : DryEq b b') (hf : ∀ a, DryEq (f a) (f' a)) : DryEq (b >>= f) (b' >>= f') := by
  intro c hc
  have e := hbb c hc
  cases hbc : b c with
  | error e0 =>
      rw [bind_error hbc, bind_error (e ▸ hbc)]
  | ok r =>
      obtain ⟨a, c1⟩ := r
      rw [bind_ok hbc, bind_ok (e ▸ hbc)]
      have h1 := hb c a c1 hbc
      exact hf a c1 ⟨h1.1.trans hc.1, h1.2.trans hc.2⟩

/-- At a dry context a test on values does nothing, whatever its condition. -/
theorem dryEq_test (b b' : Bool) (name : String) : DryEq (test b name) (test b' name) := by
  intro c hc
  unfold test
  rw [hc.1, Bool.or_true, Bool.or_true]

/-- At a dry context a note by a thunk does nothing, whatever the thunk. -/
theorem dryEq_noteBy (w : String) (v v' : Unit → E) : DryEq (noteBy w v) (noteBy w v') := by
  intro c hc
  unfold noteBy
  rw [hc.2]
  rfl

/-- At a dry context a value that only a run on a view computes is the default, whatever the thunk.
-/
theorem dryEq_getOnView {α : Type} (d : α) (f f' : Unit → Option α) (name : String) :
    DryEq (getOnView d f name) (getOnView d f' name) := by
  intro c hc
  unfold getOnView
  rw [if_pos hc.1, if_pos hc.1]

/-- At a dry context rows that only a run on a view computes are not added, whatever the thunk. -/
theorem dryEq_addRowsOnView (g : Nat) (r r' : Unit → Option (List Row)) :
    DryEq (addRowsOnView g r) (addRowsOnView g r') :=
  dryEq_bind (keeps_group _) fun _ => dryEq_bind (keeps_must _ _) fun _ =>
    dryEq_bind2 (keeps_getOnView _ _ _) (dryEq_getOnView _ _ _ _) fun _ => DryEq.refl _

end Blk

open Blk in
/-- The conditions before anything is read give the same result at two keys that are alike: whether
a key fits hangs on its sizes, and the test on the seeds' factors does nothing in a dry run. -/
theorem dryEq_foldeqRequire {k k' : TableKey} (a : k.Alike k') (S : FoldeqShape) :
    DryEq (foldeqRequire k S) (foldeqRequire k' S) := by
  unfold foldeqRequire
  rw [a.fits S.index]
  exact dryEq_bind keeps_statement fun _ => dryEq_bind (keeps_must _ _) fun _ =>
    dryEq_bind (keeps_must _ _) fun _ => dryEq_test _ _ _

open Blk in
/-- The piece that adds the record's rows gives the same result AT ANY TWO KEYS: a dry run does not
compute these rows. -/
theorem dryEq_foldeqJoined (k k' : TableKey) (S : FoldeqShape) (e : Array E) (o g : Nat) :
    DryEq (foldeqJoined S k e o g) (foldeqJoined S k' e o g) :=
  dryEq_bind keeps_statement fun _ => dryEq_bind (keeps_join _ _ _) fun _ =>
    dryEq_bind2 (keeps_addRowsOnView _ _) (dryEq_addRowsOnView _ _ _) fun _ => DryEq.refl _

/-- This piece sees the key's item alone. -/
theorem foldeqColumnsVerify_item {k k' : TableKey} (h : k.item = k'.item) (S : FoldeqShape)
    (e : Array E) (pos : Positions) (first : Nat) (u : FoldedRow) (g : Nat) :
    foldeqColumnsVerify k S e pos first u g = foldeqColumnsVerify k' S e pos first u g := by
  unfold foldeqColumnsVerify
  rw [h]

namespace Blk

/-- At a dry context a note by a thunk does nothing. -/
theorem dryEq_noteBy_pure (w : String) (v : Unit → E) : DryEq (noteBy w v) (pure ()) := by
  intro c hc
  unfold noteBy
  rw [hc.2]
  rfl

/-- The relation can be turned round. -/
theorem DryEq.symm {α : Type} {b b' : Blk α} (h : DryEq b b') : DryEq b' b :=
  fun c hc => (h c hc).symm

end Blk

open Blk in
/-- **The block for one table gives the same result (`Blk.DryEq`) at two keys that are alike.** -/
theorem dryEq_foldeqVerify {k k' : TableKey} (a : k.Alike k') (S : FoldeqShape) (gamma : List E)
    (g : Nat) (others : Array OracleNotice) :
    DryEq (foldeqVerify k S gamma g others) (foldeqVerify k' S gamma g others) := by
  unfold foldeqVerify
  refine dryEq_bind2 (keeps_foldeqRequire _ _) (dryEq_foldeqRequire a S) fun _ =>
    dryEq_bind (keeps_must _ _) fun _ => dryEq_bind (keeps_onView _ _) fun e =>
      dryEq_bind (keeps_sendVerify _ _) fun ids =>
        dryEq_bind2 (keeps_foldeqJoined _ _ _ _ _) (dryEq_foldeqJoined k k' S _ _ _) fun u =>
          dryEq_bind (keeps_note _ _) fun _ => ?_
  simp only [foldeqColumnsVerify_item a.1]
  cases k.seeds.head? <;> cases k'.seeds.head?
  · exact DryEq.refl _
  · exact dryEq_bind2 (keeps_pure _) (dryEq_noteBy_pure _ _).symm fun _ => DryEq.refl _
  · exact dryEq_bind2 (keeps_noteBy _ _) (dryEq_noteBy_pure _ _) fun _ => DryEq.refl _
  · exact dryEq_bind2 (keeps_noteBy _ _) (dryEq_noteBy _ _ _) fun _ => DryEq.refl _

namespace Blk

/-- Two first blocks that agree at dry contexts, before one continuation. -/
theorem dryEq_bind_left {α β : Type} {b b' : Blk α} (f : α → Blk β) (h : DryEq b b') :
    DryEq (b >>= f) (b' >>= f) := by
  intro c hc
  have e := h c hc
  cases hbc : b c with
  | error e0 => rw [bind_error hbc, bind_error (e ▸ hbc)]
  | ok r =>
      obtain ⟨a, c1⟩ := r
      rw [bind_ok hbc, bind_ok (e ▸ hbc)]

end Blk

open Blk in
/-- Closes a goal `Keeps b` for the blocks of this file. -/
local macro "keeps1" : tactic => `(tactic| first
  | exact keeps_statement | exact keeps_samples | exact keeps_must _ _ | exact keeps_get _ _
  | exact keeps_pure _ | exact keeps_drawPoint _ _ | exact keeps_newGroup _ _
  | exact keeps_sendVerify _ _ | exact keeps_foldeqRequire _ _
  | exact keeps_foldeqJoined _ _ _ _ _ | exact keeps_note _ _ | exact keeps_group _
  | exact keeps_ite (keeps_newGroup _ _) (keeps_pure _))

open Blk in
/-- **The shared part up to the row (Fold) gives the same result (`Blk.DryEq`) at two keys that are
alike.** -/
theorem dryEq_linSharedVerify {k k' : TableKey} (a : k.Alike k') (S : LinShape) :
    DryEq (linSharedVerify S k) (linSharedVerify S k') := by
  unfold linSharedVerify
  refine dryEq_bind (by keeps1) fun _ => dryEq_bind (by keeps1) fun _ =>
    dryEq_bind (by keeps1) fun _ => dryEq_bind (by keeps1) fun _ => ?_
  dsimp only
  split
  · exact dryEq_bind (by keeps1) fun _ => dryEq_bind (by keeps1) fun _ =>
      dryEq_bind_left _ (dryEq_foldeqVerify a _ _ _ _)
  · exact dryEq_bind (by keeps1) fun _ => dryEq_bind (by keeps1) fun _ =>
      dryEq_bind_left _ (dryEq_foldeqVerify a _ _ _ _)

open Blk in
/-- **The link's steps give the same result (`Blk.DryEq`) at two pairs of keys that are alike.** -/
theorem dryEq_linkStepsVerify {k0 k0' k1 k1' : TableKey} (a0 : k0.Alike k0') (a1 : k1.Alike k1')
    (S : LinkShape) : DryEq (linkStepsVerify S k0 k1) (linkStepsVerify S k0' k1') := by
  unfold linkStepsVerify
  simp only [foldeqColumnsVerify_item a0.1, foldeqColumnsVerify_item a1.1]
  refine dryEq_bind (by keeps1) fun _ => dryEq_bind (by keeps1) fun _ =>
    dryEq_bind (by keeps1) fun _ =>
      dryEq_bind2 (by keeps1) (dryEq_foldeqRequire a0 _) fun _ =>
        dryEq_bind2 (by keeps1) (dryEq_foldeqRequire a1 _) fun _ =>
          dryEq_bind (by keeps1) fun _ => dryEq_bind (by keeps1) fun _ =>
            dryEq_bind (by keeps1) fun _ => ?_
  split
  · exact dryEq_bind (keeps_bind (keeps_get _ _) fun _ => keeps_pure _) fun _ =>
      dryEq_bind (by keeps1) fun _ =>
        dryEq_bind2 (by keeps1) (dryEq_foldeqJoined k0 k0' _ _ _ _) fun _ =>
          dryEq_bind (by keeps1) fun _ =>
            dryEq_bind_left _ (dryEq_foldeqJoined k1 k1' _ _ _ _)
  · exact dryEq_bind (by keeps1) fun _ =>
      dryEq_bind (by keeps1) fun _ =>
        dryEq_bind2 (by keeps1) (dryEq_foldeqJoined k0 k0' _ _ _ _) fun _ =>
          dryEq_bind (by keeps1) fun _ =>
            dryEq_bind_left _ (dryEq_foldeqJoined k1 k1' _ _ _ _)

/-! ## The dry runs -/

namespace Blk

/-- Two blocks that give the same result at every dry context have one dry run, the failure's name
and all. -/
theorem DryEq.dryRunNamed {α : Type} {b b' : Blk α} (h : DryEq b b') (s : Start) :
    b.dryRunNamed s = b'.dryRunNamed s := by
  have e : b.runNamed s true [] [] = b'.runNamed s true [] [] := by
    unfold runNamed
    split
    · exact h _ ⟨rfl, rfl⟩
    · rfl
  unfold Blk.dryRunNamed
  rw [e]

end Blk

open Blk in
/-- **An entry's block: the whole dry run, the failure's name and all, is the same at two pairs of
keys that are alike.** -/
theorem linkVerify_dry_alike (S : LinkShape) {k0 k0' k1 k1' : TableKey} (st : Start)
    (a0 : k0.Alike k0') (a1 : k1.Alike k1') :
    (linkVerify S k0 k1).dryRunNamed st = (linkVerify S k0' k1').dryRunNamed st :=
  DryEq.dryRunNamed (dryEq_bind_left _ (dryEq_linkStepsVerify a0 a1 S)) st

/-- **The rounds that an entry's block states, each with the stored trees that it opens, are the
same at all keys that fit the shape's table and name the same items.** -/
theorem linkVerify_rounds_sizes {S : LinkShape} {k0 k0' k1 k1' : TableKey} (st : Start)
    (f0 : k0.fits S.table = true) (f0' : k0'.fits S.table = true) (f1 : k1.fits S.table = true)
    (f1' : k1'.fits S.table = true) (i0 : k0.item = k0'.item) (i1 : k1.item = k1'.item) :
    (linkVerify S k0 k1).rounds st = (linkVerify S k0' k1').rounds st := by
  unfold Blk.rounds Blk.dryRun
  rw [linkVerify_dry_alike S st (TableKey.alike_of_fits f0 f0' i0)
    (TableKey.alike_of_fits f1 f1' i1)]

end OnBytes

#print axioms OnBytes.TableKey.alike_of_fits
#print axioms OnBytes.dryEq_foldeqVerify
#print axioms OnBytes.dryEq_linSharedVerify
#print axioms OnBytes.linkVerify_dry_alike
#print axioms OnBytes.linkVerify_rounds_sizes
