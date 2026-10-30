-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadLeaf.lean: at one listed position of an opening as the program's reader has read
it, the bottom level of the vertices met holds the format's leaf hash of the column and the salt as
read, written out: for the trees at the sender's run's value, for the stored table at the
configuration's digest.

Statements and proofs. OnBytes/Maker/ReadNodes.lean says it of all listed positions at once, in the
letters of the library's list of leaf digests (`Run.WalkTie.leafV`). Here it is said of one member
of what an opening lists (`listed`, OnBytes/Maker/Tables.lean: position, column, salt).

Main names:
  `leafHash h sh start x col s0`: the format's hash call for a leaf (`Fmt.leafW`, Fmt/Rules7.lean):
    the number 164, or 174 for a stored table; in the label's first word the tree's number, the
    column's and the salt's numbers of words; in the second 2 ^ a + x; the start; the bytes of the
    column, the fill and the salt (`Fmt.leafBytes`).
  `leafHash_eq`: it is `Fmt.leafW` by its body.
  `zip_leafV`: a member of the positions laid beside columns and salts, in the list of leaf digests.
  `opening_leaf`: one opening that the reader of an opening has handed out.
  `own_leaf`: a tree's opening, at the start `runOfTree W r j`.
  `trace_storedAt`, `stored_readAt`: a stored table's opening was read at the start cfg.
  `stored_leaf`: a stored table's opening, at the second chain's configuration's digest.
Under "there is": in `own_leaf` the start, fixed by `runOfTree W r z.1 = some start`; in
`StoredReadAt` and `stored_readAt` the field, the bytes of a salt, the file and the place of the
reader's call, which nothing else ties, though `trace_storedAt`'s proof lays the plan's field, the
table's own bytes of a salt and the chain's file.
Limits: these are identities of computations at the format's hash. Nothing ties them to another
verifier's hash. The premises of OnBytes/Maker/TableChain.lean and StoredRoot.lean are asked here
too. Nothing on soundness (index binding included), what a root fixes, opening-form binding, no two
openings of a commitment, correctness of extraction or whatever else names a committer or a prover.
Which hash: h is a letter in `leafHash`, `leafHash_eq`, `zip_leafV`, `opening_leaf`, `StoredReadAt`
and `trace_storedAt`; `own_leaf`, `stored_readAt` and `stored_leaf` are at the fixed `Fmt.formatHash`; at a
letter h: `own_leafH`, `stored_readAtH`, `stored_leafH` (OnBytes/Maker/Page/OwesH.lean).

-/
import OnBytes.Maker.StoredRoot

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ _root_.Run.WalkTie OnBytes.Tie
open OnBytes.Three (rootsIn)
open OnBytes.Params (Rounds)

/-- The format's hash call for a leaf. -/
def leafHash (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (sh : Fmt.Shape)
    (start : ByteArray) (x : ℕ) (col : List UInt64) (s0 : ByteArray) : ByteArray :=
  h (Fmt.leafNo sh.stored) (Fmt.leafPlace sh.tree col.length (s0.size / 8)) (2 ^ sh.a + x) start
    (Fmt.leafBytes col s0)

/-- It is the format's own. -/
theorem leafHash_eq (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (sh : Fmt.Shape)
    (start : ByteArray) (x : ℕ) (col : List UInt64) (salt : ByteArray) :
    leafHash h sh start x col salt =
      Fmt.leafW (m := Id) h (Fmt.leafNo sh.stored) sh.tree sh.a x start col salt := rfl

/-- A member of the positions laid beside columns and salts, in the list of leaf digests. -/
theorem zip_leafV (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (sh : Fmt.Shape)
    (start : ByteArray) : ∀ (xs : List ℕ) (cs : List (List UInt64 × ByteArray)) (x : ℕ)
      (c : List UInt64 × ByteArray), (x, c) ∈ xs.zip cs →
    (x, leafHash h sh start x c.1 c.2) ∈ xs.zip (leafV h sh start xs cs)
  | [], _, _, _, hm => by simp at hm
  | _ :: _, [], _, _, hm => by simp at hm
  | x0 :: xs, c0 :: cs, x, c, hm => by
    rw [List.zip_cons_cons] at hm
    show _ ∈ (x0, _) :: xs.zip (leafV h sh start xs cs)
    rcases List.mem_cons.1 hm with e | hm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (zip_leafV h sh start xs cs x c hm)

/-- **One opening that the reader of an opening has handed out, at one listed position.** -/
theorem opening_leaf (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray) (cfg : ByteArray)
    (f : Fmt.Fld) (sb : ℕ) (start b : ByteArray) (i : ℕ) (z : Opened)
    (e : Fmt.readOpeningW (m := Id) h cfg f sb z.1 start z.2.1 b i = some z.2.2) :
    ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), (x, col, salt) ∈ listed z →
      seenAt z.2.2.seen z.1.a x = some (leafHash h z.1 start x col salt) := fun x col salt hm =>
  (opening_nodes h cfg f sb z.1 start z.2.1 b i z.2.2 e).2.1 _
    (zip_leafV h z.1 start z.2.1 _ x (col, salt) hm)

/-- **A tree's opening, at the start that the tables lay.** -/
theorem own_leaf {R₁ R₂ R₃ : Rounds} {r : Proof.TailRead}
    (h₁ : rootsIn R₁ = r.first.roots.length) (h₂ : rootsIn R₂ = r.shared.roots.length)
    (h₃ : rootsIn R₃ = r.second.roots.length) {z : ℕ × Opened}
    (O : OpensTree (Three.Whole.of R₁ R₂ R₃) r z) :
    ∃ start, runOfTree (Three.Whole.of R₁ R₂ R₃) r z.1 = some start ∧
      ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray), (x, col, salt) ∈ listed z.2 →
        seenAt z.2.2.2.seen z.2.1.a x = some (leafHash Fmt.formatHash z.2.1 start x col salt) := by
  obtain ⟨start, hs, cfg, f, sb, b, i, e⟩ := opensTree_run h₁ h₂ h₃ O
  exact ⟨start, hs, opening_leaf Fmt.formatHash cfg f sb start b i z.2 e⟩

/-! ## The stored table -/

/-- Of a description's round and a round as read: in front stand the stored tables' openings, each
read at the start cfg. -/
def StoredReadAt (h : HId) (cfg : ByteArray) (x : Fmt.Round × List Fmt.Stored)
    (ro : Fmt.RoundOut) : Prop :=
  ∃ cs co : List OpenedY, ro.opens = cs ++ co ∧
    List.Forall₂ (fun (_ : Fmt.Stored) (y : OpenedY) => ∃ (f : Fmt.Fld) (sb : ℕ) (b : ByteArray)
      (i : ℕ), Fmt.readOpeningW (m := Id) h cfg f sb y.1 cfg y.2.1 b i = some y.2.2) x.2 cs

theorem trace_storedAt (h : HId) (cfg st : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) : ∀ (xs : List (Fmt.Round × List Fmt.Stored)) (ros : List Fmt.RoundOut)
      (c : Fmt.Chain) (roots : Array ByteArray), TraceX h cfg st P run b xs ros c roots →
    List.Forall₂ (StoredReadAt h cfg) xs ros
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, _, T => T.elim
  | _ :: _, [], _, _, T => T.elim
  | x :: xs, ro :: ros, c, roots, T => by
    obtain ⟨R, T'⟩ := T
    refine .cons ?_ (trace_storedAt h cfg st P run b xs ros _ _ T')
    obtain ⟨cs, co, ho, h1, -⟩ := R.opens
    refine ⟨cs, co, ho, h1.imp fun t y hy => ?_⟩
    obtain ⟨root, -, O⟩ := hy
    obtain ⟨i, hi⟩ := O.read
    exact ⟨P.field, t.salt, b, i, by rw [O.shape, O.list]; exact hi⟩

/-- One chain: each member of `storedRows` was read at the start cfg. -/
theorem stored_readAt (W : Three.Whole) (ds : List Three.RDL) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j))
    (F : DataFits W (S.base.rounds.zip S.stored) ds) :
    ∀ y ∈ storedRows ds o, ∃ (f : Fmt.Fld) (sb : ℕ) (b' : ByteArray) (k : ℕ),
      Fmt.readOpeningW (m := Id) Fmt.formatHash S.base.cfg f sb y.2.1 S.base.cfg y.2.2.1 b' k =
        some y.2.2.2 := by
  obtain ⟨-, -, -, -, T⟩ := readChain_trace S seen b i o j e
  have R := trace_storedAt Fmt.formatHash _ _ _ _ b _ _ _ _ T
  have F' : List.Forall₂ (fun (x : Fmt.Round × List Fmt.Stored) (d : Three.RDL) =>
      RoundData W (keyOf x) d) (S.base.rounds.zip S.stored) ds := List.forall₂_map_left_iff.1 F
  rintro ⟨t, z⟩ hy
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hy
  obtain ⟨x, ⟨hx, -⟩, cs, co, ho, h1⟩ := (List.forall₂_iff_zip.1 (forall₂_join R F')).2 hp
  have hx' : x.2 = d.stored := hx
  rw [hx'] at h1
  have hin' : (t, z) ∈ d.stored.zip ro.opens := hin
  rw [ho, zip_append_more _ _ _ h1.length_eq] at hin'
  exact (List.forall₂_iff_zip.1 h1).2 hin'

/-- **A stored table's opening, at one listed position**: the leaf's hash at the second chain's
configuration's digest. -/
theorem stored_leaf (W : Three.Whole) (sb a : ℕ) (S₁ S₂ S₃ : Fmt.SpecX)
    (F : FileFits W sb a S₁ S₂ S₃) (hs : StoredSecond W) (r : Proof.TailRead) (b : ByteArray)
    (n₂ : Fmt.Seen) (i₂ j₂ : ℕ) (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂)) :
    ∀ y ∈ storedRowsW W r, ∀ (x : ℕ) (col : List UInt64) (salt : ByteArray),
      (x, col, salt) ∈ listed y.2 →
      seenAt y.2.2.2.seen y.2.1.a x = some (leafHash Fmt.formatHash y.2.1 S₂.base.cfg x col salt) := by
  intro y hy
  obtain ⟨f, sb', b', k, e⟩ :=
    stored_readAt W W.ds₂ S₂ n₂ b i₂ _ j₂ e₂ F.d₂ y (storedW_second hs hy)
  exact opening_leaf Fmt.formatHash _ f sb' _ b' k y.2 e

end OnBytes.Maker
