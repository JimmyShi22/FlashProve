-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/Entry.lean: from a typed proof string of the entry's file (the written link
over letters: OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up, OnBytes/Flat/LinkSib.lean) back to a parsed leaf
file (`LeafP`, Johnson/PV/EntryInOf.lean): the way against the typing `assembleW`
(Johnson/RunOne/StrictLinkW.lean). And: what is printed comes back.

Why. The goals' verifier takes a form that holds parsed files as bytes, and lays typed proof strings
of them. An honest prover makes typed proof strings. To hand them over they have to be written down.
The like for a key file or a proof file: OnBytes/Prover/Print/Carrier.lean.

Main names (namespace `Johnson.Prover.Print`).
  `roundsOfS`, `colOfS`, `rowsOfT`, `rowsOfS`, `storedOfS`: rounds; a symbol as words; one entry for
    every tree, under the shape's own number, its opened leaves by rising leaf; a stored table's
  `entryOf root0 answers0 root answers π`: the parsed leaf file; with code. Of the string it reads
    all but rtreq, slot, path, rsalt; the two tables' roots and answers are arguments
  `PrintableL cfg π`: ten clauses on π that are enough for the typing to lay it again: lengths, the
    first 256 bits of each opened leaf's typed salt, one count, the place in a stored symbol, no
    binding tree. That each is needed is not shown
  `RootsFitL ds`, `TreesApart ds`: public: as many items "root" as trees in each round; no two trees
    with one number
  `SizesL ...`: what the bytes' reader asks beside: lengths and numbers below 2^64
  `assembleW_entryOf`: RootsFitL → TreesApart → PrintableL → assembleW lays π again of entryOf's
    chain and tables
  `wf_entryOf`, `rdLeaf_entryOf`: RootsFitL → PrintableL → SizesL → (entryOf ...).WF; so its bytes
    (`wrLeaf`, Johnson/Prover/Print/LeafBytes.lean) are read back
  `lookup_rowsAt`, `serves_blocks`: on tables made place by place, under numbers that are apart

Limits. No prover, no oracle, no verifier: the typing alone. That a prover's string meets
`PrintableL` and `SizesL` is not shown here, nor that the data at the full size meet `RootsFitL`,
`TreesApart` and the public clauses of `SizesL`. The clause cfg32 is spent by no theorem here.
`rowsOfT` and `storedOfS` walk all leaves of a tree: at the full size's depths that is no program to
run. entryOf prints every opening that π holds, read or not. Nothing on soundness or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.StrictLinkW
import Johnson.PV.EntryInOf
import Johnson.Prover.Print.LeafBytes
import OnBytes.Prover.Print.Carrier
import OnBytes.Prover.Print.Items
import Run.CodingBitsLaws
import Run.CodingPage160

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print
open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View SgX CK XO PlainOf)
open _root_.Run (bytesToBits bitsToBytes bytesToDig digToBytes)
open _root_.Fmt (ItemValue)
open OnBytes.Flat (linkSkeletonOfRoundData)
open Johnson.RunOne.StrictW (assembleW)
open PV.EntryInOf (RowP LeafP chainOut tabOwn tabStored rdLeaf)
open OnBytes.Prover.Print (itemsOf ownSalt SaltFrom ofGots_itemsOf rootsOf_itemsOf length_itemsOf
  digs_back saltFrom_back)

/-! ## Rounds -/

/-- The rounds: each takes as many of the roots as it has trees. In a round without proof of work
the nonce 0 is laid. -/
def roundsOfS (C : CK) : (ds : List PQ.RD) → List (Dig 256) → Plains (PQ.uL C ds) →
    List (List ItemValue × ℕ)
  | [], _, _ => []
  | d :: ds, rts, (pl, r) =>
    (itemsOf d.items ((rts.take d.trees.length).map digToBytes)
        (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl),
      GPlain.nonce (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl) ::
      roundsOfS C ds (rts.drop d.trees.length) r

/-! ## Opened leaves -/

/-- A symbol at a position, as a list of words. -/
def colOfS (C : CK) : (ds : List PQ.RD) → (p : OPos (PQ.uL C ds)) → OSym (PQ.uL C ds) p →
    List UInt64
  | d :: _, .inl p, c => PQ.colT d.trees p c
  | _ :: ds, .inr q, c => colOfS C ds q c

/-- One round's trees: for each its own number, and its opened leaves by rising leaf. -/
def rowsOfT : (ts : List _root_.Fmt.Shape) →
    ((p : PQ.PosT ts) → Option (Opening 256 (PQ.SymT ts p))) → List (ℕ × List RowP)
  | [], _ => []
  | s :: ts, f =>
    (s.tree, (List.range (2 ^ s.a)).filterMap fun x =>
      if h : x < 2 ^ s.a then
        (f (.inl ⟨x, h⟩)).map fun op =>
          (⟨x, PQ.colT (s :: ts) (.inl ⟨x, h⟩) op.sym, ownSalt op.salt,
            op.path.map digToBytes⟩ : RowP)
      else none) :: rowsOfT ts fun p => f (.inr p)

/-- One entry for every tree of every round, under the shape's own number. -/
def rowsOfS (C : CK) : (ds : List PQ.RD) →
    ((p : OPos (PQ.uL C ds)) → Option (Opening 256 (OSym (PQ.uL C ds) p))) → List (ℕ × List RowP)
  | [], _ => []
  | d :: ds, f => rowsOfT d.trees (fun p => f (.inl p)) ++ rowsOfS C ds fun q => f (.inr q)

/-- The opened leaves of a stored table, by rising leaf. -/
def storedOfS (a : ℕ) (ext : Fin (2 ^ a) → Option (Opening 256 SgX)) : List RowP :=
  (List.range (2 ^ a)).filterMap fun x =>
    if h : x < 2 ^ a then
      (ext ⟨x, h⟩).map fun op => (⟨x, op.sym.2, ownSalt op.salt, op.path.map digToBytes⟩ : RowP)
    else none

/-! ## The parsed leaf file -/

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- **The parsed leaf file of a typed proof string.** The two tables' roots and answers are
arguments: the string does not hold them. -/
def entryOf (root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64)) (root : ByteArray)
    (answers : List (UInt64 × UInt64 × UInt64)) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) : LeafP where
  root0 := root0
  answers0 := answers0
  root := root
  answers := answers
  run := bitsToBytes π.salt
  rounds := roundsOfS C ds π.roots π.plains.2
  trees := rowsOfS C ds fun q => π.opens (.inr q)
  stored0 := storedOfS a fun q => π.ext (.inl q)
  stored1 := storedOfS a fun q => π.ext (.inr q)

/-- **What is asked of a typed proof string of the entry's file, for the typing to lay it again.**
Enough for that (`assembleW_entryOf`); that each clause is needed is not shown. cfg: the
configuration's digest. -/
structure PrintableL (cfg : ByteArray) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) : Prop where
  /-- the first query's salt is 32 bytes -/
  salt : π.salt.length = 256
  cfg32 : cfg.size = 32
  /-- as many roots as the data's trees -/
  roots : π.roots.length = (ds.map (·.trees.length)).sum
  /-- a leaf's typed salt begins with the run value -/
  own : ∀ q op, π.opens (.inr q) = some op → SaltFrom (bitsToBytes π.salt) op.salt
  /-- a stored leaf's begins with the configuration's digest, and its symbol names its place -/
  ext0 : ∀ q op, π.ext (.inl q) = some op → SaltFrom cfg op.salt ∧ op.sym.1 = q.val
  ext1 : ∀ q op, π.ext (.inr q) = some op → SaltFrom cfg op.salt ∧ op.sym.1 = q.val
  /-- no binding tree -/
  rtreq : π.rtreq = fun _ => false
  slot : π.slot = 0
  path : π.path = []
  rsalt : π.rsalt = []

/-- What the bytes' reader asks beside: lengths and numbers. The first seven clauses are public or
the caller's; the last three are on the string. -/
structure SizesL (root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64)) (root : ByteArray)
    (answers : List (UInt64 × UInt64 × UInt64)) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up) : Prop where
  root0 : root0.size = 32
  answers0 : answers0.length < 2 ^ 64
  root : root.size = 32
  answers : answers.length < 2 ^ 64
  /-- public: the numbers of rounds, of items and of trees; no item of the base field, no bare word;
  each tree's number, depth and width; the stored tables' depth -/
  rounds : ds.length < 2 ^ 64
  items : ∀ d ∈ ds, d.items.length < 2 ^ 64 ∧ ∀ i ∈ d.items, i ≠ .f ∧ i ≠ .word
  trees : (ds.map (·.trees.length)).sum < 2 ^ 64
  shapes : ∀ d ∈ ds, ∀ s ∈ d.trees, s.tree < 2 ^ 64 ∧ s.a < 64 ∧ s.W < 2 ^ 64
  depth : a < 64
  /-- on the string: nonces; the lengths of salts, paths and stored columns -/
  nonces : ∀ r ∈ roundsOfS C ds π.roots π.plains.2, r.2 < 2 ^ 64
  own : ∀ q op, π.opens (.inr q) = some op → op.salt.length < 2 ^ 64 ∧ op.path.length < 2 ^ 64
  ext : ∀ p op, π.ext p = some op →
    op.sym.2.length < 2 ^ 64 ∧ op.salt.length < 2 ^ 64 ∧ op.path.length < 2 ^ 64

end

/-- Public: in each round of the data as many items "root" as trees. -/
def RootsFitL (ds : List PQ.RD) : Prop :=
  ∀ d ∈ ds, d.items.countP (· == .root) = d.trees.length

/-- Public: no two trees of the data have one number. -/
def TreesApart (ds : List PQ.RD) : Prop := ((ds.flatMap (·.trees)).map (·.tree)).Nodup

/-! ## Items, roots, plain parts -/

/-- a round of the parsed leaf file as the chain's reader would hand it out -/
def outOf (r : List ItemValue × ℕ) : _root_.Fmt.RoundOut :=
  { msg := ByteArray.empty, vals := r.1, nonce := r.2, drawn := ⟨[], [], [], none⟩, list := [],
    opens := [] }

theorem plainsSL_roundsOfS (C : CK) : ∀ (ds : List PQ.RD) (rts : List (Dig 256))
    (pl : Plains (PQ.uL C ds)), PQ.plainsSL C ds ((roundsOfS C ds rts pl).map outOf) = some pl
  | [], _, _ => rfl
  | d :: ds, rts, (pl, r) => by
    show (match PlainOf.ofGots d.items (itemsOf d.items ((rts.take d.trees.length).map digToBytes)
        (GPlain.old (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl)),
      PQ.plainsSL C ds ((roundsOfS C ds (rts.drop d.trees.length) r).map outOf) with
      | some p, some r' => some (GPlain.mk d.entry.work p
          (GPlain.nonce (W := ℕ) (b := d.entry.work) (P := PlainOf d.items) pl), r')
      | _, _ => none) = _
    rw [ofGots_itemsOf, plainsSL_roundsOfS C ds]
    show some (GPlain.mk d.entry.work _ _, r) = _
    rw [GPlain.mk_old_nonce]
    rfl

theorem roots_roundsOfS (C : CK) : ∀ (ds : List PQ.RD) (rts : List (Dig 256))
    (pl : Plains (PQ.uL C ds)), RootsFitL ds → rts.length = (ds.map (·.trees.length)).sum →
    ((roundsOfS C ds rts pl).map outOf).flatMap (fun r => _root_.Fmt.rootsOf r.vals) =
      rts.map digToBytes
  | [], rts, _, _, h => by
    have h0 : rts = [] := List.eq_nil_of_length_eq_zero h
    rw [h0]
    rfl
  | d :: ds, rts, (pl, r), hf, h => by
    have hd : d.items.countP (· == .root) = d.trees.length := hf d List.mem_cons_self
    have hs : rts.length = d.trees.length + (ds.map (·.trees.length)).sum := h
    have hl : ((rts.take d.trees.length).map digToBytes).length = d.trees.length := by
      rw [List.length_map, List.length_take]
      omega
    show _root_.Fmt.rootsOf (itemsOf d.items ((rts.take d.trees.length).map digToBytes) _) ++
      ((roundsOfS C ds (rts.drop d.trees.length) r).map outOf).flatMap
        (fun r => _root_.Fmt.rootsOf r.vals) = _
    rw [rootsOf_itemsOf _ _ _ (by rw [hd, hl]), hd, List.take_of_length_le (Nat.le_of_eq hl),
      roots_roundsOfS C ds _ r (fun e he => hf e (List.mem_cons_of_mem _ he))
        (by rw [List.length_drop]; omega),
      ← List.map_append, List.take_append_drop]

/-! ## Look-ups -/

/-- what a table holds for a row -/
def valOf (r : RowP) : List UInt64 × ByteArray × List (Dig 256) :=
  (r.col, r.salt, r.path.map bytesToDig)

theorem lookup_rowsAt_ne {m n : ℕ} (h : m ≠ n) (x : ℕ) : ∀ rows : List RowP,
    (PV.EntryInOf.rowsAt n rows).lookup (m, x) = none
  | [] => rfl
  | r :: rows => by
    show (((n, r.leaf), valOf r) :: PV.EntryInOf.rowsAt n rows).lookup (m, x) = none
    have hk : ((m, x) == (n, r.leaf)) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun e => h (Prod.mk.inj e).1
    rw [List.lookup_cons, hk]
    exact lookup_rowsAt_ne h x rows

/-- Rows that are made place by place, each under its own place: the look-up at a place gives what
was made there. -/
theorem lookup_rowsAt (n : ℕ) (G : ℕ → Option RowP) (hG : ∀ y r, G y = some r → r.leaf = y)
    (x : ℕ) : ∀ l : List ℕ, (PV.EntryInOf.rowsAt n (l.filterMap G)).lookup (n, x) =
      if x ∈ l then (G x).map valOf else none
  | [] => rfl
  | y :: l => by
    have ih := lookup_rowsAt n G hG x l
    cases hy : G y with
    | none =>
      rw [List.filterMap_cons_none hy, ih]
      by_cases e : x = y
      · subst e
        simp [hy]
      · simp [e]
    | some r =>
      rw [List.filterMap_cons_some hy]
      show (((n, r.leaf), valOf r) :: PV.EntryInOf.rowsAt n (l.filterMap G)).lookup (n, x) = _
      rw [List.lookup_cons, hG y r hy]
      by_cases e : x = y
      · subst e
        simp [hy]
      · have hk : ((n, x) == (n, y)) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun e' => e (Prod.mk.inj e').2
        rw [hk, ih]
        simp [e]

/-- The table serves the blocks B: at a block's number it answers as the block alone. -/
def Serves (tab : Johnson.RunOne.StrictB.Tab) (B : List (ℕ × List RowP)) : Prop :=
  ∀ t ∈ B, ∀ x, tab.lookup (t.1, x) = (PV.EntryInOf.rowsAt t.1 t.2).lookup (t.1, x)

theorem lookup_blocks_none (n x : ℕ) : ∀ B : List (ℕ × List RowP), n ∉ B.map (·.1) →
    (B.flatMap fun t => PV.EntryInOf.rowsAt t.1 t.2).lookup (n, x) = none
  | [], _ => rfl
  | t :: B, h => by
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [List.flatMap_cons, List.lookup_append, lookup_rowsAt_ne h.1 x, lookup_blocks_none n x B h.2]
    rfl

/-- Blocks under numbers that are apart: their joined table serves them. -/
theorem serves_blocks : ∀ B : List (ℕ × List RowP), (B.map (·.1)).Nodup →
    Serves (B.flatMap fun t => PV.EntryInOf.rowsAt t.1 t.2) B
  | [], _ => fun _ h => nomatch h
  | t :: B, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    intro u hu x
    rw [List.flatMap_cons, List.lookup_append]
    rcases List.mem_cons.1 hu with rfl | hu
    · rw [lookup_blocks_none u.1 x B hn.1, Option.or_none]
    · have hne : u.1 ≠ t.1 := fun e => hn.1 (e ▸ List.mem_map_of_mem hu)
      rw [lookup_rowsAt_ne hne x, Option.none_or]
      exact serves_blocks B hn.2 u hu x

theorem labels_rowsOfT : ∀ (ts : List _root_.Fmt.Shape)
    (f : (p : PQ.PosT ts) → Option (Opening 256 (PQ.SymT ts p))),
    (rowsOfT ts f).map (·.1) = ts.map (·.tree)
  | [], _ => rfl
  | s :: ts, f => congrArg (s.tree :: ·) (labels_rowsOfT ts fun p => f (.inr p))

theorem labels_rowsOfS (C : CK) : ∀ (ds : List PQ.RD)
    (f : (p : OPos (PQ.uL C ds)) → Option (Opening 256 (OSym (PQ.uL C ds) p))),
    (rowsOfS C ds f).map (·.1) = (ds.flatMap (·.trees)).map (·.tree)
  | [], _ => rfl
  | d :: ds, f => by
    show (rowsOfT d.trees _ ++ rowsOfS C ds _).map (·.1) = _
    rw [List.map_append, labels_rowsOfT, labels_rowsOfS C ds, List.flatMap_cons, List.map_append]

/-! ## Openings -/

/-- One round's trees: the typing's look-up gives the openings back. -/
theorem opTS_rowsOfT (run : ByteArray) (tab : Johnson.RunOne.StrictB.Tab) :
    ∀ (ts : List _root_.Fmt.Shape) (f : (p : PQ.PosT ts) → Option (Opening 256 (PQ.SymT ts p)))
      (n : ℕ), Serves tab (rowsOfT ts f) → (∀ p op, f p = some op → SaltFrom run op.salt) →
      ∀ p, TypedOracleCompiler.Slice.opTS (TypedOracleCompiler.Slice.lookE run tab) n ts p = f p
  | s :: ts, f, n, hS, hs, .inl x => by
    have h1 := hS _ List.mem_cons_self x.val
    rw [lookup_rowsAt s.tree _ (fun y r hy => by
      by_cases hlt : y < 2 ^ s.a
      · rw [dif_pos hlt] at hy
        obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hy
        rfl
      · rw [dif_neg hlt] at hy
        cases hy) x.val, if_pos (List.mem_range.2 x.isLt), dif_pos x.isLt] at h1
    show (match tab.lookup (s.tree, x.val) with
      | none => none
      | some (col, salt, path) =>
        if h : col.length = s.W then
          some ⟨fun i => col[i.val]'(by rw [h]; exact i.isLt), _root_.Run.leafSalt run salt, path⟩
        else none) = f (.inl x)
    rw [h1]
    cases hf : f (.inl x) with
    | none => rfl
    | some op =>
      obtain ⟨sym, salt, path⟩ := op
      have hsalt := saltFrom_back (hs _ _ hf)
      show (if h : (List.ofFn (sym : Fin s.W → UInt64)).length = s.W then
          some (⟨fun i => (List.ofFn (sym : Fin s.W → UInt64))[i.val]'(by rw [h]; exact i.isLt),
            _root_.Run.leafSalt run (ownSalt salt), (path.map digToBytes).map bytesToDig⟩ :
              Opening 256 (Fin s.W → UInt64))
        else none) = some ⟨sym, salt, path⟩
      rw [dif_pos List.length_ofFn, hsalt, digs_back]
      congr 2
      funext i
      exact List.getElem_ofFn _
  | s :: ts, f, n, hS, hs, .inr p =>
    opTS_rowsOfT run tab ts (fun p => f (.inr p)) (n + 1)
      (fun t ht => hS t (List.mem_cons_of_mem _ ht)) (fun p op h => hs (.inr p) op h) p

/-- All rounds. -/
theorem opLS_rowsOfS (C : CK) (run : ByteArray) (tab : Johnson.RunOne.StrictB.Tab) :
    ∀ (ds : List PQ.RD)
      (f : (p : OPos (PQ.uL C ds)) → Option (Opening 256 (OSym (PQ.uL C ds) p))) (n : ℕ),
      Serves tab (rowsOfS C ds f) → (∀ p op, f p = some op → SaltFrom run op.salt) →
      ∀ p, TypedOracleCompiler.Slice.opLS C (TypedOracleCompiler.Slice.lookE run tab) n ds p = f p
  | d :: _, f, n, hS, hs, .inl p =>
    opTS_rowsOfT run tab d.trees (fun p => f (.inl p)) n
      (fun t ht => hS t (List.mem_append_left _ ht)) (fun p op h => hs (.inl p) op h) p
  | d :: ds, f, n, hS, hs, .inr q =>
    opLS_rowsOfS C run tab ds (fun q => f (.inr q)) (n + d.trees.length)
      (fun t ht => hS t (List.mem_append_right _ ht)) (fun p op h => hs (.inr p) op h) q

/-- A stored table: the look-up under its number gives the openings back. -/
theorem stored_back (a n : ℕ) (cfg : ByteArray) (ext : Fin (2 ^ a) → Option (Opening 256 SgX))
    (h : ∀ q op, ext q = some op → SaltFrom cfg op.salt ∧ op.sym.1 = q.val) (q : Fin (2 ^ a)) :
    ((PV.EntryInOf.rowsAt n (storedOfS a ext)).lookup (n, q.val)).map
      (fun z => (⟨(q.val, z.1), _root_.Run.leafSalt cfg z.2.1, z.2.2⟩ : Opening 256 SgX)) =
      ext q := by
  unfold storedOfS
  rw [lookup_rowsAt n _ (fun y r hy => by
    by_cases hlt : y < 2 ^ a
    · rw [dif_pos hlt] at hy
      obtain ⟨op, -, rfl⟩ := Option.map_eq_some_iff.1 hy
      rfl
    · rw [dif_neg hlt] at hy
      cases hy) q.val, if_pos (List.mem_range.2 q.isLt), dif_pos q.isLt]
  cases hf : ext q with
  | none => rfl
  | some op =>
    obtain ⟨⟨s1, s2⟩, salt, path⟩ := op
    obtain ⟨hs, hp⟩ := h q _ hf
    have hp' : s1 = q.val := hp
    show some (⟨(q.val, s2), _root_.Run.leafSalt cfg (ownSalt salt),
      (path.map digToBytes).map bytesToDig⟩ : Opening 256 SgX) = _
    rw [saltFrom_back hs, digs_back, hp']

/-! ## What is printed comes back -/

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- **What is printed comes back**: the library's typing lays the string again of its parsed leaf
file. -/
theorem assembleW_entryOf :
  ∀ (cfg root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64)) (root : ByteArray)
    (answers : List (UInt64 × UInt64 × UInt64)) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up),
  RootsFitL ds → TreesApart ds → PrintableL C ds a xs dec cfg π →
  assembleW C ds a xs dec cfg (chainOut (entryOf C ds a xs dec root0 answers0 root answers π))
    (tabOwn (entryOf C ds a xs dec root0 answers0 root answers π))
    (tabStored (entryOf C ds a xs dec root0 answers0 root answers π)) = some π := by
  intro cfg root0 answers0 root answers π hf ha hp
  have hpl : PQ.plainsSL C ds
      (chainOut (entryOf C ds a xs dec root0 answers0 root answers π)).rounds.toList =
      some π.plains.2 := by
    show PQ.plainsSL C ds ((roundsOfS C ds π.roots π.plains.2).map outOf).toArray.toList = _
    rw [List.toList_toArray]
    exact plainsSL_roundsOfS C ds π.roots π.plains.2
  have hroots : (_root_.Run.rootsB
      (chainOut (entryOf C ds a xs dec root0 answers0 root answers π))).map bytesToDig =
      π.roots := by
    show (((roundsOfS C ds π.roots π.plains.2).map outOf).toArray.toList.flatMap
      fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig = _
    rw [List.toList_toArray, roots_roundsOfS C ds π.roots π.plains.2 hf hp.roots, digs_back]
  have hsalt : bytesToBits (bitsToBytes π.salt) = π.salt :=
    _root_.Run.bytesToBits_bitsToBytes _ ((_root_.Run.whole_iff _).2 ⟨32, hp.salt⟩)
  have hserve : Serves (tabOwn (entryOf C ds a xs dec root0 answers0 root answers π))
      (rowsOfS C ds fun q => π.opens (.inr q)) :=
    serves_blocks _ (by
      show ((rowsOfS C ds fun q => π.opens (.inr q)).map (·.1)).Nodup
      rw [labels_rowsOfS]
      exact ha)
  have hopens : ∀ q, TypedOracleCompiler.Slice.opLS C (TypedOracleCompiler.Slice.lookE (bitsToBytes π.salt)
              (tabOwn (entryOf C ds a xs dec root0 answers0 root answers π))) 0 ds q = π.opens (.inr q) :=
    opLS_rowsOfS C _ _ ds (fun q => π.opens (.inr q)) 0 hserve hp.own
  have hext : TypedOracleCompiler.Slice.extE a cfg
      (tabStored (entryOf C ds a xs dec root0 answers0 root answers π)) = π.ext := by
    funext p
    cases p with
    | inl q =>
      show ((PV.EntryInOf.rowsAt 0 (storedOfS a fun q => π.ext (.inl q)) ++
        PV.EntryInOf.rowsAt 1 (storedOfS a fun q => π.ext (.inr q))).lookup (0, q.val)).map _ = _
      rw [List.lookup_append, lookup_rowsAt_ne (by decide : (0 : ℕ) ≠ 1), Option.or_none]
      exact stored_back a 0 cfg (fun q => π.ext (.inl q)) hp.ext0 q
    | inr q =>
      show ((PV.EntryInOf.rowsAt 0 (storedOfS a fun q => π.ext (.inl q)) ++
        PV.EntryInOf.rowsAt 1 (storedOfS a fun q => π.ext (.inr q))).lookup (1, q.val)).map _ = _
      rw [List.lookup_append, lookup_rowsAt_ne (by decide : (1 : ℕ) ≠ 0), Option.none_or]
      exact stored_back a 1 cfg (fun q => π.ext (.inr q)) hp.ext1 q
  unfold assembleW
  rw [hpl]
  show some _ = some π
  congr 1
  obtain ⟨salt, roots, plains, opens, ext, rtreq, slot, path, rsalt⟩ := π
  simp only [OneProtocolProof.mk.injEq]
  refine ⟨hsalt, hroots, rfl, ?_, hext, hp.rtreq.symm, hp.slot.symm, hp.path.symm, hp.rsalt.symm⟩
  funext p
  cases p with
  | inl e => exact e.elim
  | inr q => exact hopens q

end

/-! ## What is printed is taken by the bytes' reader -/

/-- Where no item is of the base field or a bare word, and enough roots of 32 bytes are laid in,
each item is one that the leaf file's reader takes. -/
theorem okItemL_itemsOf : ∀ (l : List _root_.Fmt.Item) (rts : List ByteArray) (x : PlainOf l),
    (∀ i ∈ l, i ≠ .f ∧ i ≠ .word) → l.countP (· == .root) ≤ rts.length →
    (∀ r ∈ rts, r.size = 32) → ∀ g ∈ itemsOf l rts x, PV.EntryInOf.okItemL g
  | [], _, _, _, _, _, g, hg => nomatch hg
  | .root :: l, [], _, _, h, _, _, _ => by
    rw [List.countP_cons_of_pos (by rfl)] at h
    exact absurd h (by simp)
  | .root :: l, r :: rts, x, hi, h, hr, g, hg => by
    rw [List.countP_cons_of_pos (by rfl)] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hr r List.mem_cons_self
    · exact okItemL_itemsOf l rts x (fun i h' => hi i (List.mem_cons_of_mem _ h'))
        (Nat.le_of_succ_le_succ h) (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) g hg
  | .f :: l, _, _, hi, _, _, _, _ => absurd rfl (hi .f List.mem_cons_self).1
  | .word :: l, _, _, hi, _, _, _, _ => absurd rfl (hi .word List.mem_cons_self).2
  | .e :: l, rts, (x : _root_.Fmt.Ext × PlainOf l), hi, h, hr, g, hg => by
    rw [List.countP_cons_of_neg (by decide)] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact trivial
    · exact okItemL_itemsOf l rts x.2 (fun i h' => hi i (List.mem_cons_of_mem _ h')) h hr g hg
  | .answer :: l, rts, (x : _root_.Fmt.Ext × PlainOf l), hi, h, hr, g, hg => by
    rw [List.countP_cons_of_neg (by decide)] at h
    rcases List.mem_cons.1 hg with rfl | hg
    · exact trivial
    · exact okItemL_itemsOf l rts x.2 (fun i h' => hi i (List.mem_cons_of_mem _ h')) h hr g hg

theorem length_roundsOfS (C : CK) : ∀ (ds : List PQ.RD) (rts : List (Dig 256))
    (pl : Plains (PQ.uL C ds)), (roundsOfS C ds rts pl).length = ds.length
  | [], _, _ => rfl
  | d :: ds, rts, (_, r) => congrArg (· + 1) (length_roundsOfS C ds (rts.drop d.trees.length) r)

theorem items_roundsOfS (C : CK) : ∀ (ds : List PQ.RD) (rts : List (Dig 256))
    (pl : Plains (PQ.uL C ds)), RootsFitL ds → rts.length = (ds.map (·.trees.length)).sum →
    (∀ d ∈ ds, d.items.length < 2 ^ 64 ∧ ∀ i ∈ d.items, i ≠ .f ∧ i ≠ .word) →
    ∀ r ∈ roundsOfS C ds rts pl, r.1.length < 2 ^ 64 ∧ ∀ x ∈ r.1, PV.EntryInOf.okItemL x
  | [], _, _, _, _, _, r, hr => nomatch hr
  | d :: ds, rts, (pl, rest), hf, h, hi, r, hr => by
    have hd : d.items.countP (· == .root) = d.trees.length := hf d List.mem_cons_self
    have hs : rts.length = d.trees.length + (ds.map (·.trees.length)).sum := h
    rcases List.mem_cons.1 hr with rfl | hr
    · refine ⟨?_, ?_⟩
      · show (itemsOf d.items _ _).length < 2 ^ 64
        rw [length_itemsOf]
        exact (hi d List.mem_cons_self).1
      · refine okItemL_itemsOf d.items _ _ (hi d List.mem_cons_self).2 ?_ ?_
        · rw [hd, List.length_map, List.length_take]
          omega
        · intro b hb
          obtain ⟨e, -, rfl⟩ := List.mem_map.1 hb
          exact _root_.Run.size_digToBytes e
    · exact items_roundsOfS C ds _ rest (fun e he => hf e (List.mem_cons_of_mem _ he))
        (by rw [List.length_drop]; omega) (fun e he => hi e (List.mem_cons_of_mem _ he)) r hr

/-- the size of a leaf's own salt -/
theorem size_ownSalt {start : ByteArray} {s : Rom.Bits} (h : SaltFrom start s)
    (hl : s.length < 2 ^ 64) : (ownSalt s).size < 2 ^ 64 := by
  obtain ⟨n, hn⟩ := (_root_.Run.whole_iff _).1 h.2
  have e : (ownSalt s).size = n := _root_.Run.size_bitsToBytes _ n hn
  rw [List.length_drop] at hn
  omega

theorem two_pow_lt {n : ℕ} (h : n < 64) : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) h

theorem length_rowsOfT : ∀ (ts : List _root_.Fmt.Shape)
    (f : (p : PQ.PosT ts) → Option (Opening 256 (PQ.SymT ts p))),
    (rowsOfT ts f).length = ts.length
  | [], _ => rfl
  | _ :: ts, f => congrArg (· + 1) (length_rowsOfT ts fun p => f (.inr p))

theorem length_rowsOfS (C : CK) : ∀ (ds : List PQ.RD)
    (f : (p : OPos (PQ.uL C ds)) → Option (Opening 256 (OSym (PQ.uL C ds) p))),
    (rowsOfS C ds f).length = (ds.map (·.trees.length)).sum
  | [], _ => rfl
  | d :: ds, f => by
    show (rowsOfT d.trees _ ++ rowsOfS C ds _).length = _
    rw [List.length_append, length_rowsOfT, length_rowsOfS C ds]
    rfl

theorem okTreeL_rowsOfT (run : ByteArray) : ∀ (ts : List _root_.Fmt.Shape)
    (f : (p : PQ.PosT ts) → Option (Opening 256 (PQ.SymT ts p))),
    (∀ s ∈ ts, s.tree < 2 ^ 64 ∧ s.a < 64 ∧ s.W < 2 ^ 64) →
    (∀ p op, f p = some op →
      SaltFrom run op.salt ∧ op.salt.length < 2 ^ 64 ∧ op.path.length < 2 ^ 64) →
    ∀ t ∈ rowsOfT ts f, PV.EntryInOf.okTreeL t
  | [], _, _, _, t, ht => nomatch ht
  | s :: ts, f, hsh, hop, t, ht => by
    rcases List.mem_cons.1 ht with rfl | ht
    · obtain ⟨h1, h2, h3⟩ := hsh s List.mem_cons_self
      refine ⟨h1, ?_, ?_⟩
      · refine Nat.lt_of_le_of_lt (List.length_filterMap_le _ _) ?_
        rw [List.length_range]
        exact two_pow_lt h2
      · intro r hr
        obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hr
        by_cases hlt : x < 2 ^ s.a
        · rw [dif_pos hlt] at hx
          obtain ⟨op, hf, rfl⟩ := Option.map_eq_some_iff.1 hx
          obtain ⟨g1, g2, g3⟩ := hop _ op hf
          refine ⟨Nat.lt_trans hlt (two_pow_lt h2), ?_, size_ownSalt g1 g2, ?_, ?_⟩
          · show (List.ofFn _).length < 2 ^ 64
            rw [List.length_ofFn]
            exact h3
          · show (op.path.map digToBytes).length < 2 ^ 64
            rw [List.length_map]
            exact g3
          · intro d hd
            obtain ⟨e, -, rfl⟩ := List.mem_map.1 hd
            exact _root_.Run.size_digToBytes e
        · rw [dif_neg hlt] at hx
          cases hx
    · exact okTreeL_rowsOfT run ts (fun p => f (.inr p))
        (fun s' h' => hsh s' (List.mem_cons_of_mem _ h')) (fun p op h' => hop (.inr p) op h') t ht

theorem okTreeL_rowsOfS (C : CK) (run : ByteArray) : ∀ (ds : List PQ.RD)
    (f : (p : OPos (PQ.uL C ds)) → Option (Opening 256 (OSym (PQ.uL C ds) p))),
    (∀ d ∈ ds, ∀ s ∈ d.trees, s.tree < 2 ^ 64 ∧ s.a < 64 ∧ s.W < 2 ^ 64) →
    (∀ p op, f p = some op →
      SaltFrom run op.salt ∧ op.salt.length < 2 ^ 64 ∧ op.path.length < 2 ^ 64) →
    ∀ t ∈ rowsOfS C ds f, PV.EntryInOf.okTreeL t
  | [], _, _, _, t, ht => nomatch ht
  | d :: ds, f, hsh, hop, t, ht => by
    rcases List.mem_append.1 ht with ht | ht
    · exact okTreeL_rowsOfT run d.trees (fun p => f (.inl p)) (hsh d List.mem_cons_self)
        (fun p op h' => hop (.inl p) op h') t ht
    · exact okTreeL_rowsOfS C run ds (fun q => f (.inr q))
        (fun e he => hsh e (List.mem_cons_of_mem _ he)) (fun p op h' => hop (.inr p) op h') t ht

theorem wf_storedOfS (a : ℕ) (ha : a < 64) (cfg : ByteArray)
    (ext : Fin (2 ^ a) → Option (Opening 256 SgX))
    (h : ∀ q op, ext q = some op → SaltFrom cfg op.salt ∧ op.sym.2.length < 2 ^ 64 ∧
      op.salt.length < 2 ^ 64 ∧ op.path.length < 2 ^ 64) :
    (storedOfS a ext).length < 2 ^ 64 ∧ ∀ r ∈ storedOfS a ext, r.WF := by
  refine ⟨?_, ?_⟩
  · refine Nat.lt_of_le_of_lt (List.length_filterMap_le _ _) ?_
    rw [List.length_range]
    exact two_pow_lt ha
  · intro r hr
    obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hr
    by_cases hlt : x < 2 ^ a
    · rw [dif_pos hlt] at hx
      obtain ⟨op, hf, rfl⟩ := Option.map_eq_some_iff.1 hx
      obtain ⟨g1, g2, g3, g4⟩ := h _ op hf
      refine ⟨Nat.lt_trans hlt (two_pow_lt ha), g2, size_ownSalt g1 g3, ?_, ?_⟩
      · show (op.path.map digToBytes).length < 2 ^ 64
        rw [List.length_map]
        exact g4
      · intro d hd
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hd
        exact _root_.Run.size_digToBytes e
    · rw [dif_neg hlt] at hx
      cases hx

section
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- **The parsed leaf file of a printable string is one that the bytes' reader takes.** -/
theorem wf_entryOf :
  ∀ (cfg root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64)) (root : ByteArray)
    (answers : List (UInt64 × UInt64 × UInt64)) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up),
  RootsFitL ds → PrintableL C ds a xs dec cfg π →
  SizesL C ds a xs dec root0 answers0 root answers π →
  (entryOf C ds a xs dec root0 answers0 root answers π).WF := by
  intro cfg root0 answers0 root answers π hf hp hz
  have s0 := wf_storedOfS a hz.depth cfg (fun q => π.ext (.inl q)) fun q op h =>
    ⟨(hp.ext0 q op h).1, hz.ext _ op h⟩
  have s1 := wf_storedOfS a hz.depth cfg (fun q => π.ext (.inr q)) fun q op h =>
    ⟨(hp.ext1 q op h).1, hz.ext _ op h⟩
  exact
    { root0 := hz.root0
      answers0Count := hz.answers0
      root := hz.root
      answersCount := hz.answers
      run := _root_.Run.size_bitsToBytes _ 32 hp.salt
      roundsCount := by
        show (roundsOfS C ds π.roots π.plains.2).length < 2 ^ 64
        rw [length_roundsOfS]
        exact hz.rounds
      rounds := fun r hr =>
        ⟨items_roundsOfS C ds π.roots π.plains.2 hf hp.roots hz.items r hr, hz.nonces r hr⟩
      treesCount := by
        show (rowsOfS C ds fun q => π.opens (.inr q)).length < 2 ^ 64
        rw [length_rowsOfS]
        exact hz.trees
      trees := okTreeL_rowsOfS C (bitsToBytes π.salt) ds (fun q => π.opens (.inr q)) hz.shapes
        fun q op h => ⟨hp.own q op h, hz.own q op h⟩
      stored0Count := s0.1
      stored0 := s0.2
      stored1Count := s1.1
      stored1 := s1.2 }

/-- So its bytes are read back. -/
theorem rdLeaf_entryOf :
  ∀ (cfg root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64)) (root : ByteArray)
    (answers : List (UInt64 × UInt64 × UInt64)) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up),
  RootsFitL ds → PrintableL C ds a xs dec cfg π →
  SizesL C ds a xs dec root0 answers0 root answers π →
  rdLeaf (wrLeaf (entryOf C ds a xs dec root0 answers0 root answers π)) =
    some (entryOf C ds a xs dec root0 answers0 root answers π) :=
  fun cfg root0 answers0 root answers π hf hp hz =>
    rdLeaf_wrLeaf _ (wf_entryOf C ds a xs dec cfg root0 answers0 root answers π hf hp hz)

end

end Johnson.Prover.Print
