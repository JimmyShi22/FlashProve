-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ChainStmJoin.lean: for each of a file's three chains, the string that is hashed for the chain's
first value (the library's "first query") determines what the chain's statement was written from,
under the hypotheses counted below. A chain is the non-interactive form of one protocol.
As this library writes the file format, that string is `firstBytes`: the digest of the chain's
parameter bytes, the chain's statement behind a word for its length, a record, and the run's value
if the chain has one. A key file and a proof file have three chains each: the first, the shared, the
second. `keyStmAt` and `proofStmAt` write a statement from arguments: a table (a root and a list of
answers) or a `ProofStm` (what a proof's chains are given from outside), two seals, a root.
`KeyParsed.stmAtW` and `ProofParsed.stmAtW` make it from a parsed file and two seals (a proof's also
from a `ProofStm`), test the forms themselves and compute the root by the hash. The hash is a
parameter h, any ordinary function of five arguments; no theorem here names a fixed one.
States, with smaller theorems around these:
(1) `keyStmAt_hashed_inj`, `proofStmAt_hashed_inj` (7 hypotheses each),
    `KeyParsed.stmAtW_hashed_inj`, `ProofParsed.stmAtW_hashed_inj` (4 each): if two `firstBytes`
    with the statements of the same chain of the three are the same bytes, the two statements tell
    the same (`keyTold`, `proofTold`): at a first chain the table, for a proof also the number of
    the stored copy, the value of the item "request" and the bytes of the request file; at a shared
    chain the table and the root of the binding tree; at a second chain the two seals. The other
    three parts of `firstBytes` are equal too.
(2) Six theorems whose names end in `_iff` (0 hypotheses) say exactly where `firstStm` (a key's; a
    proof's), `secondStm`, `sharedStmOfW`, `ChainDecl.bindShape` and `KeyParsed.idOkW`, the test of
    a caller's commitment ID, answer, and what. For the two `sharedStmW` between `stmAtW` and these,
    one direction alone is stated (`sharedStmW_of`).
Under (the counts leave out the equation of bytes; each theorem lists its own at its statement): (i)
conditions of form on the values: roots and seals of 32 bytes, `TableShape.count` answers
(2 ^ logRows times the shape's number `answers`), canonical field elements, and two bounds by which
the statements are shorter than 2 ^ 64 bytes (`TableShape.fitsWord`; a clause of `ProofStm.ok`); at
`stmAtW` instead, that the function answers on both sides; (ii) `First.Rest` on both sides: three
conditions on the lengths of the other parts; (iii) on the hash: no hypothesis of its own (that
`stmAtW` answers at a shared chain includes that the root computed by h has 32 bytes). Both sides
are under one field and one tables' shape, and at `stmAtW` under one `Declared` (the library's
description of what is public) and one h.
Does not show:
(1) No theorem of the library on a verifier uses these theorems, and that a verifier or the programs
    hash these strings is not shown here.
(2) Under a random oracle two different strings get one answer only with small probability; no bound
    on it is proved here, and nothing is concluded here from two equal first values.
(3) The table, seals and root of `keyStmAt` and `proofStmAt` are arguments, related to nothing.
(4) Nothing about the hash: no statement here says that two calls with the same answer hash the same
    bytes.
(5) At a shared chain the two roots are equal, and no more: of the first seals, the places, the
    salts and the paths from which the roots were computed nothing follows (that needs the hash). No
    theorem here or in the neighbouring files says what `SlotParsed.rootW` or `climbW` compute; that
    the root has 32 bytes is a clause of the statements, not a theorem.
(6) At a second chain `keyTold` and `proofTold` have a default for the table, and at `stmAtW` no
    hypothesis reads the two files or `Declared`. At a first chain the seals are read by nothing.
(7) The two seals are arguments of `stmAtW` too: nothing here says that a seal is what a chain's run
    has drawn.
(8) Nothing about two queries under two fields or two shapes.
(9) Nothing about the reply (it is no item of a statement).
(10) "The bytes of the request file" are the field `ProofStm.words`, which whoever builds the value
    fills: nothing here or below compares it with a file.
(11) Nothing about which chain a query belongs to: a chain's label is in the call's place, not in
    these bytes.
(12) The bound 2 ^ 64 is the spelling's. The format's bound on a hashed string is lower.
(13) That the statement of a proof's first chain is spelled as the format page spells it is checked
    by a test, not by a theorem.
Notes in full, with every limit at length, stand at the end of this file.

-/
import Fmt.ChainStmLaws
import Fmt.Rules4Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fmt

/-- The parts of a first query beside the statement have a spelling: the parameters' digest has
32 bytes, the record fewer than 2 ^ 64, and the run's value, if there is one, 32. These are
`First.ok`'s clauses but for the one on the statement. -/
def First.Rest (pd rc : ByteArray) (run : Option ByteArray) : Prop :=
  pd.size = 32 ∧ rc.size < 2 ^ 64 ∧ ∀ r, run = some r → r.size = 32

/-- With a statement of fewer than 2 ^ 64 bytes these are `First.ok`. -/
theorem First.ok_of_rest (pd st rc : ByteArray) (run : Option ByteArray)
    (h : First.Rest pd rc run) (hs : st.size < 2 ^ 64) : First.ok (pd, st, rc, run) :=
  ⟨h.1, hs, h.2.1, h.2.2⟩

/-- The frame of the four theorems below: two first queries on the same bytes have the same four
parts, where the statements have fewer than 2 ^ 64 bytes. -/
theorem firstBytes_parts (pd st rc pd' st' rc' : ByteArray) (run run' : Option ByteArray)
    (h : First.Rest pd rc run) (h' : First.Rest pd' rc' run') (hs : st.size < 2 ^ 64)
    (hs' : st'.size < 2 ^ 64) (e : firstBytes pd st rc run = firstBytes pd' st' rc' run') :
    pd = pd' ∧ st = st' ∧ rc = rc' ∧ run = run' :=
  firstBytes_inj pd st rc pd' st' rc' run run' (First.ok_of_rest pd st rc run h hs)
    (First.ok_of_rest pd' st' rc' run' h' hs') e

/-- A KEY's ONE-TIME CHAIN. Asked: `TableShape.fitsWord`; both tables have the form. Two first
queries on the same bytes speak of the same table, under the same parameters' digest, record and
run's value. -/
theorem firstBytes_item_inj (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t u : TableSt)
    (ht : t.ok f s = true) (hu : u.ok f s = true) (pd rc pd' rc' : ByteArray)
    (run run' : Option ByteArray) (h : First.Rest pd rc run) (h' : First.Rest pd' rc' run')
    (e : firstBytes pd t.item rc run = firstBytes pd' u.item rc' run') :
    t = u ∧ pd = pd' ∧ rc = rc' ∧ run = run' := by
  obtain ⟨a, b, c, d⟩ := firstBytes_parts pd t.item rc pd' u.item rc' run run' h h'
    (TableSt.item_size_lt f s hs t ht) (TableSt.item_size_lt f s hs u hu) e
  exact ⟨TableSt.item_inj f s hs t u ht hu b, a, c, d⟩

/-- A SHARED CHAIN, of a key or of a proof. Asked: `TableShape.fitsWord`; both tables have the form;
both roots have 32 bytes. Two first queries on the same bytes speak of the same table and the
same root of the binding tree. -/
theorem firstBytes_shared_inj (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t u : TableSt)
    (r q : ByteArray) (ht : t.ok f s = true) (hu : u.ok f s = true) (hr : r.size = 32)
    (hq : q.size = 32) (pd rc pd' rc' : ByteArray) (run run' : Option ByteArray)
    (h : First.Rest pd rc run) (h' : First.Rest pd' rc' run')
    (e : firstBytes pd (sharedStm t r) rc run = firstBytes pd' (sharedStm u q) rc' run') :
    (t = u ∧ r = q) ∧ pd = pd' ∧ rc = rc' ∧ run = run' := by
  obtain ⟨a, b, c, d⟩ := firstBytes_parts pd (sharedStm t r) rc pd'
      (sharedStm u q) rc' run run' h h'
    (sharedStm_size_lt f s hs t r ht hr) (sharedStm_size_lt f s hs u q hu hq) e
  exact ⟨sharedStm_inj f s hs t u r q ht hu hr hq b, a, c, d⟩

/-- A statement of two seals of 32 bytes has fewer than 2 ^ 64 bytes (it has 152: `sealItems_size`,
Fmt/ChainStmLaws.lean). -/
theorem sealItems_size_lt (s1 s2 : ByteArray) (h1 : s1.size = 32) (h2 : s2.size = 32) :
    (sealItems [s1, s2]).size < 2 ^ 64 := by
  rw [sealItems_size, h1, h2]
  decide

/-- A SECOND CHAIN, of a key or of a proof. Asked: all four seals have 32 bytes. Two first
queries on the same bytes speak of the same two seals, in the same order. -/
theorem firstBytes_seals_inj (s1 s2 u1 u2 : ByteArray) (h1 : s1.size = 32) (h2 : s2.size = 32)
    (g1 : u1.size = 32) (g2 : u2.size = 32) (pd rc pd' rc' : ByteArray)
    (run run' : Option ByteArray) (h : First.Rest pd rc run) (h' : First.Rest pd' rc' run')
    (e : firstBytes pd (sealItems [s1, s2]) rc run = firstBytes pd' (sealItems [u1, u2]) rc' run') :
    (s1 = u1 ∧ s2 = u2) ∧ pd = pd' ∧ rc = rc' ∧ run = run' := by
  obtain ⟨a, b, c, d⟩ := firstBytes_parts pd (sealItems [s1, s2]) rc pd' (sealItems [u1, u2]) rc'
    run run' h h' (sealItems_size_lt s1 s2 h1 h2) (sealItems_size_lt u1 u2 g1 g2) e
  exact ⟨sealItems_inj s1 s2 u1 u2 h1 h2 g1 g2 b, a, c, d⟩

/-- A proof's first chain's statement, of a value with the form, has fewer than 2 ^ 64 bytes. -/
theorem ProofStm.bytes_size_lt (D : Declared) (x : ProofStm) (hx : x.ok D = true) :
    x.bytes.size < 2 ^ 64 := by
  obtain ⟨a, -, c⟩ := (ProofStm.ok_iff D x).1 hx
  rw [ProofStm.bytes_size_ok _ _ x a]
  exact c

/-- A PROOF's FIRST CHAIN. Asked: both values have the form `ProofStm.ok` under one declared
structure. No premise on the shape. Two first queries on the same bytes speak of the same table,
the same number of the stored copy, the same value of the item "request" and the same bytes of the
request file. Of the replies nothing follows. -/
theorem firstBytes_proof_inj (D : Declared) (x y : ProofStm) (hx : x.ok D = true)
    (hy : y.ok D = true) (pd rc pd' rc' : ByteArray) (run run' : Option ByteArray)
    (h : First.Rest pd rc run) (h' : First.Rest pd' rc' run')
    (e : firstBytes pd x.bytes rc run = firstBytes pd' y.bytes rc' run') :
    x.hashed = y.hashed ∧ pd = pd' ∧ rc = rc' ∧ run = run' := by
  obtain ⟨a, b, c, d⟩ := firstBytes_parts pd x.bytes rc pd' y.bytes rc' run run' h h'
    (ProofStm.bytes_size_lt D x hx) (ProofStm.bytes_size_lt D y hy) e
  exact ⟨ProofStm.bytes_inj D x y hx hy b, a, c, d⟩

/-- A PROOF's FIRST CHAIN: two first queries on the same bytes speak of the same bytes of the
request file. Asked: as in `firstBytes_proof_inj`. The premise is on the bytes that are hashed: no
hash stands in this law, and nothing is asked of how the value of the item "request" is made. -/
theorem firstBytes_proof_words (D : Declared) (x y : ProofStm) (hx : x.ok D = true)
    (hy : y.ok D = true) (pd rc pd' rc' : ByteArray) (run run' : Option ByteArray)
    (h : First.Rest pd rc run) (h' : First.Rest pd' rc' run')
    (e : firstBytes pd x.bytes rc run = firstBytes pd' y.bytes rc' run') : x.words = y.words :=
  congrArg (fun z => z.2.2.2)
    (firstBytes_proof_inj D x y hx hy pd rc pd' rc' run run' h h' e).1

/-- What the statement of each chain of a KEY file tells: the table; the table and the binding
tree's root; the two seals. -/
def keyTold (t : TableSt) (seal1 bindRoot seal2 : ByteArray) :
    Which → TableSt × ByteArray × ByteArray
  | .first => (t, ByteArray.empty, ByteArray.empty)
  | .shared => (t, bindRoot, ByteArray.empty)
  | .second => (default, seal1, seal2)

/-- What the statement of each chain of a PROOF file tells: table, copy, the item "request"'s value
and the request file's bytes; the table and the binding tree's root; the two seals. No bytes are
written of this value: the shared and the second chain's statements do not read the request file's
bytes. -/
def proofTold (x : ProofStm) (seal1 bindRoot seal2 : ByteArray) :
    Which → (TableSt × UInt32 × ByteArray × ByteArray) × ByteArray × ByteArray
  | .first => (x.hashed, ByteArray.empty, ByteArray.empty)
  | .shared => ((x.table, 0, ByteArray.empty, ByteArray.empty), bindRoot, ByteArray.empty)
  | .second => (default, seal1, seal2)

/-- THE THREE CHAINS OF A KEY FILE, at `keyStmAt`. Asked: `TableShape.fitsWord`; both tables have
the form; the seals and roots have 32 bytes (`sealsOk`); `First.Rest` on both sides. For each chain
w: two first queries on the same bytes tell the same (`keyTold`). -/
theorem keyStmAt_hashed_inj (f : Fld) (s : TableShape) (hs : s.fitsWord = true) (t u : TableSt)
    (ht : t.ok f s = true) (hu : u.ok f s = true) (s1 r s2 u1 q u2 : ByteArray)
    (k : sealsOk s1 r s2 = true) (k' : sealsOk u1 q u2 = true) (w : Which)
    (pd rc pd' rc' : ByteArray) (run run' : Option ByteArray) (h : First.Rest pd rc run)
    (h' : First.Rest pd' rc' run')
    (e : firstBytes pd (keyStmAt t s1 r s2 w) rc run = firstBytes pd'
        (keyStmAt u u1 q u2 w) rc' run') :
    keyTold t s1 r s2 w = keyTold u u1 q u2 w ∧ pd = pd' ∧ rc = rc' ∧ run = run' := by
  obtain ⟨a1, a2, a3⟩ := (sealsOk_iff s1 r s2).1 k
  obtain ⟨c1, c2, c3⟩ := (sealsOk_iff u1 q u2).1 k'
  cases w with
  | first =>
    obtain ⟨x, y⟩ := firstBytes_item_inj f s hs t u ht hu pd rc pd' rc' run run' h h' e
    exact ⟨by simp only [keyTold, x], y⟩
  | shared =>
    obtain ⟨⟨x1, x2⟩, y⟩ :=
      firstBytes_shared_inj f s hs t u r q ht hu a2 c2 pd rc pd' rc' run run' h h' e
    exact ⟨by simp only [keyTold, x1, x2], y⟩
  | second =>
    obtain ⟨⟨x1, x2⟩, y⟩ :=
      firstBytes_seals_inj s1 s2 u1 u2 a1 a3 c1 c3 pd rc pd' rc' run run' h h' e
    exact ⟨by simp only [keyTold, x1, x2], y⟩

/-- THE THREE CHAINS OF A PROOF FILE, at `proofStmAt`. Asked: `TableShape.fitsWord` (for the shared
chain); both values have the form `ProofStm.ok`; the seals and roots have 32 bytes; `First.Rest` on
both sides. For each chain w: two first queries on the same bytes tell the same (`proofTold`). -/
theorem proofStmAt_hashed_inj (D : Declared) (hs : D.table.fitsWord = true) (x y : ProofStm)
    (hx : x.ok D = true) (hy : y.ok D = true) (s1 r s2 u1 q u2 : ByteArray)
    (k : sealsOk s1 r s2 = true) (k' : sealsOk u1 q u2 = true) (w : Which)
    (pd rc pd' rc' : ByteArray) (run run' : Option ByteArray) (h : First.Rest pd rc run)
    (h' : First.Rest pd' rc' run')
    (e : firstBytes pd (proofStmAt x s1 r s2 w) rc run =
      firstBytes pd' (proofStmAt y u1 q u2 w) rc' run') :
    proofTold x s1 r s2 w = proofTold y u1 q u2 w ∧ pd = pd' ∧ rc = rc' ∧ run = run' := by
  obtain ⟨a1, a2, a3⟩ := (sealsOk_iff s1 r s2).1 k
  obtain ⟨c1, c2, c3⟩ := (sealsOk_iff u1 q u2).1 k'
  cases w with
  | first =>
    obtain ⟨z, v⟩ := firstBytes_proof_inj D x y hx hy pd rc pd' rc' run run' h h' e
    exact ⟨by simp only [proofTold, z], v⟩
  | shared =>
    obtain ⟨⟨z1, z2⟩, v⟩ := firstBytes_shared_inj D.setting.field D.table hs x.table y.table r q
      ((ProofStm.ok_iff D x).1 hx).1 ((ProofStm.ok_iff D y).1 hy).1 a2 c2 pd
          rc pd' rc' run run' h h' e
    exact ⟨by simp only [proofTold, z1, z2], v⟩
  | second =>
    obtain ⟨⟨z1, z2⟩, v⟩ :=
      firstBytes_seals_inj s1 s2 u1 u2 a1 a3 c1 c3 pd rc pd' rc' run run' h h' e
    exact ⟨by simp only [proofTold, z1, z2], v⟩

/-! ## The closed forms (Fmt/ChainStm.lean) -/

/-- A key's one-time chain: the closed form answers b exactly where the file's table has the form,
the shape has `TableShape.fitsWord`, and b is the item "table" of the file's own table. -/
theorem KeyParsed.firstStm_iff (D : Declared) (F : KeyParsed) (b : ByteArray) :
    F.firstStm D = some b ↔
      (F.table.ok D.setting.field D.table = true ∧ D.table.fitsWord = true) ∧ b = F.table.item := by
  unfold KeyParsed.firstStm
  by_cases c : (F.table.ok D.setting.field D.table && D.table.fitsWord) = true
  · rw [if_pos c]
    rw [Bool.and_eq_true] at c
    exact ⟨fun g => ⟨c, (Option.some.inj g).symm⟩, fun g => by rw [g.2]⟩
  · rw [if_neg c]
    exact ⟨fun g => absurd g (by simp), fun g => absurd (by rw [Bool.and_eq_true]; exact g.1) c⟩

/-- A proof's first chain: the closed form answers b exactly where x has the form, the file's head
names x's stored copy (one number), and b is the statement written of x. -/
theorem ProofParsed.firstStm_iff (D : Declared) (x : ProofStm) (F : ProofParsed) (b : ByteArray) :
    F.firstStm D x = some b ↔ (x.ok D = true ∧ F.copyFits x = true) ∧ b = x.bytes := by
  unfold ProofParsed.firstStm
  by_cases c : (x.ok D && F.copyFits x) = true
  · rw [if_pos c]
    rw [Bool.and_eq_true] at c
    exact ⟨fun g => ⟨c, (Option.some.inj g).symm⟩, fun g => by rw [g.2]⟩
  · rw [if_neg c]
    exact ⟨fun g => absurd g (by simp), fun g => absurd (by rw [Bool.and_eq_true]; exact g.1) c⟩

/-- A second chain: the closed form answers b exactly where both seals have 32 bytes and b is the
statement written of them. -/
theorem secondStm_iff (s1 s2 b : ByteArray) :
    secondStm s1 s2 = some b ↔ (s1.size = 32 ∧ s2.size = 32) ∧ b = sealItems [s1, s2] := by
  unfold secondStm
  by_cases c : (s1.size == 32 && s2.size == 32) = true
  · rw [if_pos c]
    simp only [Bool.and_eq_true, beq_iff_eq] at c
    exact ⟨fun g => ⟨c, (Option.some.inj g).symm⟩, fun g => by rw [g.2]⟩
  · rw [if_neg c]
    refine ⟨fun g => absurd g (by simp), fun g => absurd ?_ c⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact g.1

/-- A shared chain, AT EVERY PLAIN HASH h, for any shape b of a binding tree, table and slot:
`sharedStmOfW` answers c exactly where the table has the form, the tables' shape has
`TableShape.fitsWord`, THE SLOT HAS THE FORM OF THE SHAPE b, the seal and the root have 32 bytes,
and c is the statement written of the table and of THE ROOT THAT THE SEAL AND THE SLOT GIVE by h at
b's depth under the declared files' digest by h. -/
theorem sharedStmOfW_iff (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (b : BindShape) (t : TableSt) (s : SlotParsed) (seal1 c : ByteArray) :
    Id.run (sharedStmOfW h D b t s seal1) = some c ↔
      (((t.ok D.setting.field D.table = true ∧ D.table.fitsWord = true) ∧ s.fits b = true) ∧
        seal1.size = 32) ∧ (Id.run (s.rootW h b.depth (Id.run (D.cfgW h)) seal1)).size = 32 ∧
        c = sharedStm t (Id.run (s.rootW h b.depth (Id.run (D.cfgW h)) seal1)) := by
  unfold sharedStmOfW
  by_cases k : (t.ok D.setting.field D.table && D.table.fitsWord && s.fits b
      && seal1.size == 32) = true
  · rw [if_pos k]
    simp only [Bool.and_eq_true, beq_iff_eq] at k
    show (if (Id.run (s.rootW h b.depth (Id.run (D.cfgW h)) seal1)).size == 32 then
      some (sharedStm t (Id.run (s.rootW h b.depth (Id.run (D.cfgW h)) seal1))) else none) =
        some c ↔ _
    by_cases q : ((Id.run (s.rootW h b.depth (Id.run (D.cfgW h)) seal1)).size == 32) = true
    · rw [if_pos q]
      exact ⟨fun g => ⟨k, beq_iff_eq.1 q, (Option.some.inj g).symm⟩, fun g => by rw [g.2.2]⟩
    · rw [if_neg q]
      exact ⟨fun g => absurd g (by simp), fun g => absurd (beq_iff_eq.2 g.2.1) q⟩
  · rw [if_neg k]
    refine ⟨fun g => absurd (show (none : Option ByteArray) = some c from g) (by simp),
      fun g => absurd ?_ k⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact g.1

/-- THE BINDING TREE's SHAPE OUT OF THE HASHED ITEM: `ChainDecl.bindShape` gives b exactly where the
depth is at most 48, the salt's length is one that a leaf can have, and the value of the chain's
first parameter item of the name "binding tree" is the two words of b and nothing more. -/
theorem ChainDecl.bindShape_iff (c : ChainDecl) (b : BindShape) :
    c.bindShape = some b ↔
      (depthOK b.depth = true ∧ saltLenOK b.saltBytes = true) ∧
        c.others.lookup "binding tree" = some (u64n b.depth ++ u64n b.saltBytes) := by
  have hw := whole_both (undoes_pair undoes_word undoes_word)
    (cuts_pair (cuts_of_only only_word) (cuts_of_only only_word))
  unfold ChainDecl.bindShape
  constructor
  · intro e
    obtain ⟨x, e1, e2⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨v, e3, e4⟩ := Option.bind_eq_some_iff.1 e1
    split at e2
    · rename_i k
      obtain rfl := Option.some.inj e2
      rw [Bool.and_eq_true] at k
      refine ⟨k, ?_⟩
      rw [e3, ((hw v x).1 e4).2]
      simp only [pair, u64n, UInt64.ofNat_toNat]
    · simp at e2
  · rintro ⟨⟨k1, k2⟩, e⟩
    have d1 : b.depth < 2 ^ 64 := by
      have := of_decide_eq_true k1
      omega
    have d2 : b.saltBytes < 2 ^ 64 := by
      simp only [saltLenOK, Bool.and_eq_true, decide_eq_true_eq] at k2
      omega
    have t1 : (UInt64.ofNat b.depth).toNat = b.depth := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt d1
    have t2 : (UInt64.ofNat b.saltBytes).toNat = b.saltBytes := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt d2
    have g : whole (rdPair rdWord rdWord) (u64n b.depth ++ u64n b.saltBytes) =
        some (UInt64.ofNat b.depth, UInt64.ofNat b.saltBytes) :=
      (hw _ _).2 ⟨⟨trivial, trivial⟩, rfl⟩
    simp only [e, Option.bind_some, g, t1, t2, k1, k2, Bool.and_self, if_true]

/-- THE CLOSED FORM OF THE TEST ON THE COMMITMENT ID, AT EVERY PLAIN HASH h: it says yes exactly
where the key file's own table has the form, the caller's ID has 32 bytes, and that ID is what h
gives under 179 on the ID's string (R4.11) of that table under the declared shape, the declared
files' digest by h, the seeds drawn by h from the table's name, and no digest at the end. -/
theorem KeyParsed.idOkW_iff (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (F : KeyParsed) (x : KeyStm) :
    Id.run (F.idOkW h D x) = true ↔
      (F.table.ok D.setting.field D.table = true ∧ x.ok = true) ∧
        Id.run (publishedIDW h (Id.run (D.cfgW h))
          (D.table.name (Id.run (D.cfgW h)) F.table.root)
          (Id.run (D.seedsW h (Id.run (D.cfgW h)) F.table)) F.table.answers []) = x.id := by
  unfold KeyParsed.idOkW
  by_cases k : (F.table.ok D.setting.field D.table && x.ok) = true
  · rw [if_pos k]
    rw [Bool.and_eq_true] at k
    show Id.run (x.idOkW h D (Id.run (D.cfgW h)) F.table
      (Id.run (D.seedsW h (Id.run (D.cfgW h)) F.table)) []) = true ↔ _
    unfold KeyStm.idOkW
    rw [if_pos k.2]
    show decide (Id.run (publishedIDW h (Id.run (D.cfgW h))
      (D.table.name (Id.run (D.cfgW h)) F.table.root)
      (Id.run (D.seedsW h (Id.run (D.cfgW h)) F.table)) F.table.answers []) = x.id) = true ↔ _
    rw [decide_eq_true_eq]
    exact ⟨fun g => ⟨k, g⟩, fun g => g.2⟩
  · rw [if_neg k]
    refine ⟨fun g => absurd (show false = true from g) (by simp), fun g => absurd ?_ k⟩
    rw [Bool.and_eq_true]
    exact g.1

/-- What an answer of the closed form for a KEY file's shared chain says, at every plain hash h: the
one-time chain's hashed item "binding tree" gives a shape, its depth is 0, and the answer is
`sharedStmOfW`'s at that shape, the file's own table and the file's slot. -/
theorem KeyParsed.sharedStmW_of (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (F : KeyParsed) (s1 c : ByteArray)
    (e : Id.run (F.sharedStmW h D s1) = some c) :
    ∃ b, D.key.first.bindShape = some b ∧ b.depth = 0 ∧
      Id.run (sharedStmOfW h D b F.table F.slot s1) = some c := by
  unfold KeyParsed.sharedStmW at e
  rcases hb : D.key.first.bindShape with _ | b
  · rw [hb] at e
    exact absurd (show (none : Option ByteArray) = some c from e) (by simp)
  · rw [hb] at e
    have e' : Id.run (if (b.depth == 0) = true then sharedStmOfW h D b F.table F.slot s1
        else pure none) = some c := e
    by_cases k : (b.depth == 0) = true
    · rw [if_pos k] at e'
      exact ⟨b, rfl, beq_iff_eq.1 k, e'⟩
    · rw [if_neg k] at e'
      exact absurd (show (none : Option ByteArray) = some c from e') (by simp)

/-- THE CLOSED FORM GIVES WHAT THE OPEN FORM SPELLS, for a key file, at every plain hash h: whatever
`KeyParsed.stmAtW` answers is `keyStmAt` at the file's own table, the two seals, and the root that
the first seal and the file's slot give by h at depth 0 under the declared files' digest by h. -/
theorem KeyParsed.stmAtW_open (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (F : KeyParsed) (s1 s2 : ByteArray) (w : Which) (c : ByteArray)
    (e : Id.run (F.stmAtW h D s1 s2 w) = some c) :
    c = keyStmAt F.table s1 (Id.run (F.slot.rootW h 0 (Id.run (D.cfgW h)) s1)) s2 w := by
  cases w with
  | first => exact ((KeyParsed.firstStm_iff D F c).1 e).2
  | shared =>
    obtain ⟨b, -, hd, e1⟩ := KeyParsed.sharedStmW_of h D F s1 c e
    have a := ((sharedStmOfW_iff h D b F.table F.slot s1 c).1 e1).2.2
    rw [hd] at a
    exact a
  | second => exact ((secondStm_iff s1 s2 c).1 e).2

/-- THE THREE CHAINS OF A KEY FILE, AT THE CLOSED FORM, AT EVERY PLAIN HASH h. NOTHING IS ASKED OF
TABLES, SEALS, SLOTS OR THE SHAPE: that the closed form answers at all says it. For each chain w: if
it answers b for one file and two seals, and c for another file and two seals, under one declared
structure and one h, and two first queries on b and on c hash the same bytes, then the two chains
tell the same (`keyTold`, with the roots computed by h). Asked: the other three parts of each query
have a spelling (`First.Rest`). At the shared chain the ROOTS are equal; of the seals and slots from
which they come nothing follows. -/
theorem KeyParsed.stmAtW_hashed_inj (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (F G : KeyParsed) (s1 s2 u1 u2 : ByteArray) (w : Which) (b c : ByteArray)
    (hb : Id.run (F.stmAtW h D s1 s2 w) = some b) (hc : Id.run (G.stmAtW h D u1 u2 w) = some c)
    (pd rc pd' rc' : ByteArray) (run run' : Option ByteArray)
    (k : First.Rest pd rc run) (k' : First.Rest pd' rc' run')
    (e : firstBytes pd b rc run = firstBytes pd' c rc' run') :
    keyTold F.table s1 (Id.run (F.slot.rootW h 0 (Id.run (D.cfgW h)) s1)) s2 w =
        keyTold G.table u1 (Id.run (G.slot.rootW h 0 (Id.run (D.cfgW h)) u1)) u2 w ∧
      pd = pd' ∧ rc = rc' ∧ run = run' := by
  cases w with
  | first =>
    obtain ⟨⟨a1, a2⟩, rfl⟩ := (KeyParsed.firstStm_iff D F b).1 hb
    obtain ⟨⟨c1, -⟩, rfl⟩ := (KeyParsed.firstStm_iff D G c).1 hc
    obtain ⟨x, y⟩ :=
      firstBytes_item_inj _ _ a2 F.table G.table a1 c1 pd rc pd' rc' run run' k k' e
    exact ⟨by simp only [keyTold, x], y⟩
  | shared =>
    obtain ⟨b1, -, d1, e1⟩ := KeyParsed.sharedStmW_of h D F s1 b hb
    obtain ⟨b2, -, d2, e2⟩ := KeyParsed.sharedStmW_of h D G u1 c hc
    obtain ⟨⟨⟨⟨a1, a2⟩, -⟩, -⟩, a5, a6⟩ := (sharedStmOfW_iff h D b1 F.table F.slot s1 b).1 e1
    obtain ⟨⟨⟨⟨c1, -⟩, -⟩, -⟩, c5, c6⟩ := (sharedStmOfW_iff h D b2 G.table G.slot u1 c).1 e2
    rw [d1] at a5 a6
    rw [d2] at c5 c6
    rw [a6, c6] at e
    obtain ⟨⟨x1, x2⟩, y⟩ := firstBytes_shared_inj _ _ a2 F.table G.table _ _ a1 c1 a5 c5 pd rc pd'
      rc' run run' k k' e
    exact ⟨by simp only [keyTold, x1, x2], y⟩
  | second =>
    obtain ⟨⟨a1, a2⟩, rfl⟩ := (secondStm_iff s1 s2 b).1 hb
    obtain ⟨⟨c1, c2⟩, rfl⟩ := (secondStm_iff u1 u2 c).1 hc
    obtain ⟨⟨x1, x2⟩, y⟩ :=
      firstBytes_seals_inj s1 s2 u1 u2 a1 a2 c1 c2 pd rc pd' rc' run run' k k' e
    exact ⟨by simp only [keyTold, x1, x2], y⟩

/-- Where the first chain's hashed item gives a shape, `Declared.proofDepth` is its depth. -/
theorem Declared.proofDepth_of (D : Declared) (b : BindShape)
    (hb : D.proof.first.bindShape = some b) : D.proofDepth = b.depth := by
  simp only [Declared.proofDepth, hb, Option.map_some, Option.getD_some]

/-- What an answer of the closed form for a PROOF file's shared chain says, at every plain hash h:
x has the form, the file's head names x's stored copy, the first chain's hashed item "binding tree"
gives a shape, and the answer is `sharedStmOfW`'s at that shape, x's table and the file's slot. -/
theorem ProofParsed.sharedStmW_of (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (x : ProofStm) (F : ProofParsed) (s1 c : ByteArray)
    (e : Id.run (F.sharedStmW h D x s1) = some c) :
    (x.ok D = true ∧ F.copyFits x = true) ∧ ∃ b, D.proof.first.bindShape = some b ∧
      Id.run (sharedStmOfW h D b x.table F.slot s1) = some c := by
  unfold ProofParsed.sharedStmW at e
  rcases hb : D.proof.first.bindShape with _ | b
  · rw [hb] at e
    exact absurd (show (none : Option ByteArray) = some c from e) (by simp)
  · rw [hb] at e
    have e' : Id.run (if (F.firstStm D x).isSome = true then
        sharedStmOfW h D b x.table F.slot s1 else pure none) = some c := e
    by_cases k : (F.firstStm D x).isSome = true
    · rw [if_pos k] at e'
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 k
      exact ⟨((ProofParsed.firstStm_iff D x F v).1 hv).1, b, rfl, e'⟩
    · rw [if_neg k] at e'
      exact absurd (show (none : Option ByteArray) = some c from e') (by simp)

/-- The same for a proof file: `proofStmAt` at x, the two seals, and the root at the hashed item's
depth (`Declared.proofDepth`). -/
theorem ProofParsed.stmAtW_open (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (x : ProofStm) (F : ProofParsed) (s1 s2 : ByteArray) (w : Which) (c : ByteArray)
    (e : Id.run (F.stmAtW h D x s1 s2 w) = some c) :
    c = proofStmAt x s1 (Id.run (F.slot.rootW h D.proofDepth (Id.run (D.cfgW h)) s1)) s2 w := by
  cases w with
  | first => exact ((ProofParsed.firstStm_iff D x F c).1 e).2
  | shared =>
    obtain ⟨-, b, hb, e1⟩ := ProofParsed.sharedStmW_of h D x F s1 c e
    have a := ((sharedStmOfW_iff h D b x.table F.slot s1 c).1 e1).2.2
    rw [← Declared.proofDepth_of D b hb] at a
    exact a
  | second => exact ((secondStm_iff s1 s2 c).1 e).2

/-- THE THREE CHAINS OF A PROOF FILE, AT THE CLOSED FORM, AT EVERY PLAIN HASH h. Nothing is asked of
the outer statements, seals, slots or the shape. As `KeyParsed.stmAtW_hashed_inj` (one declared
structure and one h on both sides), with `proofTold` and the roots at the hashed item's depth
(`Declared.proofDepth`). Of the replies nothing follows; at the shared chain the ROOTS are equal,
and of the seals and slots nothing follows. -/
theorem ProofParsed.stmAtW_hashed_inj (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray)
    (D : Declared) (x y : ProofStm) (F G : ProofParsed) (s1 s2 u1 u2 : ByteArray) (w : Which)
    (b c : ByteArray) (hb : Id.run (F.stmAtW h D x s1 s2 w) = some b)
    (hc : Id.run (G.stmAtW h D y u1 u2 w) = some c) (pd rc pd' rc' : ByteArray)
    (run run' : Option ByteArray) (k : First.Rest pd rc run) (k' : First.Rest pd' rc' run')
    (e : firstBytes pd b rc run = firstBytes pd' c rc' run') :
    proofTold x s1 (Id.run (F.slot.rootW h D.proofDepth (Id.run (D.cfgW h)) s1)) s2 w =
        proofTold y u1 (Id.run (G.slot.rootW h D.proofDepth (Id.run (D.cfgW h)) u1)) u2 w ∧
      pd = pd' ∧ rc = rc' ∧ run = run' := by
  cases w with
  | first =>
    obtain ⟨⟨a1, -⟩, rfl⟩ := (ProofParsed.firstStm_iff D x F b).1 hb
    obtain ⟨⟨c1, -⟩, rfl⟩ := (ProofParsed.firstStm_iff D y G c).1 hc
    obtain ⟨z, v⟩ := firstBytes_proof_inj D x y a1 c1 pd rc pd' rc' run run' k k' e
    exact ⟨by simp only [proofTold, z], v⟩
  | shared =>
    obtain ⟨-, b1, k1, e1⟩ := ProofParsed.sharedStmW_of h D x F s1 b hb
    obtain ⟨-, b2, k2, e2⟩ := ProofParsed.sharedStmW_of h D y G u1 c hc
    obtain ⟨⟨⟨⟨a1, a2⟩, -⟩, -⟩, a5, a6⟩ := (sharedStmOfW_iff h D b1 x.table F.slot s1 b).1 e1
    obtain ⟨⟨⟨⟨c1, -⟩, -⟩, -⟩, c5, c6⟩ := (sharedStmOfW_iff h D b2 y.table G.slot u1 c).1 e2
    rw [← Declared.proofDepth_of D b1 k1] at a5 a6
    rw [← Declared.proofDepth_of D b2 k2] at c5 c6
    rw [a6, c6] at e
    obtain ⟨⟨z1, z2⟩, v⟩ := firstBytes_shared_inj _ _ a2 x.table y.table _ _ a1 c1 a5 c5 pd rc pd'
      rc' run run' k k' e
    exact ⟨by simp only [proofTold, z1, z2], v⟩
  | second =>
    obtain ⟨⟨a1, a2⟩, rfl⟩ := (secondStm_iff s1 s2 b).1 hb
    obtain ⟨⟨c1, c2⟩, rfl⟩ := (secondStm_iff u1 u2 c).1 hc
    obtain ⟨⟨z1, z2⟩, v⟩ :=
      firstBytes_seals_inj s1 s2 u1 u2 a1 a2 c1 c2 pd rc pd' rc' run run' k k' e
    exact ⟨by simp only [proofTold, z1, z2], v⟩

end Fmt

#print axioms Fmt.First.ok_of_rest
#print axioms Fmt.firstBytes_parts
#print axioms Fmt.firstBytes_item_inj
#print axioms Fmt.firstBytes_shared_inj
#print axioms Fmt.sealItems_size_lt
#print axioms Fmt.firstBytes_seals_inj
#print axioms Fmt.ProofStm.bytes_size_lt
#print axioms Fmt.firstBytes_proof_inj
#print axioms Fmt.firstBytes_proof_words
#print axioms Fmt.keyStmAt_hashed_inj
#print axioms Fmt.proofStmAt_hashed_inj
#print axioms Fmt.KeyParsed.firstStm_iff
#print axioms Fmt.ProofParsed.firstStm_iff
#print axioms Fmt.secondStm_iff
#print axioms Fmt.sharedStmOfW_iff
#print axioms Fmt.ChainDecl.bindShape_iff
#print axioms Fmt.KeyParsed.idOkW_iff
#print axioms Fmt.KeyParsed.sharedStmW_of
#print axioms Fmt.KeyParsed.stmAtW_open
#print axioms Fmt.KeyParsed.stmAtW_hashed_inj
#print axioms Fmt.Declared.proofDepth_of
#print axioms Fmt.ProofParsed.sharedStmW_of
#print axioms Fmt.ProofParsed.stmAtW_open
#print axioms Fmt.ProofParsed.stmAtW_hashed_inj

/-
Notes in full (other files' comments call these notes "the head of" this file).

Fmt/ChainStmJoin.lean: the bytes of a chain's first query fix what its statement was written of.

What kind of laws. Laws on the format's spellings, as Fmt/Rules4.lean and Fmt/Parsed.lean write
them. No theorem of the library on a verifier uses them, and that a verifier or the programs hash
these strings is not shown here. NO FIXED HASH FUNCTION IS NAMED IN A LAW OF THIS FILE: a hash is a
letter h, "a plain hash": any function of the hash's five arguments with values in the monad Id (an
ordinary function), of which nothing is asked here. (The neighbours have, for some forms with a W, a
flat name at one fixed hash function; no law here names one.)

In plain words. By the format (R4.6) a chain's first value is the answer of one hash call, its first
query, on `firstBytes` (Fmt/Rules4.lean): the digest of the chain's parameter bytes, the chain's
statement behind a word for its length, a record, and the run's value if the chain has one. IF TWO
FIRST QUERIES OF THE SAME CHAIN OF THE THREE, UNDER ONE FIELD AND ONE TABLES' SHAPE, HASH THE SAME
BYTES, THEN THE TWO CHAINS SPEAK OF THE SAME THINGS: the same table (root and answers); for a
proof's first chain also the same number of the stored copy, the same value of the item "request"
and the same bytes of the request file; for a shared chain also the same root of the binding tree;
for a second chain the same two seals. Under a random oracle two different strings get one answer
only with small probability; no bound on it is proved here, and nothing is concluded here from two
equal first values.

Main names:
  `First.Rest`, `firstBytes_parts`: the frame, over `firstBytes_inj` (Fmt/Rules4Laws.lean).
  ON THE WRITERS AND THE OPEN FORMS, whose table, seals and root are tied to nothing; no hash:
  `firstBytes_item_inj`, `firstBytes_shared_inj`, `firstBytes_seals_inj`, `firstBytes_proof_inj`,
  `firstBytes_proof_words`; `keyTold`, `proofTold`, `keyStmAt_hashed_inj`, `proofStmAt_hashed_inj`.
  Asked: each value has its form, both under one field and one shape; for a key's one-time chain and
  a shared chain also `TableShape.fitsWord` (without it no form bounds the statement's length below
  2 ^ 64); the same chain on both sides; `First.Rest` (the library's own start of a chain from a
  digest of 32 bytes meets it wherever the hash's answers under the number 172 have 32 bytes:
  `startChainW_rest`, Fmt/ChainStmMore.lean; that this can be met: Fmt/TestChainStm.lean, part E).
  ON THE CLOSED FORMS of Fmt/ChainStm.lean, which compute the root and ask the forms themselves.
  Without a hash: `ChainDecl.bindShape_iff`, `KeyParsed.firstStm_iff`, `ProofParsed.firstStm_iff`,
  `secondStm_iff`, `Declared.proofDepth_of`. At every plain hash h: `KeyParsed.idOkW_iff`,
  `sharedStmOfW_iff` (exactly where); `KeyParsed.sharedStmW_of`, `ProofParsed.sharedStmW_of` (one
  direction); `KeyParsed.stmAtW_open`, `ProofParsed.stmAtW_open`: an answer is the open form's
  spelling at the computed root; `KeyParsed.stmAtW_hashed_inj`, `ProofParsed.stmAtW_hashed_inj`: the
  join WITHOUT a premise on tables, seals, slots or the shape. Asked there: the closed form answers
  on both sides, under ONE declared structure, ONE h and for THE SAME chain of the three;
  `First.Rest` twice.
Limits:
  Nothing about the hash: no statement here says that two calls with the same ANSWER hash the same
  bytes.
  AT A SHARED CHAIN THE TWO ROOTS ARE EQUAL, AND NO MORE: of the first seals, the places, the salts
  and the paths from which the roots were computed nothing follows (that needs the hash). No law
  here or in the neighbours says what `SlotParsed.rootW` or `climbW` compute; that the root has 32
  bytes is a clause of the statements, not a law.
  At a second chain `keyTold` and `proofTold` have a default for the table, and the two files and
  the declared structure are read by no premise: the theorem there is `firstBytes_seals_inj`. At a
  first chain the seals are read by nothing.
  The two seals are arguments of the closed forms: nothing here says that a seal is what a chain's
  run has drawn.
  Nothing about two queries under two fields or two shapes.
  Nothing about the reply (it is no item of a statement: R14.8).
  "The bytes of the request file" are the field `ProofStm.words`, which whoever builds the value
  fills: nothing here or below holds it against a file.
  Nothing about which chain a query belongs to: a chain's label stands in the call's place, not in
  these bytes.
  The bound 2 ^ 64 is the spelling's. FORMAT.md's bound on a hashed string is lower (R2.3, R2.7):
  Fmt/ChainStmSmall.lean.
  THAT THE STATEMENT OF A PROOF's FIRST CHAIN IS SPELLED AS THE FORMAT PAGE SPELLS IT (R14.3: four
  items, the last the request file's bytes) IS HELD BY A TEST, NOT BY A LAW: Fmt/TestChainStm.lean,
  part B, block 6, holds `proofStmAt` at the first chain against the page's known answer for that
  statement (docs/format/format-vectors.txt).
  No Mathlib, neither directly nor through the imports.
-/
