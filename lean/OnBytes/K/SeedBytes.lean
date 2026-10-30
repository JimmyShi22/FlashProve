-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/SeedBytes.lean: the seeds of a stored table's record, as the program draws them, as a
function of the one oracle's answers at strings that are written out. For proofs only; the program
does not import this file.

The program `verify-on-bytes` draws the seeds of a table's record from the table's name, on a chain
of its own (`recordSeeds`, OnBytes/Entry/Table.lean; R4.8): one call with the number 160 under the
label 2^32, then calls with the number 162, each cut into two blocks of 32 bytes. A typed verifier
that asks one typed query for a seed, and makes the seed of the answer's digests, is tied to the
program if the typed oracle function's answer at that query is these blocks. Here the program's side
of that tie is said in plain bytes.

Main definitions.
 `seedFirst name`      the string of the first value: a function of the table's name.
 `seedStr ρ0 b`        the string of block b of the seeds' round (call b / 2, half b % 2): a
                       function of the first value.
 `seedBlock name t`    block t of the verifier's message in that round: the format's oracle at
                       `seedStr` of its own answer at `seedFirst name`, at b = t + 1 (block 0 is
                       the chain's next value).
 `nBlocks bits count`  how many blocks the program fetches.
 `seedsOf f bits count vb`  the seeds, of the blocks: the program's own draws.
 `seedsAtName`         the two put together: the seeds as a function of the name.
 `seedDigs name K`, `seedsOfDigs`  the same with the blocks as K digests, for a typed answer.
Main theorems.
 `fetch_get`, `row_get`  the format's loop over a round's calls, at the format's hash, entry by
                       entry.
 `recordSeeds_blocks`  `recordSeeds f name bits count = some (seedsAtName f name bits count)`.
 `seedsOfDigs_seedDigs`  the seeds of the K digests are these, if K is at least `nBlocks`.
 `tableKey_seeds`      the seeds in a key that `tableKey` returns, for tables with a record, are
                       these, at the table's name.
 `entry_check_keys`    if `Entry.check` says yes, the block that `Tie.entrySpec` gives for the two
                       tables is `linkVerify` at the keys that `tableKey` gives for them.
 `entry_check_seeds`   so the seeds in these two keys are functions of the two tables' names.
 `key_check_key`       if `Key.check` says yes, `Key.readKey` reads the file's two later chains,
                       from some byte offset, with the key that `tableKey` gives for the table that
                       the check returns.

What is not claimed. Nothing on how the seeds are distributed; nothing on any hash function; nothing
on soundness. Here no second text of `recordSeeds` is written: the theorem is on the program's own.


-/
import OnBytes.Tie.EntryFile
import OnBytes.Tie.KeyFile
import Run.PageXSpare

set_option autoImplicit false

namespace OnBytes.K

/-- The string of the first value of the seeds' chain: a function of the table's name. -/
def seedFirst (name : ByteArray) : ByteArray :=
  Fmt.oStr 0 160 0 Fmt.recordLabel Fmt.zero32
    (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none)

/-- The string of block b of the answer of the seeds' one round: call b / 2, half b % 2. -/
def seedStr (ρ0 : ByteArray) (b : ℕ) : ByteArray :=
  Fmt.oStr (if b % 2 = 0 then 0 else 1) 162 Fmt.recordLabel 1 ρ0
    (ByteArray.empty ++ Fmt.tail .seeds 0 0 (b / 2))

/-- Block t of the verifier's message in the seeds' round, at the format's oracle. -/
def seedBlock (name : ByteArray) (t : ℕ) : ByteArray :=
  Fmt.oracle (seedStr (Fmt.oracle (seedFirst name)) (t + 1))

/-- How many blocks of the verifier's message the program fetches for `count` seeds with points of
`bits` coordinates. -/
def nBlocks (bits count : ℕ) : ℕ := Fmt.blocksFor (count * (bits * 18 + 36))

/-- The seeds, of the blocks of the verifier's message: the program's own draws. -/
def seedsOf (f : Fmt.Fld) (bits count : ℕ) (vb : Array ByteArray) : List (List E × E) :=
  (timesT (Fmt.drawSeed f bits) count (Fmt.rowOf vb) 0).1.map fun x =>
    (x.1.map E.ofTriple, E.ofTriple x.2)

/-- The seeds as a function of the table's name. -/
def seedsAtName (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) : List (List E × E) :=
  seedsOf f bits count ((Array.range (nBlocks bits count)).map (seedBlock name))

/-- Half b % 2 of call j + b / 2 of a round, at the format's hash. -/
def halfAt (lab : ℕ) (ρ : ByteArray) (i : ℕ) (msg : ByteArray) (kind : Fmt.Kind) (w nonce j b : ℕ) :
    ByteArray :=
  (Fmt.formatHash 162 lab i ρ (msg ++ Fmt.tail kind w nonce (j + b / 2))).extract (32 * (b % 2))
    (32 * (b % 2) + 32)

/-- The format's loop over a round's calls (`Fmt.fetchFrom`), at the format's hash. -/
def fetchH (lab : ℕ) (ρ : ByteArray) (i : ℕ) (msg : ByteArray) (kind : Fmt.Kind) (w nonce m j : ℕ)
    (acc : Array ByteArray) : Array ByteArray :=
  Fmt.fetchFrom (m := Id) Fmt.formatHash lab ρ i msg kind w nonce m j acc

/-- The loop adds two blocks a call. -/
theorem fetch_size (lab : ℕ) (ρ : ByteArray) (i : ℕ) (msg : ByteArray) (kind : Fmt.Kind)
    (w nonce : ℕ) :
    ∀ (m j : ℕ) (acc : Array ByteArray),
      (fetchH lab ρ i msg kind w nonce m j acc).size = acc.size + 2 * m
  | 0, _, _ => rfl
  | m + 1, j, acc => by
    show (fetchH lab ρ i msg kind w nonce m (j + 1)
      ((acc.push ((Fmt.formatHash 162 lab i ρ (msg ++ Fmt.tail kind w nonce j)).extract 0 32)).push
        ((Fmt.formatHash 162 lab i ρ (msg ++ Fmt.tail kind w nonce j)).extract 32 64))).size = _
    rw [fetch_size lab ρ i msg kind w nonce m (j + 1), Array.size_push, Array.size_push]
    omega

/-- The loop, entry by entry: what was there; then the halves of the calls j, j + 1, ..; then
nothing. -/
theorem fetch_get (lab : ℕ) (ρ : ByteArray) (i : ℕ) (msg : ByteArray) (kind : Fmt.Kind)
    (w nonce : ℕ) :
    ∀ (m j : ℕ) (acc : Array ByteArray) (k : ℕ),
      (fetchH lab ρ i msg kind w nonce m j acc)[k]? =
        if k < acc.size then acc[k]?
        else if k < acc.size + 2 * m then some (halfAt lab ρ i msg kind w nonce j (k - acc.size))
        else none
  | 0, j, acc, k => by
    show acc[k]? = _
    by_cases h : k < acc.size
    · rw [if_pos h]
    · rw [if_neg h, if_neg (by omega)]
      exact Array.getElem?_eq_none (by omega)
  | m + 1, j, acc, k => by
    show (fetchH lab ρ i msg kind w nonce m (j + 1)
      ((acc.push ((Fmt.formatHash 162 lab i ρ (msg ++ Fmt.tail kind w nonce j)).extract 0 32)).push
        ((Fmt.formatHash 162 lab i ρ (msg ++ Fmt.tail kind w nonce j)).extract 32 64)))[k]? = _
    rw [fetch_get lab ρ i msg kind w nonce m (j + 1), Array.size_push, Array.size_push]
    by_cases h0 : k < acc.size
    · rw [if_pos (by omega), if_pos h0, Array.getElem?_push, Array.size_push,
        if_neg (by omega), Array.getElem?_push, if_neg (by omega)]
    · rw [if_neg h0]
      by_cases h1 : k = acc.size
      · subst h1
        rw [if_pos (by omega), if_pos (by omega), Array.getElem?_push, Array.size_push,
          if_neg (by omega), Array.getElem?_push, if_pos rfl]
        simp only [halfAt, Nat.sub_self, Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Nat.add_zero,
          Nat.zero_add]
      · by_cases h2 : k = acc.size + 1
        · subst h2
          rw [if_pos (by omega), if_pos (by omega), Array.getElem?_push, Array.size_push,
            if_pos rfl]
          have e : acc.size + 1 - acc.size = 1 := by omega
          simp only [halfAt, e]
          rfl
        · rw [if_neg (by omega)]
          by_cases h3 : k < acc.size + 2 * (m + 1)
          · rw [if_pos (by omega), if_pos h3]
            have e1 : j + 1 + (k - (acc.size + 1 + 1)) / 2 = j + (k - acc.size) / 2 := by omega
            have e2 : (k - (acc.size + 1 + 1)) % 2 = (k - acc.size) % 2 := by omega
            simp only [halfAt, e1, e2]
          · rw [if_neg (by omega), if_neg h3]

/-- The blocks of the verifier's message of a round without work, entry by entry: block k is block
k + 1 of the round's answer. -/
theorem row_get (lab : ℕ) (ρ : ByteArray) (i : ℕ) (msg : ByteArray) (kind : Fmt.Kind)
    (nonce n k : ℕ) :
    (Fmt.msgA 0 ((fetchH lab ρ i msg kind 0 nonce ((Fmt.firstBlock 0 + n + 1) / 2) 0 #[]).extract 0
      (Fmt.firstBlock 0 + n)))[k]? =
      if k < n then some (halfAt lab ρ i msg kind 0 nonce 0 (k + 1)) else none := by
  have hf : Fmt.firstBlock 0 = 1 := rfl
  have hX := fetch_size lab ρ i msg kind 0 nonce ((Fmt.firstBlock 0 + n + 1) / 2) 0 #[]
  rw [hf] at hX ⊢
  unfold Fmt.msgA
  rw [hf, Array.getElem?_extract, Array.getElem?_extract, Array.size_extract, hX, fetch_get]
  simp only [Array.size_empty, Nat.zero_add, Nat.sub_zero, Nat.not_lt_zero, if_false]
  by_cases hk : k < n
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos hk, Nat.add_comm 1 k]
  · rw [if_neg (by omega), if_neg hk]

/-- What the format asks of a query's data holds at the seeds' one round. -/
theorem seed_askOK (ρ0 : ByteArray) (h : ρ0.size = 32) :
    Fmt.askOK Fmt.recordLabel ρ0 (0 + 1) ByteArray.empty .seeds 0 0 = true := by
  unfold Fmt.askOK
  rw [h]
  decide

/-- The first value of the seeds' chain is the format's oracle's answer at `seedFirst name`. -/
theorem recordFirst_oracle (name : ByteArray) (hn : name.size + 56 ≤ 2 ^ 32 - 144) :
    Fmt.recordFirst name = Fmt.oracle (seedFirst name) := by
  have hd : Fmt.hDom 160 0 Fmt.recordLabel Fmt.zero32
      (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none) = true :=
    Run.dom0 160 Fmt.recordLabel _ (by decide) (by decide) (by decide)
      (by rw [Run.size_seedFirstBytes]; exact hn)
  unfold seedFirst
  rw [Fmt.oracle_in0 160 0 Fmt.recordLabel Fmt.zero32 _ hd]
  have hs : (Fmt.formatHash 160 0 Fmt.recordLabel Fmt.zero32
      (Fmt.firstBytes Fmt.zero32 name ByteArray.empty none)).size = 32 := Fmt.size_H _ _ _ _ _
  show Fmt.formatHash 160 0 Fmt.recordLabel Fmt.zero32 _ = _
  rw [← hs, ByteArray.extract_zero_size]

/-- A half of a call of the seeds' round is the format's oracle's answer at `seedStr`. -/
theorem half_oracle (ρ0 : ByteArray) (h : ρ0.size = 32) (b : ℕ) :
    halfAt Fmt.recordLabel ρ0 1 ByteArray.empty .seeds 0 0 0 b = Fmt.oracle (seedStr ρ0 b) := by
  have hd : Fmt.hDom 162 Fmt.recordLabel 1 ρ0 (ByteArray.empty ++ Fmt.tail .seeds 0 0 (b / 2)) =
      true :=
    Run.dom162 Fmt.recordLabel ρ0 1 ByteArray.empty .seeds 0 0 (b / 2) (seed_askOK ρ0 h)
      (by decide) (by decide)
  unfold halfAt seedStr
  rw [Nat.zero_add]
  rcases Nat.mod_two_eq_zero_or_one b with e | e
  · rw [e, if_pos rfl, Fmt.oracle_in0 162 _ _ _ _ hd]
  · rw [e, if_neg (by decide), Fmt.oracle_in1 _ _ _ _ hd]

/-- The program's `recordSeeds`, as a map over the value of the seeds' one round. The program's text
is unfolded while it stands without arguments, and a letter stands for the round's value before the
two texts are compared: so no checker need compute that value. -/
theorem recordSeeds_text : recordSeeds = fun f name bits count =>
    ((⟨Fmt.recordLabel, Fmt.recordFirst name, 0⟩ : Fmt.Chain).query ByteArray.empty .seeds 0 0
      (nBlocks bits count)).map fun p => seedsOf f bits count p.2 := by
  delta recordSeeds
  funext f name bits count
  rw [nBlocks]
  generalize Fmt.Chain.query _ _ _ _ _ _ = x
  cases x with
  | none => rfl
  | some p =>
    cases p
    rfl

/-- The same with its four arguments. -/
theorem recordSeeds_apply (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ) :
    recordSeeds f name bits count =
      ((⟨Fmt.recordLabel, Fmt.recordFirst name, 0⟩ : Fmt.Chain).query ByteArray.empty .seeds 0 0
        (nBlocks bits count)).map fun p => seedsOf f bits count p.2 :=
  congrFun (congrFun (congrFun (congrFun recordSeeds_text f) name) bits) count

/-- The step of a chain in a round without work, at a letter for the hash: where the round may be
asked it returns the next chain and the verifier's message. -/
theorem queryW_noWork (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (lab : ℕ)
    (ρ : ByteArray) (i : ℕ) (msg : ByteArray) (kind : Fmt.Kind) (nonce K : ℕ)
    (hok : Fmt.askOK lab ρ (i + 1) msg kind 0 nonce = true) :
    Fmt.Chain.queryW (m := Id) h ⟨lab, ρ, i⟩ msg kind 0 nonce K =
      some (⟨lab, Fmt.nextA 0 (Fmt.fetchW (m := Id) h lab ρ (i + 1) msg kind 0 nonce
          (Fmt.firstBlock 0 + K)), i + 1⟩,
        Fmt.msgA 0 (Fmt.fetchW (m := Id) h lab ρ (i + 1) msg kind 0 nonce
          (Fmt.firstBlock 0 + K))) := by
  rw [Fmt.Chain.queryW, if_pos hok]
  rfl

/-- **The program's seeds are the program's draws on the format's oracle's answers at the written
strings.** The bound keeps the first string within the hash's domain. -/
theorem recordSeeds_blocks (f : Fmt.Fld) (name : ByteArray) (bits count : ℕ)
    (hn : name.size + 56 ≤ 2 ^ 32 - 144) :
    recordSeeds f name bits count = some (seedsAtName f name bits count) := by
  have hs : (Fmt.recordFirst name).size = 32 := Fmt.size_H _ _ _ _ _
  have hv : Fmt.msgA 0 (Fmt.fetchW (m := Id) Fmt.formatHash Fmt.recordLabel (Fmt.recordFirst name) (0 + 1)
      ByteArray.empty .seeds 0 0 (Fmt.firstBlock 0 + nBlocks bits count)) =
      (Array.range (nBlocks bits count)).map (seedBlock name) := by
    refine Array.ext_getElem? fun k => ?_
    have e := row_get Fmt.recordLabel (Fmt.recordFirst name) (0 + 1) ByteArray.empty .seeds 0
      (nBlocks bits count) k
    rw [show (Fmt.msgA 0 (Fmt.fetchW (m := Id) Fmt.formatHash Fmt.recordLabel (Fmt.recordFirst name) (0 + 1)
      ByteArray.empty .seeds 0 0 (Fmt.firstBlock 0 + nBlocks bits count)))[k]? = _ from e,
      Array.getElem?_map, Array.getElem?_range]
    by_cases hk : k < nBlocks bits count
    · rw [if_pos hk, if_pos hk, half_oracle _ hs, recordFirst_oracle name hn]
      rfl
    · rw [if_neg hk, if_neg hk]
      rfl
  rw [recordSeeds_apply, Fmt.Chain.query,
    queryW_noWork Fmt.formatHash Fmt.recordLabel (Fmt.recordFirst name) 0 ByteArray.empty .seeds 0
      (nBlocks bits count) (seed_askOK _ hs), Option.map_some, hv, seedsAtName]

/-! ## The blocks as digests -/

/-- The first K blocks of the verifier's message in the seeds' round, as digests. -/
def seedDigs (name : ByteArray) (K : ℕ) : Fin K → Iop.Dig 256 :=
  fun t => Run.bytesToDig (seedBlock name t.val)

/-- The seeds, of K digests: the first `nBlocks` of them as bytes, then the program's own draws. -/
def seedsOfDigs (f : Fmt.Fld) (bits count : ℕ) {K : ℕ} (a : Fin K → Iop.Dig 256) :
    List (List E × E) :=
  seedsOf f bits count ((Array.range (nBlocks bits count)).map fun t =>
    if h : t < K then Run.digToBytes (a ⟨t, h⟩) else ByteArray.empty)

/-- The seeds of the K digests of the seeds' round are the seeds at the name, if K is at least the
number of blocks that the program fetches. -/
theorem seedsOfDigs_seedDigs (f : Fmt.Fld) (name : ByteArray) (bits count K : ℕ)
    (hK : nBlocks bits count ≤ K) :
    seedsOfDigs f bits count (seedDigs name K) = seedsAtName f name bits count := by
  have e : ((Array.range (nBlocks bits count)).map fun t =>
      if h : t < K then Run.digToBytes (seedDigs name K ⟨t, h⟩) else ByteArray.empty) =
      (Array.range (nBlocks bits count)).map (seedBlock name) := by
    refine Array.map_congr_left fun k hk => ?_
    have hk' : k < nBlocks bits count := Array.mem_range.1 hk
    have hb : Run.digToBytes (Run.bytesToDig (seedBlock name k)) = seedBlock name k :=
      Run.TieTree.dig_bytes (seedBlock name k) (by unfold seedBlock; exact Fmt.size_oracle _)
    rw [dif_pos (show k < K by omega)]
    exact hb
  unfold seedsOfDigs seedsAtName
  rw [e]

/-! ## The keys that the program's checks use -/

/-- A table's name has 48 bytes more than its root and the configuration's digest. -/
theorem size_nameOf (s : Params.IndexShape) (cfg : ByteArray) (t : Params.TableName) :
    (Key.nameOf s cfg t).size = t.root.size + cfg.size + 48 := by
  simp only [Key.nameOf, Fmt.tableName, ByteArray.size_append, Fmt.size_u64n]

/-- **The seeds in a key that `tableKey` returns**, for tables with a record: the program's draws on
the format's oracle's answers at the written strings, at the table's name. The key's other two
fields are the item's number and the table's answers. -/
theorem tableKey_seeds (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : ℕ) (k : TableKey)
    (h : tableKey f cfg s table item = some k) (ha : s.answers ≠ 0)
    (hn : (Key.nameOf s cfg table).size + 56 ≤ 2 ^ 32 - 144) :
    k.seeds = (seedsAtName f (Key.nameOf s cfg table) s.cubeBits s.answers).map
        (fun x => ⟨x.1, x.2⟩) ∧
      k.item = item ∧ k.record = table.answers.toArray := by
  unfold tableKey at h
  rw [show Fmt.tableName table.root cfg s.code.logN s.code.ell s.code.r s.v s.answers s.saltBytes =
      Key.nameOf s cfg table from rfl, recordSeeds_blocks _ _ _ _ hn] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · injection h with h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- **If `Entry.check` says yes**, the block that `Tie.entrySpec` (OnBytes/Tie/EntryFile.lean: the
block and the description of an entry's chain) gives for the two tables is `linkVerify` at the two
keys that `tableKey` gives for the first table (item 0) and for the table that the check returns
(item 1). With `tableKey_seeds`: their seeds are functions of the two tables' names. That the check
read or judged under that block is no part of this statement. -/
theorem entry_check_keys (params : ByteArray) (first further : Params.TableName)
    (file : ByteArray) (h : Entry.check params first file = .ok further) :
    ∃ (p : Params.Link) (k0 k1 : TableKey) (S : Fmt.SpecX),
      Params.Link.read params = some p ∧
      tableKey p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 = some k1 ∧
      Tie.entrySpec p first further = some (linkVerify p.link k0 k1, S) := by
  obtain ⟨p, block, S, j, r, s', hp, hs, -⟩ := Tie.entry_check_compiled params first further file h
  have hs' := hs
  unfold Tie.entrySpec at hs'
  split at hs'
  · rename_i k0 k1 h0 h1
    obtain ⟨S', -, e⟩ := Option.map_eq_some_iff.1 hs'
    have eb : block = linkVerify p.link k0 k1 := (congrArg (·.1) e).symm
    exact ⟨p, k0, k1, S, hp, h0, h1, eb ▸ hs⟩
  · cases hs'

/-- The root of the table that `Entry.check` returns has 32 bytes. -/
theorem entry_check_root (params : ByteArray) (first further : Params.TableName)
    (file : ByteArray) (h : Entry.check params first file = .ok further) :
    further.root.size = 32 := by
  unfold Entry.check at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i r hr
      split at h
      · have hfur : r.further = further := by
          injection h
        subst hfur
        obtain ⟨j, S, s', -, -, h32⟩ := Tie.entry_read_spec p first file r hr
        exact h32
      · cases h

/-- **If `Entry.check` says yes against a first table with a root of 32 bytes**, under parameters
with a configuration's digest of 32 bytes and tables with a record: the seeds in the two keys of the
block that `Tie.entrySpec` gives are the program's draws on the format's oracle's answers at the
written strings, at the two tables' names. -/
theorem entry_check_seeds (params : ByteArray) (first further : Params.TableName)
    (file : ByteArray) (h : Entry.check params first file = .ok further)
    (h0 : first.root.size = 32) :
    ∃ (p : Params.Link) (k0 k1 : TableKey) (S : Fmt.SpecX),
      Params.Link.read params = some p ∧
      tableKey p.given.plan.field p.given.cfg p.link.table first 0 = some k0 ∧
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 = some k1 ∧
      Tie.entrySpec p first further = some (linkVerify p.link k0 k1, S) ∧
      (p.link.table.answers ≠ 0 → p.given.cfg.size = 32 →
        k0.seeds = (seedsAtName p.given.plan.field (Key.nameOf p.link.table p.given.cfg first)
          p.link.table.cubeBits p.link.table.answers).map (fun x => ⟨x.1, x.2⟩) ∧
        k1.seeds = (seedsAtName p.given.plan.field (Key.nameOf p.link.table p.given.cfg further)
          p.link.table.cubeBits p.link.table.answers).map (fun x => ⟨x.1, x.2⟩)) := by
  obtain ⟨p, k0, k1, S, hp, e0, e1, hS⟩ := entry_check_keys params first further file h
  have h1 := entry_check_root params first further file h
  refine ⟨p, k0, k1, S, hp, e0, e1, hS, fun ha hc => ⟨?_, ?_⟩⟩
  · exact (tableKey_seeds _ _ _ _ _ _ e0 ha (by rw [size_nameOf, h0, hc]; decide)).1
  · exact (tableKey_seeds _ _ _ _ _ _ e1 ha (by rw [size_nameOf, h1, hc]; decide)).1

open OnBytes.Proof in
/-- The key in a tail that was read is the one that `tableKey` gives for the tail's table. -/
theorem readTail_key (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray)
    (s s' : Session) (r : TailRead) (h : readTail p dry first b s = .ok (r, s')) :
    tableKey p.shared.given.plan.field p.shared.given.cfg p.lin.fold.index p.table 0 =
      some r.key := by
  unfold readTail at h
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨key, _, h3, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨e3, -⟩ := Tie.need_ok _ _ _ _ _ h3
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  obtain ⟨_, _, _, h⟩ := Tie.bind_ok _ _ _ _ _ h
  injection h with h1
  rw [← (congrArg (·.1.key) h1 : key = r.key)]
  exact e3

attribute [local irreducible] tableKey in
open OnBytes.Proof in
/-- The key in what `Key.readKey` returns. -/
theorem readKey_key (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray) (j : ℕ)
    (s s' : Session) (t : TailRead) (h : Key.readKey k table file j s = .ok (t, s')) :
    tableKey k.shared.given.plan.field k.shared.given.cfg k.shared.lin.fold.index table 0 =
      some t.key := by
  unfold Key.readKey at h
  obtain ⟨⟨rounds, dry⟩, s1, h1, ha⟩ := Tie.bind_ok _ _ _ _ _ h
  dsimp only at ha
  obtain ⟨S, s2, h2, hb⟩ := Tie.bind_ok _ _ _ _ _ ha
  obtain ⟨first, s3, h3, hc⟩ := Tie.bind_ok _ _ _ _ _ hb
  obtain ⟨r, s4, h4, hd⟩ := Tie.bind_ok _ _ _ _ _ hc
  split at hd
  · obtain ⟨_, _, hth, _⟩ := Tie.bind_ok _ _ _ _ _ hd
    cases hth
  · obtain ⟨_, s5, _, he⟩ := Tie.bind_ok _ _ _ _ _ hd
    injection he with h5
    have e5 : r = t := congrArg (·.1) h5
    subst e5
    exact readTail_key _ _ _ _ _ _ _ h4

open OnBytes.Proof in
/-- **If `Key.check` says yes**, `Key.readKey` reads the file's two later chains, from some byte
offset, and the key in what it has read is the one that `tableKey` gives for the table that the
check returns (item 0), at the shared chain's parameters. With `tableKey_seeds`: its seeds are a
function of the table's name. That the check judged under that key is no part of this statement. -/
theorem key_check_key (k : Params.KeyChains) (file : ByteArray) (table : Params.TableName)
    (h : Key.check k file = .ok table) :
    ∃ (j : ℕ) (t : TailRead) (s' : Session),
      Key.readKey k table file j Session.start = .ok (t, s') ∧
      tableKey k.shared.given.plan.field k.shared.given.cfg k.shared.lin.fold.index table 0 =
        some t.key := by
  unfold Key.check at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i table' j hrt
        split at h
        · cases h
        · rename_i t ht
          split at h
          · cases h
          · injection h with h'
            subst h'
            have hrun : ∃ s', Key.readKey k table' file j Session.start = .ok (t, s') := by
              unfold Reading.fromStart at ht
              cases hq : Key.readKey k table' file j Session.start with
              | error e => rw [hq] at ht; cases ht
              | ok y =>
                rw [hq] at ht
                injection ht with hy
                exact ⟨y.2, by rw [← hy]⟩
            obtain ⟨s', hs'⟩ := hrun
            exact ⟨j, t, s', hs', readKey_key k table' file j _ _ t hs'⟩

end OnBytes.K
