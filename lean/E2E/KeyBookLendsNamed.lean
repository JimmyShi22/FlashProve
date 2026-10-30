-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookLendsNamed.lean: at the key file's book of coins, at the written sizes of the full size,
the frame (Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest prover is written,
and the functions that run it) gives a list of parts its coins if each part states exactly what the
book has for it. This is the theorem `key_lends`: `lendRow`, the frame's function that gives the
parts at a place their coins, returns no error. It holds at every place in the literal lists of the
three chains' places (E2E/KeyPlaces.lean), at all coins, and at every list of parts that meets the
hypothesis. It is `lendRow_ok` (E2E/KeyBookLends.lean), which is general in the book, applied to
this book. It matters because the frame's `chainSteps`, which prepares a chain's rounds, returns
an error where `lendRow` does. Four lemmas at the end, general in the book's counts of coins and in
the two lookups' faces, help to prove the hypothesis of a part. Definitions and theorems.

Terms. A book (`ProverCoinCounts`, in the frame) is a public table; here it is `keyBook K` (E2E/KeyBook.lean),
computed from the public data K (`KeyPub`). For each of the three chains (number 0: the first, 1:
the shared, 2: the second) it has a table of rows: a row is the address of a part (`Addr`: a place,
and the part's number there) with that part's count of coins (`Due`: so many of the base field, so
many of the extension field). A place (`Place`) is the label of a sub-protocol. An entry (`Ahead`)
is a named block of the coins of one part, its owner, that one other part, its spender, is given
too; it is marked as spent or as carried. A part (`Part`) is the prover's side of some consecutive
rounds of a sub-protocol. It states its own count (`takes`) and the names and counts of the entries
that it spends and carries. `Stated B rows a p` (E2E/KeyBookLends.lean) says that these three fields
of p are what the book B has for the address a: the count of a's row in the table rows (0 if it has
none), and the names and counts of the spent and of the carried entries whose spender is a, in the
book's order. A face (`K3.Face`, Johnson/Desc/First/Look/K3LookupGeneral.lean) holds a lookup's public
parameters.

  `key_lends`: under the four hypotheses below, at any coins c of the book (`Coins (keyBook K)`) and
    at parts of any types V, W, X: `lendRow (keyBook K) ((keyBook K).rowsOf ch) (c.look ch) a ps 0`
    returns coins. `rowsOf ch` is the book's table for the chain, and `c.look ch` gives the coins
    that the chain may be given, by address
  `full_lends`: `lendsSmall` is true at the written sizes. By evaluation in Lean's kernel
    (`decide +kernel`)
  `full_lends_no`: a negative test, by evaluation in the kernel too: `lendsSmall` is false where the
    index-mask message has one coin fewer than the spent entries take of it
  `lendsSmall K`: a definition: the Boolean that the kernel evaluates. For each chain, each of the
    25 entries that are not the lookups' (`K.others`, E2E/KeyBookPasses.lean) and whose spender is
    at a place of the chain lies within its owner's count in the tables that the chain sees (`seen`,
    E2E/KeyBookLends.lean). No row of the first or the shared chain is at a place of the second
    chain. `K.top`, the two owners' next unused coins after the lookups' entries, is within the
    counts of the two owners' rows in the first chain's table
  `chainPlaces ch`: a definition: the places of chain number ch in the literal lists `fullFirst`,
    `fullShared` and `fullSecond`
  `withinB T e`: a definition: as a Boolean: the block of the entry e ends within its owner's count
    in the table T
  `lookup_none`: a table that has no row at the place a returns nothing at any address ⟨a, j⟩
  `mine_off_looks`: at every K with two faces: the book's entries whose spender is a given address
    at neither lookup's place are those of `K.others` with that spender
  `others_spenders`, `others_none`: at every K: the list of the spenders of `K.others` does not
    depend on K; no entry of `K.others` has a spender outside that list
  `stated_nothing`: at every K with two faces: a part that takes, spends and carries nothing is
    `Stated` at an address that is at neither lookup's place, has no row in the table and is not
    among the spenders of `K.others`

By what. `key_lends` is `lendRow_ok` (E2E/KeyBookLends.lean); its two other hypotheses are proved
here. The first: each part's count in the chain's table is within what `c.look ch` has at its
address. `look_due` (same file) gives the count of `c.look ch` as `dueAt (seen B ch)`. Chains 0 and
1 see their own table only. Chain 2 sees all three, and the second conjunct of `lendsSmall`, with
`lookup_none`, shows that the first two have no row at the place. The second: every entry whose
spender is at the place is `Within (c.look ch)`. `ahead_eq` (E2E/KeyBookPasses.lean) divides the
book's entries into the lookups' (`K.looks`) and `K.others`. The lookups' entries are not evaluated
one by one (there are 983 + 967 at these sizes, by a `#guard` on the number of spent entries in
E2E/KeyBookAtWritten.lean). `looks_block` (E2E/KeyBookPasses.lean, from `lay_block`,
E2E/KeyBookTile.lean) shows of each: its spender is at a lookup's place, which is in neither
`chainPlaces 1` nor `chainPlaces 2`; it has no coin of the base field; and it ends at `K.top` or
before, among the coins of one of two owners. The last two conjuncts of `lendsSmall` bound `K.top`.
For the entries of `K.others` the first conjunct says it. `of_atFull` brings the evaluations
`full_lends` and `full_two` (there are two lookups) to K; it and `full_two` are in
E2E/KeyBookPassesNamed.lean. `mine_off_looks` follows from `ahead_eq` and `looks_block`,
`others_spenders` holds by `rfl`, and `stated_nothing` follows from `mine_off_looks` and
`others_none`. Definitions: `fullPub`, `atFull` (E2E/KeyBookAtWritten.lean); `lookPlace`,
`msgPlace`, `idxPlace` (E2E/KeyPlaces.lean); `toyPub` (E2E/KeyBookTests.lean); `dueAt`,
`ProverCoinCounts.rowsOf`, `Coins.look` (the frame).

Hypotheses of `key_lends`. hK: `fullPub = some K`: K is the public data that `KeyPub.of` returns at
the library's written sizes of the full size (`keyFull`); `full_made` (E2E/KeyBookPassesNamed.lean)
shows that there is such a K. hch: ch is 0, 1 or 2. ha: the place a is in `chainPlaces ch`. hs: for
every i, part number i of the list ps is `Stated` at the book, at the table `(keyBook K).rowsOf ch`
and at the address ⟨a, i⟩.

Limits.
- Coins only, as in E2E/KeyBookLends.lean. `chainSteps` has other tests on a list of parts, of which
  nothing is shown: that it has as many rounds as its sub-protocol, that it is cut as the book says,
  and that it has a part for every row and entry of the book at its place. Nothing is said on what a
  part does with its coins.
- `Stated` is a hypothesis. Whoever defines a list of parts has to prove it. This file proves it of
  no part of a prover: `stated_nothing` is general in the part. E2E/KeyBookHeldK1.lean and
  E2E/KeyBookHeldHash.lean, which import this file, prove it of some parts, under hypotheses of
  their own.
- The list of a lookup's parts `lookRow` (Johnson/Desc/ProofFile/Honest/K3/Row.lean) is not
  `Stated` at this book: it states other names than the book's entries have (see the limits of
  E2E/KeyBookHeldK3.lean). This is by reading of the two definitions; no theorem says it. Of the
  list that takes the owners' names as a parameter (`lookRowOwned`,
  Johnson/Desc/ProofFile/Honest/K3/RowOwned.lean) `Stated` is not shown either.
- The book's carried entries are a proposal (see the limits of E2E/KeyBook.lean). The theorems are
  stated at the book that has them.
- That `rowsOf ch`, `c.look ch` and the part number 0 are the arguments with which the frame calls
  `lendRow` in a run (`ready`, `sharedSteps`, `chainSteps`) is by reading of the frame; no statement
  here says it.
- The full size only. `key_lends` and the two evaluations are at `fullPub`, and `chainPlaces` reads
  literal lists. That the key file's description has these places at public files in scope is
  `places_named` (E2E/KeyPlacesNamed.lean), which is not called here. `mine_off_looks` and
  `stated_nothing` are for two lookups, as the key file has at the full size.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookLends
import E2E.KeyBookPassesNamed

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (Face)
open ProofFile.Honest

variable {V W X : Type}

/-- The places of chain number ch, from 0, in the literal lists of E2E/KeyPlaces.lean: those of
`fullFirst` at 0, of `fullShared` at 1, of `fullSecond` at every other ch. -/
def chainPlaces (ch : Nat) : List Place :=
  if ch == 0 then fullFirst.map (·.1) else if ch == 1 then fullShared.map (·.1)
  else fullSecond.map (·.1)

/-- As a Boolean: in each of the two fields the entry's block, `count` coins from number `start` on,
ends within the count that the table T has for the entry's owner (`dueAt`: 0 if the owner has no
row). -/
def withinB (T : List (Addr × Due)) (e : Ahead) : Bool :=
  decide (e.start.f + e.count.f ≤ (dueAt T e.owner).f) &&
    decide (e.start.e + e.count.e ≤ (dueAt T e.owner).e)

/-- What `key_lends` takes from an evaluation, at the book `keyBook K`. Four conjuncts. (1) For each
chain number 0, 1 and 2: every entry of `K.others` whose spender is at a place of the chain passes
`withinB` at the tables that the chain sees (`seen`). (2) No row of the first or the shared chain's
table is at a place of the second chain. (3), (4) `K.top`, the two owners' next unused coins after
the lookups' entries, is at most the count, in the extension field, of the first chain's row at
`⟨msgPlace, 0⟩` and at `⟨idxPlace, 0⟩`. -/
def lendsSmall (K : KeyPub) : Bool :=
  let B := keyBook K
  ([0, 1, 2].all fun ch =>
      K.others.all fun e => !(chainPlaces ch).contains e.spender.place || withinB (seen B ch) e) &&
    (B.first ++ B.shared).all (fun r => !(chainPlaces 2).contains r.1.place) &&
    decide (K.top.1 ≤ (dueAt B.first ⟨msgPlace, 0⟩).e) &&
    decide (K.top.2 ≤ (dueAt B.first ⟨idxPlace, 0⟩).e)

theorem full_lends : atFull lendsSmall = true := by decide +kernel

/-- A negative test: `lendsSmall` is false at the K of the written sizes with its field `sIdx`
replaced. `sIdx` is the sending of the index-mask message (`Sending`, E2E/KeyBook.lean: a list of
oracle messages' counts of coins); it is replaced by one message whose only coins are 84 in its mask
table. That is one coin fewer than the spent entries take of it: the lookups' take 48 and the
batching's takes `1 + 2 * K.kCol`, where `K.kCol` is 18 (`#guard`s in E2E/KeyBookAtWritten.lean
state the 48, and the batching's cut `[1, 1 + K.kCol]` as `[1, 19]`). The theorem does not say which
conjunct is false. -/
theorem full_lends_no :
    atFull (fun K => lendsSmall { K with sIdx := [⟨0, 0, 84, 0⟩] }) = false := by
  decide +kernel

theorem lookup_none {l : List (Addr × Due)} {a : Place} (h : ∀ r ∈ l, r.1.place ≠ a) (j : Nat) :
    l.lookup ⟨a, j⟩ = none := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [List.lookup_cons]
    have hne : ((⟨a, j⟩ : Addr) == r.1) = false := beq_eq_false_iff_ne.2 fun e =>
      h r List.mem_cons_self (by rw [← e])
    rw [hne]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- **At the key file's book a list of parts that state what the book has for them is given its
coins.** The head explains the hypotheses. -/
theorem key_lends (K : KeyPub) (hK : fullPub = some K) (c : Coins (keyBook K)) (ch : Nat)
    (hch : ch = 0 ∨ ch = 1 ∨ ch = 2) (a : Place) (ha : (chainPlaces ch).contains a = true)
    (ps : List (Part V W X))
    (hs : ∀ i p, ps[i]? = some p → Stated (keyBook K) ((keyBook K).rowsOf ch) ⟨a, i⟩ p) :
    ∃ r, lendRow (keyBook K) ((keyBook K).rowsOf ch) (c.look ch) a ps 0 = .ok r := by
  have h2 := of_atFull full_two hK
  obtain ⟨f₀, f₁, hf⟩ := List.length_eq_two.1 (by simpa using h2)
  have hsm := of_atFull full_lends hK
  simp only [lendsSmall, decide_eq_true_eq, Bool.and_eq_true] at hsm
  obtain ⟨⟨⟨s1, s2⟩, s3⟩, s4⟩ := hsm
  rw [List.all_eq_true] at s1 s2
  have hmem : ch ∈ [0, 1, 2] := by rcases hch with rfl | rfl | rfl <;> simp
  have s1' := List.all_eq_true.1 (s1 ch hmem)
  refine lendRow_ok _ _ _ a ?_ ?_ ps 0 fun i p hp => by
    rw [Nat.zero_add]
    exact hs i p hp
  · -- each part's own count is within what the chain may be given at the part's address
    intro j
    rw [look_due]
    rcases hch with rfl | rfl | rfl
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · have hn : ((keyBook K).first ++ (keyBook K).shared).lookup ⟨a, j⟩ = none :=
        lookup_none (fun r hr e => by
          have := s2 r hr
          rw [e, ha] at this
          cases this) j
      have e : dueAt (seen (keyBook K) 2) ⟨a, j⟩ = dueAt ((keyBook K).rowsOf 2) ⟨a, j⟩ := by
        show (((keyBook K).first ++ (keyBook K).shared ++ (keyBook K).second).lookup _).getD _ =
          ((keyBook K).second.lookup _).getD _
        rw [List.lookup_append, hn]
        rfl
      rw [e]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · -- every entry whose spender is at the place lies within what the chain sees of its owner
    intro e he hp
    unfold Within
    rw [look_due]
    rw [ahead_eq, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨i, hi, -, e2, e3, e4, e5⟩ := looks_block hf e he
      have h0 : ch = 0 := by
        rw [← hp, e4] at ha
        rcases hch with rfl | rfl | rfl
        · rfl
        · rcases hi with rfl | rfl <;> exact absurd ha (by decide)
        · rcases hi with rfl | rfl <;> exact absurd ha (by decide)
      subst h0
      rw [e2, e3]
      refine ⟨Nat.zero_le _, ?_⟩
      show _ ≤ (dueAt (keyBook K).first e.owner).e
      rcases e5 with ⟨o, -, h⟩ | ⟨o, -, h⟩ <;> rw [o] <;> omega
    · have := s1' e he
      rw [hp, ha] at this
      simp only [Bool.not_true, Bool.false_or, withinB, decide_eq_true_eq, Bool.and_eq_true] at this
      exact this

/-! ## What the book has for a part at neither lookup's place -/

theorem mine_off_looks {K : KeyPub} {f₀ f₁ : Face} (hf : K.faces = [f₀, f₁]) (a : Addr)
    (h0 : a.place ≠ lookPlace 0) (h1 : a.place ≠ lookPlace 1) :
    (keyBook K).ahead.filter (fun e => e.spender == a) =
      K.others.filter fun e => e.spender == a := by
  rw [ahead_eq, List.filter_append]
  have : K.looks.filter (fun e => e.spender == a) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he hs
    obtain ⟨i, hi, -, -, -, e4, -⟩ := looks_block hf e he
    have := beq_iff_eq.1 hs
    rw [← this, e4] at h0 h1
    rcases hi with rfl | rfl
    · exact h0 rfl
    · exact h1 rfl
  rw [this, List.nil_append]

/-- The list of the spenders of the 25 entries of `K.others` does not depend on K: it is the list at
the small example `toyPub` (E2E/KeyBookTests.lean). -/
theorem others_spenders (K : KeyPub) : K.others.map (·.spender) = toyPub.others.map (·.spender) :=
  rfl

/-- No entry of `K.others` has as its spender an address outside that list, taken at `toyPub`. -/
theorem others_none (K : KeyPub) (a : Addr)
    (h : (toyPub.others.map (·.spender)).contains a = false) :
    K.others.filter (fun e => e.spender == a) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he hs
  have hm : e.spender ∈ K.others.map (·.spender) := List.mem_map_of_mem he
  rw [others_spenders, beq_iff_eq.1 hs] at hm
  have := List.contains_iff_mem.2 hm
  rw [h] at this
  cases this

/-- A part that takes, spends and carries nothing is `Stated` at an address for which the book has
nothing: it is at neither lookup's place, has no row in the table rows, and is not among the
spenders of `K.others`. -/
theorem stated_nothing {V W X : Type} {K : KeyPub} {f₀ f₁ : Face} (hf : K.faces = [f₀, f₁])
    (rows : List (Addr × Due)) (a : Addr) (p : Part V W X) (h0 : a.place ≠ lookPlace 0)
    (h1 : a.place ≠ lookPlace 1) (hr : rows.lookup a = none)
    (hn : (toyPub.others.map (·.spender)).contains a = false)
    (hp : (p.takes, p.spends, p.carries) = (⟨0, 0⟩, [], [])) : Stated (keyBook K) rows a p := by
  unfold Stated hasFor
  rw [mine_off_looks hf a h0 h1, others_none K a hn, hp]
  unfold dueAt
  rw [hr]
  rfl

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.full_lends
#print axioms AtPublicFiles.KeyBook.full_lends_no
#print axioms AtPublicFiles.KeyBook.key_lends
#print axioms AtPublicFiles.KeyBook.mine_off_looks
#print axioms AtPublicFiles.KeyBook.stated_nothing
#print axioms AtPublicFiles.KeyBook.chainPlaces
#print axioms AtPublicFiles.KeyBook.withinB
#print axioms AtPublicFiles.KeyBook.lendsSmall
#print axioms AtPublicFiles.KeyBook.lookup_none
#print axioms AtPublicFiles.KeyBook.others_spenders
#print axioms AtPublicFiles.KeyBook.others_none
