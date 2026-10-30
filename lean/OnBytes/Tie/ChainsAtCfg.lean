-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/ChainsAtCfg.lean: if `chainsOf`, a function of the Lean port of the C++ verifier ("the
program" below), returns its seven chains at one digest of 32 bytes, it returns them at every other
digest of 32 bytes, the same but for the digest and the parameter bytes, under the 3 hypotheses
below. A bound under a random oracle for a verifier that forms the digest by the oracle needs this
at every value of the digest.
A chain is the non-interactive form of one protocol; a key file has three, an entry file one, a
proof file three. `chainsOf X lay c`, with c in the place of the digest of the public files, makes
shapes and sizes, tests the links, calls the planner with c, and reads the planner's seven strings
of parameter bytes back; it refuses if a reader does. `planned` forms the digest by the format's
hash and calls `chainsOf` with it. `plannedAt`, defined here, is the text of `planned` with the
digest as an argument.
States, with smaller theorems around these:
(1) `chainsOf_at` (3 hypotheses): if `chainsOf X lay c` returns ch, then `chainsOf X lay c'` returns
    `chainsAtCfg ch c'`, a function of ch and c' alone: in each chain as read back c' is the digest
    and the bytes are spelled anew from the chain's own plan and items; the planner's seven strings
    are these bytes; sizes and plans are the same.
(2) `plannedAt_at` (the same 3): what `plannedAt` returns at c it returns at c', with c' as its
    digest and the chains put at c'. `planned_eq` (0, by definition): `planned` is `plannedAt` at
    the digest that the format's hash gives.
Under: c and c' have 32 bytes each (2); each of the seven strings in ch, in (2) in the chains of
what `plannedAt` returns at c, has fewer than 2 ^ 64 bytes (1).
Does not show:
(1) The whole call's text over a monad forms the digest by the hash that it is handed
    (`M.Model.Verify.planned`), and `K.Oracle.askedAt` runs that text at an oracle; nothing is
    stated of either here. No bound under a random oracle for the program is in OnBytes/: the
    program forms the digest by BLAKE2b.
(2) That each of the seven strings has fewer than 2 ^ 64 bytes is a hypothesis. For three of them
    OnBytes/Tie/SameChains.lean takes it from a yes of the file's check, for two of these at a value
    of `planned` alone, so not at what `plannedAt` returns at another digest. For the other four
    that file gives nothing; `short_of_test` (OnBytes/Tie/PlanAtDigest.lean) takes the bound for
    all seven from a yes of the test `shortB` on a plan, not from the program's yes on a whole
    call.
(3) No probability and nothing on soundness.
(4) Nothing if `chainsOf` refuses at c.
(5) Nothing on what the stages do with the digest behind `planned`.
(6) `chainsOf_at` holds at a c' of 32 zero bytes too, a digest that three later tests refuse.
(7) That `chainsOf` returns a value on any files is not shown.
(8) All limits in the heads of the imported files and of the file named in (2) hold here too.
(9) For proofs only; the program does not import this file.

Notes in full, with every limit at length, stand at the end of this file.
-/
import OnBytes.Tie.EntryPlanAtCfg
import OnBytes.Params.ReadBackAt
import OnBytes.Model.VerifyRead

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Params OnBytes.Model OnBytes.Model.Verify

/-- The five names of the items of a key's one-time chain are within the format's rule for names. -/
theorem names_oneTime (z : Plan.KeySized) : ∀ y ∈ Plan.oneTimeItems z, Fmt.okName y.1 = true := by
  intro y hy
  simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

/-- So are the two names of the items of a shared chain. -/
theorem names_lin (codes : Codes) (S : LinShape) :
    ∀ y ∈ linItems codes S, Fmt.okName y.1 = true := by
  intro y hy
  simp only [linItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> (dsimp only; decide)

/-- So are the two names of the items of an entry's chain. -/
theorem names_entry (z : Sized) : ∀ y ∈ entryItems z, Fmt.okName y.1 = true := by
  intro y hy
  simp only [entryItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> (dsimp only; decide)

/-- So are the seven names of the items of a proof's first chain. -/
theorem names_first (l : Lines) (x : Shapes) (z : Sized) :
    ∀ y ∈ proofFirstItems l x z, Fmt.okName y.1 = true := by
  intro y hy
  simp only [proofFirstItems, linItems, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hy
  rcases hy with (rfl | rfl) | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

/-- A second chain has no items. -/
theorem names_none : ∀ y ∈ ([] : List (String × ByteArray)), Fmt.okName y.1 = true :=
  fun _ h => absurd h List.not_mem_nil

/-- A key's three chains as read back, each with c' in the place of the digest and its bytes spelled
anew. -/
def keyAtCfg (q : KeyChains) (c' : ByteArray) : KeyChains :=
  ⟨{ q.oneTime with given := q.oneTime.given.atCfg c' },
    { q.shared with given := q.shared.given.atCfg c' },
    { q.second with given := q.second.given.atCfg c' }⟩

/-- A proof's three chains as read back, each with c' in the place of the digest and its bytes
spelled anew. -/
def proofAtCfg (q : ProofChains) (c' : ByteArray) : ProofChains :=
  ⟨{ q.first with given := q.first.given.atCfg c' },
    { q.shared with given := q.shared.given.atCfg c' },
    { q.second with given := q.second.given.atCfg c' }⟩

/-- The seven chains with c' in the place of the digest: each chain as read back is put at c'; the
planner's value holds c' and, as its seven strings, the bytes of these; its sizes and plans stay. -/
def chainsAtCfg (ch : Chains) (c' : ByteArray) : Chains :=
  { made := { ch.made with
      configuration := c'
      keyOneTime := (ch.key.oneTime.given.atCfg c').bytes
      keyShared := (ch.key.shared.given.atCfg c').bytes
      keySecond := (ch.key.second.given.atCfg c').bytes
      entryLink := (ch.link.given.atCfg c').bytes
      first := (ch.proof.first.given.atCfg c').bytes
      shared := (ch.proof.shared.given.atCfg c').bytes
      second := (ch.proof.second.given.atCfg c').bytes }
    key := keyAtCfg ch.key c'
    link := linkAtCfg ch.link c'
    proof := proofAtCfg ch.proof c' }

/-- **The seven chains at c, so at c'.** If `chainsOf X lay c` returns ch, the two digests have 32
bytes and the seven strings in ch fewer than 2^64 bytes each, then `chainsOf X lay c'` returns
`chainsAtCfg ch c'`. The proof follows the text of `chainsOf`: the steps before the planner do not
take the digest; the planner by `configure_at`; the three readers by `Params.KeyChains.read_at`,
`Params.Link.read_at` and `Params.ProofChains.read_at`; that the planner's strings at c' are the
bytes of the chains as read back by `Params.Given.read_spells`. Nothing on soundness. -/
theorem chainsOf_at {X : Public} {lay : Option ByteArray} {c c' : ByteArray} {ch : Chains}
    (hc : c.size = 32) (hc' : c'.size = 32) (hb : ∀ n : ChainName, (ch.bytes n).size < 2 ^ 64)
    (h : chainsOf X lay c = .ok ch) : chainsOf X lay c' = .ok (chainsAtCfg ch c') := by
  unfold chainsOf at h
  obtain ⟨⟨links, shapes⟩, e1, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨z, e2, h⟩ := exc_bind h
  obtain ⟨u, e3, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  obtain ⟨k1, k2, k3, p1, p2, p3, -, -, hall⟩ := configure_at hm
  have hself := madeAt_self hm hall
  have s1 : made.keyOneTime = Fmt.paramsBytes k1.plan c (Plan.oneTimeItems made.sized.key) :=
    (congrArg Configured.keyOneTime hself).symm
  have s2 : made.keyShared = Fmt.paramsBytes k2.plan c
      (linItems made.sized.key.codes made.sized.key.once.shape) :=
    (congrArg Configured.keyShared hself).symm
  have s3 : made.keySecond = Fmt.paramsBytes k3.plan c [] :=
    (congrArg Configured.keySecond hself).symm
  have s4 : made.entryLink = Fmt.paramsBytes made.entry.plan c (entryItems made.sized) :=
    (congrArg Configured.entryLink hself).symm
  have s5 : made.first = Fmt.paramsBytes p1.plan c
      (proofFirstItems X.P.frame shapes made.sized) :=
    (congrArg Configured.first hself).symm
  have s6 : made.shared = Fmt.paramsBytes p2.plan c
      (linItems made.sized.proof.codes made.sized.proof.batch.shape) :=
    (congrArg Configured.shared hself).symm
  have s7 : made.second = Fmt.paramsBytes p3.plan c [] :=
    (congrArg Configured.second hself).symm
  cases hK : KeyChains.read made.keyOneTime made.keyShared made.keySecond with
  | none =>
    rw [hK] at h
    cases h
  | some key =>
    cases hL : Link.read made.entryLink with
    | none =>
      rw [hK, hL] at h
      cases h
    | some link =>
      cases hP : ProofChains.read made.first made.shared made.second with
      | none =>
        rw [hK, hL, hP] at h
        cases h
      | some proof =>
        rw [hK, hL, hP] at h
        cases h
        have b1 : made.keyOneTime.size < 2 ^ 64 := hb .keyOneTime
        have b2 : made.keyShared.size < 2 ^ 64 := hb .keyShared
        have b3 : made.keySecond.size < 2 ^ 64 := hb .keySecond
        have b4 : made.entryLink.size < 2 ^ 64 := hb .link
        have b5 : made.first.size < 2 ^ 64 := hb .proofFirst
        have b6 : made.shared.size < 2 ^ 64 := hb .proofShared
        have b7 : made.second.size < 2 ^ 64 := hb .proofSecond
        rw [s1] at b1
        rw [s2] at b2
        rw [s3] at b3
        rw [s4] at b4
        rw [s5] at b5
        rw [s6] at b6
        rw [s7] at b7
        rw [s1, s2, s3] at hK
        rw [s4] at hL
        rw [s5, s6, s7] at hP
        have n1 := names_oneTime made.sized.key
        have n2 := names_lin made.sized.key.codes made.sized.key.once.shape
        have n4 := names_entry made.sized
        have n5 := names_first X.P.frame shapes made.sized
        have n6 := names_lin made.sized.proof.codes made.sized.proof.batch.shape
        have K' := KeyChains.read_at b1 b2 b3 hc hc' n1 n2 names_none hK
        have L' := Link.read_at b4 hc hc' n4 hL
        have P' := ProofChains.read_at b5 b6 b7 hc hc' n5 n6 names_none hP
        obtain ⟨r1, r2, r3⟩ := KeyChains.read_each hK
        obtain ⟨r5, r6, r7⟩ := ProofChains.read_each hP
        have t1 := Given.read_spells b1 hc n1 (OneTime.read_given r1) c'
        have t2 := Given.read_spells b2 hc n2 (Shared.read_given r2) c'
        have t3 := Given.read_spells b3 hc names_none (Second.read_given r3) c'
        have t4 := Given.read_spells b4 hc n4 (Link.read_given hL) c'
        have t5 := Given.read_spells b5 hc n5 (First.read_given r5) c'
        have t6 := Given.read_spells b6 hc n6 (Shared.read_given r6) c'
        have t7 := Given.read_spells b7 hc names_none (Second.read_given r7) c'
        unfold chainsOf
        refine (exc_step _ e1).trans ?_
        dsimp only
        refine (exc_step _ e2).trans ?_
        refine (exc_step _ e3).trans ?_
        refine (exc_step _ (hall c')).trans ?_
        show (match KeyChains.read (Fmt.paramsBytes k1.plan c' (Plan.oneTimeItems made.sized.key))
            (Fmt.paramsBytes k2.plan c' (linItems made.sized.key.codes made.sized.key.once.shape))
            (Fmt.paramsBytes k3.plan c' []),
          Link.read (Fmt.paramsBytes made.entry.plan c' (entryItems made.sized)),
          ProofChains.read
            (Fmt.paramsBytes p1.plan c' (proofFirstItems X.P.frame shapes made.sized))
            (Fmt.paramsBytes p2.plan c'
              (linItems made.sized.proof.codes made.sized.proof.batch.shape))
            (Fmt.paramsBytes p3.plan c' []) with
          | some key, some link, some proof => _
          | _, _, _ => _) = _
        rw [K', L', P']
        unfold chainsAtCfg madeAt keyAtCfg proofAtCfg linkAtCfg Given.atCfg
        simp only [t1, t2, t3, t4, t5, t6, t7]
        rfl

/-- `builtOf` reads of the chains the proof's first chain, and of what that chain holds neither the
digest nor the bytes. -/
theorem builtOf_at (X : Public) (ch : Chains) (c' : ByteArray) :
    builtOf X (chainsAtCfg ch c') = builtOf X ch := rfl

/-- The shape of the stored tables does not hang on the digest. -/
theorem tableShape_at (ch : Chains) (c' : ByteArray) :
    (chainsAtCfg ch c').tableShape = ch.tableShape := rfl

/-- In what `chainsOf` returns, the bytes of the entry's chain as read back are spelled from that
chain's own plan, digest and items. Asked: the digest has 32 bytes, the string fewer than 2^64. -/
theorem chainsOf_link_own {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (hc : c.size = 32) (hb : (ch.bytes .link).size < 2 ^ 64) (h : chainsOf X lay c = .ok ch) :
    ch.link.given.bytes =
      Fmt.paramsBytes ch.link.given.plan ch.link.given.cfg ch.link.given.items := by
  unfold chainsOf at h
  obtain ⟨⟨links, shapes⟩, e1, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨z, e2, h⟩ := exc_bind h
  obtain ⟨u, e3, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  obtain ⟨k1, k2, k3, p1, p2, p3, -, -, hall⟩ := configure_at hm
  have s4 : made.entryLink = Fmt.paramsBytes made.entry.plan c (entryItems made.sized) :=
    (congrArg Configured.entryLink (madeAt_self hm hall)).symm
  split at h
  · rename_i key link proof hK hL hP
    cases h
    have b4 : made.entryLink.size < 2 ^ 64 := hb
    rw [s4] at b4 hL
    exact Given.read_own b4 hc (names_entry made.sized) (Link.read_given hL)
  · cases h

/-- The chains put at c' and then at c'' are the chains put at c''. -/
theorem chainsAtCfg_twice (ch : Chains) (c' c'' : ByteArray) :
    chainsAtCfg (chainsAtCfg ch c') c'' = chainsAtCfg ch c'' := rfl

/-- What `chainsOf` returned at c, put at c, is itself. So all seven chains as read back hold c as
their digest. Conditions as in `chainsOf_at`. -/
theorem chainsAtCfg_self {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (hc : c.size = 32) (hb : ∀ n : ChainName, (ch.bytes n).size < 2 ^ 64)
    (h : chainsOf X lay c = .ok ch) : chainsAtCfg ch c = ch :=
  Except.ok.inj ((chainsOf_at hc hc hb h).symm.trans h)

/-- Each of the seven strings has the same length at c' as at c. Conditions as in `chainsOf_at`. -/
theorem size_bytes_chainsAtCfg {X : Public} {lay : Option ByteArray} {c c' : ByteArray}
    {ch : Chains} (hc : c.size = 32) (hc' : c'.size = 32)
    (hb : ∀ n : ChainName, (ch.bytes n).size < 2 ^ 64) (h : chainsOf X lay c = .ok ch)
    (n : ChainName) : ((chainsAtCfg ch c').bytes n).size = (ch.bytes n).size := by
  have hs := chainsAtCfg_self hc hb h
  have e : (ch.bytes n).size = ((chainsAtCfg ch c).bytes n).size := by rw [hs]
  rw [e]
  cases n <;> exact size_paramsBytes_at _ _ _ _ (hc'.trans hc.symm)

/-- The chains put at two digests of one length have strings of the same lengths. No other
condition. -/
theorem size_bytes_chainsAtCfg_any (ch : Chains) (c' c'' : ByteArray) (h : c'.size = c''.size)
    (n : ChainName) :
    ((chainsAtCfg ch c').bytes n).size = ((chainsAtCfg ch c'').bytes n).size := by
  cases n <;> exact size_paramsBytes_at _ _ _ _ h

/-- The text of `Model.Verify.planned` with the digest of the public files as an argument, where
`planned` forms it by the format's hash. c need not be the digest of these files. For statements
only: the program does not call this function. -/
def plannedAt (pol KL : ByteArray) (layout : Option ByteArray) (c : ByteArray) :
    Except String Verify.Planned := do
  let X ← publicOf pol KL layout
  let chains ← chainsOf X layout c
  pure { X := X, cfg := c, chains := chains, built := ← builtOf X chains }

/-- `planned` is `plannedAt` at the digest that the format's hash gives on the three files. By
definition. -/
theorem planned_eq (pol KL : ByteArray) (layout : Option ByteArray) :
    planned pol KL layout =
      plannedAt pol KL layout (configuration pol (layout.getD .empty) KL) := rfl

/-- What `plannedAt` returns at c it returns at c', with c' as its digest and the chains put at c';
the public part and the links are the same. Conditions as in `chainsOf_at`. -/
theorem plannedAt_at {pol KL : ByteArray} {layout : Option ByteArray} {c c' : ByteArray}
    {p : Verify.Planned} (hc : c.size = 32) (hc' : c'.size = 32)
    (hb : ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64)
    (h : plannedAt pol KL layout c = .ok p) :
    plannedAt pol KL layout c' = .ok { p with cfg := c', chains := chainsAtCfg p.chains c' } := by
  unfold plannedAt at h ⊢
  obtain ⟨X, hX, h⟩ := exc_bind h
  obtain ⟨chains, hch, h⟩ := exc_bind h
  obtain ⟨built, hbu, h⟩ := exc_bind h
  cases h
  refine (exc_step _ hX).trans ?_
  refine (exc_step _ (chainsOf_at hc hc' hb hch)).trans ?_
  refine (exc_step _ ((builtOf_at X chains c').trans hbu)).trans ?_
  rfl

end OnBytes.Tie

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Tie/ChainsAtCfg.lean: if the program's `chainsOf` returns the seven chains at one digest of
32 bytes, each with fewer than 2^64 parameter bytes, it returns them at every other digest of 32
bytes, the same but for the digest and the parameter bytes.

`Model.Verify.chainsOf X lay cfg` (OnBytes/Model/VerifyChains.lean) makes shapes and sizes, tests
the links, calls the planner (`Params.configure`) with the digest, and reads the planner's seven
strings of parameter bytes back; it refuses if a reader does. `Model.Verify.planned` forms the
digest by the format's hash, calls `chainsOf` with it, and then `builtOf`. A bound under a random
oracle for a verifier that forms the digest by the oracle needs this text at every value of the
digest. The whole call's text over a monad forms the digest by the hash that it is handed
(`M.Model.Verify.planned`, OnBytes/ChecksWithHashAsArgument/M/Model/Verify.lean);
nothing is
stated of it here. No such bound for the program stands in OnBytes/: the program forms the
digest by BLAKE2b. OnBytes/Tie/EntryPlanAtCfg.lean says how the planner's value hangs on
the digest (`configure_at`), OnBytes/Params/ReadBackAt.lean how the readers' values do. Here the two
are joined along the text of `chainsOf`.

Main definitions: `keyAtCfg`, `proofAtCfg`, `chainsAtCfg`, `plannedAt`.
Main theorems.
- `chainsOf_at`: if `chainsOf X lay c` returns ch, then `chainsOf X lay c'` returns
  `chainsAtCfg ch c'`, a function of ch and c' alone: in each of the seven chains as read back, c'
  is the digest and the bytes are spelled anew from the chain's own plan and items
  (`Params.Given.atCfg`); the planner's seven strings are these bytes; sizes and plans are the same.
- `builtOf_at`, `tableShape_at`: `builtOf` and the shape of the stored tables have the same value at
  `chainsAtCfg ch c'` as at ch. By definition. `chainsAtCfg_twice`, `chainsAtCfg_self`,
  `size_bytes_chainsAtCfg`: put at c' and then at c'' is put at c''; what `chainsOf` returned at c,
  put at c, is itself; the seven strings have the same lengths at c' as at c; the last two under the
  conditions of `chainsOf_at`. `size_bytes_chainsAtCfg_any`: put at two digests of one length, the
  strings have the same lengths; no other condition.
- `chainsOf_link_own`: the parameter bytes of the entry's chain as read back are spelled from that
  chain's own plan, digest and items: the second condition of `withinX_linkAtCfg`
  (OnBytes/Tie/EntryAtCfg.lean), for the program's own value. Asked: the digest has 32 bytes, the
  string fewer than 2^64.
- `planned_eq`, `plannedAt_at`: `plannedAt` is the text of `planned` with the digest as an argument;
  `planned` is `plannedAt` at the digest that the format's hash gives, by definition; and what
  `plannedAt` returns at c it returns at c', with c' as its digest and the chains put at c', under
  the conditions of `chainsOf_at`.
- `names_oneTime`, `names_lin`, `names_entry`, `names_first`: the names of the planner's items are
  within the format's rule for names.

What is asked. Both digests have 32 bytes. Each of the seven strings in ch has fewer than 2^64
bytes: a hypothesis. For three of them OnBytes/Tie/SameChains.lean takes it from a yes of the file's
check: for the entry's chain at any chains (`entry_yes_small`); for the key's one-time chain and the
proof's first chain at a value of `planned` alone (`key_yes_small`, `proof_yes_small`), so not at
what `plannedAt` returns at another digest. For the other four that file gives nothing;
`short_of_test` (OnBytes/Tie/PlanAtDigest.lean) takes the bound for all seven from a yes of the test
`shortB` on a plan, not from the program's yes on a whole call. The strings' lengths do
not hang on the digest (`size_bytes_chainsAtCfg_any`).

What is not claimed. No probability and nothing on soundness. Nothing if `chainsOf` refuses at c.
Nothing on what the stages do with the digest behind `planned`: `commonOf` reads the key's table
under it and forms the commitment ID from it; three tests refuse a digest of 32 zero bytes; and the
three checks read their files under descriptions that hold it, and hash under it in every round.
`chainsOf_at` holds at a c' of 32 zero bytes too. That `chainsOf` returns a value on any files is
not shown. All limits in the heads of the files named above hold here too. For proofs only; the
program does not import this file.


-/
