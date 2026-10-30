-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/NumberPrices/AtDigest.lean: the clauses of `PricesAt`
(Johnson/Desc/Ok/NumberPrices/AtRelease.lean), and the library's test on the lengths of the
parameter bytes, with the plan AND the sendings made at a digest c that is an argument; and: if the
eight hold at one digest of 32 bytes they hold at every digest of 32 bytes, with ONE set of data and
records for all.

WHERE THINGS STAND. No file under this folder imports a file under Ladder/: where the three public
files occur they are the letters pol, lay, KL; where a bound on a round's error occurs it is a
literal. `PricesAtRelease`, `PricesAtGap`, `PricesRungs`, `pricesRungs`, `PricesNamed`,
`pricesNamed_of`, `prices_at_release`, `below_step`, `pricedAt_of_release`, wherever a head under
this folder names them, stand in Johnson/Goal/Numbers/NumberPricesAt.lean [not in this library].

Why. `madeOf` (Johnson/G/RoundsOfPlan.lean) calls `Model.Verify.planned`, which forms the digest of
the three public files by the format's hash as a concrete function and plans at that digest;
`sendsOf` (Johnson/G/Sends.lean), which `madeOf` also calls, does so once more. A verifier that asks
a hash function drawn at random for the files' digest plans at whatever value c that function gives.
So a statement on `madeOf`'s value speaks of the plan at ONE value of c. The library has the text of
`planned` with the digest as an argument (`plannedAt`) and the law that what it returns at one
digest it returns at every other, the same but for the digest and the parameter bytes
(`plannedAt_at`, OnBytes/Tie/ChainsAtCfg.lean). Here that law is brought to our clauses.

THE THEOREMS HERE ARE TOOLS, AND NO STATEMENT AT NAMED FILES IS PROVED. No line under
Owed/ [not in this library] is to be
laid on them. The row number_prices stays owed, and does not reach a verifier by them: see the
Limits.

Definitions, statements and proofs.
  `sendsFrom c`: the sendings of the seven chains from a value c of the planner's record. IT IS A
    SECOND TEXT of the body of `sendsOf`, from its third line on, letter for letter. `sendsOf_eq`:
    `sendsOf` is `planned`, then `sendsFrom` of what it made. By definition: so the two texts cannot
    part without this file failing to compile. `sendsFrom_at`: it has one value at a record and at
    that record put at another digest. By definition: it reads the sizes and the seven records,
    which `chainsAtCfg` keeps.
  `packMade`, `madeOfAt pol lay KL c`: `plannedAt … c`, then `sendsFrom` of what it made, then the
    record `Made`. No step of it calls the FORMAT's hash: of the two hashes on `madeOf`'s road the
    format's is gone; the older stays: `publicOf`, the first step of `plannedAt`, forms a digest of
    the three files by it at every c (Limits). `madeOfAt_of_madeOf`, `madeOf_of_madeOfAt`: at the
    digest that the format's hash gives it returns what `madeOf` returns.
  `atDigest m c'`: m with c' for the digest and the seven chains put at c' (`chainsAtCfg`): sizes,
    the planner's seven records with their rounds, entries and numbers for the errors, the plans as
    read back, and the sendings stay; the digest and the parameter bytes turn.
  `madeOfAt_planned`, `madeOfAt_chains`, `madeOfAt_at`: what `madeOfAt` returns at c it returns at
    c', put at c'; both of 32 bytes; each of the seven strings of parameter bytes below 2^64 bytes.
  `PricesAtDigest pol lay KL c`: the seven clauses of `PricesAt pol lay KL` with `madeOfAt … c`, and
    the library's test on the strings' lengths (`Tie.shortB`, OnBytes/Tie/PlanAtDigest.lean), which
    is the third hypothesis of `plannedAt_at`.
  `PricesAtOwn pol lay KL`: at the digest that the format's hash gives. `pricesAt_of_own`: it gives
    `PricesAt pol lay KL`. `own_of_pricesAt`: `PricesAt pol lay KL` gives it where `shortB` says yes
    of every value of `madeOf` at pol lay KL. `pricesOwnOk pol lay KL`: the eight clauses as ONE
    test with code, with one call of `madeOf`; `own_of_ok`: a yes of it gives PricesAtOwn pol lay
    KL. THIS, not `pricesAtOk`, is the test whose yes the theorems below spend.
  `pricesAtDigest_at`: **from one digest of 32 bytes to every other.** `pricesAt_every_digest`:
    PricesAtOwn pol lay KL → ∀ c of 32 bytes, PricesAtDigest pol lay KL c. `pricesAt_every_answer`:
    so at `Run.digToBytes d` for every d : Digest, the type of an answer of the hash function.
    `pricesAt_of_zero`: the like from 32 zero bytes, the anchor of the library's `planZero`, at
    which the format's hash is not called.
  `keyPlansPriced_at`, `entryPlanPriced_at`, `proofPlansPriced_at`: the plans as read back are the
    planner's records' plans, at `madeOfAt`'s value at any c.
  `prices_of_digest`: PricesAtDigest pol lay KL c → `PricesOf` at each of the seven plans made at c,
    at its own w, and the line on slots. `entry_of_digest`: the entry file's chain at c.
  `pricedAt_of_digest`: PricesAtDigest pol lay KL c → `PricedRounds`
    (Johnson/Desc/Ok/NumberPrices/AtData.lean) of both files' data at the plan made at c.
  `pricedAt_one`: **ONE SET OF DATA AND RECORDS FOR ALL c.** From PricesAtOwn pol lay KL: there are
    data DK, DP, sizes, the key's three records, the entry's and the proof's three, with
    `PricedRounds` of both files' data, such that at EVERY c of 32 bytes `madeOfAt` returns an m
    with just these data, sizes and records. `pricedAt_every_digest`: the weaker form, at each c
    some.

Beside it, and used or not. Used: `Tie.shortB`, `short_of_test`, `test_of_short`.
Not imported: `Flat.planAt`
(Johnson/Flat/AtCfg/PlanLay.lean [not in this library]), which is the planner's part of `atDigest`.
`Tie.planZero`,
`plannedAt_of_zero`, `plan_of_zero`, `planZero_of` (OnBytes/Tie/PlanAtDigest.lean) say "the plan at
every digest" from one written string; `pricesAt_of_zero` stands at their anchor.

What of OnBytes/Model/ and OnBytes/Tie/ is used. Named: `Tie.plannedAt`, `Tie.chainsAtCfg`
(OnBytes/Tie/ChainsAtCfg.lean), `Tie.shortB`, `Model.Verify.planned`, `chainsOf`, `Chains`,
`Chains.bytes`, `configuration` (OnBytes/Model/Verify.lean, VerifyChains.lean), `ChainName`
(OnBytes/Model/VerifyInputs.lean). Unfolded: `Tie.plannedAt`. Called: `Tie.plannedAt_at`,
`Tie.size_bytes_chainsAtCfg`, `Tie.exc_step`, `Params.configurationDigest_size`
(OnBytes/Model/VerifyDigest.lean), `key_read_made`, `entry_read_made`, `proof_read_made`
(OnBytes/Model/ReadBackMade.lean), `Run.size_digToBytes` (Run/CodingPage160.lean). All of it is a
function of the public files and of c.

Limits. NO DESCRIPTION IS NAMED: that a description of the protocol plans by `plannedAt` at the
digest that it was given, takes its sendings from `sendsFrom` and its data from `dataKAt`,
`dataPAt`, and ASKS the tests, is said nowhere. `C`, `F` and `P` of a description are functions of
the public files alone (Ladder.lean): `pricedAt_one` says that there is one value to take, not that
any description takes it. `OnBytes.secondHashFunction` stands in `publicOf`, the first step of `plannedAt`, as a
constant, at every c: whether `madeOfAt` returns hangs on its answers on the files, the same at all
c. WHAT THAT COSTS: `madeOfAt` takes no such hash as an argument, so it reaches a hash function by
name, which a description may not (Ladder.lean, the notes under the goals): `madeOfAt`, and every
statement here that bears it, may stand in no description as it is. Whether it returns also hangs on
`builtOf`, the last step of `plannedAt`; no statement here reads the field that it fills. THE FILES:
a yes at two sets of files serves these two sets; nothing here brings PricesAtOwn from one pol lay
KL to another. Where the planner refuses at the own digest the premise is false and nothing is said;
it is not said that it then refuses at every c. `PricesAtOwn` is proved at no files, and no run of
`pricesOwnOk` is known to this file. No control can make `shortB` say no: it would take a string of
2^64 bytes. Nothing is said at a c that has not 32 bytes. The first chain's last round and every
entry RECORD are passed over, and the entry file has no rounds' data, as in
Johnson/Desc/Ok/NumberPrices/AtData.lean. Nothing on probabilities or on soundness.


-/
import Johnson.Desc.Ok.NumberPrices.AtData
import OnBytes.Tie.PlanAtDigest
import OnBytes.Model.VerifyDigest
import Run.CodingPage160
import VerifiableInference.RandomOracleModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number
open Johnson.G Johnson.G.OfPlan OnBytes OnBytes.Params OnBytes.Maker
open OnBytes.Model.Verify (planned chainsOf Chains configuration ChainName)
open OnBytes.Tie (plannedAt plannedAt_at chainsAtCfg size_bytes_chainsAtCfg exc_step shortB
  short_of_test test_of_short)

/-! ## 1. The sendings from a value of the planner -/

/-- The sendings of the seven chains, from a value of the planner's record. A second text of the
body of `Johnson.G.sendsOf` (Johnson/G/Sends.lean), letter for letter; `sendsOf_eq` ties the two. -/
def sendsFrom (c : Configured) : Except String (List ChainSends) := do
  let z := c.sized
  let a := z.set.samples
  let one (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (P : Planned) :
      Except String ChainSends := do
    let R := P.rounds.toArray
    let seeds := P.rounds.zipIdx.filter fun r => r.1.entry.name == "SEND seed"
    unless seeds.length == l.length do
      throw s!"{file} {ch}: {l.length} sendings listed, {seeds.length} entries SEND seed"
    let out ← (seeds.zip l).mapM fun (r, s) => do
      unless treesOf codes s.sent.toArray == some r.1.entry.roots do
        throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
      match R[r.2 + 1]? with
      | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1.entry, b.entry⟩ : Sending)
      | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it"
    pure ⟨file, ch, codes, out⟩
  let K := z.key.once.shape
  let B := z.proof.batch.shape
  let x := z.key.ranges.x
  match c.key, c.proof with
  | [k0, k1, k2], [p0, p1, p2] =>
    [ one "key" 0 z.key.codes
        ([⟨"the index-mask message", [z.key.once.input]⟩,
          ⟨"the multiplicities", (Wf.messageOf x).toList⟩] ++
          ioppSends "the ranges' test" a x.choice.masksRide 1 x.stages ++ [← wSend K]) k0,
      one "key" 1 z.key.codes (← linSharedSends K a) k1,
      one "key" 2 z.key.codes (ioppSends "the own test" a K.choice.masksRide 1 K.testOwn) k2,
      one "entry" 0 z.entryCodes
        (⟨"the link's message", (linkMessage z.link.shape a).toList⟩ ::
          ioppSends "the link's test" a z.link.shape.choice.masksRide 1 z.link.shape.test) c.entry,
      one "proof" 0 z.proof.codes
        (frameSends z.proof a 0 (reqGroups z.proof.request).toList z.proof.request.link ++
          [← wSend B]) p0,
      one "proof" 1 z.proof.codes (← linSharedSends B a) p1,
      one "proof" 2 z.proof.codes (ioppSends "the own test" a B.choice.masksRide 1 B.testOwn) p2
    ].mapM id
  | _, _ => throw "the key or the proof has not three plans"

/-- **`sendsOf` is `planned`, then `sendsFrom` of what it made.** By definition. -/
theorem sendsOf_eq (pol lay KL : ByteArray) :
    sendsOf pol lay KL = planned pol KL (some lay) >>= fun p => sendsFrom p.chains.made := rfl

/-- The sendings do not hang on the digest. By definition. -/
theorem sendsFrom_at (ch : Chains) (c' : ByteArray) :
    sendsFrom (chainsAtCfg ch c').made = sendsFrom ch.made := rfl

/-! ## 2. `madeOf` with the digest as an argument -/

/-- The planner's value and the list of the seven chains' sendings, as the record `Made`. -/
def packMade (p : OnBytes.Model.Verify.Planned) : List ChainSends → Except String Made
  | [k0, k1, k2, _, p0, p1, p2] => .ok ⟨p, (k0, k1, k2), (p0, p1, p2)⟩
  | _ => .error "the list of sendings has not seven chains (key 0 1 2, entry, proof 0 1 2)"

/-- What `madeOf` makes, with the digest of the public files as an argument: the planner's text at
c, the sendings from what it made, the record. No step calls the format's hash; the second hash
function stands in `publicOf` (Limits). -/
def madeOfAt (pol lay KL c : ByteArray) : Except String Made :=
  plannedAt pol KL (some lay) c >>= fun p => sendsFrom p.chains.made >>= packMade p

/-- What `packMade` returns holds the planner's value. -/
theorem packMade_p {p : OnBytes.Model.Verify.Planned} {s : List ChainSends} {m : Made}
    (h : packMade p s = .ok m) : m.p = p := by
  unfold packMade at h
  split at h
  · rw [← Except.ok.inj h]
  · cases h

/-- With another value of the planner in the first place, the same sendings are packed. -/
theorem packMade_with {p : OnBytes.Model.Verify.Planned} {s : List ChainSends} {m : Made}
    (h : packMade p s = .ok m) (p' : OnBytes.Model.Verify.Planned) :
    packMade p' s = .ok { m with p := p' } := by
  unfold packMade at h ⊢
  split at h
  · rw [← Except.ok.inj h]
  · cases h

/-- At the digest that the format's hash gives, `madeOfAt` returns what `madeOf` returns. -/
theorem madeOfAt_of_madeOf {pol lay KL : ByteArray} {m : Made} (h : madeOf pol lay KL = .ok m) :
    madeOfAt pol lay KL (configuration pol lay KL) = .ok m := by
  unfold madeOf at h
  obtain ⟨p, hp, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  rw [sendsOf_eq] at hs
  obtain ⟨p', hp', hs⟩ := bind_ok hs
  obtain rfl : p' = p := Except.ok.inj (hp'.symm.trans hp)
  have pe : plannedAt pol KL (some lay) (configuration pol lay KL) = .ok p' := hp
  refine (exc_step _ pe).trans ((exc_step _ hs).trans ?_)
  split at h
  · rw [← Except.ok.inj h]
    rfl
  · exact absurd h (throw_ne _ _)

/-- And the way back. -/
theorem madeOf_of_madeOfAt {pol lay KL : ByteArray} {m : Made}
    (h : madeOfAt pol lay KL (configuration pol lay KL) = .ok m) : madeOf pol lay KL = .ok m := by
  unfold madeOfAt at h
  obtain ⟨p, hp, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  have pe : planned pol KL (some lay) = .ok p := hp
  have se : sendsOf pol lay KL = .ok s := by
    rw [sendsOf_eq]
    exact (exc_step _ pe).trans hs
  unfold madeOf
  refine (exc_step _ pe).trans ((exc_step _ se).trans ?_)
  unfold packMade at h
  split at h
  · rw [← Except.ok.inj h]
    rfl
  · cases h

/-- m with c' for the digest and the seven chains put at c'. -/
def atDigest (m : Made) (c' : ByteArray) : Made :=
  { m with p := { m.p with cfg := c', chains := chainsAtCfg m.p.chains c' } }

/-- What `madeOfAt` returns: its planner's value is `plannedAt`'s at c. -/
theorem madeOfAt_planned {pol lay KL c : ByteArray} {m : Made}
    (h : madeOfAt pol lay KL c = .ok m) : plannedAt pol KL (some lay) c = .ok m.p := by
  unfold madeOfAt at h
  obtain ⟨p, hp, h⟩ := bind_ok h
  obtain ⟨s, _, h⟩ := bind_ok h
  rw [packMade_p h]
  exact hp

/-- What `madeOfAt` returns at c holds chains that `chainsOf` has returned at c. -/
theorem madeOfAt_chains {pol lay KL c : ByteArray} {m : Made}
    (h : madeOfAt pol lay KL c = .ok m) : ∃ X, chainsOf X (some lay) c = .ok m.p.chains := by
  have hp := madeOfAt_planned h
  unfold plannedAt at hp
  obtain ⟨X, _, hp⟩ := bind_ok hp
  obtain ⟨ch, hc, hp⟩ := bind_ok hp
  obtain ⟨b, _, hp⟩ := bind_ok hp
  have e : m.p.chains = ch := by
    rw [← Except.ok.inj hp]
  rw [e]
  exact ⟨X, hc⟩

/-- **What `madeOfAt` returns at c it returns at c', put at c'.** -/
theorem madeOfAt_at {pol lay KL c c' : ByteArray} {m : Made} (hc : c.size = 32)
    (hc' : c'.size = 32) (hb : ∀ n : ChainName, (m.p.chains.bytes n).size < 2 ^ 64)
    (h : madeOfAt pol lay KL c = .ok m) : madeOfAt pol lay KL c' = .ok (atDigest m c') := by
  have hp' := plannedAt_at hc hc' hb (madeOfAt_planned h)
  unfold madeOfAt at h
  obtain ⟨p, _, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  have ep := packMade_p h
  rw [← ep] at hs
  have hs' : sendsFrom (chainsAtCfg m.p.chains c').made = .ok s :=
    (sendsFrom_at m.p.chains c').trans hs
  exact (exc_step _ hp').trans ((exc_step _ hs').trans (packMade_with h _))

/-! ## 3. The clauses at a digest -/

/-- The seven clauses of `PricesAt` with the plan and the sendings made at the digest c, and the
library's test on the lengths of the seven strings of parameter bytes. -/
def PricesAtDigest (pol lay KL : ByteArray) (c : ByteArray) : Prop :=
  ∃ m DK DP, madeOfAt pol lay KL c = .ok m ∧
    Desc.madeOk m.p.chains.made = true ∧ Desc.fitOk m.p.chains.made = true ∧
    shortB m.p = true ∧
    dataKAt m = .ok DK ∧ dataPAt m = .ok DP ∧ DK.ds₃ ≠ [] ∧ DP.ds₃ ≠ []

/-- At the digest that the format's hash gives. -/
def PricesAtOwn (pol lay KL : ByteArray) : Prop := PricesAtDigest pol lay KL (configuration pol lay
    KL)

/-- It gives `PricesAt`. -/
theorem pricesAt_of_own {pol lay KL : ByteArray} (h : PricesAtOwn pol lay KL) : PricesAt pol lay KL
    := by
  obtain ⟨m, DK, DP, hm, h1, h2, _, hK, hP, nK, nP⟩ := h
  exact ⟨m, DK, DP, madeOf_of_madeOfAt hm, h1, h2, hK, hP, nK, nP⟩

/-- `PricesAt` gives it where the test on the strings' lengths says yes. -/
theorem own_of_pricesAt {pol lay KL : ByteArray} (h : PricesAt pol lay KL)
    (hs : ∀ m, madeOf pol lay KL = .ok m → shortB m.p = true) : PricesAtOwn pol lay KL := by
  obtain ⟨m, DK, DP, hm, h1, h2, hK, hP, nK, nP⟩ := h
  exact ⟨m, DK, DP, madeOfAt_of_madeOf hm, h1, h2, hs m hm, hK, hP, nK, nP⟩

/-- The eight clauses of `PricesAtOwn` as one test, with code, with one call of `madeOf`. -/
def pricesOwnOk (pol lay KL : ByteArray) : Bool :=
  match madeOf pol lay KL with
  | .ok m =>
    Desc.madeOk m.p.chains.made && Desc.fitOk m.p.chains.made && shortB m.p &&
      match dataKAt m, dataPAt m with
      | .ok DK, .ok DP => !DK.ds₃.isEmpty && !DP.ds₃.isEmpty
      | _, _ => false
  | .error _ => false

/-- A yes of that test gives the statement at the format's own digest. -/
theorem own_of_ok {pol lay KL : ByteArray} (h : pricesOwnOk pol lay KL = true) : PricesAtOwn pol lay
    KL := by
  unfold pricesOwnOk at h
  split at h
  · rename_i m hm
    have c1 := Bool.and_eq_true_iff.1 h
    have c2 := Bool.and_eq_true_iff.1 c1.1
    have c3 := Bool.and_eq_true_iff.1 c2.1
    have h3 := c1.2
    split at h3
    · rename_i DK DP hK hP
      have c4 := Bool.and_eq_true_iff.1 h3
      exact ⟨m, DK, DP, madeOfAt_of_madeOf hm, c3.1, c3.2, c2.2, hK, hP,
        ne_nil_of_not_isEmpty c4.1, ne_nil_of_not_isEmpty c4.2⟩
    · cases h3
  · cases h

/-- The test on the strings' lengths: a yes at m is a yes at m put at c'. -/
theorem short_atDigest {pol lay KL c c' : ByteArray} {m : Made} (hc : c.size = 32)
    (hc' : c'.size = 32) (hm : madeOfAt pol lay KL c = .ok m) (hb : shortB m.p = true) :
    shortB (atDigest m c').p = true := by
  obtain ⟨X, hX⟩ := madeOfAt_chains hm
  refine test_of_short fun n => ?_
  show ((chainsAtCfg m.p.chains c').bytes n).size < 2 ^ 64
  rw [size_bytes_chainsAtCfg hc hc' (short_of_test hb) hX n]
  exact short_of_test hb n

/-- **From one digest of 32 bytes to every other.** -/
theorem pricesAtDigest_at {pol lay KL : ByteArray} {c c' : ByteArray} (hc : c.size = 32)
    (hc' : c'.size = 32) (h : PricesAtDigest pol lay KL c) : PricesAtDigest pol lay KL c' := by
  obtain ⟨m, DK, DP, hm, h1, h2, h3, hK, hP, nK, nP⟩ := h
  exact ⟨atDigest m c', DK, DP, madeOfAt_at hc hc' (short_of_test h3) hm, h1, h2,
    short_atDigest hc hc' hm h3, hK, hP, nK, nP⟩

/-- **And so at every digest of 32 bytes.** -/
theorem pricesAt_every_digest {pol lay KL : ByteArray} (h : PricesAtOwn pol lay KL) (c : ByteArray)
    (hc : c.size = 32) : PricesAtDigest pol lay KL c :=
  pricesAtDigest_at (configurationDigest_size _) hc h

/-- So at the bytes of every value of the type of an answer of the hash function. -/
theorem pricesAt_every_answer {pol lay KL : ByteArray} (h : PricesAtOwn pol lay KL) (d : Digest) :
    PricesAtDigest pol lay KL (_root_.Run.digToBytes d) :=
  pricesAt_every_digest h _ (_root_.Run.size_digToBytes d)

/-- The like from 32 zero bytes, at which the format's hash is not called; the second hash function
stands in `publicOf` (Limits). -/
theorem pricesAt_of_zero {pol lay KL : ByteArray} (h : PricesAtDigest pol lay KL Fmt.zero32) (c :
    ByteArray)
    (hc : c.size = 32) : PricesAtDigest pol lay KL c :=
  pricesAtDigest_at (Fmt.size_zeros 32) hc h

/-! ## 4. What follows at a digest -/

/-- The key file's three equations between plans, at the plan made at c. -/
theorem keyPlansPriced_at {pol lay KL c : ByteArray} {m : Made}
    (h : madeOfAt pol lay KL c = .ok m) {K₁ K₂ K₃ : Planned}
    (hm : m.p.chains.made.key = [K₁, K₂, K₃]) (hf : Desc.keyFit m.p.chains.made = true) :
    KeyPlansPriced m K₁ K₂ K₃ := by
  obtain ⟨X, hX⟩ := madeOfAt_chains h
  obtain ⟨l, x, h1, h2, _, _⟩ := chainsOf_made hX
  exact key_read_made h1 h2 (fun P hP => List.all_eq_true.1 hf P hP) hm

/-- The entry file's equation between plans, at the plan made at c. -/
theorem entryPlanPriced_at {pol lay KL c : ByteArray} {m : Made}
    (h : madeOfAt pol lay KL c = .ok m) (hf : Desc.entryFit m.p.chains.made = true) :
    EntryPlanPriced m := by
  obtain ⟨X, hX⟩ := madeOfAt_chains h
  obtain ⟨l, x, h1, _, h2, _⟩ := chainsOf_made hX
  exact entry_read_made h1 h2 hf

/-- The proof file's three equations between plans, at the plan made at c. -/
theorem proofPlansPriced_at {pol lay KL c : ByteArray} {m : Made}
    (h : madeOfAt pol lay KL c = .ok m) {F₁ F₂ F₃ : Planned}
    (hm : m.p.chains.made.proof = [F₁, F₂, F₃]) (hf : Desc.proofFit m.p.chains.made = true) :
    ProofPlansPriced m F₁ F₂ F₃ := by
  obtain ⟨X, hX⟩ := madeOfAt_chains h
  obtain ⟨l, x, h1, _, _, h3⟩ := chainsOf_made hX
  exact proof_read_made h1 h3 (fun P hP => List.all_eq_true.1 hf P hP) hm

/-- `PricesOf` at the seven plans that are made at c, and the line on slots. -/
theorem prices_of_digest {pol lay KL : ByteArray} {c : ByteArray} (h : PricesAtDigest pol lay KL c)
    :
    ∃ m K₁ K₂ K₃ F₁ F₂ F₃,
      madeOfAt pol lay KL c = .ok m ∧
      m.p.chains.made.key = [K₁, K₂, K₃] ∧ m.p.chains.made.proof = [F₁, F₂, F₃] ∧
      PricesOf 32 K₁ ∧ PricesOf 32 K₂ ∧ PricesOf 32 K₃ ∧ PricesOf 32 m.p.chains.made.entry ∧
      PricesOf 20 F₁ ∧ PricesOf 28 F₂ ∧ PricesOf 20 F₃ ∧
      m.p.chains.made.sized.lines.slots = Desc.slots := by
  obtain ⟨m, _, _, hm, hok, _⟩ := h
  obtain ⟨hk, he, hp⟩ := (Desc.madeOk_iff _).1 hok
  obtain ⟨K₁, K₂, K₃, ek, k1, k2, k3⟩ := keyOk_parts hk
  obtain ⟨F₁, F₂, F₃, ef, f1, f2, f3, hs⟩ := proofOk_parts hp
  exact ⟨m, K₁, K₂, K₃, F₁, F₂, F₃, hm, ek, ef, pricesGeneral _ _ k1, pricesGeneral _ _ k2,
    pricesGeneral _ _ k3, pricesGeneral _ _ (chainOk_of_all he), pricesGeneral _ _ f1,
    pricesGeneral _ _ f2, pricesGeneral _ _ f3, hs⟩

/-- The entry file's chain, at the plan made at c. -/
theorem entry_of_digest {pol lay KL : ByteArray} {c : ByteArray} (h : PricesAtDigest pol lay KL c) :
    ∃ m, madeOfAt pol lay KL c = .ok m ∧ EntryPlanPriced m ∧
      PricesOf 32 m.p.chains.made.entry := by
  obtain ⟨m, _, _, hm, hok, hfit, _⟩ := h
  obtain ⟨_, he, _⟩ := (Desc.madeOk_iff _).1 hok
  simp only [Desc.fitOk, Bool.and_eq_true] at hfit
  exact ⟨m, hm, entryPlanPriced_at hm hfit.1.2, pricesGeneral _ _ (chainOk_of_all he)⟩

/-- **`PricedAt` at every round of the two files' data, at the plan made at c.** -/
theorem pricedAt_of_digest {pol lay KL : ByteArray} {c : ByteArray} (h : PricesAtDigest pol lay KL
    c) :
    ∃ m DK DP K₁ K₂ K₃ F₁ F₂ F₃,
      madeOfAt pol lay KL c = .ok m ∧ shortB m.p = true ∧
      dataKAt m = .ok DK ∧ dataPAt m = .ok DP ∧
      m.p.chains.made.key = [K₁, K₂, K₃] ∧ m.p.chains.made.proof = [F₁, F₂, F₃] ∧
      PricedRounds DK K₁ K₂ K₃ ∧ PricedRounds DP F₁ F₂ F₃ ∧ DK.ds₃ ≠ [] ∧ DP.ds₃ ≠ [] := by
  obtain ⟨m, DK, DP, hm, hok, hfit, hb, hK, hP, nK, nP⟩ := h
  obtain ⟨hk, _, hp⟩ := (Desc.madeOk_iff _).1 hok
  simp only [Desc.fitOk, Bool.and_eq_true] at hfit
  obtain ⟨K₁, K₂, K₃, ek, k1, k2, k3⟩ := keyOk_parts hk
  obtain ⟨F₁, F₂, F₃, ef, f1, f2, f3, _⟩ := proofOk_parts hp
  exact ⟨m, DK, DP, K₁, K₂, K₃, F₁, F₂, F₃, hm, hb, hK, hP, ek, ef,
    pricedRounds_of_data (key_pricedAt hK (keyPlansPriced_at hm ek hfit.1.1) k1 k2 k3) nK,
    pricedRounds_of_data (proof_pricedAt hP (proofPlansPriced_at hm ef hfit.2) f1 f2 f3) nP,
    nK, nP⟩

/-- **One set of data and records for all digests of 32 bytes.** -/
theorem pricedAt_one {pol lay KL : ByteArray} (h : PricesAtOwn pol lay KL) :
    ∃ (DK DP : WholeD) (S : Sized) (K₁ K₂ K₃ E F₁ F₂ F₃ : Planned),
      PricedRounds DK K₁ K₂ K₃ ∧ PricedRounds DP F₁ F₂ F₃ ∧ DK.ds₃ ≠ [] ∧ DP.ds₃ ≠ [] ∧
      ∀ c : ByteArray, c.size = 32 →
        ∃ m, madeOfAt pol lay KL c = .ok m ∧ dataKAt m = .ok DK ∧ dataPAt m = .ok DP ∧
          m.p.chains.made.sized = S ∧ m.p.chains.made.key = [K₁, K₂, K₃] ∧
          m.p.chains.made.entry = E ∧ m.p.chains.made.proof = [F₁, F₂, F₃] := by
  obtain ⟨m, DK, DP, K₁, K₂, K₃, F₁, F₂, F₃, hm, hb, hK, hP, ek, ef, pK, pP, nK, nP⟩ :=
    pricedAt_of_digest h
  exact ⟨DK, DP, m.p.chains.made.sized, K₁, K₂, K₃, m.p.chains.made.entry, F₁, F₂, F₃, pK, pP, nK,
    nP, fun c hc => ⟨atDigest m c,
      madeOfAt_at (configurationDigest_size _) hc (short_of_test hb) hm, hK, hP, rfl, ek, rfl, ef⟩⟩

/-- The weaker form: at each digest of 32 bytes some data and records. -/
theorem pricedAt_every_digest {pol lay KL : ByteArray} (h : PricesAtOwn pol lay KL) (c : ByteArray)
    (hc : c.size = 32) :
    ∃ m DK DP K₁ K₂ K₃ F₁ F₂ F₃,
      madeOfAt pol lay KL c = .ok m ∧ shortB m.p = true ∧
      dataKAt m = .ok DK ∧ dataPAt m = .ok DP ∧
      m.p.chains.made.key = [K₁, K₂, K₃] ∧ m.p.chains.made.proof = [F₁, F₂, F₃] ∧
      PricedRounds DK K₁ K₂ K₃ ∧ PricedRounds DP F₁ F₂ F₃ ∧ DK.ds₃ ≠ [] ∧ DP.ds₃ ≠ [] :=
  pricedAt_of_digest (pricesAt_every_digest h c hc)

end VerifiableInference.Number

#print axioms VerifiableInference.Number.sendsOf_eq
#print axioms VerifiableInference.Number.sendsFrom_at
#print axioms VerifiableInference.Number.packMade_p
#print axioms VerifiableInference.Number.packMade_with
#print axioms VerifiableInference.Number.madeOfAt_of_madeOf
#print axioms VerifiableInference.Number.madeOf_of_madeOfAt
#print axioms VerifiableInference.Number.madeOfAt_planned
#print axioms VerifiableInference.Number.madeOfAt_chains
#print axioms VerifiableInference.Number.madeOfAt_at
#print axioms VerifiableInference.Number.pricesAt_of_own
#print axioms VerifiableInference.Number.own_of_pricesAt
#print axioms VerifiableInference.Number.own_of_ok
#print axioms VerifiableInference.Number.short_atDigest
#print axioms VerifiableInference.Number.pricesAtDigest_at
#print axioms VerifiableInference.Number.pricesAt_every_digest
#print axioms VerifiableInference.Number.pricesAt_every_answer
#print axioms VerifiableInference.Number.pricesAt_of_zero
#print axioms VerifiableInference.Number.keyPlansPriced_at
#print axioms VerifiableInference.Number.entryPlanPriced_at
#print axioms VerifiableInference.Number.proofPlansPriced_at
#print axioms VerifiableInference.Number.prices_of_digest
#print axioms VerifiableInference.Number.entry_of_digest
#print axioms VerifiableInference.Number.pricedAt_of_digest
#print axioms VerifiableInference.Number.pricedAt_one
#print axioms VerifiableInference.Number.pricedAt_every_digest
