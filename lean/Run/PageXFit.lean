-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageXFit.lean: at the description of a chain that opens stored tables, the strings of the
encoding of the queries (Run/PageX.lean) are the strings of the calls by which `famX`
(Run/PlanQXRun.lean) spells typed queries, for all queries that the format writes.

Three definitions that compute, theorems. For a description D (`XD`) and a decision, Run/PageX.lean
fills the data `PageCX` (Run/CodingPageX.lean) at the interface `D.L dec` and the tag "link". Here
it is shown that what the five partial codes write are the bits of the strings of the calls by which
`famXPd` spells typed queries. With Run/CodingAgreeX.lean: for every function g on bit strings,
`famXPd D dec (digToBytes pd) (oB (g ())) K` and the family that the encoding reads out of g give
the same answer at every query that the encoding writes in the format (at round 0: the same chain
value; the Main names say it exactly). At the format's own digest `famXPd` is `famX` and `pageXPd`
is `pageX`: the last section says the main statements once more of these two.

The digest of the parameter bytes is an argument, pd: any 256 bits; nothing here ties pd to the
parameter bytes. `famX` turns a function O on the format's strings into typed oracle functions: it
spells every typed query as a hash call of the format and takes O's answer. In one spelling, that of
the first chain query (`firstX`), stands a constant: the format's own digest of the description's
parameter bytes, `Fmt.paramsDigest D.base.params`, a value of the format's hash. A verifier that
hashes by an oracle has the oracle's answer in that place. So this file has these two definitions
once more, with a byte string pd in the place of the constant (`firstXPd`, `famXPd`). pd stands in
the first query's string too (`pageXPd`); `pageX` is the data at the format's own digest, `pdX D`.

Two things are asked beside D and pd, as in Run/PageX.lean. (1) `D.base.cfg` has 32 bytes. (2)
`StmInv D`: a reader for the statement, as data with both laws.

Main names:
  `firstXPd`, `famXPd`; `firstX_eq_pd`, `famX_eq_pd`: at the format's own digest they are
    `firstX` and `famX`.
  `chainDX_fit`, `leafPX_fit`, `firstPX_fit`, `storedX_fit`: the fit of the rounds behind the first
    query, of the chain's own leaves, of the first query, of the stored tables' leaves.
  `callsX`; `famXPd_eq_famT`: `famXPd D dec (digToBytes pd) O K` is the family of the three plain
    maps `leafX`, `nodeCallC`, `firstXPd`.
  `pageXPd_fit`: 0 < K → FitX (pageXPd ..) (callsX D dec pd K).
  `implX_stored_string`, `implX_first_string`: the encoding's string of a stored table's leaf, and
    of the first chain query at the block of the chain value, each as one equation with `Fmt.oStr`.
  `famXPd_leaf_read`, `famXPd_node_read`, `famXPd_last_read`, `famXPd_whole_read`: for every g: at
    a leaf query that passes the test `fitsCX`, and at a vertex's query on two digests, the answers
    are one; at a chain query that passes the test the chain values are one, and the whole answers
    are one if the round is not 0.
  `famXPd_readSome`: the same with marked blocks (`readSome`, Run/DetOverOne.lean).
  `famX_eq_famT`, `pageX_fit`, `famX_readSome`: at the format's own digest: `famX` is the family of
    the three plain maps at `pdX D`; the fit holds of `pageX`; `famX` against what `theImplX (pageX
    ..)` reads.

Limits: nothing on soundness, and no probability. Nothing on BLAKE2b or on any other hash, but that
at `pageX` the parameters' digest, a value of the format's hash, stands in the first query's string
as a constant of 32 bytes. That `firstXPd` and `famXPd` follow the text of `firstX` and `famX` is
seen by the two equations, at the one value alone; for other values it is a matter of reading. Where
the test fails, and at the K blocks of the verifier's message of round 0, nothing is said, and the
two families can differ. The test is narrower than "famXPd has a call": `leafX`, `firstXPd` and
`nodeCallC` spell also queries whose salt, chain value, nonce, position, column or digest do not fit
the format's fields; `nodeCallC` spells every pair of strings, filled up with zeros to whole bytes;
and `firstXPd` does not look at a first query's root and plain part. That the compiled verifier asks
only queries that pass the test is not said here (for an argument string with `TypedOK`:
Run/PageXAsked.lean). It tests only the length of a leaf's salt (the head of Run/ParseBS.lean, "To
be declared with every use"), so a typed proof string (`OneProtocolProof`) that no reader has made can make it
ask a stored leaf with another start; no such string is exhibited. At such a leaf `leafX` has no
call and `famXPd` answers zeros, whatever the symbol; the encoding writes the query behind an
escape. No `StmInv` is given at any description here. "The format" is this library's Lean text of it
(Fmt/Rules23.lean: `Fmt.oStr`); it is not compared here with the format page or with any program.
That a string written here lies in the format's domain (`Fmt.hDom`; among its clauses: a leaf's
column of at least one word and salt of 5 to 8 words, an index below 2^63, a number below 2^48 in
the tree's place, at most 2^32 - 144 bytes) is not asked and not claimed; outside it `Fmt.oracle`
does not answer by the format's hash of the call, and no lemma here takes the domain from `D.ok`.
Not asked either, by the codes or by that domain: that a stored symbol's position is below 2^a (a
greater one is written as the leaf of a deeper tree), that a column's words are below the field's
modulus, that a run's value is not 32 zero bytes. The first query's code writes also the form with
an empty typed salt (no run's value), which no chain with random bytes has.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingAgreeX
import Run.PageX
import Run.PlanQXRun
import Run.PageQFit
import Run.PageIsReaders

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch

/-! ## The typed oracle functions, with the digest of the parameter bytes as an argument -/

/-- `firstX` (Run/PlanQXRun.lean) with pd in the place of the format's digest of the parameter
bytes. -/
def firstXPd (D : XD) (dec : View → Bool) (pd : ByteArray) (K : Nat)
    (q : FbIn 256 (D.L dec) .link) (j : Fin (K + 1)) : Option _root_.Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [cm, cm'] none salt =>
      if j.val = K then
        some ⟨0, 160, 0, D.base.label, _root_.Fmt.zero32,
            firstBytes pd (D.stm (digToBytes cm) (digToBytes cm')) salt⟩
      else none
  | 0, _ => none
  | _, _ => fbCall (PDX D dec) K q j

/-- `famX` (Run/PlanQXRun.lean) with pd in the place of the format's digest of the parameter
bytes. -/
def famXPd (D : XD) (dec : View → Bool) (pd : ByteArray) (O : ByteArray → ByteArray) (K : Nat) :
    Fam (spec 256 K (D.L dec))
  | .leaf, q => ansOf O (leafX D dec q)
  | .node, q => ansOf O (nodeCallC D.base.cfg q)
  | .fb .link, q =>
      (fun k => ansOf O (firstXPd D dec pd K q k.castSucc),
        ansOf O (firstXPd D dec pd K q (Fin.last K)))
  | .fb .test, _ => (fun _ _ => false, fun _ => false)
  | .fb .onl, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- At the format's digest it is `firstX`. -/
theorem firstX_eq_pd (D : XD) (dec : View → Bool) (K : Nat) (q : FbIn 256 (D.L dec) .link)
    (j : Fin (K + 1)) :
    firstX D dec K q j = firstXPd D dec (_root_.Fmt.paramsDigest D.base.params) K q j := rfl

/-- At the format's digest it is `famX`. -/
theorem famX_eq_pd (D : XD) (dec : View → Bool) (O : ByteArray → ByteArray) (K : Nat) :
    famX D dec O K = famXPd D dec (_root_.Fmt.paramsDigest D.base.params) O K := by
  funext o q
  cases o <;> rfl

variable (D : XD) (dec : View → Bool)

/-! ## The chain behind the first query, and the chain's own leaves -/

/-- The chain's data fit the spellings `PDX D dec`. -/
theorem chainDX_fit : ChainFit (chainDX D dec) (PDX D dec) where
  label := rfl
  kind := fun _ => rfl
  work := fun _ => rfl
  rc := fun i rt pl s h => by
    match i, h with
    | 0, h => cases h
    | i + 1, h =>
        obtain ⟨b, rfl, h1⟩ := inR_put' _ rt pl s h
        exact rcL_fit D.C D.ds i rt b s h1

/-- What the own leaves' code writes: the bits of the label and of the column with its fill, by the
spellings `PDX D dec`. -/
theorem leafPX_fit (y : SymAny (Compile.Batch.shapeOf (D.L dec) .link)) (m : List Bool)
    (h : (leafPX D dec).put y = some m) :
    m = bytesToBits (_root_.Fmt.label 164 ((PDX D dec).leaf y).1 ((PDX D dec).leaf y).2.1) ++
        bytesToBits ((PDX D dec).leaf y).2.2 := by
  obtain ⟨p, col⟩ := y
  rcases p with p | q
  · exact p.elim
  · exact leafCL_fit D.C D.base.plan.salt D.ds ⟨q, col⟩ m (PCode.sumF_inr _ _ _ m h)

/-! ## The first query -/

variable (pd : Dig 256)

variable {D} in
/-- What the first query's code writes is the string of the call by which `firstXPd` spells the
query at the block of the chain value. -/
theorem firstPX_fit (V : StmInv D) (K : ℕ) (q : FbIn 256 (D.L dec) .link) (s : List Bool)
    (h : (firstPX dec pd V).put q = some s) :
    q.round = 0 ∧ ∃ c, firstXPd D dec (digToBytes pd) K q (Fin.last K) = some c ∧ s = bytesToBits
        (strOf c) := by
  obtain ⟨a, ha, hs⟩ := PCode.pull_put _ _ _ _ _ q s h
  obtain ⟨cm, cm', salt, rfl, rfl⟩ := selF_some D dec pd q a ha
  refine ⟨rfl, ⟨0, 160, 0, D.base.label, _root_.Fmt.zero32,
    Run.firstBytes (digToBytes pd) (D.stm (digToBytes cm) (digToBytes cm')) salt⟩,
    if_pos (Fin.val_last K), ?_⟩
  have h1 : (if (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64 ∧
        (salt = [] ∨ salt.length = 256) then
      some (hdr160 D.base.label ++ bytesToBits (_root_.Fmt.firstBytes (digToBytes pd)
        (D.stm (digToBytes cm) (digToBytes cm')) ByteArray.empty (runOf salt)))
      else none) = some s := hs
  by_cases hc : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64 ∧
      (salt = [] ∨ salt.length = 256)
  · rw [if_pos hc] at h1
    rw [← Option.some.inj h1, Toy1.bits_first]
    exact (oStr_bits 0 160 0 D.base.label _root_.Fmt.zero32 _).symm
  · rw [if_neg hc] at h1
    cases h1

/-! ## The plain maps of famXPd -/

/-- The three plain maps by which `famXPd` spells typed queries. -/
def callsX (K : ℕ) : CallsX (D.L dec) K .link := ⟨leafX D dec, nodeCallC D.base.cfg, firstXPd D dec
    (digToBytes pd) K⟩

/-- `famXPd` is the family of its three plain maps. -/
theorem famXPd_eq_famT (O : ByteArray → ByteArray) (K : ℕ) :
    famXPd D dec (digToBytes pd) O K = famT (callsX D dec pd K) O := by
  funext o
  match o with
  | .leaf => rfl
  | .node => rfl
  | .fb .link =>
      funext q
      exact (famT_fb_self (callsX D dec pd K) O q).symm
  | .fb .test => rfl
  | .fb .onl => rfl
  | .fbw _ _ => rfl
  | .rleaf => rfl
  | .rnode => rfl
  | .g _ => rfl
  | .ann => rfl
  | .other => rfl

/-- Behind round 0 `firstXPd` is the map for plain chains (`fbCall`), at the spellings `PDX`. -/
theorem firstXPd_succ (K : ℕ) (q : FbIn 256 (D.L dec) .link) (j : Fin (K + 1)) (h : q.round ≠ 0) :
    firstXPd D dec (digToBytes pd) K q j = fbCall (PDX D dec) K q j := by
  unfold firstXPd
  split
  · rename_i e _
    exact absurd e h
  · rename_i e _
    exact absurd e h
  · rfl

/-- At round 0 `firstXPd` has a call at the block of the chain value alone. -/
theorem firstXPd_zero (K : ℕ) (q : FbIn 256 (D.L dec) .link) (j : Fin (K + 1)) (h : q.round = 0)
    (hj : j.val ≠ K) : firstXPd D dec (digToBytes pd) K q j = none := by
  unfold firstXPd
  split
  · exact if_neg hj
  · rfl
  · exact fbCall_zero (PDX D dec) q j h hj

/-- A leaf query whose body is no symbol of a stored table is spelled by the map for plain
chains (`leafCall`). -/
theorem leafX_own (q : LeafIn (D.L dec)) (h : ∀ s, q.body ≠ some (.inl s)) :
    leafX D dec q = leafCall (PDX D dec) q := by
  unfold leafX
  split
  · rename_i s e
    exact absurd e (h s)
  · rfl

/-- What the fifth code writes is the string of the call number 174 by which `leafX` spells a
stored table's leaf. -/
theorem storedX_fit (hcfg : D.base.cfg.size = 32) (q : LeafIn (D.L dec)) (s : List Bool)
    (h : (pLeafS D.base.cfg (8 * D.base.plan.salt) (pStored D.a D.base.plan.salt)).put q = some s) :
    ∃ c, leafX D dec q = some c ∧ s = bytesToBits (strOf c) := by
  obtain ⟨y, m, hb, hc, hl, hm, rfl⟩ := pLeafS_put _ _ _ q s h
  obtain ⟨body, salt⟩ := q
  have hb' : body = some (.inl y) := hb
  subst hb'
  have hl' : salt.length = 256 + 8 * D.base.plan.salt := hl
  have hc' : (bitsToBytes (salt.take 256) == D.base.cfg) = true := hc
  have e1 : (salt.take 256).length = 8 * 32 := by rw [List.length_take, hl']; omega
  have e2 : (salt.drop 256).length = 8 * D.base.plan.salt := by rw [List.length_drop, hl']; omega
  have e3 : (salt.length - 256) / 64 = D.base.plan.salt / 8 := by rw [hl']; omega
  refine ⟨_, if_pos hc', ?_⟩
  show _ = bytesToBits (_root_.Fmt.oStr 0 174 _ _ D.base.cfg _)
  rw [oStr32_bits _ _ _ _ _ (by decide) hcfg, (pStored_put _ _ y m hm).2, e3]
  unfold storedStr _root_.Fmt.leafBytes
  rw [size_bitsToBytes _ _ e2, ← bytes_beq _ _ hc',
    bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, e1⟩), bytesToBits_append (_ ++ _),
    bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨_, e2⟩), List.append_assoc]

variable {D} in
/-- What the five partial codes write are the bits of the strings of `famXPd`'s calls, for 0 <
K, at every description whose configuration digest has 32 bytes and whose statement has a reader
(`StmInv`: there is one only if the statement is one-to-one in the two roots). One way only:
`famXPd` has calls at queries that the codes do not write. The encoding's strings behind the two
escapes are no calls. Nothing on soundness, no probability, nothing on any hash. -/
theorem pageXPd_fit (K : ℕ) (hK : 0 < K) (hcfg : D.base.cfg.size = 32) (V : StmInv D) :
    FitX (pageXPd dec pd K hcfg V) (callsX D dec pd K) where
  leaf := fun q s h => by
    rcases PCode.join_put _ _ _ _ q s h with h1 | h1
    · obtain ⟨c, hc, e⟩ := pLeaf_put (PDX D dec) (8 * D.base.plan.salt) D.base.plan.salt rfl
        (leafPX D dec) (leafPX_fit D dec) q s h1
      refine ⟨c, ?_, e⟩
      show leafX D dec q = some c
      rw [leafX_own D dec q fun y hy => ?_]
      · exact hc
      · unfold leafCall at hc
        rw [hy] at hc
        cases hc
    · exact storedX_fit D dec hcfg q s h1
  node := fun q s h => node_tie D.base.cfg q s h
  fb := fun q j s h => by
    by_cases h0 : q.round = 0
    · rw [pFb_zero _ q j h0] at h
      by_cases hj : j.val = K
      · rw [if_pos hj] at h
        have hl : j = Fin.last K := Fin.ext hj
        rw [hl]
        exact (firstPX_fit dec pd V K q s h).2
      · rw [if_neg hj] at h
        cases h
    · rw [pFb_succ _ q j h0] at h
      obtain ⟨c, hc, e⟩ := p162_put (chainDX D dec) (PDX D dec) K hK (chainDX_fit D dec) (q, j) s h
      exact ⟨c, (firstXPd_succ D dec pd K q j h0).trans hc, e⟩
  zero := fun q j h0 hj => firstXPd_zero D dec pd K q j h0 hj

/-! ## Two strings of the encoding, each as one equation -/

variable {D} in
/-- The encoding's string of a stored table's leaf is the bits of the string of the call number
174: tree's place 0 with the numbers of the column's and the salt's words, index 2^a + position,
start the configuration's digest, bytes the column, the fill and the file's salt. Asked: the typed
salt has 256 + 8 (the plan's salt) bits and begins with the configuration's digest, and `storedOK`.
Strings only: no hash is applied. -/
theorem implX_stored_string (K : ℕ) (hcfg : D.base.cfg.size = 32) (V : StmInv D)
    (y : ℕ × List UInt64) (salt : Bits)
    (hc : (bitsToBytes (salt.take 256) == D.base.cfg) = true)
    (hl : salt.length = 256 + 8 * D.base.plan.salt) (hy : storedOK D.a D.base.plan.salt y)
    (j : Fin 1) :
    (theImplX (pageXPd dec pd K hcfg V)).code .leaf (⟨some (.inl y), salt⟩ : LeafIn (D.L dec)) j =
      bytesToBits (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 y.2.length (D.base.plan.salt / 8))
        (2 ^ D.a + y.1) D.base.cfg (_root_.Fmt.leafBytes y.2 (bitsToBytes (salt.drop 256)))) := by
  have hp := pLeafS_some (L := D.L dec) D.base.cfg (8 * D.base.plan.salt)
    (pStored D.a D.base.plan.salt) y salt _ hc hl (pStored_some D.a D.base.plan.salt y hy)
  have e1 : (salt.take 256).length = 8 * 32 := by rw [List.length_take, hl]; omega
  have e2 : (salt.drop 256).length = 8 * D.base.plan.salt := by rw [List.length_drop, hl]; omega
  rw [theImplX_stored (pageXPd dec pd K hcfg V) _ _ hp j, oStr32_bits _ _ _ _ _ (by decide) hcfg]
  unfold storedStr _root_.Fmt.leafBytes
  rw [size_bitsToBytes _ _ e2, ← bytes_beq _ _ hc,
    bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, e1⟩), bytesToBits_append (_ ++ _),
    bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨_, e2⟩), List.append_assoc]

variable {D} in
/-- The encoding's string of the first chain query, at the block of the chain value, is the bits
of the string of the call number 160: index the chain's label, no start, bytes pd (in the place of
the parameters' digest), the statement of the two roots, an empty record and the salt. Asked: the
salt is empty or has 256 bits, and the statement has fewer than 2^64 bytes. Strings only: no hash is
applied. -/
theorem implX_first_string (K : ℕ) (hcfg : D.base.cfg.size = 32) (V : StmInv D)
    (cm cm' : Dig 256) (salt : Bits) (hs : salt = [] ∨ salt.length = 256)
    (hst : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64) :
    (theImplX (pageXPd dec pd K hcfg V)).code (.fb .link)
        (⟨0, .f1 [cm, cm'] none salt, none, p0Q D.base D.C dec⟩ : FbIn 256 (D.L dec) .link)
        (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 D.base.label _root_.Fmt.zero32
        (Run.firstBytes (digToBytes pd)
          (D.stm (digToBytes cm) (digToBytes cm')) salt)) := by
  have hp : (firstPX dec pd V).put
      (⟨0, .f1 [cm, cm'] none salt, none, p0Q D.base D.C dec⟩ : FbIn 256 (D.L dec) .link) =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 D.base.label _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd) (D.stm (digToBytes cm) (digToBytes cm'))
          ByteArray.empty (runOf salt)))) := by
    show (first0X V).put (pd, some (cm, cm'), salt) = _
    unfold first0X
    exact pFirst0_put D.base.label (stmX D) (unstmX V) (unstm_stmX V) (stm_unstmX V) pd
      (some (cm, cm')) salt _ rfl hst hs
  rw [theImplX_fb (pageXPd dec pd K hcfg V) _ (Fin.last K) _ (by
    rw [pFb_zero _ _ _ rfl, if_pos (Fin.val_last K)]
    exact hp), oStr_bits, oStr_bits, Toy1.bits_first]

/-! ## famXPd against what the encoding reads out of a function on bit strings -/

section
variable {D}
variable (K : ℕ) (hK : 0 < K) (hcfg : D.base.cfg.size = 32) (V : StmInv D) (g : Fam (rom 256))
include hK

/-- A leaf query, of the chain's own trees or of a stored table, that passes the test: `famXPd`
at the function on byte strings that g induces answers as the encoding reads out of g. A stored
table's leaf passes only if its typed salt begins with the configuration's digest. Of other leaf
queries nothing is said. Nothing on soundness, no probability, nothing on any hash. -/
theorem famXPd_leaf_read (q : LeafIn (D.L dec)) (h : fitsCX
    (pageXPd dec pd K hcfg V) .leaf q = true) :
    (famXPd D dec (digToBytes pd) (oB (g ())) K .leaf q : Dig 256) =
      readBlocks (theImplX (pageXPd dec pd K hcfg V)) g .leaf q :=
  leafT_agree (pageXPd_fit dec pd K hK hcfg V) g q h

/-- A vertex's query on two strings of 256 bits: the two answers are one. Of a pair with a
string of another length nothing is said: there `famXPd` still has a call, and the two can differ.
-/
theorem famXPd_node_read (a b : Dig 256) :
    (famXPd D dec (digToBytes pd) (oB (g ())) K .node
        ((List.ofFn a, List.ofFn b) : Bits × Bits) : Dig 256) =
      readBlocks (theImplX (pageXPd dec pd K hcfg V)) g .node (List.ofFn a, List.ofFn b) :=
  nodeT_agree (pageXPd_fit dec pd K hK hcfg V) g _ (by
    show ((pNode D.base.cfg).put (List.ofFn a, List.ofFn b)).isSome = true
    rw [pNode_put D.base.cfg _ _ List.length_ofFn List.length_ofFn]
    rfl)

/-- A chain query that passes the test: the chain values are one. At round 0 this is all: of the
K blocks of the verifier's message nothing is said; there `famXPd` answers zeros. -/
theorem famXPd_last_read (q : FbIn 256 (D.L dec) .link)
    (h : fitsCX (pageXPd dec pd K hcfg V) (.fb .link) q = true) :
    (famXPd D dec (digToBytes pd) (oB (g ())) K (.fb .link) q : (Fin K → Dig 256) × Dig 256).2 =
      (readBlocks (theImplX (pageXPd dec pd K hcfg V)) g (.fb .link) q :
        (Fin K → Dig 256) × Dig 256).2 :=
  fb_agree_last (pageXPd_fit dec pd K hK hcfg V) g q (fits_last _ q h)

/-- A chain query of a round other than 0 that passes the test: the whole answers are one. Not
at round 0. -/
theorem famXPd_whole_read (q : FbIn 256 (D.L dec) .link)
    (h : fitsCX (pageXPd dec pd K hcfg V) (.fb .link) q = true) (h0 : q.round ≠ 0) :
    famXPd D dec (digToBytes pd) (oB (g ())) K (.fb .link) q =
      readBlocks (theImplX (pageXPd dec pd K hcfg V)) g (.fb .link) q :=
  fb_agree_all (pageXPd_fit dec pd K hK hcfg V) g q (fits_all _ q h h0)

/-- With marked blocks, for every g: at a query that passes the test, `famXPd` answers as the
encoding reads out of g when the marked blocks are read and zeros stand at the others. Of a query
that does not pass the test nothing is said. That a verifier asks only such queries is not said.
Nothing on soundness, no probability, nothing on any hash. -/
theorem famXPd_readSome (o : Batch.OracleName) (q : Batch.domOf 256 (D.L dec) o)
    (h : fitsCX (pageXPd dec pd K hcfg V) o q = true) :
    famXPd D dec (digToBytes pd) (oB (g ())) K o q =
      readSome (theImplX (pageXPd dec pd K hcfg V)) (needCX (pageXPd dec pd K hcfg V)) g o q := by
  rw [famXPd_eq_famT]
  exact agreeX (pageXPd_fit dec pd K hK hcfg V) g o q h

end

/-! ## At the format's own digest -/

/-- `famX` is the family of the three plain maps at the format's own digest. -/
theorem famX_eq_famT (O : ByteArray → ByteArray) (K : ℕ) :
    famX D dec O K = famT (callsX D dec (pdX D) K) O := by
  rw [famX_eq_pd, ← bytes_pdX, famXPd_eq_famT]

/-- `pageXPd_fit` at the format's own digest: what the five partial codes of `pageX` write are the
bits of the strings of `famX`'s calls, for 0 < K. One way only, as there. -/
theorem pageX_fit (K : ℕ) (hK : 0 < K) (hcfg : D.base.cfg.size = 32) (V : StmInv D) :
    FitX (pageX dec K hcfg V) (callsX D dec (pdX D) K) :=
  pageXPd_fit dec (pdX D) K hK hcfg V

/-- `famXPd_readSome` at the format's own digest. For every g, at a query that passes the test:
`famX` at the function on byte strings that g induces answers as the encoding at `pageX` reads out
of g when the marked blocks are read and zeros stand at the others. Of a query that does not pass
the test nothing is said. That a verifier asks only such queries is not said. -/
theorem famX_readSome (K : ℕ) (hK : 0 < K) (hcfg : D.base.cfg.size = 32) (V : StmInv D)
    (g : Fam (rom 256)) (o : Batch.OracleName) (q : Batch.domOf 256 (D.L dec) o)
    (h : fitsCX (pageX dec K hcfg V) o q = true) :
    famX D dec (oB (g ())) K o q =
      readSome (theImplX (pageX dec K hcfg V)) (needCX (pageX dec K hcfg V)) g o q := by
  rw [famX_eq_famT]
  exact agreeX (pageX_fit D dec K hK hcfg V) g o q h

end Run.PQ
