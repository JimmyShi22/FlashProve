-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/AllRoots.lean: one encoding for all roots: the join of
OnBytes/TypedOracleCompiler/Run/OneOracle.lean with protocol, wiring and encoding fixed before the roots. The
compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Why. A maker picks the two roots, and the statement under which the reader reads holds them.
`read_accepts_oneOracle` stands at one description, under which the reader reads and at which the
encoding is written. A bound under a random oracle needs an encoding that is fixed before the makers
choose. So a description S0 and a function `stm` are fixed; protocol, wiring, family and encoding
stand at `xdOf S0 stm`; the reader reads under S0 with the statement `stm r0 r1` in the place of its
own.

The obstacle, and the way round it. `stored_core` speaks at the description under which the reader
reads.
The rounds' data of two descriptions that differ in the statement alone are equal (`rds_congr`), and
so are the numbers of blocks, but not by evaluation while the rounds are a variable; and they stand
in the types of the argument string, of the family and of the embedding of own symbols. (1) The body
of `famXPd` is written once more over the components that it reads, with the rounds' data as a
variable (`Parts`, `famGPd`; `famXPd_parts`). (2) The whole conclusion of `stored_core`, with "for
every embedding of own symbols" in front, is written as a statement `AccG` on rounds' data and a
number. (3) That statement is carried along the two equations by rewriting (`accG_reStated`). No
embedding, string or family is carried, and no equation between terms of two types is used.

After OnBytes/Slice/NamesAt.lean (its part "The body of `famX`", to `compiledAt_reStated`: 15
declarations; and `small_of_ok`, `ok_reStated`, `withinX_reStated`), OnBytes/Slice/NamesAtPd.lean
(8), `accept_to` of OnBytes/Slice/TopNames.lean and the library's `Run.rds_congr`.
22 declarations.
As text but for `_root_.`, names and the argument B (7). `rds_congr`, `small_of_ok`, `ok_reStated`,
`firstGPd`, `famGPd`, `firstGPd_parts`, `famXPd_parts`.
Turned (9).
 `Parts`, `partsOf`  without the parameter bytes and the salt's length, which `famXPd` does not
     read.
 `Parts.L`  the type of bodies is a parameter.
 `pdG`, `pdG_parts`  a list of roots a query; a body's spelling is `B.own`.
 `leafG`, `leafG_parts`  which bodies are stored symbols is read by `B.getE`.
 `xdOk_withStatement` the original's `withinX_reStated`, of the sibling's `XD.ok`.
 `accG_reStated`  stands for the original's `compiledAtPd_reStated`: an equivalence, for every O, S,
     x: acceptance does not read the statement in the description.
New (6).
 `kOf_congr`  the numbers of blocks are equal. `XD.K` is the library's `kOf`, which goes through the
     library's rounds' data: its proof is the one place in this file that names them.
 `AccG`  the conclusion of `stored_core` over components, rounds' data and a number, the embedding
     bound inside.
 `accG_core`  `stored_core` in that form.
 `accepts_allRoots`  the join at one encoding for all roots, the reader at any function that agrees
     with g's off the calls with the number 169.
 `accepts_allRoots_once`  the same with the limits asked once.
 `read_accepts_allRoots`  the instance with one string pinned.
No counterpart (3): `famGPd_heq`, `famXPd_reStated`, `accept_to`: the equations between terms of two
types. Not said: `compiledAtPd_to`; a name for "the compiled verifier accepts" like the original's
`CompiledAcceptsXAtPd` (the conclusion is written out); the originals' forms at the format's own
digest (`firstG`, `famG` and their laws).

What is not said. That the description which a checker forms at two roots is S0 with the statement
put in: `withStatement` turns the field `statement` alone; label, plan, parameter bytes,
configuration digest, rounds and stored tables are S0's.
At each pair of roots it is asked
that the statement's items hold the roots. One direction: an implication between two yeses. That the
reader reads any file. That any description, bodies, embedding or statement's reader meet the
hypotheses. An
interface with one stored table, or a protocol other than `skeletonOverBothExternalStrings`, is not treated. pd is any 256
bits. Nothing on soundness; no probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.OneOracle
import OnBytes.TypedOracleCompiler.Run.SmallTrees
import Run.PlanPullM1

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run

/-! ## The rounds' data do not read the statement -/

/-- Two descriptions with the same rounds and the same first tree have the same rounds' data.
The library's text (Run/PlanPullM1.lean), over the sibling's rounds' data. An equation, not by
evaluation: `rdsFrom` goes through the list of rounds with the description as a parameter. -/
theorem rds_congr (S S' : _root_.Fmt.Spec)
    (h : S.rounds = S'.rounds) (hf : S.firstTree = S'.firstTree) : rds S = rds S' := by
  have ho : ∀ n, shapeOfOwn S n = shapeOfOwn S' n := fun n => by
    unfold shapeOfOwn allOpens
    rw [h]
  have hr : ∀ (l : List _root_.Fmt.Round) (n : ℕ), rdsFrom S n l = rdsFrom S' n l := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons r rs ih =>
      intro n
      simp only [rdsFrom, ho, hf, ih]
  unfold rds
  rw [hr, h]

/-- Two such descriptions over one field have the same number of blocks. `XD.K` is the library's
`kOf`, a function of the description through the LIBRARY'S rounds' data: so this proof, and nothing
else in this file, names them (`Run.rds_congr`). -/
theorem kOf_congr (S S' : _root_.Fmt.Spec) (h : S.rounds = S'.rounds)
    (hf : S.firstTree = S'.firstTree) (hp : S.plan.field = S'.plan.field) : kOf S = kOf S' := by
  unfold kOf
  rw [_root_.Run.rds_congr S S' h hf, hp]

/-! ## The limits read the statement through one test alone -/

/-- In a description in order the statement is within the hash's bound. -/
theorem small_of_ok (A : _root_.Fmt.Spec) (h : A.ok = true) :
    A.statement.size + 88 ≤ 2 ^ 32 - 144 := by
  unfold _root_.Fmt.Spec.ok _root_.Fmt.Spec.small at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- The format's conditions on a description without its stored tables (`Fmt.Spec.ok`) read the
statement through one test alone: whether it is within the hash's bound. -/
theorem ok_reStated (A : _root_.Fmt.Spec) (x : ByteArray)
    (h : x.size + 88 ≤ 2 ^ 32 - 144 ↔ A.statement.size + 88 ≤ 2 ^ 32 - 144) :
    ({ A with statement := x } : _root_.Fmt.Spec).ok = A.ok := by
  have e : decide (x.size + 88 ≤ 2 ^ 32 - 144) = decide (A.statement.size + 88 ≤ 2 ^ 32 - 144) :=
    decide_eq_decide.2 h
  unfold _root_.Fmt.Spec.ok _root_.Fmt.Spec.small
  rw [e]
  rfl

/-- The sibling's limits `XD.ok` read the statement through that one test alone. -/
theorem xdOk_withStatement (S : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (x : ByteArray)
    (h : x.size + 88 ≤ 2 ^ 32 - 144 ↔ S.base.statement.size + 88 ≤ 2 ^ 32 - 144) :
    (xdOf (withStatement S x) stm).ok = (xdOf S stm).ok := by
  have e1 : PQ.ok (inFile (withStatement S x).base) = PQ.ok (inFile S.base) := by
    unfold PQ.ok
    rw [show (inFile (withStatement S x).base).ok = (inFile S.base).ok from
      ok_reStated (inFile S.base) x h]
    rfl
  have e2 : rds (inFile (withStatement S x).base) = rds (inFile S.base) := rds_congr _ _ rfl rfl
  unfold XD.ok
  show (PQ.ok (inFile (withStatement S x).base) &&
      okX (rds (inFile (withStatement S x).base)) (xdOf S stm).a (xdOf S stm).xs && _) = _
  rw [e1, e2]
  rfl

/-! ## The body of `famXPd`, with the rounds' data as a variable -/

/-- What `famXPd` reads of a description, but for the rounds' data. -/
structure Parts where
  /-- the chain's label -/
  label : ℕ
  /-- the rounds as the format has them: read for each round's kind and bits of work -/
  rounds : List _root_.Fmt.Round
  /-- the field -/
  field : _root_.Fmt.Fld
  /-- the configuration's digest -/
  cfg : ByteArray
  /-- the statement's bytes as a function of the two roots -/
  stm : ByteArray → ByteArray → ByteArray
  /-- the stored trees' depth -/
  a : ℕ
  /-- the openings of stored tables -/
  xs : List XO

/-- The components of a description. The field "statement" of its base is not among them. -/
def partsOf (D : XD) : Parts :=
  ⟨D.base.label, D.base.rounds, D.base.plan.field, D.base.cfg, D.stm, D.a, D.xs⟩

/-- The interface at given components and rounds' data. -/
abbrev Parts.L (Bd : Type) (P : Parts) (ds : List RD) (dec : View → Bool) : BatchProtocolWithLeafBody Unit Unit :=
  LkX (I := Unit) (RI := Unit) Bd (ckP P.field) ds P.a P.xs dec (fun _ _ p => (p.val, []))
    (fun _ => some ())

variable {Bd : Type} (B : BodyD Bd)

/-- The text of `PDX` over components and rounds' data. -/
def pdG (P : Parts) (ds : List RD) (dec : View → Bool) : PageD (P.L Bd ds dec) .link where
  label := P.label
  kind := fun i => if i = 0 then 7 else ((P.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((P.rounds[i - 1]?).map (·.entry.work)).getD 0
  stm := fun _ => ByteArray.empty
  msg := fun _ rt pl => match pl with
    | .inl _ => ByteArray.empty
    | .inr q => msgSL (ckP P.field) rt ds q
  nonce := fun _ pl => match pl with
    | .inl _ => 0
    | .inr q => nonceSL (ckP P.field) ds q
  leaf := B.own
  cfg := P.cfg

/-- The text of `firstXPd` over components and rounds' data. -/
def firstGPd (P : Parts) (pd : ByteArray) (ds : List RD) (dec : View → Bool) (K : ℕ)
    (q : FbIn 256 (P.L Bd ds dec) .link) (j : Fin (K + 1)) : Option _root_.Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [cm, cm'] none salt =>
      if j.val = K then
        some ⟨0, 160, 0, P.label, _root_.Fmt.zero32,
            firstBytes pd (P.stm (digToBytes cm) (digToBytes cm')) salt⟩
      else none
  | 0, _ => none
  | _, _ => fbCall (pdG B P ds dec) K q j

/-- The text of `leafX` over components and rounds' data. -/
def leafG (P : Parts) (ds : List RD) (dec : View → Bool) (q : LeafIn (P.L Bd ds dec)) :
    Option _root_.Fmt.OQ :=
  match B.getE q.body with
  | some s =>
      if bitsToBytes (q.salt.take 256) == P.cfg then
        some ⟨0, 174, _root_.Fmt.leafPlace 0 s.2.length ((q.salt.length - 256) / 64), 2 ^ P.a + s.1,
          P.cfg, _root_.Fmt.leafBytes s.2 (bitsToBytes (q.salt.drop 256))⟩
      else none
  | none => leafCall (pdG B P ds dec) q

/-- The text of `famXPd` over components and rounds' data. -/
def famGPd (P : Parts) (pd : ByteArray) (ds : List RD) (dec : View → Bool)
    (O : ByteArray → ByteArray) (K : ℕ) : Fam (typedOracleFamily 256 K (P.L Bd ds dec))
  | .leaf, q => ansOf O (leafG B P ds dec q)
  | .node, q => ansOf O (nodeCallC P.cfg q)
  | .fb .link, q =>
    (fun k => ansOf O (firstGPd B P pd ds dec K q k.castSucc),
      ansOf O (firstGPd B P pd ds dec K q (Fin.last K)))
  | .fb .test, _ => (fun _ _ => false, fun _ => false)
  | .fb .onl, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- `PDX` at a description is `pdG` at the description's components and rounds' data. -/
theorem pdG_parts (D : XD) (dec : View → Bool) : PDX B D dec = pdG B (partsOf D) D.ds dec := by
  unfold PDX pdG
  congr 1
  · funext _ rt pl
    cases pl <;> rfl
  · funext _ pl
    cases pl <;> rfl

/-- `firstXPd` at a description is `firstGPd` at its components and rounds' data. -/
theorem firstGPd_parts (D : XD) (dec : View → Bool) (pd : ByteArray) (K : ℕ)
    (q : FbIn 256 (D.L Bd dec) .link) (j : Fin (K + 1)) :
    firstXPd B D dec pd K q j = firstGPd B (partsOf D) pd D.ds dec K q j := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold firstXPd firstGPd
  rw [pdG_parts]
  cases round with
  | succ n => rfl
  | zero =>
    cases head with
    | f1 cms x salt => rcases cms with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> cases x <;> rfl
    | f2 _ _ => rfl
    | f3 _ _ => rfl
    | f4 _ _ => rfl
    | f5 _ => rfl

/-- `leafX` at a description is `leafG` at its components and rounds' data. -/
theorem leafG_parts (D : XD) (dec : View → Bool) (q : LeafIn (D.L Bd dec)) :
    leafX B D dec q = leafG B (partsOf D) D.ds dec q := by
  obtain ⟨body, salt⟩ := q
  unfold leafX leafG
  rw [pdG_parts]
  rfl

/-- `famXPd` at a description is `famGPd` at its components and rounds' data. -/
theorem famXPd_parts (D : XD) (dec : View → Bool) (pd : ByteArray) (O : ByteArray → ByteArray)
    (K : ℕ) : famXPd B D dec pd O K = famGPd B (partsOf D) pd D.ds dec O K := by
  funext o
  match o with
  | .leaf =>
    funext q
    exact congrArg (ansOf O) (leafG_parts B D dec q)
  | .node => rfl
  | .fb .link =>
    funext q
    exact Prod.ext
      (funext fun k => congrArg (ansOf O) (firstGPd_parts B D dec pd K q k.castSucc))
      (congrArg (ansOf O) (firstGPd_parts B D dec pd K q (Fin.last K)))
  | .fb .test => rfl
  | .fb .onl => rfl
  | .fbw _ _ => rfl
  | .rleaf => rfl
  | .rnode => rfl
  | .g _ => rfl
  | .ann => rfl
  | .other => rfl

/-! ## "The compiled verifier accepts what was read", as a statement on rounds' data and a number -/

/-- "For every embedding of the chain's own symbols into bodies that spells them as the format
does and meets no stored symbol, the typing makes a string of o and the evaluable form of the
compiled verifier accepts it", written over components, with the rounds' data ds and the number K
of blocks as variables. The embedding is bound inside: so the statement can be carried along an
equation on ds with no embedding carried. -/
def AccG (P : Parts) (salt : ℕ) (pd : ByteArray) (O : ByteArray → ByteArray) (dec : View → Bool)
    (cm cm' : Dig 256) (o : _root_.Fmt.ChainOut) (ds : List RD) (K : ℕ) : Prop :=
  ∀ embS : (p : OPos (Twin.up (SOf (ckP P.field) ds))) →
      OSym (Twin.up (SOf (ckP P.field) ds)) p → Bd,
    (∀ p a, B.own (embS (.inr p) a) = some (leafSL (ckP P.field) salt ds ⟨p, a⟩)) →
    (∀ p a, B.getE (embS (.inr p) a) = none) →
    ∃ π : OneProtocolProof 256 (skeletonOverBothExternalStrings (ckP P.field) ds P.a P.xs dec).up,
      toBPrfX salt P.cfg (ckP P.field) ds P.a P.xs dec o = some π ∧
      verifyP (fun _ => P.L Bd ds dec) (famGPd B P pd ds dec O (K + 1)) id none
        (256 + 8 * salt) 256 .link (skeletonOverBothExternalStrings (ckP P.field) ds P.a P.xs dec)
        (wqX (ckP P.field) K (chalP P.field K) ds P.a P.xs dec) embS
        (embPX Bd (ckP P.field) ds P.a P.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
        (fun _ => none) B.embE 0 [cm, cm'] () π = true

/-- `stored_core` in that form, at the description under which the reader has read. -/
theorem accG_core (S : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (pd : ByteArray)
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : (xdOf S stm).ok = true) (hn : S.base.rand.isNone = false)
    (honce : (S.stored.flatten.map (·.item == 1)).Nodup)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      _root_.Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (hpd : _root_.Fmt.HO O 169 0 1 _root_.Fmt.zero32 S.base.params = pd)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) S seen b i = some (o, j))
    (hdec : dec (_root_.Fmt.viewX S o) = true) :
    AccG B (partsOf (xdOf S stm)) S.base.plan.salt pd O dec (bytesToDig r0) (bytesToDig r1) o
      (xdOf S stm).ds (xdOf S stm).K := by
  intro embS hi hns
  obtain ⟨π, t1, t2⟩ := stored_core S stm dec O hO B pd embS r0 r1 h0 h1 hok hn honce hst hroot hpd
    hi hns seen b i o j e hdec
  rw [famXPd_parts] at t2
  exact ⟨π, t1, t2⟩

/-- That statement does not read the statement in the description: it holds at S with x in the
place of its statement exactly if it holds at S. -/
theorem accG_reStated (S : _root_.Fmt.SpecX) (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray) (pd : ByteArray) (O : ByteArray → ByteArray)
    (dec : View → Bool) (cm cm' : Dig 256) (o : _root_.Fmt.ChainOut) :
    AccG B (partsOf (xdOf (withStatement S x) stm)) S.base.plan.salt pd O dec cm cm' o
        (xdOf (withStatement S x) stm).ds (xdOf (withStatement S x) stm).K ↔
      AccG B (partsOf (xdOf S stm)) S.base.plan.salt pd O dec cm cm' o (xdOf S stm).ds
        (xdOf S stm).K := by
  have hds : (xdOf (withStatement S x) stm).ds = (xdOf S stm).ds := rds_congr _ _ rfl rfl
  have hK : (xdOf (withStatement S x) stm).K = (xdOf S stm).K := kOf_congr _ _ rfl rfl rfl
  rw [hds, hK]
  exact Iff.rfl

/-! ## One encoding for all roots -/

section
variable (S0 : _root_.Fmt.SpecX)
  (stm : ByteArray → ByteArray → ByteArray) (Lf : LeafD (xdOf S0 stm) B) (dec : View → Bool)
  (hcfg : S0.base.cfg.size = 32) (V : StmInv (xdOf S0 stm))
  (embS : (p : OPos (Twin.up (SOf (xdOf S0 stm).C (xdOf S0 stm).ds))) →
    OSym (Twin.up (SOf (xdOf S0 stm).C (xdOf S0 stm).ds)) p → Bd)

/-- One encoding for all roots: what the strict reader with stored tables has read, under the
statement of any two roots, the compiled verifier's run over the one oracle accepts, if the decision
does. S0, `stm`, the decision, the bodies' data, the embedding of own symbols, pd, and with them
protocol, wiring and the encoding `implAtPd B S0 stm .. pd` are fixed before the roots. g is any
function on bit strings. The reader stands at the hash of any function O' on byte strings with
answers of 32 bytes that gives the bytes of pd as the digest of the parameter bytes (`hpd`) and
agrees with the function that g induces at every call whose number is not 169 modulo 65536 (`hag`).
For all r0, r1 of 32 bytes: if the reader has read o under S0 with the statement `stm r0 r1` in the
place of its own, and the decision says yes on o's view, then the typing at `xdOf S0 stm` makes a
string π of o, and the run of `verifyOneProtocol` on π under the two roots, at the family that the one
encoding reads out of g, says yes. Asked at each pair of roots: the statement's items hold the
roots; the description with that statement is within the sibling's limits (`XD.ok`; asked once
instead: `accepts_allRoots_once`). The other hypotheses are on what is fixed, as in
`read_accepts_oneOracle`. An implication between two yeses: nothing on soundness; no probability. -/
theorem accepts_allRoots (pd : Dig 256) (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hOwn : OwnFits B (xdOf S0 stm) Lf embS)
    (hi : ∀ p a, B.own (embS (.inr p) a) =
      some (leafSL (xdOf S0 stm).C S0.base.plan.salt (xdOf S0 stm).ds ⟨p, a⟩))
    (hn : S0.base.rand.isNone = false)
    (honce : (S0.stored.flatten.map (·.item == 1)).Nodup)
    (g : Fam (rom 256)) (O' : ByteArray → ByteArray) (hO : ∀ s, (O' s).size = 32)
    (hpd : _root_.Fmt.HO O' 169 0 1 _root_.Fmt.zero32 S0.base.params = digToBytes pd)
    (hag : ∀ q : _root_.Fmt.OQ, q.number % 65536 ≠ 169 → O' (strOf q) = oB (g ()) (strOf q))
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : (xdOf (withStatement S0 (stm r0 r1)) stm).ok = true)
    (hroot : ∀ t ∈ S0.stored.flatten,
      _root_.Fmt.itemRoot (stm r0 r1) t.item = some (if t.item == 1 then r1 else r0))
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O') (withStatement S0 (stm r0 r1)) seen b
      i = some (o, j))
    (hdec : dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) = true) :
    ∃ π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up,
      toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
        (xdOf S0 stm).xs dec o = some π ∧
      (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L Bd dec)
        (256 + 8 * S0.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
        (wX (xdOf S0 stm) dec) embS (embX Bd (xdOf S0 stm) dec)
        (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π).det
        (readBlocks (implAtPd B S0 stm Lf dec hcfg V pd) g) = true := by
  have hokb : PQ.ok (inFile (withStatement S0 (stm r0 r1)).base) = true := by
    have hok' := hok
    unfold XD.ok at hok'
    simp only [Bool.and_eq_true] at hok'
    exact hok'.1.1
  have hlen : (stm r0 r1).size < 2 ^ 64 := by
    have h : (stm r0 r1).size + 88 ≤ 2 ^ 32 - 144 := small_of_ok _ (PQ.specOk_of _ hokb)
    omega
  have A := (accG_reStated B S0 (stm r0 r1) stm (digToBytes pd) O' dec (bytesToDig r0)
    (bytesToDig r1) o).1 (accG_core B (withStatement S0 (stm r0 r1)) stm dec O' hO (digToBytes pd)
      r0 r1 h0 h1 hok hn honce rfl hroot hpd seen b i o j e hdec)
  obtain ⟨π, t1, t2⟩ : ∃ π : OneProtocolProof 256
        (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up,
      toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
        (xdOf S0 stm).xs dec o = some π ∧
      verifyP (fun _ => (xdOf S0 stm).L Bd dec)
        (famGPd B (partsOf (xdOf S0 stm)) (digToBytes pd) (xdOf S0 stm).ds dec O' ((xdOf S0 stm).K +
            1)) id none
        (256 + 8 * S0.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec)
        (wX (xdOf S0 stm) dec) embS (embX Bd (xdOf S0 stm) dec)
        (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π = true :=
    A embS hi (fun p a => hOwn.notStored (.inr p) a)
  rw [← famXPd_parts, famXPd_agree B (xdOf S0 stm) dec (digToBytes pd) O' (oB (g ())) hag] at t2
  refine ⟨π, t1, ?_⟩
  have E := read_verifyBSPd (xdOf S0 stm) dec B Lf embS pd hcfg V F hOwn g
    (withStatement S0 (stm r0 r1)) rfl O' hO
    (own_of_ok (inFile (withStatement S0 (stm r0 r1)).base) hokb) hn seen b i o j e
    (bytesToDig r0) (bytesToDig r1)
    (by
      rw [_root_.Run.TieTree.dig_bytes _ h0, _root_.Run.TieTree.dig_bytes _ h1]
      exact hlen) π t1
  refine E.symm.trans ?_
  rw [← thin_verify Unit Unit 256 _ ((xdOf S0 stm).L Bd dec)
    (famXPd B (xdOf S0 stm) dec (digToBytes pd) (oB (g ())) ((xdOf S0 stm).K + 1)) Unit _ _ 256
    .link
    _ _ _ _ (fun _ => none) B.embE 0 _ () π]
  exact t2

/-- The same with the limits asked ONCE, of the fixed description: `XD.ok` at `xdOf S0 stm`, and
every statement of two roots of 32 bytes is within the hash's bound. By `xdOk_withStatement`. At
each pair of roots one thing is left: the statement's items hold the roots. -/
theorem accepts_allRoots_once (pd : Dig 256) (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hOwn : OwnFits B (xdOf S0 stm) Lf embS)
    (hi : ∀ p a, B.own (embS (.inr p) a) =
      some (leafSL (xdOf S0 stm).C S0.base.plan.salt (xdOf S0 stm).ds ⟨p, a⟩))
    (hn : S0.base.rand.isNone = false)
    (honce : (S0.stored.flatten.map (·.item == 1)).Nodup)
    (hok0 : (xdOf S0 stm).ok = true)
    (hstm : ∀ a b : ByteArray, a.size = 32 → b.size = 32 → (stm a b).size + 88 ≤ 2 ^ 32 - 144)
    (g : Fam (rom 256)) (O' : ByteArray → ByteArray) (hO : ∀ s, (O' s).size = 32)
    (hpd : _root_.Fmt.HO O' 169 0 1 _root_.Fmt.zero32 S0.base.params = digToBytes pd)
    (hag : ∀ q : _root_.Fmt.OQ, q.number % 65536 ≠ 169 → O' (strOf q) = oB (g ()) (strOf q))
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hroot : ∀ t ∈ S0.stored.flatten,
      _root_.Fmt.itemRoot (stm r0 r1) t.item = some (if t.item == 1 then r1 else r0))
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O') (withStatement S0 (stm r0 r1)) seen b
      i = some (o, j))
    (hdec : dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) = true) :
    ∃ π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up,
      toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
        (xdOf S0 stm).xs dec o = some π ∧
      (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L Bd dec)
        (256 + 8 * S0.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
        (wX (xdOf S0 stm) dec) embS (embX Bd (xdOf S0 stm) dec)
        (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π).det
        (readBlocks (implAtPd B S0 stm Lf dec hcfg V pd) g) = true := by
  have hokb : PQ.ok (inFile S0.base) = true := by
    have hok' := hok0
    unfold XD.ok at hok'
    simp only [Bool.and_eq_true] at hok'
    exact hok'.1.1
  exact accepts_allRoots B S0 stm Lf dec hcfg V embS pd F hOwn hi hn honce g O' hO hpd hag r0 r1 h0
    h1 ((xdOk_withStatement S0 stm (stm r0 r1)
      ⟨fun _ => small_of_ok (inFile S0.base) (PQ.specOk_of _ hokb), fun _ => hstm r0 r1 h0
          h1⟩).trans
      hok0) hroot seen b i o j e hdec

/-- The instance at g's function with the one string of the call on the parameter bytes pinned at
pd. -/
theorem read_accepts_allRoots (pd : Dig 256) (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hOwn : OwnFits B (xdOf S0 stm) Lf embS)
    (hi : ∀ p a, B.own (embS (.inr p) a) =
      some (leafSL (xdOf S0 stm).C S0.base.plan.salt (xdOf S0 stm).ds ⟨p, a⟩))
    (hn : S0.base.rand.isNone = false)
    (honce : (S0.stored.flatten.map (·.item == 1)).Nodup)
    (g : Fam (rom 256)) (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hok : (xdOf (withStatement S0 (stm r0 r1)) stm).ok = true)
    (hroot : ∀ t ∈ S0.stored.flatten,
      _root_.Fmt.itemRoot (stm r0 r1) t.item = some (if t.item == 1 then r1 else r0))
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id)
      (_root_.Fmt.HO (pinnedAt (oB (g ())) S0.base.params (digToBytes pd)))
      (withStatement S0 (stm r0 r1)) seen b i = some (o, j))
    (hdec : dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) = true) :
    ∃ π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up,
      toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
        (xdOf S0 stm).xs dec o = some π ∧
      (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L Bd dec)
        (256 + 8 * S0.base.plan.salt) 256 .link
        (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
        (wX (xdOf S0 stm) dec) embS (embX Bd (xdOf S0 stm) dec)
        (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π).det
        (readBlocks (implAtPd B S0 stm Lf dec hcfg V pd) g) = true :=
  accepts_allRoots B S0 stm Lf dec hcfg V embS pd F hOwn hi hn honce g
    (pinnedAt (oB (g ())) S0.base.params (digToBytes pd))
    (size_pinnedAt _ (fun _ => size_digToBytes _) _ _ (size_digToBytes _))
    (HO_pinnedAt_digest _ _ _) (pinnedAt_agree _ _ _) r0 r1 h0 h1 hok hroot seen b i o j e hdec

end

end TypedOracleCompiler.Run.PQ
