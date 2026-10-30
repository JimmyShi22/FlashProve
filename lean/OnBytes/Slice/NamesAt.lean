-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/NamesAt.lean: one protocol, one wiring and one family of typed oracle functions for
all statements of a chain that opens stored tables, at any function on byte strings.


`CompiledAcceptsXAt O S stm dec r0 r1 o` (OnBytes/Tie/StoredAt.lean) says that the library's
compiled verifier accepts what was read, under the typed oracle functions that a function O on byte
strings induces (`Run.PQ.famX`). Protocol, wiring and oracle functions are made from the description
S. A description holds the chain's statement, and the statement of an entry's chain holds the two
tables' roots. This file proves that none of the three reads the statement in the description: the
typed first query takes the statement's bytes from `stm` and the two roots that are typed in the
query.

The types. The protocols of two descriptions that differ in the statement alone are equal, but while
the rounds are a variable they are not equal by evaluation (`Run.rds_congr`). So the body of `famX`
is written once more here, over the components that it reads and with the rounds in the library's
form as a variable (`famG`), and the equation on the rounds is substituted there.

Main definitions: `Parts`, `partsOf`, `Parts.L`, `pdG`, `firstG`, `leafG`, `famG`: tools of the
proofs.
Main theorems.
 `famX_parts`          `famX D` is `famG` at the components of D and the rounds of D.
 `famX_reStated`       the oracle functions at S with another statement are those at S (`HEq`).
 `compiledAt_reStated`   `CompiledAcceptsXAt O (reStated S x) ..` if and only if
                       `CompiledAcceptsXAt O S ..`. No hypothesis.


 `entrySpec_params`    the description's parameter bytes are the bytes that were read.



 `withinX_reStated`   the limits test reads the statement through its length alone.






What is not claimed. Nothing on soundness, and no probability. Nothing on one block for all names of
tables: a table's key, of which the block is made, holds answers and seeds that depend on the
table's name. That any description is within the limits test (`withinX`). The reader at the pinned
function takes BLAKE2b's digest of the parameter bytes as a constant. The program does not call that
reader or any function of this file: "the program" is the Lean port that is built from OnBytes/, not
the C++ verifier. Nothing on the named set of bad traces (`badAny`, OnBytes/Slice/TopAny.lean).

-/
import OnBytes.Slice.TopNames
import OnBytes.Tie.DigestPoint

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Compile Compile.Batch _root_.Run _root_.Run.PQ
open OnBytes.Tie (xdOf inFile withinX entrySpec entryStatement CompiledAcceptsXAt pinned readInAt
  readInPinned_compiled)

/-! ## The body of `famX`, with the rounds as a variable -/

/-- What `Run.PQ.famX` reads of a description, but for the rounds in the library's form. -/
structure Parts where
  /-- the chain's label -/
  label : ℕ
  /-- the rounds as the format has them: read for each round's kind and bits of work -/
  rounds : List Fmt.Round
  /-- the parameter bytes -/
  params : ByteArray
  /-- the field -/
  field : Fmt.Fld
  /-- the bytes of a leaf's salt -/
  salt : ℕ
  /-- the configuration's digest -/
  cfg : ByteArray
  /-- the statement's bytes as a function of the two roots -/
  stm : ByteArray → ByteArray → ByteArray
  /-- the stored trees' depth -/
  a : ℕ
  /-- the openings of stored tables -/
  xs : List XO

/-- The components of a description in the library's form. The field "statement" of its base is not
among them. -/
def partsOf (D : XD) : Parts :=
  ⟨D.base.label, D.base.rounds, D.base.params, D.base.plan.field, D.base.plan.salt, D.base.cfg,
    D.stm, D.a, D.xs⟩

/-- The interface at given components and rounds. -/
abbrev Parts.L (P : Parts) (ds : List RD) (dec : View → Bool) : BatchProtocol Unit Unit :=
  Lu (ckP P.field) ds P.a P.xs dec

/-- The text of `Run.PQ.PDX` over components and rounds. -/
def pdG (P : Parts) (ds : List RD) (dec : View → Bool) : PageD (P.L ds dec) .link where
  label := P.label
  kind := fun i => if i = 0 then 7 else ((P.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((P.rounds[i - 1]?).map (·.entry.work)).getD 0
  stm := fun _ => ByteArray.empty
  msg := fun _ rt pl => match pl with
    | .inl _ => ByteArray.empty
    | .inr q => msgSL (ckP P.field) (rt.getD ByteArray.empty) ds q
  nonce := fun _ pl => match pl with
    | .inl _ => 0
    | .inr q => nonceSL (ckP P.field) ds q
  leaf := fun s => match s with
    | ⟨.inl p, _⟩ => p.elim
    | ⟨.inr q, col⟩ => leafSL (ckP P.field) P.salt ds ⟨q, col⟩
  cfg := P.cfg

/-- The text of `Run.PQ.firstX` over components and rounds. -/
def firstG (P : Parts) (ds : List RD) (dec : View → Bool) (K : ℕ)
    (q : FbIn 256 (P.L ds dec) .link) (j : Fin (K + 1)) : Option Fmt.OQ :=
  match q.round, q.head with
  | 0, .f1 [cm, cm'] none salt =>
      if j.val = K then
        some ⟨0, 160, 0, P.label, Fmt.zero32,
            firstBytes (Fmt.paramsDigest P.params) (P.stm (digToBytes cm) (digToBytes cm')) salt⟩
      else none
  | 0, _ => none
  | _, _ => fbCall (pdG P ds dec) K q j

/-- The text of `Run.PQ.leafX` over components and rounds. -/
def leafG (P : Parts) (ds : List RD) (dec : View → Bool) (q : LeafIn (P.L ds dec)) :
    Option Fmt.OQ :=
  match q.body with
  | some (.inl s) =>
      if bitsToBytes (q.salt.take 256) == P.cfg then
        some ⟨0, 174, Fmt.leafPlace 0 s.2.length ((q.salt.length - 256) / 64), 2 ^ P.a + s.1,
          P.cfg, Fmt.leafBytes s.2 (bitsToBytes (q.salt.drop 256))⟩
      else none
  | _ => leafCall (pdG P ds dec) q

/-- The text of `Run.PQ.famX` over components and rounds. -/
def famG (P : Parts) (ds : List RD) (dec : View → Bool) (O : ByteArray → ByteArray) (K : ℕ) :
    Fam (spec 256 K (P.L ds dec))
  | .leaf, q => ansOf O (leafG P ds dec q)
  | .node, q => ansOf O (nodeCallC P.cfg q)
  | .fb .link, q =>
    (fun k => ansOf O (firstG P ds dec K q k.castSucc), ansOf O (firstG P ds dec K q (Fin.last K)))
  | .fb .test, _ => (fun _ _ => false, fun _ => false)
  | .fb .onl, _ => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- `Run.PQ.PDX` at a description is `pdG` at the description's components and rounds. -/
theorem pdG_parts (D : XD) (dec : View → Bool) : PDX D dec = pdG (partsOf D) D.ds dec := by
  unfold PDX pdG
  congr 1
  · funext _ rt pl
    cases pl <;> rfl
  · funext _ pl
    cases pl <;> rfl
  · funext s
    obtain ⟨p | q, col⟩ := s
    · exact p.elim
    · rfl

/-- `Run.PQ.firstX` at a description is `firstG` at the description's components and rounds. -/
theorem firstG_parts (D : XD) (dec : View → Bool) (K : ℕ) (q : FbIn 256 (D.L dec) .link)
    (j : Fin (K + 1)) : firstX D dec K q j = firstG (partsOf D) D.ds dec K q j := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold firstX firstG
  rw [pdG_parts]
  cases round with
  | succ n => rfl
  | zero =>
    cases head with
    | f1 cms x salt => rcases cms with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> cases x <;> rfl
    | f2 _ _ => rfl
    | f3 _ _ => rfl
    | f4 _ _ => rfl
    | f5 => rfl

/-- `Run.PQ.leafX` at a description is `leafG` at the description's components and rounds. -/
theorem leafG_parts (D : XD) (dec : View → Bool) (q : LeafIn (D.L dec)) :
    leafX D dec q = leafG (partsOf D) D.ds dec q := by
  obtain ⟨body, salt⟩ := q
  unfold leafX leafG
  rw [pdG_parts]
  cases body with
  | none => rfl
  | some x => cases x <;> rfl

/-- `Run.PQ.famX` at a description is `famG` at the description's components and rounds. -/
theorem famX_parts (D : XD) (dec : View → Bool) (O : ByteArray → ByteArray) (K : ℕ) :
    famX D dec O K = famG (partsOf D) D.ds dec O K := by
  funext o
  match o with
  | .leaf =>
    funext q
    exact congrArg (ansOf O) (leafG_parts D dec q)
  | .node => rfl
  | .fb .link =>
    funext q
    exact Prod.ext (funext fun k => congrArg (ansOf O) (firstG_parts D dec K q k.castSucc))
      (congrArg (ansOf O) (firstG_parts D dec K q (Fin.last K)))
  | .fb .test => rfl
  | .fb .onl => rfl
  | .fbw _ _ => rfl
  | .rleaf => rfl
  | .rnode => rfl
  | .g _ => rfl
  | .ann => rfl
  | .other => rfl

/-- `famG` along an equation between two lists of rounds. The number of blocks is a function Kf of
the rounds. -/
theorem famG_heq (P : Parts) (Kf : List RD → ℕ) (dec : View → Bool) (O : ByteArray → ByteArray)
    (ds ds' : List RD) (h : ds' = ds) :
    HEq (famG P ds' dec O (Kf ds' + 1)) (famG P ds dec O (Kf ds + 1)) := by
  subst h
  rfl

/-! ## The statement in the description is not read -/

/-- The typed oracle functions that O induces at S with another statement are those that it induces
at S. The two have types that are equal, but not by evaluation. -/
theorem famX_reStated (S : Fmt.SpecX) (x : ByteArray) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (O : ByteArray → ByteArray) :
    HEq (famX (xdOf (reStated S x) stm) dec O ((xdOf (reStated S x) stm).K + 1))
      (famX (xdOf S stm) dec O ((xdOf S stm).K + 1)) := by
  rw [famX_parts, famX_parts]
  exact famG_heq (partsOf (xdOf S stm)) (kMax fun e k => (bsRound S.base.plan.field e k).b) dec O
    (rds (inFile S.base)) (rds (inFile (reStated S x).base)) (_root_.Run.rds_congr _ _ rfl rfl)

/-- One direction of `compiledAt_reStated`. -/
theorem compiledAt_to (O : ByteArray → ByteArray) (S : Fmt.SpecX) (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool) (r0 r1 : ByteArray)
    (o : Fmt.ChainOut) (h : CompiledAcceptsXAt O (reStated S x) stm dec r0 r1 o) :
    CompiledAcceptsXAt O S stm dec r0 r1 o := by
  obtain ⟨π', hty', hv'⟩ := h
  obtain ⟨π, g, hty, hg, hv⟩ := accept_to (ckP S.base.plan.field)
    (kMax fun e k => (bsRound S.base.plan.field e k).b) (fun K => chalP S.base.plan.field K)
    (xdOf S stm).a (xdOf S stm).xs dec (rds (inFile S.base)) (rds (inFile (reStated S x).base))
    (_root_.Run.rds_congr _ _ rfl rfl) S.base.plan.salt S.base.cfg (256 + 8 * S.base.plan.salt)
    (bytesToDig r0) (bytesToDig r1) o (famX (xdOf (reStated S x) stm) dec O _) π' hty' hv'
  have e : g = famX (xdOf S stm) dec O ((xdOf S stm).K + 1) :=
    eq_of_heq (hg.trans (famX_reStated S x stm dec O))
  subst e
  exact ⟨π, hty, hv⟩

/-- **`CompiledAcceptsXAt` does not read the statement in the description.** For every function O on
byte strings, description S, string x, function `stm`, decision, pair of roots and chain as read:
the compiled verifier accepts at S with the statement x, under the typed oracle functions that O
induces there, if and only if it accepts at S, under those that O induces there. -/
theorem compiledAt_reStated (O : ByteArray → ByteArray) (S : Fmt.SpecX) (x : ByteArray)
    (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool) (r0 r1 : ByteArray)
    (o : Fmt.ChainOut) :
    CompiledAcceptsXAt O (reStated S x) stm dec r0 r1 o ↔ CompiledAcceptsXAt O S stm dec r0 r1 o :=
  ⟨compiledAt_to O S x stm dec r0 r1 o,
    fun h => compiledAt_to O (reStated S x) S.base.statement stm dec r0 r1 o h⟩

/-! ## The parameter bytes of a description -/

/-- What `Params.Link.read` returns holds the bytes from which it was read. -/
theorem linkRead_bytes (params : ByteArray) (p : Params.Link)
    (hp : Params.Link.read params = some p) : p.given.bytes = params := by
  unfold Params.Link.read at hp
  obtain ⟨g, hg, hp⟩ := Option.bind_eq_some_iff.1 hp
  split at hp
  · rename_i c l _
    obtain ⟨c', -, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨l', -, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain rfl : (⟨g, c', l'⟩ : Params.Link) = p := Option.some.inj hp
    exact Params.Given.read_bytes hg
  · cases hp

/-- **The parameter bytes of the description that `entrySpec` gives are the bytes that were read**,
whatever the two names. So `pinned O S.base.params` is pinned at one string for all names. -/
theorem entrySpec_params (params : ByteArray) (p : Params.Link)
    (hp : Params.Link.read params = some p) (first further : Params.TableName) (block : Blk Unit)
    (S : Fmt.SpecX) (h : entrySpec p first further = some (block, S)) :
    S.base.params = params := by
  unfold entrySpec at h
  split at h
  · obtain ⟨T, hT, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rs, -, hd⟩ := Option.bind_eq_some_iff.1 hT
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    rw [Params.Given.describe_eq hd]
    exact linkRead_bytes params p hp
  · cases h

/-! ## The limits test at all names -/

/-- In a description in order the statement is within the hash's bound. -/
theorem small_of_ok (B : Fmt.Spec) (h : B.ok = true) : B.statement.size + 88 ≤ 2 ^ 32 - 144 := by
  unfold Fmt.Spec.ok Fmt.Spec.small at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- The format's conditions on a description without its stored tables (`Fmt.Spec.ok`) read the
statement through one test alone: whether it is within the hash's bound. `Fmt.SpecX.ok` reads the
statement's items too; the limits test does not hold it. -/
theorem ok_reStated (B : Fmt.Spec) (x : ByteArray)
    (h : x.size + 88 ≤ 2 ^ 32 - 144 ↔ B.statement.size + 88 ≤ 2 ^ 32 - 144) :
    ({ B with statement := x } : Fmt.Spec).ok = B.ok := by
  have e : decide (x.size + 88 ≤ 2 ^ 32 - 144) = decide (B.statement.size + 88 ≤ 2 ^ 32 - 144) :=
    decide_eq_decide.2 h
  unfold Fmt.Spec.ok Fmt.Spec.small
  rw [e]
  rfl

/-- The limits test reads the statement through that one test alone. -/
theorem withinX_reStated (S : Fmt.SpecX) (x : ByteArray)
    (h : x.size + 88 ≤ 2 ^ 32 - 144 ↔ S.base.statement.size + 88 ≤ 2 ^ 32 - 144) :
    withinX (reStated S x) = withinX S := by
  have e1 : PQ.ok (inFile (reStated S x).base) = PQ.ok (inFile S.base) := by
    unfold PQ.ok
    rw [show (inFile (reStated S x).base).ok = (inFile S.base).ok from
      ok_reStated (inFile S.base) x h]
    rfl
  have e2 : rds (inFile (reStated S x).base) = rds (inFile S.base) :=
    _root_.Run.rds_congr _ _ rfl rfl
  unfold withinX XD.ok
  show (PQ.ok (inFile (reStated S x).base) &&
      okX (rds (inFile (reStated S x).base)) (xdOf S fun _ _ => ByteArray.empty).a
        (xdOf S fun _ _ => ByteArray.empty).xs && _ && _ && _) = _
  rw [e1, e2]
  rfl

end OnBytes.Slice
