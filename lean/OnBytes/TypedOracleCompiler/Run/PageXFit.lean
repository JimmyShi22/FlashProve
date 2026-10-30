-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageXFit.lean: all data of the encoding of typed queries into one oracle's strings,
from the description of a chain that opens stored tables, over the sibling's widened page; and its
fit with the typed oracle functions `famXPd`.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/PageXFit.lean (41 declarations, 579 lines). Bodies are a parameter:
the bodies' data `B : BodyD Bd` (OnBytes/TypedOracleCompiler/Run/PlanQXRun.lean) and the page's one code of bodies
with what is asked of it (`LeafD D B`) are arguments. An instance at string bodies is not
here.

AS TEXT BUT FOR NAMES AND THE NEW ARGUMENTS (22). `PBX`, `chainDX`, `chainDX_fit`, `StmInv`, `stmX`,
`unstmX`, `unstm_stmX`, `stm_unstmX`, `mkF_selF`, `first0X`, `firstPX`, `firstPX_hdr`,
`firstPX_fit`, `callsX`, `famXPd_eq_famT`, `firstXPd_succ`, `firstXPd_zero`, `famXPd_leaf_read`,
`famXPd_node_read`, `famXPd_last_read`, `famXPd_whole_read`, `famXPd_readSome`.
TURNED (12).
 `selF`, `mkF`, `selF_some`, `selF_mkF`   a query's roots are a list: `[]` where the original has
                      `none`; `p0X` for the library's `p0Q`.
 `pbX`, `serAllX`     the case "link" is written out; a body's serialiser is a datum (`Lf.ser`),
                      where the original has one of stored symbols and one of typed own symbols.
 `pageXPd`            ONE code of bodies `Lf.p` with the widened tag condition, and the test
                      `leafOKX`; the original has two codes, joined.
 `leafX_own`          its hypothesis is `B.getE q.body = none`.
 `storedX_fit`        through `pLeafC_stored` (OnBytes/TypedOracleCompiler/Run/PageXJoin.lean); then the original's
                      text.
 `pageXPd_fit`        its clause on leaves goes by cases on `B.getE q.body`; the other three clauses
                      are as text.
 `impl_stored_string`, `impl_first_string`   the original's `implX_..`; the first through
                      `pLeafC_stored`.
NEW (9).
 `LeafD D B`          the code of bodies; its tag condition; on stored symbols it IS `pStored` at
                      the description's depth and salt (an equation of options); on other bodies it
                      follows `B.own` under the number 164; a serialiser.
 `leafOKX`            the page's test on body and salt together: at a stored symbol `startIs` the
                      configuration's digest; at every other body nothing.
 `storedIn_pageXPd`   the page meets `StoredIn`: what `sameStored_impl` asks of a page.
 `leafX_stored`       how a stored symbol's leaf is spelled, as one equation.
 `pLeaf_put1`         the sibling's `pLeaf_put` with its hypothesis asked at the query's own body
                      alone: `LeafD.own` speaks of bodies that are no stored symbols.
 `serPBL`, `p0X`, `isP0X`, `isP0X_iff`   the text of the library's Run/PageQ.lean (`serPBL`, `p0Q`,
                      `isP0Q`, `isP0Q_iff`), which is not said over the sibling.
NO COUNTERPART (7). `tagsOK_all`, `leafPX`, `leafPX_fit`, `symX`: the typed code of the chain's own
symbols; their place is taken by the fields `tag`, `own` and `ser` of `LeafD`, which are hypotheses
here. `pdX`, `bytes_pdX`, `pageX`: the page at the format's own digest; pd is an argument
throughout.

WHAT IS NOT SAID. That any code of bodies meets `LeafD`: the four facts that the original proves of
the library's typed code of own leaves are asked here. That a verifier asks only queries that fit
(OnBytes/Tie/PageXAsked.lean). One way only: `famXPd` has calls at queries that the codes do not
write. pd is any 256 bits: nothing ties it to the parameter bytes. Nothing on soundness; no
probability; nothing on any hash.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXJoin
import OnBytes.TypedOracleCompiler.Run.PlanQXRun
import OnBytes.TypedOracleCompiler.Run.SerThin
import Run.PageQFit
import Run.PageIsReaders

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run

variable (Bd : Type) (D : XD) (dec : View → Bool)

/-- A plain part of some round of the protocol under the tag "link". -/
abbrev PBX : Type := PlainPart (shapeOf (D.L Bd dec) .link) (annOf (D.L Bd dec) .link)

/-! ## The chain behind the first query: the sibling's for plain chains -/

/-- The chain's data: the description's label, kinds and work; the messages' codes are the
sibling's for plain chains, with a list of roots a query. -/
def chainDX : ChainD (D.L Bd dec) .link where
  label := D.base.label
  kind := fun i => if i = 0 then 7 else ((D.base.rounds[i - 1]?).map (·.kind.num)).getD 7
  work := fun i => if i = 0 then 0 else ((D.base.rounds[i - 1]?).map (·.entry.work)).getD 0
  rc := rcQ Bd D.base D.C dec
  hrc := rcQ_ge Bd D.base D.C dec

variable {Bd} in
/-- The chain's data fit the spellings `PDX B D dec`. -/
theorem chainDX_fit (B : BodyD Bd) : ChainFit (chainDX Bd D dec) (PDX B D dec) where
  label := rfl
  kind := fun _ => rfl
  work := fun _ => rfl
  rc := fun i rt pl s h => by
    match i, h with
    | 0, h => cases h
    | i + 1, h =>
        obtain ⟨b, rfl, h1⟩ := inR_put' _ rt pl s h
        exact rcL_fit D.C D.ds i rt b s h1

/-! ## The total code behind the escape -/

/-- A serialiser of a plain part of some round behind the trivial one. The library's text, over the
sibling's rounds' data. -/
def serPBL (C : CK) : (ds : List RD) → Ser (PBL C ds)
  | [] => Ser.empty
  | d :: ds => Ser.sum (Ser.sum Ser.unit (serG (serPl d.items) d.entry.work)) (serPBL C ds)

/-- Serialisers of a plain part of some round, for the three protocols of the interface. -/
def pbX : ∀ t : Tag, Ser (PlainPart (shapeOf (D.L Bd dec) t) (annOf (D.L Bd dec) t))
  | .link => Ser.sum (Ser.sum Ser.unit Ser.unit) (serPBL D.C D.ds)
  | .onl => Ser.empty
  | .test => Ser.empty

variable {Bd} in
/-- The serialisers. TWO: that of a body is data. -/
def serAllX (sb : Ser Bd) : SerP (fun _ : Unit => D.L Bd dec) :=
  ⟨Ser.unit, sb, pbX Bd D dec⟩

/-! ## The first query -/

/-- The plain part of the trivial round 0. -/
def p0X : PBX Bd D dec := .inl (.inr ())

/-- The test for it. -/
def isP0X : PBX Bd D dec → Bool
  | .inl (.inr ()) => true
  | _ => false

/-- The test is right. -/
theorem isP0X_iff (p : PBX Bd D dec) : isP0X Bd D dec p = true ↔ p = p0X Bd D dec := by
  rcases p with (_ | ⟨⟩) | _
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- A reader for the statement: from the bytes `D.stm r0 r1` back to the two roots, as digests,
with both laws. -/
structure StmInv where
  /-- the reader -/
  un     : ByteArray → Option (Dig 256 × Dig 256)
  /-- it reads the roots out of their statement -/
  un_stm : ∀ a b, un (D.stm (digToBytes a) (digToBytes b)) = some (a, b)
  /-- it reads roots only out of their statement -/
  stm_un : ∀ s a b, un s = some (a, b) → D.stm (digToBytes a) (digToBytes b) = s

/-- The statement's bytes, of the two roots. -/
def stmX : Option (Dig 256 × Dig 256) → Option ByteArray
  | some r => some (D.stm (digToBytes r.1) (digToBytes r.2))
  | none => none

variable {D} in
/-- The two roots, of the statement's bytes. -/
def unstmX (V : StmInv D) (b : ByteArray) : Option (Option (Dig 256 × Dig 256)) :=
  (V.un b).map some

variable {D} in
/-- The reading undoes the spelling. -/
theorem unstm_stmX (V : StmInv D) (x : Option (Dig 256 × Dig 256)) (b : ByteArray)
    (h : stmX D x = some b) : unstmX V b = some x := by
  cases x with
  | none => cases h
  | some r =>
      rw [← Option.some.inj h]
      show (V.un _).map some = _
      rw [V.un_stm]
      rfl

variable {D} in
/-- The spelling undoes the reading. -/
theorem stm_unstmX (V : StmInv D) (b : ByteArray) (x : Option (Dig 256 × Dig 256))
    (h : unstmX V b = some x) : stmX D x = some b := by
  unfold unstmX at h
  cases hu : V.un b with
  | none => rw [hu] at h; cases h
  | some r =>
      rw [hu] at h
      rw [← Option.some.inj h]
      exact congrArg some (V.stm_un b r.1 r.2 hu)

variable (pd : Dig 256)

/-- A chain query of round 0 in the first format, with a list of two digests, no statement, no root
and the trivial round's plain part, as (pd, the two roots, the salt). -/
def selF (q : FbIn 256 (D.L Bd dec) .link) :
    Option (Dig 256 × Option (Dig 256 × Dig 256) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [cm, cm'] none salt, [] =>
      if isP0X Bd D dec q.plain = true then some (pd, some (cm, cm'), salt) else none
  | _, _, _ => none

/-- The way back: refused if the first digest is not pd, or there are no roots. -/
def mkF (a : Dig 256 × Option (Dig 256 × Dig 256) × List Bool) :
    Option (FbIn 256 (D.L Bd dec) .link) :=
  match a.2.1 with
  | some r =>
      if a.1 = pd then some ⟨0, .f1 [r.1, r.2] none a.2.2, [], p0X Bd D dec⟩ else none
  | none => none

/-- What `selF` reads: the query's fields. -/
theorem selF_some (q : FbIn 256 (D.L Bd dec) .link)
    (a : Dig 256 × Option (Dig 256 × Dig 256) × List Bool) (h : selF Bd D dec pd q = some a) :
    ∃ cm cm' salt, q = ⟨0, .f1 [cm, cm'] none salt, [], p0X Bd D dec⟩ ∧
      a = (pd, some (cm, cm'), salt) := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold selF at h
  split at h
  · rename_i cm cm' salt e1 e2 e3
    have e1' : round = 0 := e1
    have e2' : head = .f1 [cm, cm'] none salt := e2
    have e3' : rt = [] := e3
    by_cases hq : isP0X Bd D dec plain = true
    · have h' : (if isP0X Bd D dec plain = true then some (pd, some (cm, cm'), salt)
          else none) = some a := h
      rw [if_pos hq] at h'
      refine ⟨cm, cm', salt, ?_, (Option.some.inj h').symm⟩
      rw [e1', e2', e3', (isP0X_iff Bd D dec plain).1 hq]
    · have h' : (if isP0X Bd D dec plain = true then some (pd, some (cm, cm'), salt)
          else none) = some a := h
      rw [if_neg hq] at h'
      cases h'
  · cases h

/-- The way back undoes `selF`. -/
theorem mkF_selF (q : FbIn 256 (D.L Bd dec) .link)
    (a : Dig 256 × Option (Dig 256 × Dig 256) × List Bool) (h : selF Bd D dec pd q = some a) :
    mkF Bd D dec pd a = some q := by
  obtain ⟨cm, cm', salt, rfl, rfl⟩ := selF_some Bd D dec pd q a h
  exact if_pos rfl

/-- `selF` undoes the way back. -/
theorem selF_mkF (a : Dig 256 × Option (Dig 256 × Dig 256) × List Bool)
    (q : FbIn 256 (D.L Bd dec) .link) (h : mkF Bd D dec pd a = some q) :
    selF Bd D dec pd q = some a := by
  obtain ⟨p, x, salt⟩ := a
  cases x with
  | none => cases h
  | some r =>
      have h0 : (if p = pd then
          some (⟨0, .f1 [r.1, r.2] none salt, [], p0X Bd D dec⟩ : FbIn 256 (D.L Bd dec) .link)
          else none) = some q := h
      by_cases hp : p = pd
      · rw [if_pos hp] at h0
        rw [← Option.some.inj h0, hp]
        show (if isP0X Bd D dec (p0X Bd D dec) = true then
          some (pd, some (r.1, r.2), salt) else none) = _
        rw [if_pos ((isP0X_iff Bd D dec _).2 rfl)]
      · rw [if_neg hp] at h0
        cases h0

variable {D} in
/-- The library's code of a first call, on (digest, the two roots, salt). -/
def first0X (V : StmInv D) : PCode (Dig 256 × Option (Dig 256 × Dig 256) × List Bool) :=
  pFirst0 D.base.label (stmX D) (unstmX V) (unstm_stmX V) (stm_unstmX V)

variable {D} in
/-- The first chain query. Written exactly if the query is of round 0, in the first format with
two digests and no statement, has no root and the trivial round's plain part, the statement's bytes
are fewer than 2^64, and the salt is empty or has 256 bits. The string is that of the call number
160 with pd in the place of the parameters' digest, the statement of the two roots, an empty record
and the salt. -/
def firstPX (V : StmInv D) : PCode (FbIn 256 (D.L Bd dec) .link) :=
  (first0X V).pull (selF Bd D dec pd) (mkF Bd D dec pd) (mkF_selF Bd D dec pd)
    (selF_mkF Bd D dec pd)

variable {D} in
/-- Every string of the first query's code begins with the header of the call number 160. -/
theorem firstPX_hdr (V : StmInv D) (q : FbIn 256 (D.L Bd dec) .link) (s : List Bool)
    (h : (firstPX Bd dec pd V).put q = some s) : ∃ r, s = hdr160 D.base.label ++ r := by
  obtain ⟨a, -, ha⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact pFirst0_hdr _ _ _ _ _ a s ha

variable {Bd D} in
/-- What the first query's code writes is the string of the call by which `firstXPd` spells the
query at the block of the chain value. -/
theorem firstPX_fit (B : BodyD Bd) (V : StmInv D) (K : ℕ) (q : FbIn 256 (D.L Bd dec) .link)
    (s : List Bool) (h : (firstPX Bd dec pd V).put q = some s) :
    q.round = 0 ∧ ∃ c, firstXPd B D dec (digToBytes pd) K q (Fin.last K) = some c ∧
      s = bytesToBits (strOf c) := by
  obtain ⟨a, ha, hs⟩ := PCode.pull_put _ _ _ _ _ q s h
  obtain ⟨cm, cm', salt, rfl, rfl⟩ := selF_some Bd D dec pd q a ha
  refine ⟨rfl, ⟨0, 160, 0, D.base.label, _root_.Fmt.zero32,
    _root_.Run.firstBytes (digToBytes pd) (D.stm (digToBytes cm) (digToBytes cm')) salt⟩,
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

/-! ## The leaves: one code of bodies -/

variable {Bd} in
/-- TWO: the page's one code of bodies, and what is asked of it, at the bodies' data B and the
description D. `tag`: the widened condition of the page. `stored`: on a stored symbol it writes what
`pStored` writes at the description's depth and salt, and nothing where that writes nothing. `own`:
what it writes on a body that is no stored symbol are the bits of the label of the call number 164
and of the bytes, by the spelling `B.own`. `ser`: a serialiser of bodies, for the total code behind
the escape. -/
structure LeafD (B : BodyD Bd) where
  /-- the code of bodies -/
  p      : PCode Bd
  /-- its strings begin with one of the two leaves' tags -/
  tag    : ∀ y m, p.put y = some m → 16 ≤ m.length ∧ (m.take 16 = t164 ∨ m.take 16 = t174)
  /-- on stored symbols it is the code of the call number 174 -/
  stored : ∀ y, p.put (B.embE y) = (pStored D.a D.base.plan.salt).put y
  /-- on other bodies it follows the spelling of the chain's own leaves -/
  own    : ∀ b m, B.getE b = none → p.put b = some m → ∃ z, B.own b = some z ∧
    m = bytesToBits (_root_.Fmt.label 164 z.1 z.2.1) ++ bytesToBits z.2.2
  /-- a serialiser of bodies -/
  ser    : Ser Bd

variable {Bd} in
/-- The page's test on body and salt together: at a stored symbol, that the first 256 bits of
the typed salt are the configuration's digest; at every other body, nothing. -/
def leafOKX (B : BodyD Bd) (q : LeafIn (D.L Bd dec)) : Bool :=
  match B.getE q.body with
  | some _ => startIs D.base.cfg q
  | none => true

/-! ## The data -/

variable {Bd D} in
/-- ALL DATA OF THE ENCODING, FROM THE DESCRIPTION, the bodies' data, the code of bodies, 256
bits pd for the place of the parameters' digest, a reader for the statement, and the fact that the
configuration's digest has 32 bytes. -/
def pageXPd (B : BodyD Bd) (Lf : LeafD D B) (K : ℕ) (hcfg : D.base.cfg.size = 32)
    (V : StmInv D) : PageC (D.L Bd dec) K .link where
  cfg := D.base.cfg
  hcfg := hcfg
  chain := chainDX Bd D dec
  chainTag := tag_low 162 D.base.label
  first := firstPX Bd dec pd V
  firstTag := fun q s hq => by
    obtain ⟨r, rfl⟩ := firstPX_hdr Bd dec pd V q s hq
    exact tag16_hdr 0 160 0 D.base.label _root_.Fmt.zero32 rfl r
  firstHd := fun q s hq e he => by
    obtain ⟨r, rfl⟩ := firstPX_hdr Bd dec pd V q s hq
    exact hdr_not_prefix e 0 he 160 0 D.base.label _root_.Fmt.zero32 r
  saltBits := 8 * D.base.plan.salt
  leafP := Lf.p
  leafTag := Lf.tag
  leafOK := leafOKX D dec B
  back := backP (fun _ : Unit => D.L Bd dec) (serAllX D dec Lf.ser) K

variable {Bd D} in
/-- The page holds the stored symbols, spelled by `pStored`, as the bodies `B.embE y`: what
`sameStored_impl` (OnBytes/TypedOracleCompiler/Run/PageXJoin.lean) asks of a page. -/
theorem storedIn_pageXPd (B : BodyD Bd) (Lf : LeafD D B) (K : ℕ) (hcfg : D.base.cfg.size = 32)
    (V : StmInv D) :
    StoredIn (pageXPd dec pd B Lf K hcfg V) (pStored D.a D.base.plan.salt) B.embE where
  put := Lf.stored
  ok := fun y salt => by
    show (match B.getE (B.embE y) with
      | some _ => startIs D.base.cfg (⟨B.embE y, salt⟩ : LeafIn (D.L Bd dec))
      | none => true) = _
    rw [B.get_e]
    rfl

/-! ## The plain maps of famXPd -/

variable {Bd} in
/-- The three plain maps by which `famXPd` spells typed queries. -/
def callsX (B : BodyD Bd) (K : ℕ) : CallsX (D.L Bd dec) K .link :=
  ⟨leafX B D dec, nodeCallC D.base.cfg, firstXPd B D dec (digToBytes pd) K⟩

variable {Bd} in
/-- `famXPd` is the family of its three plain maps. -/
theorem famXPd_eq_famT (B : BodyD Bd) (O : ByteArray → ByteArray) (K : ℕ) :
    famXPd B D dec (digToBytes pd) O K = famT (callsX D dec pd B K) O := by
  funext o
  match o with
  | .leaf => rfl
  | .node => rfl
  | .fb .link =>
      funext q
      exact (famT_fb_self (callsX D dec pd B K) O q).symm
  | .fb .test => rfl
  | .fb .onl => rfl
  | .fbw _ _ => rfl
  | .rleaf => rfl
  | .rnode => rfl
  | .g _ => rfl
  | .ann => rfl
  | .other => rfl

variable {Bd} in
/-- Behind round 0 `firstXPd` is the sibling's map for plain chains, at the spellings `PDX`. -/
theorem firstXPd_succ (B : BodyD Bd) (K : ℕ) (q : FbIn 256 (D.L Bd dec) .link) (j : Fin (K + 1))
    (h : q.round ≠ 0) :
    firstXPd B D dec (digToBytes pd) K q j = fbCall (PDX B D dec) K q j := by
  unfold firstXPd
  split
  · rename_i e _
    exact absurd e h
  · rename_i e _
    exact absurd e h
  · rfl

variable {Bd} in
/-- At round 0 `firstXPd` has a call at the block of the chain value alone. -/
theorem firstXPd_zero (B : BodyD Bd) (K : ℕ) (q : FbIn 256 (D.L Bd dec) .link) (j : Fin (K + 1))
    (h : q.round = 0) (hj : j.val ≠ K) : firstXPd B D dec (digToBytes pd) K q j = none := by
  unfold firstXPd
  split
  · exact if_neg hj
  · rfl
  · exact fbCall_zero (PDX B D dec) q j h hj

variable {Bd} in
/-- A leaf query whose body is no stored symbol is spelled by the sibling's map. -/
theorem leafX_own (B : BodyD Bd) (q : LeafIn (D.L Bd dec)) (h : B.getE q.body = none) :
    leafX B D dec q = leafCall (PDX B D dec) q := by
  unfold leafX
  rw [h]

variable {Bd} in
/-- A leaf query on a stored symbol is spelled as a call with the number 174, if the first 256 bits
of the typed salt are the configuration's digest; else it has no call. -/
theorem leafX_stored (B : BodyD Bd) (y : SgX) (salt : Bits) :
    leafX B D dec (⟨B.embE y, salt⟩ : LeafIn (D.L Bd dec)) =
      if bitsToBytes (salt.take 256) == D.base.cfg then
        some ⟨0, 174, _root_.Fmt.leafPlace 0 y.2.length ((salt.length - 256) / 64), 2 ^ D.a + y.1,
          D.base.cfg, _root_.Fmt.leafBytes y.2 (bitsToBytes (salt.drop 256))⟩
      else none := by
  show (match B.getE (B.embE y) with
    | some s =>
      if bitsToBytes (salt.take 256) == D.base.cfg then
        some (⟨0, 174, _root_.Fmt.leafPlace 0 s.2.length ((salt.length - 256) / 64),
          2 ^ D.a + s.1, D.base.cfg,
          _root_.Fmt.leafBytes s.2 (bitsToBytes (salt.drop 256))⟩ : _root_.Fmt.OQ)
      else none
    | none => leafCall (PDX B D dec) (⟨B.embE y, salt⟩ : LeafIn (D.L Bd dec))) = _
  rw [B.get_e]

variable {Bd D} in
/-- What the page writes on a stored symbol is the string of the call number 174 by which `leafX`
spells a stored table's leaf. -/
theorem storedX_fit (B : BodyD Bd) (Lf : LeafD D B) (K : ℕ) (hcfg : D.base.cfg.size = 32)
    (V : StmInv D) (y : SgX) (salt : Bits) (s : List Bool)
    (h : (pLeafC (pageXPd dec pd B Lf K hcfg V)).put ⟨B.embE y, salt⟩ = some s) :
    ∃ c, leafX B D dec (⟨B.embE y, salt⟩ : LeafIn (D.L Bd dec)) = some c ∧
      s = bytesToBits (strOf c) := by
  have h' : (if (bitsToBytes (salt.take 256) == D.base.cfg) = true then
      (if salt.length = 256 + 8 * D.base.plan.salt then
        ((pStored D.a D.base.plan.salt).put y).map
          (fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)))
      else none)
    else none) = some s :=
    (pLeafC_stored _ (storedIn_pageXPd dec pd B Lf K hcfg V) y salt).symm.trans h
  by_cases hc : (bitsToBytes (salt.take 256) == D.base.cfg) = true
  · rw [if_pos hc] at h'
    by_cases hl : salt.length = 256 + 8 * D.base.plan.salt
    · rw [if_pos hl] at h'
      obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h'
      have e1 : (salt.take 256).length = 8 * 32 := by rw [List.length_take, hl]; omega
      have e2 : (salt.drop 256).length = 8 * D.base.plan.salt := by
        rw [List.length_drop, hl]; omega
      have e3 : (salt.length - 256) / 64 = D.base.plan.salt / 8 := by rw [hl]; omega
      refine ⟨_, (leafX_stored D dec B y salt).trans (if_pos hc), ?_⟩
      show _ = bytesToBits (_root_.Fmt.oStr 0 174 _ _ D.base.cfg _)
      rw [oStr32_bits _ _ _ _ _ (by decide) hcfg, (pStored_put _ _ y m hm).2, e3]
      unfold storedStr _root_.Fmt.leafBytes
      rw [size_bitsToBytes _ _ e2, ← bytes_beq _ _ hc,
        bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, e1⟩), bytesToBits_append (_ ++ _),
        bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨_, e2⟩), List.append_assoc]
    · rw [if_neg hl] at h'
      cases h'
  · rw [if_neg hc] at h'
    cases h'

/-- The tie for one leaf. The sibling's `pLeaf_put` (OnBytes/TypedOracleCompiler/Run/CodingPut.lean) with its
hypothesis on the code asked at the query's own body alone. -/
theorem pLeaf_put1 {I X : Type} {L : BatchProtocolWithLeafBody I X} {tg : Tag} (P : PageD L tg) (n k : ℕ)
    (hn : n = 8 * k) (p : PCode L.Bd) (q : LeafIn L)
    (fit : ∀ m, p.put q.body = some m → ∃ z, P.leaf q.body = some z ∧
      m = bytesToBits (_root_.Fmt.label 164 z.1 z.2.1) ++ bytesToBits z.2.2)
    (s : List Bool) (h : (pLeaf n p).put q = some s) :
    ∃ c, leafCall P q = some c ∧ s = bytesToBits (strOf c) := by
  obtain ⟨y, sa⟩ := q
  have h1 : (if sa.length = 256 + n then
          (p.put y).map (fun m => pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256)))
        else none) = some s := h
  by_cases hl : sa.length = 256 + n
  · rw [if_pos hl] at h1
    cases hm : p.put y with
    | none => rw [hm] at h1; cases h1
    | some m =>
        rw [hm] at h1
        have es : s = pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256)) := (Option.some.inj h1).symm
        have e1 : (sa.take 256).length = 8 * 32 := by rw [List.length_take, hl]; omega
        have e2 : (sa.drop 256).length = 8 * k := by rw [List.length_drop, hl]; omega
        obtain ⟨z, hz, hfit⟩ := fit m hm
        refine ⟨⟨0, 164, z.1, z.2.1, bitsToBytes (sa.take 256),
          z.2.2 ++ bitsToBytes (sa.drop 256)⟩, ?_, ?_⟩
        · show (P.leaf y).map _ = _
          rw [hz]
          rfl
        · show s = bytesToBits
              (_root_.Fmt.oStr 0 164 z.1 z.2.1 (bitsToBytes (sa.take 256))
                (z.2.2 ++ bitsToBytes (sa.drop 256)))
          rw [oStr32_bits _ _ _ _ _ (by decide) (size_bitsToBytes _ 32 e1),
            bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, e1⟩),
            bytesToBits_append, bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨k, e2⟩),
            es, hfit, List.append_assoc]
  · rw [if_neg hl] at h1
    cases h1

variable {Bd D} in
/-- What the partial codes write are the bits of the strings of `famXPd`'s calls, for 0 < K, at
every description whose configuration digest has 32 bytes and whose statement has a reader, all
bodies' data and every code of bodies that meets `LeafD`. One way only: `famXPd` has calls at
queries that the codes do not write. The encoding's strings behind the two escapes are no calls.
Nothing on soundness, no probability, nothing on any hash. -/
theorem pageXPd_fit (B : BodyD Bd) (Lf : LeafD D B) (K : ℕ) (hK : 0 < K)
    (hcfg : D.base.cfg.size = 32) (V : StmInv D) :
    FitX (pageXPd dec pd B Lf K hcfg V) (callsX D dec pd B K) where
  leaf := fun q s h => by
    cases hg : B.getE q.body with
    | some y =>
      obtain ⟨body, salt⟩ := q
      have hb : body = B.embE y := B.e_get _ _ hg
      subst hb
      exact storedX_fit dec pd B Lf K hcfg V y salt s h
    | none =>
      obtain ⟨c, hc, e⟩ := pLeaf_put1 (PDX B D dec) (8 * D.base.plan.salt) D.base.plan.salt rfl
        Lf.p q (fun m hm => Lf.own _ m hg hm) s (pLeafC_put _ q s h).2
      exact ⟨c, (leafX_own D dec B q hg).trans hc, e⟩
  node := fun q s h => node_tie D.base.cfg q s h
  fb := fun q j s h => by
    by_cases h0 : q.round = 0
    · rw [pFb_zero _ q j h0] at h
      by_cases hj : j.val = K
      · rw [if_pos hj] at h
        have hl : j = Fin.last K := Fin.ext hj
        rw [hl]
        exact (firstPX_fit dec pd B V K q s h).2
      · rw [if_neg hj] at h
        cases h
    · rw [pFb_succ _ q j h0] at h
      obtain ⟨c, hc, e⟩ := p162_put (chainDX Bd D dec) (PDX B D dec) K hK (chainDX_fit D dec B)
        (q, j) s h
      exact ⟨c, (firstXPd_succ D dec pd B K q j h0).trans hc, e⟩
  zero := fun q j h0 hj => firstXPd_zero D dec pd B K q j h0 hj

/-! ## Two strings of the encoding, each as one equation -/

variable {Bd D} in
/-- The encoding's string of a stored table's leaf is the bits of the string of the call number
174: tree's place 0 with the numbers of the column's and the salt's words, index 2^a + position,
start the configuration's digest, bytes the column, the fill and the file's salt. Asked: the typed
salt has 256 + 8 (the plan's salt) bits and begins with the configuration's digest, and `storedOK`.
Strings only: no hash is applied. -/
theorem impl_stored_string (B : BodyD Bd) (Lf : LeafD D B) (K : ℕ) (hcfg : D.base.cfg.size = 32)
    (V : StmInv D) (y : ℕ × List UInt64) (salt : Bits)
    (hc : (bitsToBytes (salt.take 256) == D.base.cfg) = true)
    (hl : salt.length = 256 + 8 * D.base.plan.salt) (hy : storedOK D.a D.base.plan.salt y)
    (j : Fin 1) :
    (theImpl (pageXPd dec pd B Lf K hcfg V)).code .leaf
        (⟨B.embE y, salt⟩ : LeafIn (D.L Bd dec)) j =
      bytesToBits (_root_.Fmt.oStr 0 174 (_root_.Fmt.leafPlace 0 y.2.length (D.base.plan.salt / 8))
        (2 ^ D.a + y.1) D.base.cfg (_root_.Fmt.leafBytes y.2 (bitsToBytes (salt.drop 256)))) := by
  have hp : (pLeafC (pageXPd dec pd B Lf K hcfg V)).put ⟨B.embE y, salt⟩ =
      some (pre33 ++ (salt.take 256 ++ (storedStr D.a D.base.plan.salt y ++ salt.drop 256))) := by
    refine (pLeafC_stored _ (storedIn_pageXPd dec pd B Lf K hcfg V) y salt).trans ?_
    show (if (bitsToBytes (salt.take 256) == D.base.cfg) = true then
      (if salt.length = 256 + 8 * D.base.plan.salt then
        ((pStored D.a D.base.plan.salt).put y).map
          (fun m => pre33 ++ (salt.take 256 ++ (m ++ salt.drop 256)))
      else none)
    else none) = _
    rw [if_pos hc, if_pos hl, pStored_some D.a D.base.plan.salt y hy]
    rfl
  have e1 : (salt.take 256).length = 8 * 32 := by rw [List.length_take, hl]; omega
  have e2 : (salt.drop 256).length = 8 * D.base.plan.salt := by rw [List.length_drop, hl]; omega
  rw [theImpl_leaf (pageXPd dec pd B Lf K hcfg V) _ _ hp j,
    oStr32_bits _ _ _ _ _ (by decide) hcfg]
  unfold storedStr _root_.Fmt.leafBytes
  rw [size_bitsToBytes _ _ e2, ← bytes_beq _ _ hc,
    bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, e1⟩), bytesToBits_append (_ ++ _),
    bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨_, e2⟩), List.append_assoc]

variable {Bd D} in
/-- The encoding's string of the first chain query, at the block of the chain value, is the bits
of the string of the call number 160: index the chain's label, no start, bytes pd (in the place of
the parameters' digest), the statement of the two roots, an empty record and the salt. Asked: the
salt is empty or has 256 bits, and the statement has fewer than 2^64 bytes. Strings only: no hash is
applied. -/
theorem impl_first_string (B : BodyD Bd) (Lf : LeafD D B) (K : ℕ) (hcfg : D.base.cfg.size = 32)
    (V : StmInv D) (cm cm' : Dig 256) (salt : Bits) (hs : salt = [] ∨ salt.length = 256)
    (hst : (D.stm (digToBytes cm) (digToBytes cm')).size < 2 ^ 64) :
    (theImpl (pageXPd dec pd B Lf K hcfg V)).code (.fb .link)
        (⟨0, .f1 [cm, cm'] none salt, [], p0X Bd D dec⟩ : FbIn 256 (D.L Bd dec) .link)
        (Fin.last K) =
      bytesToBits (_root_.Fmt.oStr 0 160 0 D.base.label _root_.Fmt.zero32
        (_root_.Run.firstBytes (digToBytes pd)
          (D.stm (digToBytes cm) (digToBytes cm')) salt)) := by
  have hp : (firstPX Bd dec pd V).put
      (⟨0, .f1 [cm, cm'] none salt, [], p0X Bd D dec⟩ : FbIn 256 (D.L Bd dec) .link) =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 D.base.label _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd) (D.stm (digToBytes cm) (digToBytes cm'))
          ByteArray.empty (runOf salt)))) := by
    show (first0X V).put (pd, some (cm, cm'), salt) = _
    unfold first0X
    exact pFirst0_put D.base.label (stmX D) (unstmX V) (unstm_stmX V) (stm_unstmX V) pd
      (some (cm, cm')) salt _ rfl hst hs
  rw [theImpl_fb (pageXPd dec pd B Lf K hcfg V) _ (Fin.last K) _ (by
    rw [pFb_zero _ _ _ rfl, if_pos (Fin.val_last K)]
    exact hp), oStr_bits, oStr_bits, Toy1.bits_first]

/-! ## famXPd against what the encoding reads out of a function on bit strings -/

section
variable {Bd D}
variable (B : BodyD Bd) (Lf : LeafD D B) (K : ℕ) (hK : 0 < K) (hcfg : D.base.cfg.size = 32)
  (V : StmInv D) (g : Fam (rom 256))
include hK

/-- A leaf query, of the chain's own trees or of a stored table, that passes the test: `famXPd`
at the function on byte strings that g induces answers as the encoding reads out of g. A stored
table's leaf passes only if its typed salt begins with the configuration's digest. Of other leaf
queries nothing is said. Nothing on soundness, no probability, nothing on any hash. -/
theorem famXPd_leaf_read (q : LeafIn (D.L Bd dec))
    (h : fitsC (pageXPd dec pd B Lf K hcfg V) .leaf q = true) :
    (famXPd B D dec (digToBytes pd) (oB (g ())) K .leaf q : Dig 256) =
      readBlocks (theImpl (pageXPd dec pd B Lf K hcfg V)) g .leaf q :=
  leafT_agree (pageXPd_fit dec pd B Lf K hK hcfg V) g q h

/-- A vertex's query on two strings of 256 bits: the two answers are one. Of a pair with a
string of another length nothing is said: there `famXPd` still has a call, and the two can differ.
-/
theorem famXPd_node_read (a b : Dig 256) :
    (famXPd B D dec (digToBytes pd) (oB (g ())) K .node
        ((List.ofFn a, List.ofFn b) : Bits × Bits) : Dig 256) =
      readBlocks (theImpl (pageXPd dec pd B Lf K hcfg V)) g .node (List.ofFn a, List.ofFn b) :=
  nodeT_agree (pageXPd_fit dec pd B Lf K hK hcfg V) g _ (by
    show ((pNode D.base.cfg).put (List.ofFn a, List.ofFn b)).isSome = true
    rw [pNode_put256 D.base.cfg _ _ List.length_ofFn List.length_ofFn]
    rfl)

/-- A chain query that passes the test: the chain values are one. At round 0 this is all: of the
K blocks of the verifier's message nothing is said; there `famXPd` answers zeros. -/
theorem famXPd_last_read (q : FbIn 256 (D.L Bd dec) .link)
    (h : fitsC (pageXPd dec pd B Lf K hcfg V) (.fb .link) q = true) :
    (famXPd B D dec (digToBytes pd) (oB (g ())) K (.fb .link) q :
        (Fin K → Dig 256) × Dig 256).2 =
      (readBlocks (theImpl (pageXPd dec pd B Lf K hcfg V)) g (.fb .link) q :
        (Fin K → Dig 256) × Dig 256).2 :=
  fb_agree_last (pageXPd_fit dec pd B Lf K hK hcfg V) g q (fits_last _ q h)

/-- A chain query of a round other than 0 that passes the test: the whole answers are one. Not
at round 0. -/
theorem famXPd_whole_read (q : FbIn 256 (D.L Bd dec) .link)
    (h : fitsC (pageXPd dec pd B Lf K hcfg V) (.fb .link) q = true) (h0 : q.round ≠ 0) :
    famXPd B D dec (digToBytes pd) (oB (g ())) K (.fb .link) q =
      readBlocks (theImpl (pageXPd dec pd B Lf K hcfg V)) g (.fb .link) q :=
  fb_agree_all (pageXPd_fit dec pd B Lf K hK hcfg V) g q (fits_all _ q h h0)

/-- The library's form, for every g: at a query that passes the test, `famXPd` answers as the
encoding reads out of g when the marked blocks are read and zeros stand at the others. Of a query
that does not pass the test nothing is said. That a verifier asks only such queries is not said.
Nothing on soundness, no probability, nothing on any hash. -/
theorem famXPd_readSome (o : TypedOracleCompiler.Compile.Batch.OracleName)
    (q : TypedOracleCompiler.Compile.Batch.domOf 256 (D.L Bd dec) o)
    (h : fitsC (pageXPd dec pd B Lf K hcfg V) o q = true) :
    famXPd B D dec (digToBytes pd) (oB (g ())) K o q =
      readSome (theImpl (pageXPd dec pd B Lf K hcfg V)) (needC (pageXPd dec pd B Lf K hcfg V)) g o
        q := by
  rw [famXPd_eq_famT]
  exact agreeX (pageXPd_fit dec pd B Lf K hK hcfg V) g o q h

end

end TypedOracleCompiler.Run.PQ
