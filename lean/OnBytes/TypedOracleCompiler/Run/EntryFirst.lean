-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/EntryFirst.lean: the first chain query of an entry's link, which holds TWO outer
roots and both tables' answers, as the string of the format's hash under 160 on the program's own
statement of a link's chain.

An entry file holds one chain, the link between a first table and a further table. Its statement is
the first table's item and then the further table's (OnBytes/Params/Chains.lean: `Link.statement`).
In the typed protocol with instances (OnBytes/TypedOracleCompiler/Slice/EntryX.lean) the first query under the
link's tag holds the two outer roots, and, in the place of an instance, both tables' answers beside
a fixed value that stands for the seeds. OnBytes/TypedOracleCompiler/Run/FirstAnswers.lean has the like for one root
and one table; OnBytes/TypedOracleCompiler/Run/FirstLater.lean reads two items in a row back. The sibling is a
second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `stmE`, `unstmE`, with both laws: of (first root, (first answers, (further root, further
   answers))): the two tables' items under the program's two names; refused from 2 ^ 32 answers on;
   `stmE_link`: these are `Params.Link.statement`'s bytes, at tables whose roots are the two
   digests' bytes, with fewer than 2 ^ 32 answers each;
 - `selE`, `mkE`, with both laws: the query ⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, no root,
   the fixed plain part⟩ against (pd, (r₀, a₀, r₁, a₁), salt);
 - `firstPE`: the code; `firstPE_put`: what it writes at such a query: the bits of `Fmt.oStr` of the
   hash under 160 with the label lab, on `Fmt.firstBytes` of pd's bytes, the two items, an empty
   record and the salt as the run value; for fewer than 2 ^ 32 answers each and a salt that is empty
   or has 256 bits; `firstPE_hdr`: every string that it writes begins with that call's header.

Main definitions: `stmE`, `unstmE`, `firstPE`.
Main theorems: `unstm_stmE`, `stm_unstmE`, `stmE_link`, `firstPE_put`, `firstPE_hdr`.

Not claimed. A CODE, NO PAGE. A query with another number of outer roots, another value than dd
beside the answers, a root of the round or another plain part is not written. That a chain of the
compiled verifier asks this query. pd and lab are arguments. `Fmt.oStr` is total: the format's
domain is not asked. Nothing on soundness. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.FirstLater

set_option autoImplicit false

namespace TypedOracleCompiler.Run.EntryFirst
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open TypedOracleCompiler.Run.PutSome TypedOracleCompiler.Run.FirstAnswers TypedOracleCompiler.Run.FirstLater
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- What the statement holds behind the first root: the first table's answers, the further table's
root and answers. -/
abbrev YE : Type := List T3 × (Dig 256 × List T3)

/-! ## The statement: two stored tables' items -/

/-- The statement's bytes: the first table's item, then the further table's. -/
def stmE : Option (Dig 256 × YE) → Option ByteArray
  | some r =>
      if r.2.1.length < 2 ^ 32 ∧ r.2.2.2.length < 2 ^ 32 then
        some (_root_.Fmt.tableItem "the first table" (digToBytes r.1) r.2.1 ++
          _root_.Fmt.tableItem "the further table" (digToBytes r.2.2.1) r.2.2.2)
      else none
  | none => none

/-- And back: two items are read, each one's value as root and answers; what was read is kept only
if its own spelling is the string. -/
def unstmE (b : ByteArray) : Option (Option (Dig 256 × YE)) :=
  match _root_.Fmt.whole rdTwo b with
  | some v =>
      match _root_.Fmt.whole rdVal v.1.2, _root_.Fmt.whole rdVal v.2.2 with
      | some w, some w' =>
          if stmE (some (bytesToDig w.1, (w.2, (bytesToDig w'.1, w'.2)))) = some b then
            some (some (bytesToDig w.1, (w.2, (bytesToDig w'.1, w'.2))))
          else none
      | _, _ => none
  | none => none

/-- The size of a table's item's value, for fewer than 2 ^ 32 answers. -/
theorem size_val (c : Dig 256) (x : List T3) (h : x.length < 2 ^ 32) :
    (_root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext) (digToBytes c, x)).size <
      2 ^ 64 := by
  unfold _root_.Fmt.pair _root_.Fmt.text _root_.Fmt.list
  simp only [ByteArray.size_append, size_u64n, size_digToBytes, size_listExt]
  omega

/-- The reading undoes the spelling. -/
theorem unstm_stmE (x : Option (Dig 256 × YE)) (b : ByteArray) (h : stmE x = some b) :
    unstmE b = some x := by
  cases x with
  | none => cases h
  | some r =>
    have h0 : (if r.2.1.length < 2 ^ 32 ∧ r.2.2.2.length < 2 ^ 32 then
        some (_root_.Fmt.tableItem "the first table" (digToBytes r.1) r.2.1 ++
          _root_.Fmt.tableItem "the further table" (digToBytes r.2.2.1) r.2.2.2)
        else none) = some b := h
    by_cases hl : r.2.1.length < 2 ^ 32 ∧ r.2.2.2.length < 2 ^ 32
    · rw [if_pos hl] at h0
      have hb := Option.some.inj h0
      have r1 := whole_two "the first table" "the further table"
        (_root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext) (digToBytes r.1, r.2.1))
        (_root_.Fmt.pair _root_.Fmt.text (_root_.Fmt.list _root_.Fmt.ext)
          (digToBytes r.2.2.1, r.2.2.2))
        (by decide) (size_val _ _ hl.1) (by decide) (size_val _ _ hl.2)
      have r2 := _root_.Fmt.whole_of_undoes undoes_val (digToBytes r.1, r.2.1)
        ⟨by rw [size_digToBytes]; omega, (by show r.2.1.length < 2 ^ 64; omega),
          fun _ _ => trivial⟩
      have r3 := _root_.Fmt.whole_of_undoes undoes_val (digToBytes r.2.2.1, r.2.2.2)
        ⟨by rw [size_digToBytes]; omega, (by show r.2.2.2.length < 2 ^ 64; omega),
          fun _ _ => trivial⟩
      have r1' : _root_.Fmt.whole rdTwo b = _ := hb ▸ r1
      unfold unstmE
      rw [r1']
      dsimp only
      rw [r2, r3]
      dsimp only
      rw [TieTree.bytes_dig, TieTree.bytes_dig, if_pos h]
    · rw [if_neg hl] at h0
      cases h0

/-- The spelling undoes the reading. -/
theorem stm_unstmE (b : ByteArray) (x : Option (Dig 256 × YE)) (h : unstmE b = some x) :
    stmE x = some b := by
  unfold unstmE at h
  split at h
  · split at h
    · split at h
      · rename_i he
        rw [← Option.some.inj h]
        exact he
      · cases h
    · cases h
  · cases h

/-- The bytes are those of the program's statement of a link's chain, at tables whose roots are
the two digests' bytes, with fewer than 2 ^ 32 answers each. -/
theorem stmE_link (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256)
    (h₀ : first.root = digToBytes c₀) (h₁ : further.root = digToBytes c₁)
    (l₀ : first.answers.length < 2 ^ 32) (l₁ : further.answers.length < 2 ^ 32) :
    stmE (some (c₀, (first.answers.map OnBytes.E.triple, (c₁, further.answers.map OnBytes.E.triple)))) =
      some (OnBytes.Params.Link.statement first further) := by
  unfold OnBytes.Params.Link.statement
  rw [h₀, h₁]
  exact if_pos ⟨by rw [List.length_map]; exact l₀, by rw [List.length_map]; exact l₁⟩

/-! ## The query and the tuple -/

variable {I Sd : Type} (L : BatchProtocolWithLeafBody I ((List T3 × List T3) × Sd)) (t : Tag)
  (p0 : PlainPart (shapeOf L t) (annOf L t)) (isP0 : PlainPart (shapeOf L t) (annOf L t) → Bool) (dd : Sd)
  (isD : Sd → Bool) (pd : Dig 256)

/-- Of a first query with two outer roots, both tables' answers beside dd, no root of the round and
the fixed plain part: (pd, roots and answers, salt). -/
def selE (q : FbIn 256 L t) : Option (Dig 256 × Option (Dig 256 × YE) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [r₀, r₁] (some x) salt, [] =>
      if isP0 q.plain = true ∧ isD x.2 = true then
        some (pd, some (r₀, (x.1.1, (r₁, x.1.2))), salt) else none
  | _, _, _ => none

/-- The way back: refused if the first digest is not pd, or there is no statement. -/
def mkE (a : Dig 256 × Option (Dig 256 × YE) × List Bool) : Option (FbIn 256 L t) :=
  match a.2.1 with
  | some r =>
      if a.1 = pd then
        some ⟨0, .f1 [r.1, r.2.2.1] (some ((r.2.1, r.2.2.2), dd)) a.2.2, [], p0⟩ else none
  | none => none

variable (hp : ∀ p, isP0 p = true ↔ p = p0) (hd : ∀ s, isD s = true ↔ s = dd)

include hp hd in
/-- What `selE` reads: the query's fields. -/
theorem selE_some (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256 × YE) × List Bool)
    (h : selE L t isP0 isD pd q = some a) :
    ∃ r₀ r₁ a₀ a₁ salt, q = ⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, [], p0⟩ ∧
      a = (pd, some (r₀, (a₀, (r₁, a₁))), salt) := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold selE at h
  split at h
  · rename_i r₀ r₁ x salt e1 e2 e3
    have e1' : round = 0 := e1
    have e2' : head = .f1 [r₀, r₁] (some x) salt := e2
    have e3' : rt = [] := e3
    by_cases hq : isP0 plain = true ∧ isD x.2 = true
    · have h' : (if isP0 plain = true ∧ isD x.2 = true then
          some (pd, some (r₀, (x.1.1, (r₁, x.1.2))), salt) else none) = some a := h
      rw [if_pos hq] at h'
      refine ⟨r₀, r₁, x.1.1, x.1.2, salt, ?_, (Option.some.inj h').symm⟩
      have ex : x = ((x.1.1, x.1.2), dd) := Prod.ext rfl ((hd x.2).1 hq.2)
      rw [e1', e2', e3', (hp plain).1 hq.1, ← ex]
    · have h' : (if isP0 plain = true ∧ isD x.2 = true then
          some (pd, some (r₀, (x.1.1, (r₁, x.1.2))), salt) else none) = some a := h
      rw [if_neg hq] at h'
      cases h'
  · cases h

include hp hd in
/-- The way back undoes `selE`. -/
theorem mkE_selE (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256 × YE) × List Bool)
    (h : selE L t isP0 isD pd q = some a) : mkE L t p0 dd pd a = some q := by
  obtain ⟨r₀, r₁, a₀, a₁, salt, rfl, rfl⟩ := selE_some L t p0 isP0 dd isD pd hp hd q a h
  exact if_pos rfl

include hp hd in
/-- `selE` undoes the way back. -/
theorem selE_mkE (a : Dig 256 × Option (Dig 256 × YE) × List Bool) (q : FbIn 256 L t)
    (h : mkE L t p0 dd pd a = some q) : selE L t isP0 isD pd q = some a := by
  obtain ⟨p, x, salt⟩ := a
  cases x with
  | none => cases h
  | some r =>
      have h0 : (if p = pd then
          some (⟨0, .f1 [r.1, r.2.2.1] (some ((r.2.1, r.2.2.2), dd)) salt, [], p0⟩ : FbIn 256 L t)
          else none) = some q := h
      by_cases hpd : p = pd
      · rw [if_pos hpd] at h0
        rw [← Option.some.inj h0, hpd]
        show (if isP0 p0 = true ∧ isD dd = true then
          some (pd, some (r.1, (r.2.1, (r.2.2.1, r.2.2.2))), salt) else none) = _
        rw [if_pos ⟨(hp p0).2 rfl, (hd dd).2 rfl⟩]
      · rw [if_neg hpd] at h0
        cases h0

variable (lab : ℕ)

/-- The library's code of a first call, on (digest, roots and answers, salt). -/
def first0E : PCode (Dig 256 × Option (Dig 256 × YE) × List Bool) :=
  pFirst0 lab stmE unstmE unstm_stmE stm_unstmE

/-- The first chain query of an entry's link. -/
def firstPE : PCode (FbIn 256 L t) :=
  (first0E lab).pull (selE L t isP0 isD pd) (mkE L t p0 dd pd)
    (mkE_selE L t p0 isP0 dd isD pd hp hd) (selE_mkE L t p0 isP0 dd isD pd hp hd)

/-- What it writes is `Fmt.oStr` of the hash under 160, for fewer than 2 ^ 32 answers each and a
salt that is empty or has 256 bits: under the label lab, with pd in the place of the parameters'
digest, the two tables' items as the statement, an empty record, and the salt as the run's value. -/
theorem firstPE_put (r₀ r₁ : Dig 256) (a₀ a₁ : List T3) (salt : List Bool)
    (h₀ : a₀.length < 2 ^ 32) (h₁ : a₁.length < 2 ^ 32) (hl : salt = [] ∨ salt.length = 256) :
    (firstPE L t p0 isP0 dd isD pd hp hd lab).put
        ⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, [], p0⟩ =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd)
          (_root_.Fmt.tableItem "the first table" (digToBytes r₀) a₀ ++
            _root_.Fmt.tableItem "the further table" (digToBytes r₁) a₁)
          ByteArray.empty (runOf salt)))) := by
  have hs : selE L t isP0 isD pd
      (⟨0, .f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, [], p0⟩ : FbIn 256 L t) =
      some (pd, some (r₀, (a₀, (r₁, a₁))), salt) := if_pos ⟨(hp p0).2 rfl, (hd dd).2 rfl⟩
  show (selE L t isP0 isD pd _).bind _ = _
  rw [hs]
  refine pFirst0_put lab stmE unstmE unstm_stmE stm_unstmE pd (some (r₀, (a₀, (r₁, a₁)))) salt _
    (if_pos ⟨h₀, h₁⟩) ?_ hl
  unfold _root_.Fmt.tableItem _root_.Fmt.item _root_.Fmt.textS _root_.Fmt.text _root_.Fmt.list
  have n0 : (_root_.Fmt.ascii "the first table").size < 2 ^ 32 := by decide
  have n1 : (_root_.Fmt.ascii "the further table").size < 2 ^ 32 := by decide
  simp only [ByteArray.size_append, size_u64n, size_digToBytes, size_listExt]
  omega

/-- Every string that it writes begins with the header of the call number 160 under that label. -/
theorem firstPE_hdr (q : FbIn 256 L t) (s : List Bool)
    (h : (firstPE L t p0 isP0 dd isD pd hp hd lab).put q = some s) :
    ∃ r, s = hdr160 lab ++ r := by
  obtain ⟨a, -, ha⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact pFirst0_hdr _ _ _ _ _ a s ha

end TypedOracleCompiler.Run.EntryFirst
