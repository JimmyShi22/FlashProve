-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/LinkFirstAns.lean: a partial code of the first chain query of an entry's link in the
typed form that holds both tables' roots AND both tables' answers in its list of digests, as the
string of the format's hash under 160 on the program's own statement of a link's chain.

OnBytes/TypedOracleCompiler/Run/EntryFirst.lean has the like for the typed form with the answers in the field x:
⟨0, f1 [r₀, r₁] (some ((a₀, a₁), dd)) salt, no root, p0⟩. Here the field x is empty, and the answers
stand behind the two roots, each written as a list of digests:
  `qA cm cm' an an' salt` := ⟨0, f1 (cm :: cm' :: (cA an ++ cA an')) none salt, no root, p0⟩.
The string is the same: that file's code of the tuple (`first0E`) is pulled along another selector.

The interface L, the tag t, the fixed plain part with its test, the digest pd and the label are
parameters. So are: the type An of a table's typed answers; cA, how they are written as digests: one
to one, and with one number of digests for all; tr, the answers as the triples of words that the
statement holds: one to one. The ways back from a list of digests, and from a list of triples, to
the typed answers are the inverses that exist by "one to one": no program is given for them.

Main definitions: `backOf`, `pairA`, `qA`, `selLA`, `mkLA`, `lf0`.
Main theorems.
 `lf0_put`         THE LAW: at `qA cm cm' an an' salt`: the bits of `Fmt.oStr` of the hash under 160
                  with the label lab, on `Fmt.firstBytes` of pd's bytes, the two tables' items with
                  `tr an` and `tr an'`, an empty record and the salt as the run value; for fewer
                  than 2 ^ 32 answers each and a salt that is empty or has 256 bits.
 `lf0_link`        the same with the program's `Params.Link.statement` for the two items.
 `lf0_is`          every string that it writes has the form of a call 160 under that label.
 `lf0_only`        whatever it writes, it writes at a query of the form.

Not claimed. A CODE, NO PAGE. That a chain of a compiled verifier asks this query. That any cA and
tr are one to one. That any program hashes these strings. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.EntryFirst
import OnBytes.TypedOracleCompiler.Run.Apart

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.LinkFirstAns
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open TypedOracleCompiler.Run.PutSome TypedOracleCompiler.Run.FirstAnswers TypedOracleCompiler.Run.EntryFirst
open TypedOracleCompiler.Run.Apart
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-! ## The way back along a function -/

open Classical in
/-- Some value that f sends to b, if there is one. -/
def backOf {α β : Type} (f : α → β) (b : β) : Option α :=
  if h : ∃ a, f a = b then some h.choose else none

theorem backOf_some {α β : Type} (f : α → β) (b : β) (a : α) (h : backOf f b = some a) :
    f a = b := by
  unfold backOf at h
  split at h
  · rename_i hx
    rw [← Option.some.inj h]
    exact hx.choose_spec
  · cases h

theorem backOf_apply {α β : Type} (f : α → β) (hf : Function.Injective f) (a : α) :
    backOf f (f a) = some a := by
  have hx : ∃ a', f a' = f a := ⟨a, rfl⟩
  unfold backOf
  rw [dif_pos hx]
  exact congrArg some (hf hx.choose_spec)

/-! ## The query and the tuple -/

variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (t : Tag) (p0 : PlainPart (shapeOf L t) (annOf L t))
  (isP0 : PlainPart (shapeOf L t) (annOf L t) → Bool) (pd : Dig 256)
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3)

/-- Two tables' answers as digests, in a row. -/
def pairA (aa : An × An) : List (Dig 256) := cA aa.1 ++ cA aa.2

/-- It is one to one, if cA is and all its lists have one length. -/
theorem pairA_inj (hinj : Function.Injective cA) (hlen : ∀ a a', (cA a).length = (cA a').length) :
    Function.Injective (pairA cA) := fun x y h =>
  have h2 := List.append_inj h (hlen x.1 y.1)
  Prod.ext (hinj h2.1) (hinj h2.2)

/-- The typed form: both roots, then both tables' answers as digests; no instance in the field x. -/
def qA (cm cm' : Dig 256) (an an' : An) (salt : Bits) : FbIn 256 L t :=
  ⟨0, .f1 (cm :: cm' :: (cA an ++ cA an')) none salt, [], p0⟩

/-- Of a query of the form: (pd, roots and answers as triples, salt). -/
def selLA (q : FbIn 256 L t) : Option (Dig 256 × Option (Dig 256 × YE) × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 (cm :: cm' :: l) none salt, [] =>
      match backOf (pairA cA) l with
      | some aa =>
          if isP0 q.plain = true then some (pd, some (cm, (tr aa.1, (cm', tr aa.2))), salt)
          else none
      | none => none
  | _, _, _ => none

/-- The way back: refused if the first digest is not pd, there is no statement, or a list of triples
is no table's answers. -/
def mkLA (a : Dig 256 × Option (Dig 256 × YE) × List Bool) : Option (FbIn 256 L t) :=
  match a.2.1 with
  | some r =>
      match backOf tr r.2.1, backOf tr r.2.2.2 with
      | some an, some an' =>
          if a.1 = pd then some (qA L t p0 cA r.1 r.2.2.1 an an' a.2.2) else none
      | _, _ => none
  | none => none

variable (hp : ∀ p, isP0 p = true ↔ p = p0) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)

include hp in
/-- What `selLA` reads: the query's fields. -/
theorem selLA_some (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256 × YE) × List Bool)
    (h : selLA L t isP0 pd cA tr q = some a) :
    ∃ cm cm' an an' salt, q = qA L t p0 cA cm cm' an an' salt ∧
      a = (pd, some (cm, (tr an, (cm', tr an'))), salt) := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold selLA at h
  split at h
  · rename_i cm cm' l salt e1 e2 e3
    have e1' : round = 0 := e1
    have e2' : head = .f1 (cm :: cm' :: l) none salt := e2
    have e3' : rt = [] := e3
    split at h
    · rename_i aa b1
      have h' : (if isP0 plain = true then
          some (pd, some (cm, (tr aa.1, (cm', tr aa.2))), salt) else none) = some a := h
      by_cases hq : isP0 plain = true
      · rw [if_pos hq] at h'
        refine ⟨cm, cm', aa.1, aa.2, salt, ?_, (Option.some.inj h').symm⟩
        have el : l = cA aa.1 ++ cA aa.2 := (backOf_some (pairA cA) l aa b1).symm
        rw [e1', e2', e3', (hp plain).1 hq, el]
        rfl
      · rw [if_neg hq] at h'
        cases h'
    · cases h
  · cases h

include hinj hlen in
/-- `selLA` at a query of the form. -/
theorem selLA_qA (h0 : isP0 p0 = true) (cm cm' : Dig 256) (an an' : An) (salt : Bits) :
    selLA L t isP0 pd cA tr (qA L t p0 cA cm cm' an an' salt) =
      some (pd, some (cm, (tr an, (cm', tr an'))), salt) := by
  show (match backOf (pairA cA) (pairA cA (an, an')) with
    | some aa =>
        if isP0 p0 = true then some (pd, some (cm, (tr aa.1, (cm', tr aa.2))), salt) else none
    | none => none) = _
  rw [backOf_apply (pairA cA) (pairA_inj cA hinj hlen) (an, an')]
  exact if_pos h0

include hp htr in
/-- The way back undoes `selLA`. -/
theorem mkLA_selLA (q : FbIn 256 L t) (a : Dig 256 × Option (Dig 256 × YE) × List Bool)
    (h : selLA L t isP0 pd cA tr q = some a) : mkLA L t p0 pd cA tr a = some q := by
  obtain ⟨cm, cm', an, an', salt, rfl, rfl⟩ := selLA_some L t p0 isP0 pd cA tr hp q a h
  show (match backOf tr (tr an), backOf tr (tr an') with
    | some an, some an' =>
        if pd = pd then some (qA L t p0 cA cm cm' an an' salt) else none
    | _, _ => none) = _
  rw [backOf_apply tr htr an, backOf_apply tr htr an']
  exact if_pos rfl

include hp hinj hlen in
/-- `selLA` undoes the way back. -/
theorem selLA_mkLA (a : Dig 256 × Option (Dig 256 × YE) × List Bool) (q : FbIn 256 L t)
    (h : mkLA L t p0 pd cA tr a = some q) : selLA L t isP0 pd cA tr q = some a := by
  obtain ⟨p, x, salt⟩ := a
  cases x with
  | none => cases h
  | some r =>
      obtain ⟨r0, a0, r1, a1⟩ := r
      have h0 : (match backOf tr a0, backOf tr a1 with
        | some an, some an' =>
            if p = pd then some (qA L t p0 cA r0 r1 an an' salt) else none
        | _, _ => none) = some q := h
      cases b0 : backOf tr a0 with
      | none => rw [b0] at h0; cases h0
      | some an =>
        cases b1 : backOf tr a1 with
        | none => rw [b0, b1] at h0; cases h0
        | some an' =>
          rw [b0, b1] at h0
          have h1 : (if p = pd then some (qA L t p0 cA r0 r1 an an' salt) else none) = some q := h0
          by_cases hpd : p = pd
          · rw [if_pos hpd] at h1
            rw [← Option.some.inj h1, selLA_qA L t p0 isP0 pd cA tr hinj hlen ((hp p0).2 rfl),
              backOf_some tr a0 an b0, backOf_some tr a1 an' b1, hpd]
          · rw [if_neg hpd] at h1
            cases h1

variable (lab : ℕ)

/-- **The first chain query of an entry's link, with the answers in its list of digests.** -/
def lf0 : PCode (FbIn 256 L t) :=
  (first0E lab).pull (selLA L t isP0 pd cA tr) (mkLA L t p0 pd cA tr)
    (mkLA_selLA L t p0 isP0 pd cA tr hp htr) (selLA_mkLA L t p0 isP0 pd cA tr hp hinj hlen)

/-- **THE LAW: what it writes is `Fmt.oStr` of the hash under 160**, for fewer than 2 ^ 32 answers
each and a salt that is empty or has 256 bits: under the label lab, with pd in the place of the
parameters' digest, the two tables' items as the statement, an empty record, and the salt as the
run's value. -/
theorem lf0_put (cm cm' : Dig 256) (an an' : An) (salt : List Bool)
    (h₀ : (tr an).length < 2 ^ 32) (h₁ : (tr an').length < 2 ^ 32)
    (hl : salt = [] ∨ salt.length = 256) :
    (lf0 L t p0 isP0 pd cA tr hp hinj hlen htr lab).put (qA L t p0 cA cm cm' an an' salt) =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd)
          (_root_.Fmt.tableItem "the first table" (digToBytes cm) (tr an) ++
            _root_.Fmt.tableItem "the further table" (digToBytes cm') (tr an'))
          ByteArray.empty (runOf salt)))) := by
  show (selLA L t isP0 pd cA tr _).bind _ = _
  rw [selLA_qA L t p0 isP0 pd cA tr hinj hlen ((hp p0).2 rfl)]
  refine pFirst0_put lab stmE unstmE unstm_stmE stm_unstmE pd
    (some (cm, (tr an, (cm', tr an')))) salt _ (if_pos ⟨h₀, h₁⟩) ?_ hl
  unfold _root_.Fmt.tableItem _root_.Fmt.item _root_.Fmt.textS _root_.Fmt.text _root_.Fmt.list
  have n0 : (_root_.Fmt.ascii "the first table").size < 2 ^ 32 := by decide
  have n1 : (_root_.Fmt.ascii "the further table").size < 2 ^ 32 := by decide
  simp only [ByteArray.size_append, size_u64n, size_digToBytes, size_listExt]
  omega

/-- **The same with the program's statement of a link's chain**, at tables whose roots are the two
digests' bytes and whose answers, as triples, are `tr an` and `tr an'`. -/
theorem lf0_link (first further : OnBytes.Params.TableName) (cm cm' : Dig 256) (an an' : An)
    (salt : List Bool) (r₀ : first.root = digToBytes cm) (r₁ : further.root = digToBytes cm')
    (a₀ : tr an = first.answers.map OnBytes.E.triple) (a₁ : tr an' = further.answers.map OnBytes.E.triple)
    (l₀ : first.answers.length < 2 ^ 32) (l₁ : further.answers.length < 2 ^ 32)
    (hl : salt = [] ∨ salt.length = 256) :
    (lf0 L t p0 isP0 pd cA tr hp hinj hlen htr lab).put (qA L t p0 cA cm cm' an an' salt) =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd) (OnBytes.Params.Link.statement first further)
          ByteArray.empty (runOf salt)))) := by
  rw [lf0_put L t p0 isP0 pd cA tr hp hinj hlen htr lab cm cm' an an' salt
    (by rw [a₀, List.length_map]; exact l₀) (by rw [a₁, List.length_map]; exact l₁) hl, a₀, a₁]
  unfold OnBytes.Params.Link.statement
  rw [r₀, r₁]

/-- Every string that it writes has the form of a call 160 under that label. -/
theorem lf0_is (q : FbIn 256 L t) (s : List Bool)
    (h : (lf0 L t p0 isP0 pd cA tr hp hinj hlen htr lab).put q = some s) : Is160 lab s := by
  obtain ⟨a, -, ha⟩ := PCode.pull_put _ _ _ _ _ q s h
  exact is160_of_hdr _ _ (pFirst0_hdr _ _ _ _ _ a s ha)

/-- Whatever it writes, it writes at a query of the form. -/
theorem lf0_only (q : FbIn 256 L t) (s : List Bool)
    (h : (lf0 L t p0 isP0 pd cA tr hp hinj hlen htr lab).put q = some s) :
    ∃ cm cm' an an' salt, q = qA L t p0 cA cm cm' an an' salt := by
  obtain ⟨a, ha, -⟩ := PCode.pull_put _ _ _ _ _ q s h
  obtain ⟨cm, cm', an, an', salt, e, -⟩ := selLA_some L t p0 isP0 pd cA tr hp q a ha
  exact ⟨cm, cm', an, an', salt, e⟩

end TypedOracleCompiler.Run.LinkFirstAns
