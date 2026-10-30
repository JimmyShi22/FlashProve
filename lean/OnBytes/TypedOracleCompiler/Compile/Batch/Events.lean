-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/Events.lean: a second form of Compile/Batch/Events.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Compile/Batch/Events.lean, comments apart: definitions: `rootFields`,
`chainFields`, `evM`, `pairR`, `evF`, `extEnc`. Every other declaration has that file's text.

Where the head below counts what occurs at an entry: here the first `maxRt` roots of a query occur;
in (F1) the first two external roots; in (F4) the request root and the first external root; in (F5)
no external root. So at most `maxRt` + 2 = 4 digests occur at an entry. The third clause of `EF`
speaks of the first lam bits of the input of an earlier query to `rleaf`, and `extReq` finds the
first lam bits of a leaf's input.

The rest of this head is the head of Compile/Batch/Events.lean, to be read with these changes; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/Events.lean: the two hash events, and extraction of committed strings from a trace.

The file has definitions on traces over the typed oracles of Compile/Batch/Oracles.lean, and three
lemmas on `digOf` and `nodeView`. The notions are those of Hash/MerklePure.lean (`Events`,
`HashEvent`, `OraclePair`, `preimage`).

  `EM`, `EF`           The answer of a new Merkle query occurs earlier in the trace; the chaining
                       value of a new query collides with an earlier value (the docstrings have the
                       clauses).

Details.
  * What occurs at an entry (`evM.occ`): the answer of a Merkle query, the halves of a node query's
    input, the root fields of a query to `fb t` or `g t`, an announced digest (the input of a query
    to `ann`).
  * A trace lists a repeated query again; in both events only new entries count.
  * The halves of a node query's input and the request root in a Fiat-Shamir query are bit strings,
    and occur as digests if they have `lam` bits (`digOf`).
  * At most three digests occur at an entry: of the external roots (`cms`) of a Fiat-Shamir query
    only the first two or the first count (`rootFields`).
  * Root fields and chain fields (`chainFields`; at `g t` the field `ρ`) count at every query to
    `fb t` or `g t`, well-formed or not.
  * A node query with a half that does not have `lam` bits counts for `EM`, but extraction does not
    see it (`nodeView`).

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier
import Compile.MerkleList
import Compile.Spec

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol
open scoped ENNReal

variable {I X : Type}

/-- read a string as a digest, if it has lam bits -/
def digOf {lam : ℕ} (v : Bits) : Option (Dig lam) :=
  if h : v.length = lam then some fun i => v.get (i.cast h.symm) else none

theorem digOf_ofFn {lam : ℕ} (c : Dig lam) : digOf (List.ofFn c) = some c := by
  unfold digOf
  rw [dif_pos (List.length_ofFn)]
  congr 1
  funext i
  simp

theorem eq_ofFn_of_digOf {lam : ℕ} {v : Bits} {c : Dig lam} (h : digOf v = some c) :
    v = List.ofFn c := by
  unfold digOf at h
  split at h
  · rename_i hl
    subst hl
    cases h
    exact (List.ofFn_get v).symm
  · cases h

/-- the root fields of a Fiat-Shamir query -/
def rootFields {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {t : Tag} (q : FbIn lam L t) : List (Dig lam) :=
  q.rt.take maxRt ++ match q.head with
    | .f1 cms _ _ => cms.take 2
    | .f2 _ _ => []
    | .f3 _ _ => []
    | .f4 cms rtreq => (digOf rtreq).toList ++ cms.take 1
    | .f5 _ => []

/-- the chain fields of a Fiat-Shamir query -/
def chainFields {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {t : Tag} (q : FbIn lam L t) : List Bits :=
  match q.head with
  | .f1 _ _ _ => []
  | .f2 _ ρ => [ρ]
  | .f3 ρ0 c => [ρ0, c]
  | .f4 _ _ => []
  | .f5 ρ0 => [ρ0]

variable (lam K : ℕ) (L : BatchProtocolWithLeafBody I X)

/-- Occurrence of digests. Merkle queries are those to the four Merkle oracles. -/
def evM : Merkle.Events (QA (typedOracleFamily lam K L)) (Dig lam) where
  answer := fun e => match e with
    | ⟨OracleName.leaf, _, r⟩ => some (show Dig lam from r)
    | ⟨OracleName.node, _, r⟩ => some (show Dig lam from r)
    | ⟨OracleName.rleaf, _, r⟩ => some (show Dig lam from r)
    | ⟨OracleName.rnode, _, r⟩ => some (show Dig lam from r)
    | ⟨OracleName.fb _, _, _⟩ => none
    | ⟨OracleName.g _, _, _⟩ => none
    | ⟨OracleName.ann, _, _⟩ => none
    | ⟨OracleName.other, _, _⟩ => none
    | ⟨OracleName.fbw _ _, _, _⟩ => none
  occ := fun e => match e with
    | ⟨OracleName.leaf, _, r⟩ => [show Dig lam from r]
    | ⟨OracleName.node, q, r⟩ =>
      (show Dig lam from r) ::
        ((digOf (show Bits × Bits from q).1).toList ++ (digOf (show Bits × Bits from q).2).toList)
    | ⟨OracleName.rleaf, _, r⟩ => [show Dig lam from r]
    | ⟨OracleName.rnode, q, r⟩ =>
      (show Dig lam from r) ::
        ((digOf (show Bits × Bits from q).1).toList ++ (digOf (show Bits × Bits from q).2).toList)
    | ⟨OracleName.fb t, q, _⟩ => rootFields (show FbIn lam L t from q)
    | ⟨OracleName.g t, q, _⟩ => (show JoiningRoundQuery lam L t from q).rt.take maxRt
    | ⟨OracleName.ann, q, _⟩ => [show Dig lam from q]
    | ⟨OracleName.other, _, _⟩ => []
    | ⟨OracleName.fbw _ _, _, _⟩ => []
  answer_mem_occ := by
    rintro ⟨o, q, r⟩ c h
    cases o with
    | leaf => cases Option.some.inj h; exact List.mem_cons_self
    | node => cases Option.some.inj h; exact List.mem_cons_self
    | rleaf => cases Option.some.inj h; exact List.mem_cons_self
    | rnode => cases Option.some.inj h; exact List.mem_cons_self
    | fb t => cases h
    | g t => cases h
    | ann => cases h
    | other => cases h
    | fbw t k => cases h

/-- a query to a node oracle, if both halves of its input have lam bits -/
def nodeView {lam : ℕ} (q : Bits × Bits) (r : Dig lam) : Option ((Dig lam × Dig lam) × Dig lam) :=
  match digOf q.1, digOf q.2 with
  | some a, some b => some ((a, b), r)
  | _, _ => none

theorem nodeView_eq_some {lam : ℕ} {q : Bits × Bits} {r : Dig lam} {x : Dig lam × Dig lam}
    {c : Dig lam} (h : nodeView q r = some (x, c)) :
    digOf q.1 = some x.1 ∧ digOf q.2 = some x.2 ∧ r = c := by
  unfold nodeView at h
  cases h1 : digOf (lam := lam) q.1 with
  | none => rw [h1] at h; cases h
  | some a =>
    cases h2 : digOf (lam := lam) q.2 with
    | none => rw [h1, h2] at h; cases h
    | some b =>
      rw [h1, h2] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩

/-- The pair of Merkle oracles of all trees over oracles. -/
def pairM : Merkle.OraclePair (evM lam K L) (LeafIn L) where
  leaf := fun e => match e with
    | ⟨OracleName.leaf, q, r⟩ => some (show LeafIn L from q, show Dig lam from r)
    | _ => none
  node := fun e => match e with
    | ⟨OracleName.node, q, r⟩ => nodeView (show Bits × Bits from q) (show Dig lam from r)
    | _ => none
  answer_of_leaf := by
    rintro ⟨o, q, r⟩ x c h
    cases o <;> first | (cases Option.some.inj h; rfl) | cases h
  answer_of_node := by
    rintro ⟨o, q, r⟩ x c h
    cases o <;> first | exact congrArg some (nodeView_eq_some h).2.2 | cases h
  occurs_left := by
    rintro ⟨o, q, r⟩ x c h
    cases o <;> first
      | exact List.mem_cons_of_mem _
          (List.mem_append_left _ (by rw [(nodeView_eq_some h).1]; exact List.mem_singleton.2 rfl))
      | cases h
  occurs_right := by
    rintro ⟨o, q, r⟩ x c h
    cases o <;> first
      | exact List.mem_cons_of_mem _
          (List.mem_append_right _
            (by rw [(nodeView_eq_some h).2.1]; exact List.mem_singleton.2 rfl))
      | cases h

/-- The pair of Merkle oracles of request trees. The input of a leaf is the slot value and, behind
it, a string of the prover's choice (OneProtocolProof.rsalt). The view of a leaf is the first lam bits of its
input, a string: so what extraction finds at a leaf is the slot value without that string. -/
def pairR : Merkle.OraclePair (evM lam K L) Bits where
  leaf := fun e => match e with
    | ⟨OracleName.rleaf, q, r⟩ => some ((show Bits from q).take lam, show Dig lam from r)
    | _ => none
  node := fun e => match e with
    | ⟨OracleName.rnode, q, r⟩ => nodeView (show Bits × Bits from q) (show Dig lam from r)
    | _ => none
  answer_of_leaf := by
    rintro ⟨o, q, r⟩ x c h
    cases o <;> first | (cases Option.some.inj h; rfl) | cases h
  answer_of_node := by
    rintro ⟨o, q, r⟩ x c h
    cases o <;> first | exact congrArg some (nodeView_eq_some h).2.2 | cases h
  occurs_left := by
    rintro ⟨o, q, r⟩ x c h
    cases o <;> first
      | exact List.mem_cons_of_mem _
          (List.mem_append_left _ (by rw [(nodeView_eq_some h).1]; exact List.mem_singleton.2 rfl))
      | cases h
  occurs_right := by
    rintro ⟨o, q, r⟩ x c h
    cases o <;> first
      | exact List.mem_cons_of_mem _
          (List.mem_append_right _
            (by rw [(nodeView_eq_some h).2.1]; exact List.mem_singleton.2 rfl))
      | cases h

/-- Link values and chain fields, in the same form as occurrence of digests: the "answer" of a query
to a Fiat-Shamir oracle is its link value, the tail of its answer; that of a query to g is the
answer itself. At such a query "occur" its link value and its chain fields; at a query to h'_lf the
first lam bits of its input. -/
def evF : Merkle.Events (QA (typedOracleFamily lam K L)) Bits where
  answer := fun e => match e with
    | ⟨OracleName.fb _, _, r⟩ => some (List.ofFn (show (Fin K → Dig lam) × Dig lam from r).2)
    | ⟨OracleName.g _, _, r⟩ => some (List.ofFn (show Dig lam from r))
    | _ => none
  occ := fun e => match e with
    | ⟨OracleName.fb t, q, r⟩ => List.ofFn (show (Fin K → Dig lam) × Dig lam from r).2 ::
        chainFields (show FbIn lam L t from q)
    | ⟨OracleName.g t, q, r⟩ => [List.ofFn (show Dig lam from r), (show JoiningRoundQuery lam L t from q).ρ]
    | ⟨OracleName.rleaf, q, _⟩ => [(show Bits from q).take lam]
    | _ => []
  answer_mem_occ := by
    rintro ⟨o, q, r⟩ c h
    cases o <;> first | (cases Option.some.inj h; exact List.mem_cons_self) | cases h

variable {lam K L}

/-- E_M: the answer of a new Merkle query occurs at an earlier entry of the trace. -/
def EM (tr : Trace (typedOracleFamily lam K L)) : Prop := (evM lam K L).HashEvent tr

/-- E_F: the chaining value of a new query to a Fiat-Shamir oracle, or the answer of a new query to
g, is such a value or a chain field of an earlier one, or (here:) the first lam bits of the input of
an earlier query to rleaf. -/
def EF (tr : Trace (typedOracleFamily lam K L)) : Prop := (evF lam K L).HashEvent tr

/-! ## Extraction -/

/-- what the trace determines at leaf j of the perfect tree of depth d under the digest c, with the
oracles of trees over oracles -/
def extLeaf (tr : Trace (typedOracleFamily lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) : Option (LeafIn L) :=
  (pairM lam K L).preimage tr (posOf d j) c

/-- the slot value, a bit string, at leaf j of a request tree (here: the first lam bits of the input
of that leaf's query); none if the trace determines none -/
def extReq (tr : Trace (typedOracleFamily lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) : Option Bits :=
  (pairR lam K L).preimage tr (posOf d j) c

abbrev Tc (W : QueryLayout lam L) : Type := Trace (typedOracleFamily lam W.K L)

variable (W : QueryLayout lam L)

/-- the string under a root of an encoded index; the fixed filling where nothing is determined -/
def extEnc (tr : Tc W) (cm : Dig lam) : Fin L.wordLength → L.Symbol :=
  W.B.ext.build fun q => (extLeaf tr W.depth cm q.val).bind fun z => W.prjE z.body

def Announced (tr : Tc W) (cm : Dig lam) : Prop := (⟨OracleName.ann, cm, ()⟩ : QA (typedOracleFamily lam W.K L)) ∈ tr

end TypedOracleCompiler.Compile.Batch
