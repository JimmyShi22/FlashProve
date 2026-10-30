-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/Rooted.lean: a form of Compile/Batch/Rooted.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a form of the verifier's side of
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

What differs in this file from Compile/Batch/Rooted.lean, comments apart: definitions: `own`, `shd`,
`rd0`, `rdJ`, `extSyms`, `m0Of`, `mJOf`, `rooted`, `Lane.flipsAt`. Every other declaration has that
file's text.

Where the head below speaks of the flags `has0`, `hasJ` of the wire record and of the root field of
a query: here the wire has the lists `depth0`, `depthJ`, and a query's root field is a list ([]: no
root). Where it says that a component whose query holds no root has the symbol 0 at all positions:
here this goes tree by tree: the symbol is 0 wherever the tree of the position has no depth or no
root (`extSyms`). In `rooted`, clause (R4): the library asks that a query (F5) name the same
external roots as the shared data before it; here (F5) holds none and nothing is compared. So more
queries are rooted, and the event E'_S is the larger for it. Where the head below quotes `extReq pre
W.depthReq rt j = some c`: here the depth goes by the lane's protocol: `extReq pre (W.dReq ℓ.t) rt j
= some c`, with j < 2 ^ (W.dReq ℓ.t).

The rest of this head is the head of Compile/Batch/Rooted.lean, to be read with these changes; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/Rooted.lean: rooted Fiat-Shamir queries (`rooted`: the cases (R1) to (R5) below), the
slots' transcripts that they continue, and the event E'_S. Definitions and first lemmas.

(Words of this library: lean/GLOSSARY.md.) E'_S is judged at one entry e: e is a new rooted query
whose answer turns the state of a transcript from 0 to 1 (`Lane.step`). E'_S is the state event of
the proof of soundness (`stepS`, Compile/Batch/Sound.lean). (F1) to (F5): the formats of a
Fiat-Shamir query (`Head`, Compile/Batch/Oracles.lean); (R1) to (R5): the clauses of `rooted`. A
query of round i, with the head h, is rooted if its data can be read from h and the earlier entries
pre of the trace (`rooted t pre i h`).

* Every chaining value in a query is looked up among the entries before e, not before the query that
  holds it, and every root is extracted from the trace before e. Outside the hash events (`EM`,
  `EF`) this is the same, and what is defined depends on the input of e and the entries before e
  only, which is all that the bound for one query (Compile/Batch/Facts.lean) uses. (The exception to
  "only": `Lane.step`, `Lane.flipsAt` and `Lane.flips` also read the answer of e.)
* The data of a rooted query of a shared round hold the data of its slots as a function of the slot
  value (`slot c`: the request, the records of the local rounds, the query to g). Live(e) is the set
  of the j with Ext_req(rt_req)[j] = c (the request tree extracted under rt_req has the leaf c at j)
  and `slot c` defined (in `Lane.flipsAt`, case `.shd`: `extReq pre W.depthReq rt j = some c`,
  `slot c = some sd`). In (R5) the data are `slot c` for the field c of the query: that c is the
  slot value of some live j is not asked. This makes E'_S larger; the bound for one query holds for
  the larger event.
* A prover message that is read from the trace is always a.join m_0 m_j. A component for which the
  format of the round has no field has the symbol 0 at all positions and the plain part of the fixed
  message of the round (Compile/Batch/Verifier.lean). A component whose query holds no root has the
  symbol 0 at all positions and the plain part of its query. The analysis reads the root field of
  the query and never the flags of the wire record: a query with a root in a round whose component
  has no tree (or the other way round) is a rooted query like any other. This makes E'_S larger, as
  the points above do.
* A trace lists a repeated query again; only a new entry can cause the event.
* The state function applied at a query is that of the request that its chain holds so far
  (`lastX`). A field xl of a query (F2) counts in whatever round it occurs, and a later one replaces
  an earlier one; the verifier writes one in the round `L.late` only. The bound for one query holds
  because it holds for every request.

Notation: `t`: a `Tag` (Compile/Oracles.lean), the tag of a protocol; `Tc W`
(Compile/Batch/Events.lean): `Trace (typedOracleFamily lam W.K L)`; `cms`: a `List (Dig lam)`: the external
roots; ρ, ρ0: chaining values, as bit strings; `rtreq`: the request root (the fields of `Head`,
Compile/Batch/Oracles.lean); the clauses of `rooted` by format: (R1): `f1`; (R2): `f2`; (R3): `f4`;
(R4): `f5`; (R5): `f3`; a round is called shared (`sh`) or local (`lo`) after its verifier message
(`Kind`, Iop/Batch.lean); m_0, m_j: the shared part of a prover message and a slot's (`RAnn`,
Iop/Batch.lean), its two components; the slot value (`g t`, Compile/Batch/Oracles.lean): the hash of
a slot's chain that becomes its leaf in the request tree; the flags of the wire record: `has0`,
`hasJ` (`WireRB`, Iop/BatchWire.lean): is there a tree over the shared component at all; the same
for a slot's component; slot, joining round, request tree, plain part: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Hash
import Iop.BatchPartial
import Iop.BatchSound

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Part 1. The two components of a prover message -/

section Comp
variable {r : Round} (a : RAnn r) (pt : r.IsPoint)

/-- the plain parts of the two components of the fixed message of the round -/
def d0 : a.P0 := (a.plain r.dPlain).1
def dJ : a.Pj := (a.plain r.dPlain).2

/-- the shared component with the symbols sy (at its own positions) and the plain part α -/
def comp0 (sy : ∀ p, r.Sym p) (α : Option a.P0) : a.M0 :=
  (a.split (pt.ofSyms sy, a.plain.symm (α.getD (d0 a), dJ a))).1
/-- the slot's component with the symbols sy (at its own positions) and the plain part α -/
def compJ (sy : ∀ p, r.Sym p) (α : Option a.Pj) : a.Mj :=
  (a.split (pt.ofSyms sy, a.plain.symm (d0 a, α.getD (dJ a)))).2

theorem join_split (M : r.Msg) : a.join (a.split M).1 (a.split M).2 = M :=
  a.split.symm_apply_apply M

variable {a}

/-- Under `a.Coherent`, what the message made of two components answers: at a position of the slot's
component the slot's symbol, else the shared one. -/
theorem rd_join (h : a.Coherent) (s0 sJ : ∀ p, r.Sym p) (α0 : Option a.P0)
    (αj : Option a.Pj) (p : r.Pos) :
    r.rd (a.join (comp0 a pt s0 α0) (compJ a pt sJ αj)).1 p = if a.own p then sJ p else s0 p := by
  by_cases ho : a.own p = true
  · rw [if_pos ho,
      h.rd_own _ (a.split (pt.ofSyms sJ, a.plain.symm (d0 a, αj.getD (dJ a)))).1 _ p ho]
    show r.rd (a.join (a.split _).1 (a.split _).2).1 p = _
    rw [join_split, pt.rd_ofSyms]
  · rw [if_neg ho,
      h.rd_shared _ _ (a.split (pt.ofSyms s0, a.plain.symm (α0.getD (d0 a), dJ a))).2 p
        (by simpa using ho)]
    show r.rd (a.join (a.split _).1 (a.split _).2).1 p = _
    rw [join_split, pt.rd_ofSyms]

/-- Under `a.Coherent`, the plain part of that message. -/
theorem plain_join (h : a.Coherent) (s0 sJ : ∀ p, r.Sym p) (α0 : Option a.P0) (αj : Option a.Pj) :
    (a.join (comp0 a pt s0 α0) (compJ a pt sJ αj)).2 =
      a.plain.symm (α0.getD (d0 a), αj.getD (dJ a)) := by
  have h0 : a.pl0 (comp0 a pt s0 α0) = α0.getD (d0 a) := by
    have h1 := h.plain_join (a.split (pt.ofSyms s0, a.plain.symm (α0.getD (d0 a), dJ a))).1
      (a.split (pt.ofSyms s0, a.plain.symm (α0.getD (d0 a), dJ a))).2
    rw [join_split, Equiv.apply_symm_apply] at h1
    exact (congrArg Prod.fst h1).symm
  have hJ : a.plj (compJ a pt sJ αj) = αj.getD (dJ a) := by
    have h1 := h.plain_join (a.split (pt.ofSyms sJ, a.plain.symm (d0 a, αj.getD (dJ a)))).1
      (a.split (pt.ofSyms sJ, a.plain.symm (d0 a, αj.getD (dJ a)))).2
    rw [join_split, Equiv.apply_symm_apply] at h1
    exact (congrArg Prod.snd h1).symm
  rw [← h0, ← hJ, ← h.plain_join, Equiv.symm_apply_apply]

end Comp

/-! ## Part 2. Entries, and pred -/

/-- an answer of a Fiat-Shamir oracle: K hash blocks, from which the verifier message is made, and
the chaining value -/
abbrev FsAns (lam K : ℕ) : Type := (Fin K → Dig lam) × Dig lam

/-- the chaining value of an answer, as a bit string -/
def link (a : FsAns lam K) : Bits := List.ofFn a.2

def fbE (t : Tag) (q : FbIn lam L t) (a : FsAns lam K) : QA (typedOracleFamily lam K L) := ⟨OracleName.fb t, q, a⟩
def gE (t : Tag) (q : JoiningRoundQuery lam L t) (c : Dig lam) : QA (typedOracleFamily lam K L) := ⟨OracleName.g t, q, c⟩

theorem fbE_inj {t : Tag} {q q' : FbIn lam L t} {a a' : FsAns lam K} (h : fbE t q a = fbE t q' a') :
    q = q' ∧ a = a' := by
  have h1 := eq_of_heq (Sigma.mk.inj h).2
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

theorem gE_inj {t : Tag} {q q' : JoiningRoundQuery lam L t}
    {c c' : Dig lam} (h : gE (K := K) t q c = gE t q' c') : q = q' ∧ c = c' := by
  have h1 := eq_of_heq (Sigma.mk.inj h).2
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

/-- read an entry as a Fiat-Shamir query of the protocol t -/
def asFb (t : Tag) : QA (typedOracleFamily lam K L) → Option (FbIn lam L t × FsAns lam K)
  | ⟨OracleName.fb t', q, a⟩ =>
    if h : t' = t then some (h ▸ (show FbIn lam L t' from q), (show FsAns lam K from a)) else none
  | _ => none

/-- read an entry as a query to g of the protocol t -/
def asG (t : Tag) : QA (typedOracleFamily lam K L) → Option (JoiningRoundQuery lam L t × Dig lam)
  | ⟨OracleName.g t', q, c⟩ =>
    if h : t' = t then some (h ▸ (show JoiningRoundQuery lam L t' from q), (show Dig lam from c)) else none
  | _ => none

theorem asFb_fbE (t : Tag) (q : FbIn lam L t) (a : FsAns lam K) :
    asFb t (fbE t q a) = some (q, a) := dif_pos rfl
theorem asG_gE (t : Tag) (q : JoiningRoundQuery lam L t) (c : Dig lam) :
    asG (K := K) t (gE t q c) = some (q, c) := dif_pos rfl

theorem eq_fbE_of_asFb {t : Tag} {e : QA (typedOracleFamily lam K L)}
    {p : FbIn lam L t × FsAns lam K} (h : asFb t e = some p) : e = fbE t p.1 p.2 := by
  obtain ⟨o, q', a'⟩ := e
  cases o
  case fb t' =>
    simp only [asFb] at h
    split at h
    · rename_i ht
      subst ht
      cases h; rfl
    · cases h
  all_goals cases h

theorem eq_gE_of_asG {t : Tag} {e : QA (typedOracleFamily lam K L)}
    {p : JoiningRoundQuery lam L t × Dig lam} (h : asG t e = some p) : e = gE t p.1 p.2 := by
  obtain ⟨o, q', a'⟩ := e
  cases o
  case g t' =>
    simp only [asG] at h
    split at h
    · rename_i ht
      subst ht
      cases h; rfl
    · cases h
  all_goals cases h

/-- the first entry that, seen through view, has the property P -/
def firstWith {E β : Type} (view : E → Option β) (P : β → Prop) [DecidablePred P] (pre : List E) :
    Option β :=
  pre.findSome? fun e => (view e).bind fun b => if P b then some b else none

section FirstWith
variable {E β : Type} {view : E → Option β} {P : β → Prop} [DecidablePred P] {pre : List E} {b : β}

theorem firstWith_spec (h : firstWith view P pre = some b) :
    (∃ e ∈ pre, view e = some b) ∧ P b := by
  obtain ⟨e, he, h2⟩ := List.exists_of_findSome?_eq_some h
  cases h3 : view e with
  | none => rw [h3] at h2; cases h2
  | some b' =>
    rw [h3] at h2
    by_cases hc : P b'
    · have h4 : some b' = some b := by rw [← h2]; exact (if_pos hc).symm
      cases h4
      exact ⟨⟨e, he, h3⟩, hc⟩
    · have h4 : (none : Option β) = some b := by rw [← h2]; exact (if_neg hc).symm
      cases h4

theorem firstWith_append (h : firstWith view P pre = some b) (more : List E) :
    firstWith view P (pre ++ more) = some b := by
  unfold firstWith at h ⊢
  rw [List.findSome?_append, h]
  rfl

/-- If only b has the property among what is seen in the list, and b is seen, then b is found. -/
theorem firstWith_eq (hu : ∀ e ∈ pre, ∀ b', view e = some b' → P b' → b' = b)
    (hm : ∃ e ∈ pre, view e = some b) (hP : P b) :
    firstWith view P pre = some b := by
  cases h : firstWith view P pre with
  | none =>
    obtain ⟨e, he, hv⟩ := hm
    have h2 := List.findSome?_eq_none_iff.1 h e he
    rw [hv] at h2
    have h3 : some b = (none : Option β) := by rw [← h2]; exact (if_pos hP).symm
    cases h3
  | some b' =>
    obtain ⟨⟨e, he, hv⟩, hP'⟩ := firstWith_spec h
    rw [hu e he b' hv hP']

end FirstWith

/-- The predecessor at a Fiat-Shamir oracle: the first entry that is a query of round i of the
protocol t whose answer has the chaining value v -/
def predF (t : Tag) (pre : Trace (typedOracleFamily lam K L)) (i : ℕ) (v : Bits) :
    Option (FbIn lam L t × FsAns lam K) :=
  firstWith (asFb t) (fun p => p.1.round = i ∧ link p.2 = v) pre

/-- The predecessor at g: the first entry that is a query to g of round i of the protocol t with the
answer c (as a bit string) -/
def predG (t : Tag) (pre : Trace (typedOracleFamily lam K L)) (i : ℕ) (c : Bits) :
    Option (JoiningRoundQuery lam L t × Dig lam) :=
  firstWith (asG t) (fun p => p.1.round = i ∧ List.ofFn p.2 = c) pre

theorem predF_spec {t : Tag} {pre : Trace (typedOracleFamily lam K L)} {i : ℕ} {v : Bits}
    {p : FbIn lam L t × FsAns lam K} (h : predF t pre i v = some p) :
    fbE t p.1 p.2 ∈ pre ∧ p.1.round = i ∧ link p.2 = v := by
  obtain ⟨⟨e, he, hv⟩, hP⟩ := firstWith_spec h
  exact ⟨eq_fbE_of_asFb hv ▸ he, hP⟩

theorem predG_spec {t : Tag} {pre : Trace (typedOracleFamily lam K L)} {i : ℕ} {c : Bits}
    {p : JoiningRoundQuery lam L t × Dig lam} (h : predG t pre i c = some p) :
    gE t p.1 p.2 ∈ pre ∧ p.1.round = i ∧ List.ofFn p.2 = c := by
  obtain ⟨⟨e, he, hv⟩, hP⟩ := firstWith_spec h
  exact ⟨eq_gE_of_asG hv ▸ he, hP⟩

theorem evF_answer_fbE (t : Tag) (q : FbIn lam L t) (a : FsAns lam K) :
    (evF lam K L).answer (fbE t q a) = some (link a) := rfl
theorem evF_answer_gE (t : Tag) (q : JoiningRoundQuery lam L t) (c : Dig lam) :
    (evF lam K L).answer (gE t q c) = some (List.ofFn c) := rfl

/-- Outside `EF` on tr, a chaining value determines its query in pre ⊆ tr. -/
theorem predF_eq {t : Tag} {tr pre : Trace (typedOracleFamily lam K L)} (hF : ¬ EF tr) (hsub : pre ⊆ tr)
    {q : FbIn lam L t} {a : FsAns lam K} (hm : fbE t q a ∈ pre) :
    predF t pre q.round (link a) = some (q, a) := by
  refine firstWith_eq (fun e he p hv hP => ?_) ⟨_, hm, asFb_fbE t q a⟩ ⟨rfl, rfl⟩
  have h1 : fbE t p.1 p.2 ∈ pre := eq_fbE_of_asFb hv ▸ he
  have h4 := Merkle.Events.eq_of_answer_eq
    hF (hsub h1) (hsub hm) (evF_answer_fbE t p.1 p.2) (hP.2 ▸ evF_answer_fbE t q a)
  obtain ⟨h5, h6⟩ := fbE_inj h4
  exact Prod.ext h5 h6

theorem predG_eq {t : Tag} {tr pre : Trace (typedOracleFamily lam K L)} (hF : ¬ EF tr) (hsub : pre ⊆ tr)
    {q : JoiningRoundQuery lam L t} {c : Dig lam} (hm : gE t q c ∈ pre) :
    predG t pre q.round (List.ofFn c) = some (q, c) := by
  refine firstWith_eq (fun e he p hv hP => ?_) ⟨_, hm, asG_gE t q c⟩ ⟨rfl, rfl⟩
  have h1 : gE t p.1 p.2 ∈ pre := eq_gE_of_asG hv ▸ he
  have h4 := Merkle.Events.eq_of_answer_eq hF (hsub h1) (hsub hm) (evF_answer_gE t p.1 p.2)
    (by rw [hP.2]; exact evF_answer_gE t q c)
  obtain ⟨h5, h6⟩ := gE_inj h4
  exact Prod.ext h5 h6

/-! ## Part 3. Items, records, and the local transcript -/

/-- What the prover message of one round of a slot's transcript is read from: in a local round a
Fiat-Shamir query, which holds the slot's component; in the joining round the query to g, which
holds the slot's component, and the query (F4), which holds the shared one; in a later shared round
the query (F5). -/
inductive Item (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (t : Tag)
  | lo (q : FbIn lam L t)
  | jn (gq : JoiningRoundQuery lam L t) (q : FbIn lam L t)
  | sh (q : FbIn lam L t)

/-- an item with the answer that gives the verifier message of its round -/
abbrev Rec (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (t : Tag) : Type := Item lam L t × FsAns lam K

namespace Item
variable {t : Tag}

def kind : Item lam L t → Kind
  | .lo _ => .lo
  | .jn _ _ => .sh
  | .sh _ => .sh

/-- root field ([]: the query holds no root) and plain field of the slot's component -/
def own : Item lam L t → Option (List (Dig lam) × PlainPart (shapeOf L t) (annOf L t))
  | .lo q => some (q.rt, q.plain)
  | .jn gq _ => some (gq.rt, gq.plain)
  | .sh _ => none

/-- root field and plain field of the shared component -/
def shd : Item lam L t → Option (List (Dig lam) × PlainPart (shapeOf L t) (annOf L t))
  | .lo _ => none
  | .jn _ q => some (q.rt, q.plain)
  | .sh q => some (q.rt, q.plain)

/-- the request that the query of a local round holds beside its chaining value
(Compile/Batch/Oracles.lean: the field xl of (F2)); none: it holds none -/
def late : Item lam L t → Option X
  | .lo q => q.head.late
  | .jn _ _ => none
  | .sh _ => none

end Item

/-- The request that a chain holds so far: x is in the first query; a later query that holds a
request replaces it. l: the records of the earlier rounds; cur: the current item. -/
def lastX {t : Tag} : Option X → List (Rec lam K L t) → Item lam L t → Option X
  | x, [], cur => cur.late.or x
  | x, rc :: l, cur => lastX (rc.1.late.or x) l cur

namespace PlainPart
variable {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}

def head0? : PlainPart (r :: s) (a, A) → Option a.P0
  | .inl (.inl α) => some α
  | _ => none
def headJ? : PlainPart (r :: s) (a, A) → Option a.Pj
  | .inl (.inr α) => some α
  | _ => none
def tail? : PlainPart (r :: s) (a, A) → Option (PlainPart s A)
  | .inr z => some z
  | _ => none

end PlainPart

section Msg
variable {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}

/-- read the fields of the shared component; none if the plain field is no plain part of the shared
component of this round -/
def rd0 (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart (r :: s) (a, A))) :
    Option (List (Dig lam) × PlainPart (shapeOf L t) (annOf L t)) →
    Option (List (Dig lam) × Option a.P0)
  | none => some ([], none)
  | some z => ((prjP z.2).bind PlainPart.head0?).map fun α => (z.1, some α)

def rdJ (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart (r :: s) (a, A))) :
    Option (List (Dig lam) × PlainPart (shapeOf L t) (annOf L t)) →
    Option (List (Dig lam) × Option a.Pj)
  | none => some ([], none)
  | some z => ((prjP z.2).bind PlainPart.headJ?).map fun α => (z.1, some α)

/-- The symbols under the roots (for one component of one round): at each position the symbol of its
leaf in its tree, if the trace determines that leaf and the leaf holds a symbol for this position;
the fixed symbol 0 elsewhere, and wherever the tree of the position has no depth or no root. -/
def extSyms (tr : Trace (typedOracleFamily lam K L)) (w : WireRB lam K r a)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p)) (depth : List ℕ) (rt : List (Dig lam)) :
    (p : r.Pos) → r.Sym p := fun p =>
  match depth[w.tree p]?, rt[w.tree p]? with
  | some d, some c => match extLeaf tr d c (w.place p) with
      | some x => (prj p x.body).getD (w.pt.zero p)
      | none => w.pt.zero p
  | _, _ => w.pt.zero p

/-- the shared component that the trace determines -/
def m0Of (tr : Trace (typedOracleFamily lam K L)) (w : WireRB lam K r a)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p)) (z : List (Dig lam) × Option a.P0) : a.M0 :=
  comp0 a w.pt (extSyms tr w prj w.depth0 z.1) z.2
/-- the slot's component that the trace determines -/
def mJOf (tr : Trace (typedOracleFamily lam K L)) (w : WireRB lam K r a)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p)) (z : List (Dig lam) × Option a.Pj) : a.Mj :=
  compJ a w.pt (extSyms tr w prj w.depthJ z.1) z.2

/-- The prover message of a round, from an item; none if the kind of the item is not that of the
round, or a field is malformed. -/
def msgOf (tr : Trace (typedOracleFamily lam K L)) (w : WireRB lam K r a)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p))
    (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart (r :: s) (a, A))) (it : Item lam L t) :
    Option r.Msg :=
  if it.kind = a.kind then
    (rd0 prjP it.shd).bind fun z0 =>
      (rdJ prjP it.own).map fun zJ => a.join (m0Of tr w prj z0) (mJOf tr w prj zJ)
  else none

end Msg

/-- The slot's transcript with the records l and the current item cur: it ends with the prover
message that cur gives. All roots are extracted from the same trace. -/
def trOf (tr : Trace (typedOracleFamily lam K L)) (t : Tag) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → Body L → Option (OSym s p)) → (PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart s A)) →
    List (Rec lam K L t) → Item lam L t → Option (AtV s)
  | [], _, _, _, _, _, _ => none
  | _ :: _, (_, _), (w, _), prjS, prjP, [], cur =>
    (msgOf tr w (fun p => prjS (.inl p)) prjP cur).map Sum.inl
  | _ :: s, (_, A), (w, ws), prjS, prjP, rc :: rest, cur =>
      (msgOf tr w (fun p => prjS (.inl p)) prjP rc.1).bind fun m =>
        (trOf tr t s A ws (fun p => prjS (.inr p))
            (fun z => (prjP z).bind PlainPart.tail?) rest cur).map fun τ =>
          Sum.inr (m, w.chal rc.2.1, τ)

/-- how hash blocks give the verifier message of the current round -/
def chalAt :
    {s : Shape} → {A : RoundSplits s} → RoundsQueryLayout lam K s A → (τ : AtV s) → (Fin K → Dig lam) → τ.round.Chal
  | _ :: _, (_, _), (w, _), .inl _ => w.chal
  | _ :: _, (_, _), (_, ws), .inr (_, _, τ) => chalAt ws τ

theorem chalAt_unif :
    ∀ {s : Shape} {A : RoundSplits s} {ws : RoundsQueryLayout lam K s A}, RoundsQueryLayout.OKG s A ws →
      ∀ τ : AtV s, (unif (Fin K → Dig lam)).map (chalAt ws τ) = unif τ.round.Chal
  | _ :: _, (_, _), (_, _), h, .inl _ => h.1.chal_unif
  | _ :: _, (_, _), (_, _), h, .inr (_, _, τ) => chalAt_unif h.2 τ

/-! ## Part 4. Rooted queries -/

/-- the data of a slot value at the joining round: the request and the records of the local rounds
of its chain, and its query to g -/
structure SlotD (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (t : Tag) where
  x : Option X
  recs : List (Rec lam K L t)
  gq : JoiningRoundQuery lam L t

/-- The data of a rooted query: of a local round before the shared rounds, of a shared round, of a
local round after them. l: the records of the earlier rounds.
sh: the earlier shared queries, the query (F4) first. -/
inductive Data (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (t : Tag)
  | locV (cms : List (Dig lam)) (x : Option X) (l : List (Rec lam K L t))
  | shd (cms : List (Dig lam)) (rtreq : Bits) (slot : Bits → Option (SlotD lam K L t))
      (sh : List (FbIn lam L t × FsAns lam K))
  | locA (cms : List (Dig lam)) (x : Option X) (l : List (Rec lam K L t))

section Rooted
variable {t : Tag}

/-- (R2): look up the chaining value ρ in round i; the query found must be a rooted query of a local
round -/
def viaTail (rec : Head lam X → Option (Data lam K L t))
    (pre : Trace (typedOracleFamily lam K L)) (i : ℕ) (ρ : Bits) : Option (Data lam K L t) :=
  (predF t pre i ρ).bind fun p => (rec p.1.head).bind fun D => match D with
    | .locV cms x l => some (.locV cms x (l ++ [(.lo p.1, p.2)]))
    | .locA cms x l => some (.locA cms x (l ++ [(.lo p.1, p.2)]))
    | .shd _ _ _ _ => none

/-- the records of a slot up to the end of the shared queries sh -/
def joinRecs (sd : SlotD lam K L t) :
    List (FbIn lam L t × FsAns lam K) → Option (List (Rec lam K L t))
  | [] => none
  | p :: rest => some (sd.recs ++ (.jn sd.gq p.1, p.2) :: rest.map fun z => (.sh z.1, z.2))

/-- records and current item of a slot at the shared query q, after the shared queries sh -/
def slotTr (sd : SlotD lam K L t) (sh : List (FbIn lam L t × FsAns lam K)) (q : FbIn lam L t) :
    List (Rec lam K L t) × Item lam L t :=
  match joinRecs sd sh with
  | none => (sd.recs, .jn sd.gq q)
  | some l => (l, .sh q)

/-- (R3): the data of the slot value c at the joining round i + 1: its query to g, and the chain
that this query continues, which must name the same external roots -/
def slotFn (rec : Head lam X → Option (Data lam K L t)) (pre : Trace (typedOracleFamily lam K L)) (i : ℕ)
    (cms : List (Dig lam)) (c : Bits) : Option (SlotD lam K L t) :=
  (predG t pre (i + 1) c).bind fun g => (viaTail rec pre i g.1.ρ).bind fun D => match D with
    | .locV cms' x l => if cms' = cms then some ⟨x, l, g.1⟩ else none
    | _ => none

/-- Rooted queries: the data of a query of round i (counted from 0) with the given head; none: it is
not rooted. -/
def rooted (t : Tag) (pre : Trace (typedOracleFamily lam K L)) : ℕ → Head lam X → Option (Data lam K L t)
  | 0, .f1 cms x _ => some (.locV cms x [])  -- (R1)
  | 0, _ => none
  | _ + 1, .f1 _ _ _ => none
  | i + 1, .f2 _ ρ => viaTail (rooted t pre i) pre i ρ  -- (R2)
  | i + 1, .f4 cms rtreq => some (.shd cms rtreq (slotFn (rooted t pre i) pre i cms) [])  -- (R3)
  | i + 1, .f5 ρ0 => (predF t pre i ρ0).bind fun p =>  -- (R4)
      (rooted t pre i p.1.head).bind fun D => match D with
      | .shd cms rtreq slot sh => some (.shd cms rtreq slot (sh ++ [p]))
      | _ => none
  | i + 1, .f3 ρ0 c => (predF t pre i ρ0).bind fun p =>  -- (R5)
      (rooted t pre i p.1.head).bind fun D => match D with
      | .shd cms _ slot sh => (slot c).bind fun sd => (joinRecs sd (sh ++ [p])).map fun l =>
          .locA cms sd.x l
      | _ => none

end Rooted

/-! ## Part 5. One protocol as the analysis sees it, and the event E'_S -/

/-- One protocol in the analysis: its tag, shape, annotation and wire records; how leaves and fields
are read back; its errors; and its state function: state tr cms x is meant to be State(Π, x, ·) of
(Snd-B) (`BatchInteractiveOracleProof.SndB`, Iop/Batch.lean) for the strings Π that tr determines under the roots cms
(none: x is no request); the record does not tie the field to it. -/
structure Lane (W : QueryLayout lam L) where
  t : Tag
  s : Shape
  A : RoundSplits s
  ws : RoundsQueryLayout lam W.K s A
  prjS : (p : OPos s) → Body L → Option (OSym s p)
  prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart s A)
  ε : Err s
  state : Tc W → List (Dig lam) → Option X → Option (PTr s → Bool)

variable {W : QueryLayout lam L}

/-- the answer a turns the state of the slot's transcript with the records l and the current item
cur from 0 to 1 -/
def Lane.flips (ℓ : Lane W) (pre : Tc W) (cms : List (Dig lam)) (x : Option X)
    (l : List (Rec lam W.K L ℓ.t)) (cur : Item lam L ℓ.t) (a : FsAns lam W.K) : Prop :=
  ∃ S τ, ℓ.state pre cms x = some S ∧ trOf pre ℓ.t ℓ.s ℓ.A ℓ.ws ℓ.prjS ℓ.prjP l cur = some τ ∧
    S (.atV τ) = false ∧ S (τ.snoc (chalAt ℓ.ws τ a.1)) = true

/-- what E'_S requires of a rooted query q with the data D and the answer a. The state function is
that of the request that the chain holds up to q (lastX): the one in the first query, or the one
that a later query (F2) holds. Here: the depth of the request tree is that of the protocol's tag
(`QueryLayout.dReq`). -/
def Lane.flipsAt (ℓ : Lane W) (pre : Tc W) (q : FbIn lam L ℓ.t) (a : FsAns lam W.K) :
    Data lam W.K L ℓ.t → Prop
  | .locV cms x l => ℓ.flips pre cms (lastX x l (.lo q)) l (.lo q) a
  | .locA cms x l => ℓ.flips pre cms (lastX x l (.lo q)) l (.lo q) a
  | .shd cms rtreq slot sh =>
    ∃ j < 2 ^ (W.dReq ℓ.t), ∃ rt c sd,
      digOf rtreq = some rt ∧
      extReq pre (W.dReq ℓ.t) rt j = some c ∧
      slot c = some sd ∧
      ℓ.flips pre cms (lastX sd.x (slotTr sd sh q).1 (slotTr sd sh q).2)
        (slotTr sd sh q).1 (slotTr sd sh q).2 a

/-- The entry e, after the trace pre, causes E'_S: it is a new, rooted query, and its answer turns
the state of its slot's transcript, or of the transcript of one of its live slots, from 0 to 1. -/
def Lane.step (ℓ : Lane W) (pre : Tc W) (e : QA (typedOracleFamily lam W.K L)) : Prop :=
  e ∉ pre ∧ ∃ (q : FbIn lam L ℓ.t) (a : FsAns lam W.K) (D : Data lam W.K L ℓ.t),
    e = fbE ℓ.t q a ∧ rooted ℓ.t pre q.round q.head = some D ∧ ℓ.flipsAt pre q a D

theorem Lane.step_oracle {ℓ : Lane W} {pre : Tc W} {o : OracleName} {q : domOf lam L o}
    {r : rngOf lam W.K o} (h : ℓ.step pre (⟨o, q, r⟩ : QA (typedOracleFamily lam W.K L))) : o = OracleName.fb ℓ.t := by
  obtain ⟨-, q', a, D, he, -⟩ := h
  exact congrArg Sigma.fst he

end TypedOracleCompiler.Compile.Batch
