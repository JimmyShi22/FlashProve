-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/FullDom.lean: the parser of proof files that fills whole Merkle paths gives the same result at
the format's hash function and at that function rebuilt from the format's oracle, given bounds on
sizes that a test can evaluate.

Why. Some theorems take the parser at one hash function, an evaluation at another. The parser is
`parseFullW` (Run/ParseFull.lean), and its first argument is a hash function. It also takes a
description of a proof's rounds and openings (`S : Fmt.Spec`, Fmt/Rules8.lean), a typing
(`T : Typing Q`, Run/ParseChain.lean) and a file b. From these it makes two of the verifier's
inputs, with a whole path for each opened leaf, or it refuses. The theorems that connect a tree of
oracle queries with a function are about the parser at `Fmt.HO Fmt.oracle`, the format's hash
function rebuilt from the format's oracle. (`Fmt.oracle`: the format's single oracle on all byte
strings, 32 bytes an answer, realised by BLAKE2b; Fmt/Rules23.lean.) An evaluation takes the
format's hash function itself, `Fmt.formatHash`. (All three names are in Fmt/Rules23.lean.) The two hash
functions agree on the hash function's domain (`Fmt.hDom`, in the same file; `Fmt.HO_oracle`,
Fmt/Rules23Laws.lean). The domain: the calls at which `hDom` is true: a number of the format's
table; a tree and an index that the table allows under that number; bytes within the bound on their
length; a start of the fixed length, all zero under a number that takes no start; and, under a
leaf's number, bytes laid out as a leaf (`hDom`, Fmt/Rules23.lean; `leafOK`, Fmt/Rules23.lean). The
calls of the lenient parser are in that domain under four bounds (`smallB`, Run/LaxDom.lean).
`parseFullW` also hashes leaves and vertices of the Merkle trees. Their calls are in the domain
under the bounds on each tree's shape (`smallSh`, Run/OpenDom.lean, five clauses), where the
vertices' start and each leaf's start have 32 bytes. (A start is the fourth argument of a hash
call.)

1. What the file contains. The main definitions and steps, not every one.
   `smallF S b : Bool`: `smallB S b`; the digest of the public files (`S.cfg`) has 32 bytes; at
      every opening of every round, `smallSh` at the plan's salt, and a start that is given has 32
      bytes.
   `fullOpens_dom`, `fullWhole_dom`, `parseFullW_dom`: one lemma for the definition of each name,
      for two hashes in the identity monad that agree on the domain, the first with answers of the
      lengths that the rules give. In the Lean text the two are h and h', the two conditions ha and
      hz, the lengths `Fmt.dlen`. Each lemma says, under the further hypotheses of its statement,
      that the function named gives the same at h' and at h.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems. The statements are `Run.Spec.full_dom` and `Run.Spec.full_HO`; both are proved here.
   Many statements of this library are written twice: a definition in the namespace `Spec` states a
   proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
   `full_dom`: for h, h' with ha and hz as under 1, every protocol Q, typing T, description S and
      file b: smallF S b = true → parseFullW (m := Id) h' S T b = parseFullW (m := Id) h S T b.
   `full_HO`: its doc comment tells it.

4. What is not claimed. It is not claimed that the bounds are needed. `smallSh` is a sufficient
   test, not a rendering of the format page's rule on sizes (see the head of Run/OpenDom.lean).
   `Fmt.Spec.ok` (Fmt/Rules8.lean) is not asked for.

Terms: lean/GLOSSARY.md: format page, description, lenient reader, domain (of the hash).
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.OpenDomProofs
import Run.ParseFull

set_option autoImplicit false

namespace Run
open _root_.Fmt (hDom dlen Plan Spec Shape Src)

/-- The test on one opening's data. -/
def smallO (sb : Nat) (o : Shape × Src) : Bool :=
  smallSh sb o.1 && (match o.2 with
    | .own _ => true
    | .given _ s => s.size == 32)

/-- The test on sizes for the parser that fills whole paths (`parseFullW`): the hypothesis on S and
b in `Spec.full_dom` and `Spec.full_HO`. The head says why the hash function's domain leads to its
clauses. -/
def smallF (S : Spec) (b : ByteArray) : Bool :=
  smallB S b && S.cfg.size == 32 && S.rounds.all fun r => r.opens.all (smallO S.plan.salt)

namespace Spec

def full_dom : Prop :=
  ∀ (h h' : HId), (∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b) →
    (∀ n t i s b, ByteArray.size (h n t i s b) = dlen n) →
    ∀ (Y : Type) (E : Iop.ExtSpec) (Q : Iop.BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
        (T : Typing Q) (b : ByteArray),
      smallF S b = true → parseFullW (m := Id) h' S T b = parseFullW (m := Id) h S T b

/-- States the equation of `full_dom` at h' := `Fmt.HO Fmt.oracle` and h := `Fmt.formatHash`; its only
hypothesis is `smallF S b = true`. -/
def full_HO : Prop :=
  ∀ (Y : Type) (E : Iop.ExtSpec) (Q : Iop.BatchInteractiveOracleProof Y E) (S : _root_.Fmt.Spec)
      (T : Typing Q) (b : ByteArray),
    smallF S b = true →
    parseFullW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S T b =
      parseFullW (m := Id) _root_.Fmt.formatHash S T b

end Spec

/-- The start of an opening's leaves, as `fullOpens` (Run/ParseFull.lean) picks it
(`fullOpens_cons`). -/
def startOf (run : Option ByteArray) (roots : Array ByteArray) : Src → Option ByteArray
  | .own n => if (roots[n]?).isSome then run else none
  | .given _ s => some s

theorem startOf_size (sb : Nat) (run : Option ByteArray) (roots : Array ByteArray) (sh : Shape)
    (src : Src) (hr : ∀ x, run = some x → x.size = 32) (ho : smallO sb (sh, src) = true)
    (st : ByteArray) (e : startOf run roots src = some st) : st.size = 32 := by
  cases src with
  | own n =>
    have e' : (if (roots[n]?).isSome then run else none) = some st := e
    by_cases hn : (roots[n]?).isSome = true
    · rw [if_pos hn] at e'
      exact hr st e'
    · rw [if_neg hn] at e'
      cases e'
  | given r s =>
    have e' : s = st := Option.some.inj e
    subst e'
    have := Bool.and_eq_true_iff.1 ho
    exact beq_iff_eq.1 this.2

theorem fullOpens_cons (h : HId) (cfg : ByteArray) (P : Plan) (b : ByteArray)
    (run : Option ByteArray) (roots : Array ByteArray) (poss : List Nat) (sh : Shape) (src : Src)
    (os : List (Shape × Src)) (i : Nat) :
    fullOpens (m := Id) h cfg P b run roots poss ((sh, src) :: os) i =
      match startOf run roots src with
      | none => none
      | some st =>
        match _root_.Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh st
            (_root_.Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
        | none => none
        | some o =>
          match fullOpens (m := Id) h cfg P b run roots poss os o.next with
          | none => none
          | some (l, k) => some ((sh, _root_.Fmt.listOf (poss.map (· % 2 ^ sh.a)), o) :: l, k) := by
  cases src <;> rfl

section
variable (h h' : HId) (ha : ∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b)
  (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = dlen n)

include ha hz in
theorem fullOpens_dom (cfg : ByteArray) (P : Plan) (b : ByteArray) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (hc : cfg.size = 32)
    (hr : ∀ x, run = some x → x.size = 32) :
    ∀ (os : List (Shape × Src)), os.all (smallO P.salt) = true →
      ∀ i : Nat, fullOpens (m := Id) h' cfg P b run roots poss os i =
        fullOpens (m := Id) h cfg P b run roots poss os i
  | [], _, _ => rfl
  | (sh, src) :: os, ho, i => by
    have ho' := Bool.and_eq_true_iff.1
      (by
        simpa [List.all_cons] using ho : (smallO P.salt (sh, src) && os.all (smallO P.salt)) = true)
    rw [fullOpens_cons, fullOpens_cons]
    cases e : startOf run roots src with
    | none => rfl
    | some st =>
      simp only []
      rw [readOpeningW_dom h h' ha hz cfg P.field P.salt sh st _ b i hc
          (startOf_size P.salt run roots sh src hr ho'.1 st e) (Bool.and_eq_true_iff.1 ho'.1).1]
      cases _root_.Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh st
          (_root_.Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
      | none => rfl
      | some o =>
        simp only []
        rw [fullOpens_dom cfg P b run roots poss hc hr os ho'.2 o.next]

include ha hz in
theorem fullWhole_dom (S : Spec) (b : ByteArray) (hS : smallF S b = true) :
    fullWhole (m := Id) h' S b = fullWhole (m := Id) h S b := by
  have h1 := Bool.and_eq_true_iff.1 hS
  have h2 := Bool.and_eq_true_iff.1 h1.1
  unfold fullWhole
  exact cutWhole_dom2 h h' ha hz _ _ S b h2.1 fun run hr r hrm roots poss j =>
    fullOpens_dom h h' ha hz S.cfg S.plan b run roots poss (beq_iff_eq.1 h2.2) hr r.opens
      (List.all_eq_true.1 h1.2 r hrm) j

include ha hz in
theorem parseFullW_dom {Y : Type} {E : Iop.ExtSpec} {Q : Iop.BatchInteractiveOracleProof Y E} (S : Spec)
    (T : Typing Q) (b : ByteArray) (hS : smallF S b = true) :
    parseFullW (m := Id) h' S T b = parseFullW (m := Id) h S T b := by
  unfold parseFullW
  rw [fullWhole_dom h h' ha hz S b hS]

end

theorem full_dom : Spec.full_dom := fun h h' ha hz _ _ _ S T b hS =>
  parseFullW_dom h h' ha hz S T b hS

theorem full_HO : Spec.full_HO := fun _ _ _ S T b hS =>
  parseFullW_dom (h := _root_.Fmt.formatHash) (h' := _root_.Fmt.HO _root_.Fmt.oracle)
    (fun n t i s b hd => _root_.Fmt.HO_oracle n t i s b hd)
    (fun n t i s b => _root_.Fmt.size_H n t i s b) S T b hS

end Run
