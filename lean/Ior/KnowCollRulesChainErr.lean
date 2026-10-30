-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesChainErr.lean: the errors of a chain of links, and the numbers of values of its
verifier messages, as plain lists.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean):
book-keeping for the lists of errors of the whole.
Definitions, statements and proofs. No protocol occurs here.
What the errors count: `Err`, `Doomed`, Iop/Rbr.lean.
These errors are numbers that a link lists (the data field `Link.P.err`): that a link is sound at
the numbers that it lists is no statement of this file; that tie is the clause `know` of `GoodT`
(Ior/KnowCollGood.lean), which `chain_ok` (Ior/KnowCollRulesChain.lean) concludes of the chain as
one link, under `c.Ok` (that condition itself asks soundness of the parts one level down: the tie
carries soundness, it does not found it).

Why: the list of errors of a chain as one link (Ior/KnowCollRulesChain.lean: `Chain.link`) has a
type that depends on the chain's shape, which is put together by recursion. To write out the errors
of a given chain, and to compare each with the number of values of its verifier message, plain
lists of numbers are handier.

Main names:
  `Spec.chainErr_link`: the two lists of the chain as one link are those of its links in a row.
  `Spec.chainErr_append`: two chains in a row.
  `ε.Small`, `Spec.chainErr_small`: `Small` is "pairwise below" for the two plain lists.

Limits: this file says nothing on what the errors mean.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesChain

set_option autoImplicit false

namespace Iop

/-- the errors, in order -/
def Err.toList : {s : Shape} → Err s → List ℕ
  | [], _ => []
  | _ :: _, (e, ε) => e :: Err.toList ε

/-- the numbers of values of the verifier messages, in order -/
def Shape.chalList : Shape → List ℕ
  | [] => []
  | r :: s => Fintype.card r.Chal :: Shape.chalList s

/-- Every error is below the number of values of its round. -/
def Err.Small : {s : Shape} → Err s → Prop
  | [], _ => True
  | r :: _, (e, ε) => e < Fintype.card r.Chal ∧ Err.Small ε

theorem Err.toList_app :
    ∀ {s t : Shape} (ε : Err s) (ε' : Err t), (Err.app ε ε').toList = ε.toList ++ ε'.toList
  | [], _, _, _ => rfl
  | _ :: _, _, (e, ε), ε' => congrArg (List.cons e) (Err.toList_app ε ε')

theorem Shape.chalList_append :
    ∀ (s t : Shape), Shape.chalList (s ++ t) = Shape.chalList s ++ Shape.chalList t
  | [], _ => rfl
  | r :: s, t => congrArg (List.cons (Fintype.card r.Chal)) (Shape.chalList_append s t)

namespace IOR
variable {K : Type}

def Link.errs {A B : Joint K} (l : Link K A B) : List ℕ := l.P.err.toList
def Link.chs {A B : Joint K} (l : Link K A B) : List ℕ := l.R.shape.chalList

def Chain.errs : {A B : Joint K} → Chain K A B → List ℕ
  | _, _, .one l => l.errs
  | _, _, .snoc c l => c.errs ++ l.errs

def Chain.chs : {A B : Joint K} → Chain K A B → List ℕ
  | _, _, .one l => l.chs
  | _, _, .snoc c l => c.chs ++ l.chs

theorem Chain.errs_one {A B : Joint K} (l : Link K A B) : (Chain.one l).errs = l.errs := by
  rw [Chain.errs]
theorem Chain.errs_snoc {A B C : Joint K} (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).errs = c.errs ++ l.errs := by rw [Chain.errs]
theorem Chain.chs_one {A B : Joint K} (l : Link K A B) : (Chain.one l).chs = l.chs := by
  rw [Chain.chs]
theorem Chain.chs_snoc {A B C : Joint K} (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).chs = c.chs ++ l.chs := by rw [Chain.chs]

end IOR

namespace Spec
open IOR

def chainErr_link : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W),
    (c.link d).errs = c.errs ∧ (c.link d).chs = c.chs

def chainErr_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C),
    (c.append c').errs = c.errs ++ c'.errs ∧ (c.append c').chs = c.chs ++ c'.chs

def chainErr_small : Prop :=
  ∀ (s : Shape) (ε : Err s), ε.Small ↔ List.Forall₂ (· < ·) ε.toList s.chalList

end Spec

open IOR

theorem chainErr_link : Spec.chainErr_link := by
  intro K A B c d
  induction c with
  | one l =>
    rw [Chain.link]
    exact ⟨by rw [Chain.errs], by rw [Chain.chs]⟩
  | snoc c l ih =>
    rw [Chain.link, Chain.errs, Chain.chs, ← ih.1, ← ih.2]
    exact ⟨Err.toList_app _ _, Shape.chalList_append _ _⟩

theorem chainErr_append : Spec.chainErr_append := by
  intro K A B C c c'
  induction c' with
  | one l =>
    rw [Chain.append, Chain.errs, Chain.chs]
    exact ⟨by rw [Chain.errs], by rw [Chain.chs]⟩
  | snoc c' l ih =>
    rw [Chain.append, Chain.errs, Chain.chs, ih.1, ih.2]
    exact ⟨by rw [Chain.errs, List.append_assoc], by rw [Chain.chs, List.append_assoc]⟩

theorem chainErr_small : Spec.chainErr_small := by
  intro s
  induction s with
  | nil => exact fun _ => ⟨fun _ => List.Forall₂.nil, fun _ => trivial⟩
  | cons r s ih =>
    rintro ⟨e, ε⟩
    exact ⟨fun h => List.Forall₂.cons h.1 ((ih ε).1 h.2), fun h => by
      cases h with
      | cons h1 h2 => exact ⟨h1, (ih ε).2 h2⟩⟩

end Iop
