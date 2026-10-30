-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/KeyCode.lean

A verification key of a compiled scheme, written as one bit string.

A key (`IVKK`, Compile/Batch/StarK.lean) holds digests and argument strings (the proof strings that
the compiler makes of an interactive protocol). This file shows that, for digests of at least one
bit (0 < lam), there are countably many keys, for every interface `L` (`BatchProtocol`, Iop/Batch.lean: an
encoding of the index with its decoder and three interactive protocols, in the form that the
compiler takes), every record `W : QueryLayout lam L` of how the compiler lays out its hash trees
(Iop/BatchWire.lean) and every coding `m` of the compiler's typed oracles into one hash function
(`OracleCoding`, Rom/Family.lean: an oracle's answer is made of blocks of lam bits, one query to the hash
function each) in which the oracle for leaves has one block. It then defines, for any countable
type, a coding of its elements as bit strings under a tag (a domain separator: a number written in
front of the code; not the compiler's `Tag`, which also occurs in this file). Every element has a
code; under one tag no two elements have the same code; codes under two different tags are
different, also for two different types. `L`, `W`, `m` and `lam` are variables: the file reads no
protocol and no table of parameters.

How keys are counted. The coding `m` is one to one from (oracle, point, block) to bit strings, so an
oracle with at least one block has countably many points (a point is an input to the oracle). The
symbols of an argument string occur in the points of the oracle for leaves, its plain parts (what
the prover sends in the clear) in the points of the oracles for verifier messages. The record `W`
makes the positions of every round finite.

What it does not give. The coding is not written out: the number of an element is picked by choice
from the fact that the type is countable. Nobody can compute it, and it is no byte format.
-/
import Compile.Batch.StarK
import Compile.Batch.ImplOf
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open Iop Rom Compile.Batch
open Compile (Tag SymAny Opening)

namespace VerifiableInference

/-! ## 1. What a coding of typed oracles says of their points -/

section Coding
variable {S : OSpec} {lam : ℕ}

/-- At one oracle and one block, the coding gives different points different strings. -/
theorem code_injective (m : OracleCoding S lam) (o : S.ι) (j : Fin (m.blocks o)) :
    Function.Injective fun q : S.Dom o => m.code o q j := by
  intro q q' e
  have e' : (⟨o, (q, j)⟩ : Σ o, S.Dom o × Fin (m.blocks o)) = ⟨o, (q', j)⟩ := m.inj e
  exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj e').2)

/-- An oracle with at least one block has countably many points. -/
theorem countable_points (m : OracleCoding S lam) (o : S.ι) (h : 0 < m.blocks o) : Countable (S.Dom o) :=
  (code_injective m o ⟨0, h⟩).countable

/-- An oracle with two different answers has at least one block. -/
theorem blocks_pos (m : OracleCoding S lam) (o : S.ι) (a b : S.Rng o) (hab : a ≠ b) : 0 < m.blocks o := by
  rcases Nat.eq_zero_or_pos (m.blocks o) with h0 | h
  · refine absurd ((m.rng o).injective (funext fun j => ?_)) hab
    exact absurd j.isLt (by omega)
  · exact h

end Coding

/-! ## 2. Counting argument strings -/

/-- The plain parts of all rounds are countable if the plain parts of single components are. -/
theorem countable_plains : ∀ (s : Shape) (A : RoundSplits s), Countable (PlainPart s A) → Countable (Plains s)
  | [], _, _ => inferInstanceAs (Countable Unit)
  | r :: s, (a, A), h => by
      haveI : Countable ((a.P0 ⊕ a.Pj) ⊕ PlainPart s A) := h
      haveI : Countable a.P0 := Function.Injective.countable
        (f := fun x : a.P0 => (Sum.inl (Sum.inl x) : (a.P0 ⊕ a.Pj) ⊕ PlainPart s A))
        fun _ _ e => Sum.inl.inj (Sum.inl.inj e)
      haveI : Countable a.Pj := Function.Injective.countable
        (f := fun x : a.Pj => (Sum.inl (Sum.inr x) : (a.P0 ⊕ a.Pj) ⊕ PlainPart s A))
        fun _ _ e => Sum.inr.inj (Sum.inl.inj e)
      have hs : Countable (PlainPart s A) := Function.Injective.countable
        (f := fun x : PlainPart s A => (Sum.inr x : (a.P0 ⊕ a.Pj) ⊕ PlainPart s A))
        fun _ _ e => Sum.inr.inj e
      haveI : Countable (Plains s) := countable_plains s A hs
      haveI : Countable r.Plain := a.plain.injective.countable
      exact inferInstanceAs (Countable (r.Plain × Plains s))

/-- The compiler's record of a shape's hash trees makes the positions of all prover oracles
finite. -/
theorem finite_positions {lam K : ℕ} : ∀ (s : Shape) (A : RoundSplits s), RoundsQueryLayout lam K s A →
    Finite (OPos s)
  | [], _, _ => inferInstanceAs (Finite Empty)
  | r :: s, (_, A), (w, W) => by
      haveI : Finite r.Pos := @Finite.of_fintype _ w.pt.finPos
      haveI : Finite (OPos s) := finite_positions s A W
      exact inferInstanceAs (Finite (r.Pos ⊕ OPos s))

/-- The alphabet at each position is countable if the pairs (position, symbol) are. -/
theorem countable_symbolsAt (s : Shape) (h : Countable (SymAny s)) (p : OPos s) :
    Countable (OSym s p) :=
  haveI : Countable ((p : OPos s) × OSym s p) := h
  Function.Injective.countable (f := fun a : OSym s p => (⟨p, a⟩ : (p : OPos s) × OSym s p))
    fun _ _ e => eq_of_heq (Sigma.mk.inj e).2

/-- Opened positions over a countable alphabet are countable. -/
theorem countable_opening (lam : ℕ) (σ : Type) [Countable σ] : Countable (Opening lam σ) :=
  Function.Injective.countable (f := fun o : Opening lam σ => (o.sym, o.salt, o.path))
    fun ⟨s1, t1, p1⟩ ⟨s2, t2, p2⟩ e => by
      have e' : (s1, t1, p1) = (s2, t2, p2) := e
      cases e'
      rfl

/-- Under the hypotheses below, argument strings are countable: their two fields that are functions
are functions on finitely many positions. -/
theorem countable_argumentString {lam : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (hPos : Finite (OPos Q.loc.shape)) (hSym : Countable (SymAny Q.loc.shape))
    (hPlain : Countable (Plains Q.loc.shape)) (hExtPos : Finite E.Pos)
    (hExtSym : Countable E.Sym) : Countable (OneProtocolProof lam Q) := by
  haveI := hPos
  haveI := hPlain
  haveI := hExtPos
  haveI := hExtSym
  haveI : Countable (Opening lam E.Sym) := countable_opening lam E.Sym
  haveI : ∀ p, Countable (Opening lam (OSym Q.loc.shape p)) := fun p =>
    haveI := countable_symbolsAt Q.loc.shape hSym p
    countable_opening lam _
  exact Function.Injective.countable
    (f := fun π : OneProtocolProof lam Q =>
      (π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path))
    fun ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ e => by
      have e' : (a1, a2, a3, a4, a5, a6, a7, a8) = (b1, b2, b3, b4, b5, b6, b7, b8) := e
      cases e'
      rfl

/-! ## 3. Counting keys -/

section Keys
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- If 0 < lam, the oracle for verifier messages has at least one block. -/
theorem blocks_pos_messages (hlam : 0 < lam) {K : ℕ} (m : OracleCoding (spec lam K L) lam) (t : Tag) :
    0 < m.blocks (OracleName.fb t) :=
  blocks_pos m (OracleName.fb t)
    ((fun _ _ => false, fun _ => false) : (Fin K → Dig lam) × Dig lam)
    ((fun _ _ => false, fun _ => true) : (Fin K → Dig lam) × Dig lam)
    fun e => Bool.false_ne_true (congrFun (congrArg Prod.snd e) ⟨0, hlam⟩)

/-- If 0 < lam, there are countably many verification keys, for every interface that has a record
`W` of its hash trees and a coding of the typed oracles in which the oracle for leaves has one
block. -/
theorem countable_key (hlam : 0 < lam) (W : QueryLayout lam L) (m : OracleCoding (spec lam W.K L) lam)
    (hleaf : m.blocks OracleName.leaf = 1) : Countable (IVKK lam L) := by
  haveI : Countable (LeafIn L) := countable_points m OracleName.leaf (by omega)
  have hSg : Countable L.Symbol := Function.Injective.countable
    (f := fun a : L.Symbol => (⟨some (Sum.inl a), []⟩ : LeafIn L))
    fun _ _ e => Sum.inl.inj (Option.some.inj (LeafIn.mk.inj e).1)
  have hSym : ∀ t : Tag, Countable (SymAny (shapeOf L t)) := fun t =>
    Function.Injective.countable
      (f := fun z : SymAny (shapeOf L t) => (⟨some (Sum.inr ⟨t, z⟩), []⟩ : LeafIn L))
      fun _ _ e => eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Option.some.inj (LeafIn.mk.inj e).1))).2
  have hPlain : ∀ t : Tag, Countable (Plains (shapeOf L t)) := fun t =>
    haveI : Countable (FbIn lam L t) := countable_points m (OracleName.fb t) (blocks_pos_messages hlam m t)
    countable_plains (shapeOf L t) (annOf L t) (Function.Injective.countable
      (f := fun x : PlainPart (shapeOf L t) (annOf L t) =>
        (⟨0, Head.f2 none [], none, x⟩ : FbIn lam L t))
      fun _ _ e => (FbIn.mk.inj e).2.2.2)
  haveI : Countable (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :=
    countable_argumentString (BatchInteractiveOracleProof.ofProto L.offline) (finite_positions _ _ W.T.sh)
      (hSym Tag.test) (hPlain Tag.test) (inferInstanceAs (Finite (Fin L.wordLength))) hSg
  haveI : Countable (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :=
    countable_argumentString (BatchInteractiveOracleProof.ofProto L.link) (finite_positions _ _ W.Lk.sh)
      (hSym Tag.link) (hPlain Tag.link) (inferInstanceAs (Finite (Fin L.wordLength ⊕ Fin L.wordLength))) hSg
  haveI : Countable (IVK lam L) := Function.Injective.countable
    (f := fun k : IVK lam L => (k.cm, k.piT))
    fun ⟨a1, a2⟩ ⟨b1, b2⟩ e => by
      have e' : (a1, a2) = (b1, b2) := e
      cases e'
      rfl
  exact inferInstanceAs (Countable (IVK lam L ×
    List (Dig lam × Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)))))

end Keys

/-! ## 4. Codes under a tag -/

/-- If two strings of ones, each followed by a zero and a rest, are equal, then they have as many
ones, and the rests are equal. -/
theorem ones_append_inj : ∀ (a a' : ℕ) (l l' : List Bool),
    List.replicate a true ++ false :: l = List.replicate a' true ++ false :: l' → a = a' ∧ l = l'
  | 0, 0, l, l', h => by
      have h' : false :: l = false :: l' := h
      exact ⟨rfl, (List.cons.inj h').2⟩
  | 0, a' + 1, l, l', h => by
      have h' : false :: l = true :: (List.replicate a' true ++ false :: l') := h
      exact absurd (List.cons.inj h').1 Bool.false_ne_true
  | a + 1, 0, l, l', h => by
      have h' : true :: (List.replicate a true ++ false :: l) = false :: l' := h
      exact absurd (List.cons.inj h').1.symm Bool.false_ne_true
  | a + 1, a' + 1, l, l', h => by
      have h' : true :: (List.replicate a true ++ false :: l)
          = true :: (List.replicate a' true ++ false :: l') := h
      have r := ones_append_inj a a' l l' (List.cons.inj h').2
      exact ⟨congrArg Nat.succ r.1, r.2⟩

/-- The string for two numbers: a zero, as many ones as the first number, a zero, as many ones as
the second number. -/
def stringOfPair (a b : ℕ) : ZKCP.Str :=
  false :: (List.replicate a true ++ false :: List.replicate b true)

/-- Different pairs of numbers have different strings. -/
theorem stringOfPair_inj {a b a' b' : ℕ} (h : stringOfPair a b = stringOfPair a' b') :
    a = a' ∧ b = b' := by
  have r := ones_append_inj a a' _ _ (List.cons.inj h).2
  have e := congrArg List.length r.2
  rw [List.length_replicate, List.length_replicate] at e
  exact ⟨r.1, e⟩

/-- A numbering of a countable type, picked by choice. -/
def numberOf {α : Type} (h : Countable α) : α → ℕ :=
  (@exists_injective_nat α h).choose

/-- Different elements have different numbers. -/
theorem numberOf_injective {α : Type} (h : Countable α) : Function.Injective (numberOf h) :=
  (@exists_injective_nat α h).choose_spec

/-- The code of an element of a countable type under a tag: the string for the tag and the
element's number. Every element has a code. -/
def codeUnderTag {α : Type} (tag : ℕ) (h : Countable α) (a : α) : Option ZKCP.Str :=
  some (stringOfPair tag (numberOf h a))

/-- Every element has a code. -/
theorem codeUnderTag_ne_none {α : Type} (tag : ℕ) (h : Countable α) (a : α) :
    codeUnderTag tag h a ≠ none :=
  Option.some_ne_none _

/-- Under one tag no two elements have the same code. -/
theorem codeUnderTag_oneToOne {α : Type} (tag : ℕ) (h : Countable α) (a a' : α) (code : ZKCP.Str)
    (e : codeUnderTag tag h a = some code) (e' : codeUnderTag tag h a' = some code) : a = a' :=
  numberOf_injective h (stringOfPair_inj (Option.some.inj (e.trans e'.symm))).2

/-- A string is a code under at most one tag, whatever the two types are. -/
theorem codeUnderTag_tag {α β : Type} (tag tag' : ℕ) (h : Countable α) (h' : Countable β) (a : α)
    (b : β) (code : ZKCP.Str) (e : codeUnderTag tag h a = some code)
    (e' : codeUnderTag tag' h' b = some code) : tag = tag' :=
  (stringOfPair_inj (Option.some.inj (e.trans e'.symm))).1

/-- Every code begins with a zero. -/
theorem codeUnderTag_head {α : Type} (tag : ℕ) (h : Countable α) (a : α) (code : ZKCP.Str)
    (e : codeUnderTag tag h a = some code) : ∃ rest, code = false :: rest :=
  ⟨_, (Option.some.inj e).symm⟩

end VerifiableInference

#print axioms VerifiableInference.countable_key
#print axioms VerifiableInference.codeUnderTag_oneToOne
#print axioms VerifiableInference.codeUnderTag_tag
#print axioms VerifiableInference.code_injective
#print axioms VerifiableInference.countable_points
#print axioms VerifiableInference.blocks_pos
#print axioms VerifiableInference.countable_plains
#print axioms VerifiableInference.finite_positions
#print axioms VerifiableInference.countable_symbolsAt
#print axioms VerifiableInference.countable_opening
#print axioms VerifiableInference.countable_argumentString
#print axioms VerifiableInference.blocks_pos_messages
#print axioms VerifiableInference.ones_append_inj
#print axioms VerifiableInference.stringOfPair_inj
#print axioms VerifiableInference.numberOf_injective
#print axioms VerifiableInference.codeUnderTag_ne_none
#print axioms VerifiableInference.codeUnderTag_head
