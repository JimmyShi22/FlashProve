-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ReadingBlind.lean: every reading of the sibling (`Reading`,
OnBytes/TypedOracleCompiler/Slice/Reading.lean) is blind to entries of a trace that stand neither at the oracle of
leaves nor at the oracle of vertices; so it reads the same off a trace and off the trace lengthened
by what is asked first (`lenB`, OnBytes/Slice/WrapBetween.lean), if that is asked at other oracles.

WHY. `Part.OKAsk` (OnBytes/TypedOracleCompiler/Slice/PartAsk.lean) has a field `blind`: the judge's reading reads
the same off a trace and off the lengthened trace. A reading is a function of what a trace
determines at the leaves under a root (`extLeaf`), and that is found by looking through the entries
of two oracles. What is to be asked first for a stored table with a record are queries of a chain:
entries at another oracle.

Main definition.
 `isTree e`             the entry e stands at the oracle of leaves or at the oracle of vertices of
                        trees over oracles.
Main theorems.
 `extLeaf_tree`         what a trace determines at a leaf under a root hangs on its entries at these
                        two oracles alone (the sibling's `Local.preimage_filter`).
 `filter_lenB`, `extLeaf_lenB`   a trace lengthened by entries at other oracles has the same entries
                        at these two, and determines the same at every leaf.
 `Reading.at_lenB`      A READING IS BLIND TO ENTRIES THAT ARE NEITHER LEAVES NOR VERTICES. The
                        condition is on the logs of what `pre` asks. For every reading, every
                        wiring, every number of blocks: nothing is asked of them.
 `Reading.blind_of_asksOnly`   the same from a property of `pre` as an algorithm (`AsksOnly`): in
                        the form of the field `blind`.

What is not claimed. NO `pre` IS GIVEN HERE (one: `preSeed`, OnBytes/TypedOracleCompiler/Slice/SeedFirstAsk.lean,
which goes through `Reading.at_lenB`; `Reading.blind_of_asksOnly` is used by nothing yet). Of trees
of requests (`extReq`) nothing is said. The other fields of `Part.OKAsk` are not touched. NOTHING ON
SOUNDNESS IS SHOWN. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made
with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Reading
import OnBytes.Slice.WrapBetween

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (lenB AsksOnly asksOnly_log)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## What stands at a leaf hangs on the entries of the leaf and the vertex oracle alone -/

section
variable {K : ℕ}

/-- The entry stands at the oracle of leaves or at the oracle of vertices of trees over oracles. -/
def isTree (e : QA (typedOracleFamily lam K L)) : Bool :=
  match e.1 with
  | OracleName.leaf => true
  | OracleName.node => true
  | _ => false

/-- What a trace determines at a leaf under a root hangs on its entries at these two oracles
alone. -/
theorem extLeaf_tree (tr : Trace (typedOracleFamily lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) :
    extLeaf (tr.filter isTree) d c j = extLeaf tr d c j := by
  unfold extLeaf
  refine Local.preimage_filter (pairM lam K L) _ ?_ ?_ tr _ c
  · rintro ⟨o, q, r⟩ ho
    cases o <;> first | rfl | cases ho
  · rintro ⟨o, q, r⟩ ho
    cases o <;> first | rfl | cases ho

/-- A trace lengthened by entries at other oracles has the same entries at these two. -/
theorem filter_lenB (pre : (o : (typedOracleFamily lam K L).ι) → (typedOracleFamily lam K L).Dom o → TypedOracleComputation lam K L Unit)
    (F : Fam (typedOracleFamily lam K L))
    (h : ∀ o q, ∀ x ∈ ((pre o q).withTrace.det F).2, isTree x = false) :
    ∀ tr : Trace (typedOracleFamily lam K L), (lenB pre F tr).filter isTree = tr.filter isTree
  | [] => rfl
  | e :: tr => by
    show (((pre e.1 e.2.1).withTrace.det F).2 ++ e :: lenB pre F tr).filter isTree = _
    rw [List.filter_append, List.filter_eq_nil_iff.2 fun x hx => by simp [h e.1 e.2.1 x hx],
      List.nil_append, List.filter_cons, List.filter_cons, filter_lenB pre F h tr]

/-- So it determines the same at every leaf. -/
theorem extLeaf_lenB (pre : (o : (typedOracleFamily lam K L).ι) → (typedOracleFamily lam K L).Dom o → TypedOracleComputation lam K L Unit)
    (F : Fam (typedOracleFamily lam K L))
    (h : ∀ o q, ∀ x ∈ ((pre o q).withTrace.det F).2, isTree x = false)
    (tr : Trace (typedOracleFamily lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) :
    extLeaf (lenB pre F tr) d c j = extLeaf tr d c j := by
  rw [← extLeaf_tree (lenB pre F tr), filter_lenB pre F h tr, extLeaf_tree]

end

/-! ## Every reading is blind to what is asked at other oracles -/

section
variable {embE : L.Symbol → L.Bd} (R : Reading L embE) (W : QueryLayout lam L)

/-- A READING IS BLIND TO ENTRIES THAT ARE NEITHER LEAVES NOR VERTICES: it reads the same off a
trace and off the trace lengthened by what `pre` asks, if no entry of what `pre` asks stands at the
oracle of leaves or of vertices. -/
theorem Reading.at_lenB (pre : (o : (typedOracleFamily lam W.K L).ι) → (typedOracleFamily lam W.K L).Dom o → TypedOracleComputation lam W.K L
    Unit)
    (F : Fam (typedOracleFamily lam W.K L))
    (h : ∀ o q, ∀ x ∈ ((pre o q).withTrace.det F).2, isTree x = false) (tr : Tc W)
    (cm : Dig lam) : R.at W (lenB pre F tr) cm = R.at W tr cm :=
  R.at_congr fun j => extLeaf_lenB pre F h tr _ cm j

/-- The same from a property of `pre` as an algorithm: on every path it asks only oracles other
than that of leaves and that of vertices. In the form of the field `blind` of `Part.OKAsk`
(OnBytes/TypedOracleCompiler/Slice/PartAsk.lean). -/
theorem Reading.blind_of_asksOnly
    (pre : (o : (typedOracleFamily lam W.K L).ι) → (typedOracleFamily lam W.K L).Dom o → TypedOracleComputation lam W.K L Unit)
    (h : ∀ o q, AsksOnly (fun o' => o' ≠ OracleName.leaf ∧ o' ≠ OracleName.node) (pre o q)) :
    ∀ F tr cm, R.at W (lenB pre F tr) cm = R.at W tr cm := fun F tr cm =>
  R.at_lenB W pre F (fun o q x hx => by
    obtain ⟨h1, h2⟩ := asksOnly_log _ F (pre o q) (h o q) x hx
    obtain ⟨o', q', r'⟩ := x
    cases o' <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2) tr cm

end

end TypedOracleCompiler.Slice
