-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/Bcs.lean: small lemmas, over the second form of the compiler's verifier side
(lean/OnBytes/TypedOracleCompiler/Compile/Batch/).

After lean/Johnson/RecCompile/Bcs.lean, of which it has `instX_of_late_none` and `agreeLk`, that
file's two lemmas on the compiler's types. CmsBcs.lean of this folder calls `agreeLk`;
`instX_of_late_none` is called by no file of this folder. New: `stOf_jointA`, the law on verifier
messages of a plain IOP under any annotation of its rounds as local or shared; `timesShared_one`;
`instR` with three lemmas, which are `instB` and its lemmas (OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean)
for an object with records.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Sound
import Hiop.RecInterface

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

theorem instX_of_late_none {I X : Type} {L : BatchProtocolWithLeafBody I X} (h : L.late = none) (xo : Option X) (i : ℕ) :
    instX L xo i = xo.map L.early := by
  unfold instX
  rw [h]

/-- A determined leaf under one of a link's two roots gives the symbol of the extracted string (the
last step of the link's clause in OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean, as a lemma). -/
theorem agreeLk {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} (hW : W.OKG) {tr : Tc W}
    {cm cm' : Dig lam} (rest : List (Dig lam)) (p : (twoExternalStrings L.wordLength L.Symbol).Pos)
    (a : (twoExternalStrings L.wordLength L.Symbol).Sym) (sl : Bits)
    (h : extLeaf tr W.Lk.ext.depth ((cm :: cm' :: rest).getD (W.Lk.ext.which p) default)
        (W.Lk.ext.leaf p) =
      some ⟨W.embE a, sl⟩) :
    (twoExternalStrings L.wordLength L.Symbol).rd (extEnc W tr cm, extEnc W tr cm') p = a := by
  rw [hW.extDepth.2.1] at h
  cases p with
  | inl p =>
    rw [(hW.extL.1 p).1, (hW.extL.1 p).2] at h
    exact extEnc_apply hW h
  | inr p =>
    rw [(hW.extL.2 p).1, (hW.extL.2 p).2] at h
    exact extEnc_apply hW h

/-- The instance that the chain of a slot of a session with the instance x has taken in with the
query of round i: `instB` (OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean) for an object with records. -/
def instR {I X : Type} (L : HolographicProtocol I X) (x : X) (i : ℕ) : X :=
  match L.late with
  | some n => if n ≤ i then x else L.early x
  | none => L.early x

section InstR
variable {I X : Type} {L : HolographicProtocol I X} {s : Shape} {A : RoundSplits s}
  (h0 : ∀ n, L.late = some n → 0 < n ∧ RoundSplits.LocalTo n s A)
include h0

theorem instR_zero {x : X} : instR L x 0 = L.early x := by
  unfold instR
  cases hl : L.late with
  | none => rfl
  | some n => simp [Nat.pos_iff_ne_zero.1 (h0 n hl).1]

/-- from round j - 1 to round j the instance stays, or j is the round L.late -/
theorem instR_step (x : X) (j : ℕ) :
    instR L x (j - 1) = instR L x j ∨
    (L.late = some j ∧ instR L x (j - 1) = L.early x ∧ instR L x j = x) := by
  unfold instR
  cases hl : L.late with
  | none => exact Or.inl rfl
  | some n =>
    have hn := (h0 n hl).1
    by_cases h1 : n ≤ j - 1
    · exact Or.inl (by simp [h1, show n ≤ j by omega])
    · by_cases h2 : n ≤ j
      · obtain rfl : n = j := by omega
        exact Or.inr ⟨rfl, by simp [h1], by simp⟩
      · exact Or.inl (by simp [h1, h2])

theorem instR_last {x : X} :
    instR L x (s.length - 1) = if L.late.isSome then x else L.early x := by
  unfold instR
  cases hl : L.late with
  | none => rfl
  | some n =>
    have := (h0 n hl).2.lt_length
    simp [show n ≤ s.length - 1 by omega]

end InstR

/-- With one slot, the errors of shared rounds are not multiplied. -/
theorem timesShared_one : ∀ {s : Shape} (A : RoundSplits s) (ε : Err s), Err.timesShared 1 A ε = ε
  | [], _, _ => rfl
  | _ :: _, (a, A), (e, ε) => by
    show ((match a.kind with | .lo => e | .sh => 1 * e), Err.timesShared 1 A ε) = (e, ε)
    rw [timesShared_one A ε]
    cases a.kind with
    | lo => rfl
    | sh => exact congrArg (fun z => (z, ε)) (Nat.one_mul e)

/-- The law on verifier messages for an IOP under any annotation: the errors of shared rounds are
multiplied by the number of slots. -/
theorem stOf_jointA {Y : Type} {E : ExtSpec} (Q : InteractiveOracleProof Y E) (A : RoundSplits Q.shape) (ε : Err Q.shape)
    (N : ℕ) (y : E.Str) (x : Fin N → Option Y) :
    JointLaw N Q.shape A (Err.timesShared N A ε) fun j => (x j).map (stOf Q ε y) :=
  BatchH4.jointLaw_of_verLaw N Q.shape A ε (fun j => (x j).map (stOf Q ε y)) fun j S hS => by
    obtain ⟨xj, -, rfl⟩ := Option.map_eq_some_iff.1 hS
    exact stOf_ver y xj

end TypedOracleCompiler.Compile.Batch
