-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/WholeAt.lean: the value of a file's whole chain under fixed oracle functions, and
the values of its three chains.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The verifier of a file walks three chains one after the other; as a batch protocol the file has one
chain over all rounds (`recomputeChainOfProof`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean; `chainF_eq`,
OnBytes/TypedOracleCompiler/Joined/Verifier.lean). A tie to a reader of bytes may give the whole chain's value at
once. This file cuts that value into the three chains' values, under fixed oracle functions g.

Main names:
  `whole_iff`: under g the whole chain has the value z exactly if the three chains have values a,
    b, e, each from where the chain before it ended, and z is these in a row (`glue`).
  `runs_unique`: under g the three values are determined.
  `seal_of_slot`: if the third chain ends with the slot value sl, then g answers the query to g
    that holds the chaining value in which the first chain ends with sl: the premise `sealAt` of
    OnBytes/TypedOracleCompiler/Joined/K/Left.lean.
  `seal_of_whole`: the same from the whole chain's value, if its last phase has the slot value sl.

Limits: nothing says what the values are, nor how g comes from a hash on strings.
No other file of the library uses `seal_of_slot` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.JoinsAt

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}
  {t : Tag} {G : Chains} {D : Desc G Y E} {wq : ProtocolQueryLayout lam K D.batch}
  {embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
  {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam D.batch}

/-- **Under g the whole chain has the value z exactly if the three chains have values, each from
where the chain before it ended, and z is these values in a row.** -/
theorem whole_iff (g : Fam (typedOracleFamily lam K L)) (z : Out lam G.sh) :
    (recomputeChainOfProof t D.batch wq embP xin cms x π).det g = some z ↔
      ∃ a b e, (run₁ t D wq embP xin cms x π).det g = some a ∧
        (run₂ t D wq embP xin cms x π a).det g = some b ∧
        (run₃ t D wq embP xin cms x π a b).det g = some e ∧ z = glue a b e := by
  rw [← chainF_eq]
  constructor
  · intro h
    have hn : (chainF t D wq embP xin cms x π).NoCoin := by
      rw [chainF_eq]
      exact noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _
    obtain ⟨tr, hg, hr⟩ := runsIn_log' g hn h
    obtain ⟨a, b, e, ha, hb, he, rfl⟩ := (runsIn_chainF_iff t D wq embP xin cms x π z).1 hr
    exact ⟨a, b, e, det_of_runsIn hg ha, det_of_runsIn hg hb, det_of_runsIn hg he, rfl⟩
  · rintro ⟨a, b, e, ha, hb, he, rfl⟩
    obtain ⟨t1, a1, r1⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) ha
    obtain ⟨t2, a2, r2⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) hb
    obtain ⟨t3, a3, r3⟩ := runsIn_log' g (noCoin_chainB _ _ _ _ _ _ _ _ _ _ _ _ _) he
    exact det_of_runsIn (a1.append (a2.append a3))
      ((runsIn_chainF_iff t D wq embP xin cms x π _).2
        ⟨a, b, e, r1.mono (by intro y hy; simp [hy]), r2.mono (by intro y hy; simp [hy]),
          r3.mono (by intro y hy; simp [hy]), rfl⟩)

/-- Under g the three chains' values are determined. -/
theorem runs_unique {g : Fam (typedOracleFamily lam K L)} {a a' : Out lam G.c₁} {b b' : Out lam G.c₂}
    {e e' : Out lam G.c₃} (h₁ : (run₁ t D wq embP xin cms x π).det g = some a)
    (h₂ : (run₂ t D wq embP xin cms x π a).det g = some b)
    (h₃ : (run₃ t D wq embP xin cms x π a b).det g = some e)
    (k₁ : (run₁ t D wq embP xin cms x π).det g = some a')
    (k₂ : (run₂ t D wq embP xin cms x π a').det g = some b')
    (k₃ : (run₃ t D wq embP xin cms x π a' b').det g = some e') : a = a' ∧ b = b' ∧ e = e' := by
  obtain rfl : a = a' := Option.some.inj (h₁.symm.trans k₁)
  obtain rfl : b = b' := Option.some.inj (h₂.symm.trans k₂)
  obtain rfl : e = e' := Option.some.inj (h₃.symm.trans k₃)
  exact ⟨rfl, rfl, rfl⟩

/-- If the third chain ends with the slot value sl, g answers the query to g that holds the chaining
value in which the first chain ends with sl. -/
theorem seal_of_slot (hG : G.Laws) {g : Fam (typedOracleFamily lam K L)} {a : Out lam G.c₁} {b : Out lam G.c₂}
    {e : Out lam G.c₃} (h₁ : (run₁ t D wq embP xin cms x π).det g = some a)
    (h₂ : (run₂ t D wq embP xin cms x π a).det g = some b)
    (h₃ : (run₃ t D wq embP xin cms x π a b).det g = some e) {sl : Dig lam}
    (hc : e.2.2.slotVal = some sl) :
    ∀ ρ₁, a.2.2 = .loc ρ₁ → g (OracleName.g t) (qSeal₁ t D embP π ρ₁ (rtJ D wq π a)) = sl := by
  intro ρ₁ h
  obtain ⟨ρ', e1, hg⟩ := slot_at hG h₁ h₂ h₃ hc
  rw [h] at e1
  cases e1
  exact hg

/-- The same from the whole chain's value, if its last phase has the slot value sl. -/
theorem seal_of_whole (hG : G.Laws) {g : Fam (typedOracleFamily lam K L)} {z : Out lam G.sh}
    (hz : (recomputeChainOfProof t D.batch wq embP xin cms x π).det g = some z) {sl : Dig lam}
    (hc : z.2.2.slotVal = some sl) {a : Out lam G.c₁} {b : Out lam G.c₂} {e : Out lam G.c₃}
    (h₁ : (run₁ t D wq embP xin cms x π).det g = some a)
    (h₂ : (run₂ t D wq embP xin cms x π a).det g = some b)
    (h₃ : (run₃ t D wq embP xin cms x π a b).det g = some e) :
    z = glue a b e ∧
      ∀ ρ₁, a.2.2 = .loc ρ₁ → g (OracleName.g t) (qSeal₁ t D embP π ρ₁ (rtJ D wq π a)) = sl := by
  obtain ⟨a', b', e', k₁, k₂, k₃, rfl⟩ := (whole_iff g z).1 hz
  obtain ⟨rfl, rfl, rfl⟩ := runs_unique h₁ h₂ h₃ k₁ k₂ k₃
  exact ⟨rfl, seal_of_slot hG h₁ h₂ h₃ hc⟩

end TypedOracleCompiler.Joined
