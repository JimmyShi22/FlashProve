-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BaseBehind.lean: what the last part of a proximity test asks of the record in
front (`BaseFront`, Johnson/Prover/Link/BasePart.lean), from what rides through the stages.

The last part reads no old rows: its test on the tree is `lastTree`
(Johnson/Desc/K12/JoinGuarded.lean).

Main names (namespace `Johnson.Prover.Link`).
  `lastTree_of`   `lastTree`, from the seat of the last message and the masking message in one tree
      (`ReadSeat`, Johnson/Prover/Link/ReadSeat.lean) and the tree's number and shape
  `lastPair_of`   `lastPairOk`, from the two codes and the two messages' records
  `lastFits_of`   the claim's form, its lowest variable fixed at 0, fits the code's message
  `baseFront_of`   `BaseFront`, with the claim written out

Limits. Every premise is asked. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BasePart
import Johnson.Prover.Link.ReadSeat
import Johnson.Prover.Link.FixEntries
import Johnson.Prover.Link.FormRow
import Johnson.Desc.K12.Law.SwTies
import OnBytes.Slice.BaseGk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12
open H2K.Sw
open OnBytes.Slice.ProxRun (DenseForm denseForm_fixLow)

/-- `lastTree`, from the seat and the tree's number and shape. -/
theorem lastTree_of (P : BasePar) (st : Statement) (B : TreeBook) (m star a : ℕ) (tr : Tree)
    (R : ReadSeat st B [m] star a tr) (hn : tr.number = P.label)
    (hs : tr.shape = ⟨P.C.a, P.Z.a, #[3, 3], #[3, 3]⟩) : lastTree P B m star = some a := by
  have p0 : B.place[m]? = some (a, 0) := R.place 0 (by simp)
  have p1 : B.place[star]? = some (a, 1) := R.place 1 (by simp)
  have hparts : tr.parts = #[m, star] := R.parts
  unfold lastTree
  simp [p0, p1, R.inBook, hparts, hn, hs, R.once]

/-- `lastPairOk`, from the two codes and the two messages' records. -/
theorem lastPair_of (P : BasePar) (S : Statement) (c : IoppStage) (m star : ℕ)
    (x o : OnBytes.Oracle) (hC : (S.codes.base[c.code]?).map codeOf = some P.C)
    (hZ : (S.codes.mask[c.maskCode]?).map codeOf = some P.Z) (hx : S.oracles[m]? = some x)
    (ho : S.oracles[star]? = some o) (hne : star ≠ m)
    (hxs : x.shape = (switchTargetStage c.code c.maskCode 0 0 1).shape)
    (hxg : x.groups.length ≤ 1) (hos : o.shape = (baseMaskNotice c.code c.maskCode 1 0).shape)
    (ho1 : o.sampled = false) (ho2 : o.spentAsMask = false) :
    lastPairOk P S c m star = true := by
  obtain ⟨k, hk, ek⟩ : ∃ k, S.codes.base[c.code]? = some k ∧ codeOf k = P.C := by
    cases h : S.codes.base[c.code]? with
    | none => rw [h] at hC; cases hC
    | some k => rw [h] at hC; exact ⟨k, rfl, Option.some.inj hC⟩
  obtain ⟨z, hz, ez⟩ : ∃ z, S.codes.mask[c.maskCode]? = some z ∧ codeOf z = P.Z := by
    cases h : S.codes.mask[c.maskCode]? with
    | none => rw [h] at hZ; cases hZ
    | some z => rw [h] at hZ; exact ⟨z, rfl, Option.some.inj hZ⟩
  have k1 : k.logN = P.C.a := congrArg (·.a) ek
  have k2 : k.ell = P.C.l := congrArg (·.l) ek
  have k3 : k.r = P.C.r := congrArg (·.r) ek
  have z1 : z.logN = P.Z.a := congrArg (·.a) ez
  have z2 : z.ell = P.Z.l := congrArg (·.l) ez
  have z3 : z.r = P.Z.r := congrArg (·.r) ez
  unfold lastPairOk
  simp [hk, hz, hx, ho, k1, k2, k3, z1, z2, z3, hne, oneRowEach, hxs, hos, hxg, ho1, ho2,
    switchTargetStage, baseMaskNotice]

/-- The claim's form, its lowest variable fixed at 0, fits. -/
theorem lastFits_of (row : GroupRow) (n : ℕ) (hc : Means.CFits (1 + n) row.c)
    (hp : DenseForm row.c) (h63 : 1 + n ≤ 63) :
    Own.formFits (row.c.fixLow [zeroE]) n = true := by
  have h1 : row.c.fits ([zeroE].length + n) = true := by
    rw [Own.formFits_agrees]
    exact formFits_of_cfits hc hp h63
  exact formFits_of_cfits (cfits_fixLow row.c [zeroE] oneE n h1) (denseForm_fixLow hp _ _)
    (by omega)

/-- **`BaseFront`**, with the claim written out. -/
theorem baseFront_of {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {t : T12} {row : GroupRow}
    {L : GroupLayout} {c : IoppStage} {m star a : ℕ} (hpass : t.pass = .claim row L)
    (hstage : stageAt p j cur = some c) (hk : c.k = 0) (k : OnBytes.Code)
    (hcode : t.st.codes.base[c.code]? = some k) (hkept : row.kept = #[])
    (hfit : Own.formFits (row.c.fixLow [zeroE]) (ceilLog2 k.ell) = true)
    (hL : L.k = 1 ∧ L.h = 0 ∧ L.members = #[m] ∧ L.kept = #[false] ∧ L.mainFirst = #[some 0] ∧
      L.maskFirst = #[some 0])
    (hmask : t.mask = some star) (hpair : lastPairOk (basePar p cur) t.st c m star = true)
    (htree : lastTree (basePar p cur) t.book m star = some a) :
    BaseFront p j cur t row L c
      ⟨dense (row.c.fixLow [zeroE]) (ceilLog2 k.ell), row.d.map (·.triple), row.target.triple⟩
      m star a where
  pass := hpass
  stage := hstage
  claim := by
    unfold claimAt
    simp [hcode, hk, hkept]
  fits := by
    rw [hcode]
    exact hfit
  member := by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hL
    unfold lastMember
    simp [l1, l2, l3, l4, l5, l6]
  mask := hmask
  pair := hpair
  tree := htree

end Johnson.Prover.Link
