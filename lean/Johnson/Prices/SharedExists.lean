-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/SharedExists.lean: there are sizes of a test on the table that meet `AtRecord` and
the three further equations of Johnson/Prices/Record.lean, with a list of codes, at which
`sharedPlan` returns a plan; and that plan holds, meets the side conditions of the library's law on
a round, has the target 128 and no round with more than 28 bits of work (`Passes 28`).

The laws of Johnson/Prices/Zeta.lean, Lin.lean, Sends.lean, Dear.lean, DearBare.lean, Record.lean
and ProxRecord.lean speak of every plan that `sharedPlan` returns. This file shows that they are not
empty at the typed full-size sizes. `linSizedWith` is the text of `linSized`
(OnBytes/Params/DeriveLin.lean) with the results of its four searches (`linTurns`, and `solveStages`
three times) handed in. `sharedSized` is its value at `recordSet`, the lines of `recordLines` for a
matrix of 3076096 rows and one mask row, `recordTable`, no codes before, and the typed groups and
stages. `shared_exists`: the existence, from one evaluation in Lean's kernel (`sharedSized_test`).

By `decide +kernel`, that is, evaluated by Lean's kernel at the written numbers, and turning with
them: `sharedSized_test`.

Adapted from OnBytes/Params/DeriveLin.lean: `linSizedWith` is `linSized` but for the four searches.

Main definitions: `linSizedWith`, `sharedOwn`, `sharedSized`, `atRecordB`, `Passes`, `passes`.
Main theorems: `atRecord_of_test`, `sharedSized_test`, `shared_exists`.
What is not claimed: that `linSized` returns this value (an evaluation outside the kernel says so).
That in a proof's plan the list of codes is this one: there the links' codes stand before. That
`recordLines` are the lines of any file.

-/
import Johnson.Prices.Record
import OnBytes.Flat.HeldAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices

/-- `linSized` with the results of its searches handed in: xyz for `linTurns`, stU, stO and stW for
the three calls of `solveStages`. -/
def linSizedWith (s : Setting) (L : LinLines) (T : TableSize) (codes : Codes)
    (xyz : Sizing × Sizing × Sizing) (stU stO stW : List StageSize) :
    Option (LinSized × Codes) := do
  let scopeShared : Scope := if L.oneTime then .once else .shared
  let split := L.folded.logN != L.omega.logN || L.folded.logL != L.omega.logL
  if L.own.logN != L.omega.logN || L.own.logL != L.omega.logL then none
  if split && (L.folded.maskLogN != L.omega.maskLogN || L.folded.maskLogL != L.omega.maskLogL) then
    none
  if T.code.n < T.code.dim then none
  let A := tableAnalysis s T
  if !tableAdmitted T A then none
  let agree := if L.oneTime then A.once.agree else A.later.agree
  let columns := scopePositions s scopeShared agree
  if columns == 0 then none
  let I := indexShapeOf s T
  if 40 < I.v || I.code.ell ≤ 3 * I.answers then none
  let spent := scopePositions s .once A.once.agree
  let batches := if spent < I.code.r then (I.code.r - spent) / columns else 0
  let ellU := 2 ^ L.folded.logL
  let ellO := 2 ^ L.omega.logL
  let matrixColumns := 2 ^ (L.kLo + I.v)
  let message := fun (mainRows maskRows : Nat) =>
    ({ mainRows := mainRows, mainDeg := 3, maskRows := maskRows, answers := s.samples }
      : OracleShape)
  let u := message (linRowsOf (foldedEntries I + s.samples) ellU true) 0
  let omega := message (linRowsOf (L.matrixRows + s.samples) ellO true) 0
  let wRows := linRowsOf matrixColumns ellO true
  let w := message wRows (if wRows * ellO - matrixColumns < s.samples then 1 else 0)
  let sharedSplit := message 0 1
  let input := message 0 L.inputMaskRows
  let (x, y, z) := xyz
  if !x.serves || (split && !y.serves) || !z.serves then none
  let (testU, codes1) := ioppStages stU codes
  let (testOmega, codes2) := ioppStages stO codes1
  let (testOwn, codes3) := ioppStages stW codes2
  match testU, testOwn with
  | gu :: _, gw :: _ =>
    let S : LinShape :=
      { fold := { index := I, u := canonical { u with code := gu.code }, rowsHigh := true,
                  leafClass := 0, columns := columns }
        kLo := L.kLo
        matrixRows := L.matrixRows
        omega := canonical { omega with code := gw.code }
        w := canonical { w with code := gw.code, maskCode := gw.maskCode }
        omegaRowsHigh := true
        wRowsHigh := true
        sharedSplit := canonical { sharedSplit with maskCode := gu.maskCode }
        ownSplit := canonical {}
        omegaLeafClass := 1
        sharedSplitLeafClass := 2
        wLeafClass := 0
        ownSplitLeafClass := 3
        sharedMaskCode := gu.maskCode
        ownMaskCode := gw.maskCode
        masksAhead := true
        testU := testU
        testOmega := testOmega
        testOwn := testOwn
        testOwnOmega := []
        choice := ⟨true⟩ }
    pure (⟨L, S, ⟨canonical { input with maskCode := gw.maskCode }, 0⟩, T, ⟨x.group, x.t, stU⟩,
      ⟨y.group, y.t, stO⟩, ⟨z.group, z.t, stW⟩, batches⟩, codes3)
  | _, _ => none

/-- The stages of the test on a request's own group. -/
def sharedOwn : List StageSize :=
  [⟨⟨⟨22, 262144, 3571, true⟩, ⟨13, 256, 55, true⟩, 5, 1, 1, .johnson, 159⟩, 55, 0⟩,
    ⟨⟨⟨18, 16384, 55, true⟩, ⟨15, 1024, 55, true⟩, 4, 3, 1, .johnson, 277⟩, 55, 3999⟩,
    ⟨⟨⟨15, 2048, 55, true⟩, ⟨14, 512, 55, true⟩, 3, 3, 1, .johnson, 423⟩, 55, 1883⟩,
    ⟨⟨⟨13, 256, 46, true⟩, ⟨13, 256, 46, true⟩, 3, 3, 1, .johnson, 378⟩, 46, 859⟩,
    ⟨⟨⟨15, 256, 44, true⟩, ⟨15, 1024, 44, true⟩, 0, 0, 1, .johnson, 345⟩, 44, 374⟩]

/-- The sizes at the typed lines, groups and stages. -/
def sharedSized : Option (LinSized × Codes) :=
  linSizedWith recordSet (linLines recordLines 3076096 1 false) recordTable {}
    (⟨⟨⟨24, 4194304, 101, true⟩, ⟨13, 64, 152, true⟩, 7, 0, 1, .johnson, 182⟩, 101, true⟩,
      ⟨⟨⟨22, 262144, 3571, true⟩, ⟨13, 64, 152, true⟩, 4, 0, 1, .johnson, 159⟩, 51, true⟩,
      ⟨⟨⟨22, 262144, 3571, true⟩, ⟨13, 256, 55, true⟩, 5, 1, 1, .johnson, 159⟩, 55, true⟩)
    sharedFolded sharedOmega sharedOwn

/-- `AtRecord` and the three further equations, as a test with code. -/
def atRecordB (x : LinSized) : Bool :=
  decide (x.table = recordTable) && !x.lines.oneTime && x.shape.sharedSplitNeeded &&
    decide (x.folded.stages = sharedFolded) && decide (x.omega.stages = sharedOmega) &&
    decide (x.shape.fold.index.answers = 1) && decide (x.shape.fold.columns = 64) &&
    x.shape.masksAhead && x.shape.choice.masksRide && decide (x.shape.kLo = 7) &&
    decide (x.lines.requests = 64) && decide (x.shape.kRow = 22)

/-- A yes of the test gives the conditions. -/
theorem atRecord_of_test {x : LinSized} (h : atRecordB x = true) :
    AtRecord x ∧ x.shape.kLo = 7 ∧ x.lines.requests = 64 ∧ x.shape.kRow = 22 := by
  unfold atRecordB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, a10, a11, a12⟩

/-- A finished plan holds; it meets the side conditions of the library's law on a round (`sideB`,
OnBytes/Flat/HeldAll.lean); its target is 128; no round has more than w bits of work. -/
def Passes (w : ℕ) (P : Planned) : Prop :=
  P.holds = true ∧ OnBytes.Flat.Held.sideB P = true ∧ P.set.target = 128 ∧
    ∀ r ∈ P.rounds, r.entry.work ≤ w

/-- `Passes`, as a test with code. -/
def passes (w : ℕ) (P : Planned) : Bool :=
  P.holds && OnBytes.Flat.Held.sideB P && decide (P.set.target = 128) &&
    P.rounds.all fun r => decide (r.entry.work ≤ w)

/-- A yes of the test gives the four. -/
theorem passes_sound {w : ℕ} {P : Planned} (h : passes w P = true) : Passes w P := by
  unfold passes at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The typed sizes are there, meet the test, and have a shared plan that passes the test at 28 bits
of work. By evaluation in Lean's kernel. -/
theorem sharedSized_test :
    (sharedSized.any fun p => atRecordB p.1 &&
      (sharedPlan recordSet p.2 p.1).toOption.any (passes 28)) = true := by
  decide +kernel

/-- **The laws on a shared plan at the typed sizes are not empty.** -/
theorem shared_exists : ∃ (x : LinSized) (codes : Codes) (P : Planned),
    AtRecord x ∧ x.shape.kLo = 7 ∧ x.lines.requests = 64 ∧ x.shape.kRow = 22 ∧
      sharedPlan recordSet codes x = .ok P ∧ Passes 28 P := by
  have h := sharedSized_test
  cases hs : sharedSized with
  | none =>
    rw [hs] at h
    cases h
  | some p =>
    rw [hs] at h
    simp only [Option.any_some, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases hP : sharedPlan recordSet p.2 p.1 with
    | error e =>
      rw [hP] at h2
      cases h2
    | ok P =>
      rw [hP] at h2
      obtain ⟨b1, b2, b3, b4⟩ := atRecord_of_test h1
      exact ⟨p.1, p.2, P, b1, b2, b3, b4, hP,
        passes_sound (by simpa [Except.toOption] using h2)⟩

end OnBytes.Params.Prices
