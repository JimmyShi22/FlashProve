-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/EarlyStep.lean: a yes of the proximity test's block holds that the place's
masks come early. Statements and proofs.

`(proximityTestKind guardedProximityTestParts p).decide t0 rs gs = .ok tE` gives `p.early = true`; the block's test on the plan is
not needed. So the premise `p.early = true` falls wherever a yes of the decision or of `Block.step`
stands beside it.
Why it holds: a yes gives declared rounds (`k12_ok`, Johnson/Desc/K12/FrameLaws.lean), so the place
has two stages or more (`H2U.roundsOfNums` gives nothing at fewer). So the base case is reached
through a switch, and the record in front of it is the one that the batching behind the switch
leaves (`behindJ`, Johnson/Desc/K12/Join.lean), whose mask is `if p.early then out.others[0]? else
none`. The question between ("the next mask has come") turns nothing. The base case (`baseJ5`,
Johnson/Desc/K12/JoinGuarded.lean) asks for that mask by name ("the base case: the masking message has
not come") and refuses where there is none. So at `early = false` the block refuses every view.
Main names:
  `behindJ_mask`: a yes of the batching behind a switch, at `early = false`, leaves a record that
    names no mask.
  `baseJ5_mask`: a yes of the base case's part: the record in front names a mask.
  `stages_no`: at `early = false` the stages from any stage on refuse, where the record names no
    mask if that stage is the last.
  `early_of_decide`: a yes of the block's decision gives `p.early = true`.
  `early_of_step`: the same of `Block.step`.
  `lastOk_of_yes`, `aloneAt_of_yes`, `hmask_of_yes`, `aloneAt_of_yes_own`: the four last theorems of
    Johnson/Desc/K12/Law/OwnSeatStep.lean and Johnson/Desc/K12/Law/OwnMaskStep.lean without their
    premise `p.early = true`.
Limits: stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean). It says nothing of a place that no view
has met: the block's test on the plan does not ask `p.early`. Where a law wants the place's numbers
in front of the rounds there is no yes to spend, and `p.early = true` stays a premise.

(Where this and lean/THEOREM.md differ, the page holds.)
No soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.OwnMaskStep

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok)
open H2K.Made (rounds_top)
open H2K.First (lastOk aloneAt)

theorem behindJ_mask (p : P12) (j : ℕ) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t2 t3 : T12) (rs : List Fmt.RoundView) (gs : Gs) (he : p.early = false)
    (h : (behindJ p j nxt cut).decide t2 rs gs = .ok t3) : t3.mask = none := by
  unfold behindJ at h
  dsimp only at h
  split at h
  · obtain ⟨x, _, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    simp [he]
  · cases h

theorem baseJ5_mask (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (baseJ5 p j cur cut).decide t rs gs = .ok tE) : t.mask ≠ none := by
  unfold baseJ5 at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨star, hs, _⟩ := bind_ok h
    intro hn
    rw [hn] at hs
    cases hs
  · cases h

/-- At early = false the stages refuse. -/
theorem stages_no (p : P12) (he : p.early = false) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs),
    (rest = [] → t.mask = none) →
    (stagesFrom guardedProximityTestParts p j cur rest l : Blk').decide t rs gs ≠ .ok t'
  | [], j, cur, l, t, t', rs, gs, hm, h => by
    rw [stagesFrom_last] at h
    exact baseJ5_mask p j cur _ t t' rs gs (ranged_ok _ _ _ _ _ _ h).1 (hm rfl)
  | next :: rest, j, cur, l, t, t', rs, gs, _, h => by
    obtain ⟨t₁, t₂, t₃, _, _, hb, _, hr⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur next rest l t t' rs gs).1 h
    exact stages_no p he rest (j + 1) next _ t₃ t' _ _
      (fun _ => behindJ_mask p (j + 1) next _ t₂ t₃ [] [] he hb) hr

/-- **A yes of the block's decision holds that the masks come early.** -/
theorem early_of_decide (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) : p.early = true := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, _, _, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  obtain ⟨s, next, rest', _, hs, _, _⟩ := rounds_top p.nums ds e2
  rw [hs] at e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e1
  cases he : p.early with
  | true => rfl
  | false => exact absurd hst (stages_no p he _ _ _ _ _ _ _ _ (fun hn => by cases hn))

theorem early_of_step (p : P12) (t0 tE : T12) (F n : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 rs cols = .ok (tE, n)) : p.early = true :=
  early_of_decide p t0 tE _ _ ((step_iff _ _ _ _ _ _ _).1 h).2.1

theorem lastOk_of_yes (p : P12) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB)) :
    lastOk p { t0 with st := SB, pass := .claim rowB LB } = true :=
  lastOk_of_step p (early_of_step p t0 tE F n _ cols hstep) t0 tE F n r0 rs' cols hp hstep eB rowB
    LB SB hbB

theorem aloneAt_of_yes (p : P12) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB))
    (hmask : t0.mask = none) :
    aloneAt p { t0 with st := SB, pass := .claim rowB LB } = some true :=
  aloneAt_of_step p (early_of_step p t0 tE F n _ cols hstep) t0 tE F n r0 rs' cols hp hstep eB rowB
    LB SB hbB hmask

theorem hmask_of_yes (p : P12) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (ho : p.nums.ownMask = true) : t0.mask = none :=
  hmask_of_step p (early_of_step p t0 tE F n _ cols hstep) t0 tE F n r0 rs' cols hp hstep ho

theorem aloneAt_of_yes_own (p : P12) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB))
    (ho : p.nums.ownMask = true) :
    aloneAt p { t0 with st := SB, pass := .claim rowB LB } = some true :=
  aloneAt_of_step_own p (early_of_step p t0 tE F n _ cols hstep) t0 tE F n r0 rs' cols hp hstep eB
    rowB LB SB hbB ho

end H2K.JointK

#print axioms H2K.JointK.early_of_decide
#print axioms H2K.JointK.early_of_step
#print axioms H2K.JointK.hmask_of_yes
#print axioms H2K.JointK.aloneAt_of_yes_own
