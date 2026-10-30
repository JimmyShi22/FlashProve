-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/MaskIffOwn.lean: at a yes of the proximity test's block the record in front
names a mask just where the place's first fold does not send its own. Statements and proofs.

It has the converse of `hmask_of_step` (Johnson/Desc/K12/Law/OwnMaskStep.lean): `p.nums.ownMask =
false`, the block's test on the plan and a yes of `Block.step` of `proximityTestKind guardedProximityTestParts p` give `t0.mask ≠
none`. With it: `t0.mask.isNone = p.nums.ownMask`.
Why it holds: where no mask is handed in, the fold (`foldD`, Johnson/Desc/First/Close/Closing.lean)
enters its own by `Ground.recvP`, and the record gains as many roots as trees are laid for that one
notice: one at least (`treesMade_gives`, Johnson/Desc/Own/TreesMean.lean: each message's tree is one
of the trees). `heard` asks that the entry of "FOLD epsilon" declares just so many roots; the plan's
entry declares none where `ownMask = false` (`epsE_roots`, Johnson/Desc/K12/Law/MadeRounds.lean). So
the fold refuses, whatever the view shows.
Main names:
  `foldD_none_root`: a yes of `foldD` with no mask handed in: its first entry declares a root at
    least.
  `foldJ_none_root`: the same of the fold's part, at the first round of the cut that it is dealt.
  `second_entry_plain`: where `ownMask = false`, the second declared round's entry declares no root.
  `mask_of_step`: `ownMask = false`, the test on the plan and a yes of the step give `t0.mask ≠
    none`.
  `mask_iff_own`: under the test on the plan and a yes of the step: `t0.mask.isNone =
    p.nums.ownMask`.
Limits: stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean). The two last take the rounds as `r0 ::
rs'`, the form of the theorems that they call; any list of rounds would do. That the premises hold
together is held by runs alone (at the proximity tests of the two example proofs, in both cases of
`ownMask`). No soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.EarlyStep
import Johnson.Desc.Own.TreesMean
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok got_ok need_ok)
open H2K.Made (rounds_top lay_stage epsE epsE_roots)
open H2K.Sw (recvP_ok)

theorem foldD_none_root (F : ℕ) (d d' : _root_.Desc.Plain.DState Unit) (Fs : FoldShape)
    (row : GroupRow) (eE : Fmt.Entry) (eR : List Fmt.Entry) (rs : List Fmt.RoundView)
    (out : SingleRows)
    (h : First.Close.foldD F d Fs row none (eE :: eR) rs = .ok (out, d')) : 0 < eE.roots := by
  cases rs with
  | nil => cases h
  | cons rE rR =>
    rw [First.Close.foldD] at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨ids, dd⟩, hr, h⟩ := bind_ok h
    obtain ⟨i0, _, h⟩ := bind_ok h
    obtain ⟨⟨id', d1⟩, hq, h⟩ := bind_ok h
    cases hq
    obtain ⟨lay, hl, _, _, rfl⟩ := recvP_ok (got_ok hr)
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨d2, _, h⟩ := bind_ok h
    obtain ⟨v, hv, _⟩ := bind_ok h
    unfold First.Close.heard at hv
    obtain ⟨_, _, hv⟩ := bind_ok hv
    obtain ⟨_, _, hv⟩ := bind_ok hv
    obtain ⟨_, h3, _⟩ := bind_ok hv
    have h4 := need_ok h3
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel_left] at h4
    rw [← Own.treesMade_eq] at hl
    have h5 := (Own.treesMade_gives hl).2.1 0 (by simp)
    have h6 := h4.1.1.1.2
    omega

theorem foldJ_none_root (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (hm : t.mask = none)
    (c0 : Fmt.DeclaredRound) (hcut : cut.head? = some c0)
    (h : (foldJ p j cur cut).decide t rs gs = .ok t1) : 0 < c0.entry.roots := by
  cases cut with
  | nil => cases hcut
  | cons c c' =>
    obtain rfl : c = c0 := Option.some.inj hcut
    unfold foldJ at h
    dsimp only at h
    split at h
    · obtain ⟨⟨rows, s1⟩, hx, _⟩ := bind_ok h
      unfold H2K.foldE at hx
      obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨_, _, hx⟩ := bind_ok hx
      obtain ⟨⟨rows', d'⟩, hf, _⟩ := bind_ok hx
      have hf' := mapError_ok hf
      rw [hm] at hf'
      simp only [lay, List.map_cons, Nat.add_comm 1, List.take_succ_cons] at hf'
      exact foldD_none_root _ _ _ _ _ _ _ _ _ hf'
    · cases h

theorem second_entry_plain (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some rds) (ho : N.ownMask = false) :
    ∃ d0 d1 R s next rest, rds = d0 :: d1 :: R ∧ d1.entry.roots = 0 ∧
      N.stages = s :: next :: rest := by
  obtain ⟨s, next, rest, R, hs, hl, rfl⟩ := rounds_top N rds h
  obtain ⟨x, t, R', _, _, _, rfl⟩ := lay_stage _ _ _ _ _ _ _ _ _ _ hl
  refine ⟨_, _, _, s, next, rest, rfl, ?_, hs⟩
  show (epsE N.ownMask false).roots = 0
  rw [epsE_roots, ho]
  rfl

/-- **Where the place's first fold sends no mask of its own, a yes of the step holds that the record
in front names one.** -/
theorem mask_of_step (p : P12) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (ho : p.nums.ownMask = false) : t0.mask ≠ none := by
  have he := early_of_step p t0 tE F n _ cols hstep
  obtain ⟨_, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 hstep
  obtain ⟨first, rest, ds, tF, t1, e1, e2, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE _ _ hdec
  obtain ⟨hfr', _, _⟩ := frontK_ok p _ _ _ _ hfr
  have hF : tF = t0 := by
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨hb, _, _⟩ := batK_ok p _ _ _ _ _ hbat
  obtain ⟨_, _, row, L, S', _, _, rfl⟩ := batJ_ok p he _ _ _ _ _ hb
  obtain ⟨d0, d1, R, s, next, rest', rfl, hroot, hs⟩ := second_entry_plain p.nums ds e2 ho
  rw [hs] at e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e1
  have hlen := oracles_len p hp _ e2
  obtain ⟨o0, o1, os, hor⟩ : ∃ o0 o1 os, p.oracles = o0 :: o1 :: os := by
    match hq : p.oracles with
    | [] => rw [hq] at hlen; simp at hlen
    | [_] => rw [hq] at hlen; simp at hlen
    | o0 :: o1 :: os => exact ⟨o0, o1, os, rfl⟩
  obtain ⟨t2, _, _, hfold, _⟩ := (stagesFrom_ok guardedProximityTestParts p 0 s next rest' _ _ _ _ _).1 hst
  have hfj := (ranged_ok _ _ _ _ _ _ hfold).1
  intro hm
  have hcut : (((((d0 :: d1 :: R).zip p.oracles).drop 1).take (1 + s.k)).map (·.1)).head? =
      some d1 := by
    rw [hor]
    simp [Nat.add_comm 1, List.take_succ_cons]
  have := foldJ_none_root p 0 s _ { tF with st := S', pass := .claim row L } _ _ _ hm d1 hcut hfj
  omega

/-- At a yes, the record in front names no mask just where the first fold sends its own. -/
theorem mask_iff_own (p : P12) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n)) :
    t0.mask.isNone = p.nums.ownMask := by
  cases ho : p.nums.ownMask with
  | true => rw [hmask_of_yes p t0 tE F n r0 rs' cols hp hstep ho]; rfl
  | false =>
    have := mask_of_step p t0 tE F n r0 rs' cols hp hstep ho
    cases hm : t0.mask with
    | none => exact absurd hm this
    | some _ => rfl

end H2K.JointK

#print axioms H2K.JointK.mask_of_step
#print axioms H2K.JointK.mask_iff_own
