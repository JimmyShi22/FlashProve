-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OwnMaskStep.lean: where the first fold of a proximity test sends its own mask,
a yes of the block's step holds that the record in front names no mask. Statements and proofs.

`p.nums.ownMask = true`, the block's test on the plan and a yes of `Block.step` of `proximityTestKind guardedProximityTestParts p`
give `t0.mask = none`, under `p.early = true`. So `accK_yes_real_own`
(Johnson/Desc/K12/Law/AccKOwn.lean) need not take that as a premise, and the block need not ask it.
Why it holds: the fold (`foldD`, Johnson/Desc/First/Close/Closing.lean) hears its first round "FOLD
epsilon" with as many roots as the record has gained in entering the mask: none where a mask was
handed in. `heard` asks that the entry declares just so many roots (its refusal is "K10.entry"). The
entry is the plan's: the frame deals the fold the declared rounds that `H2U.roundsOfNums` makes of
the place's numbers, and there the first "FOLD epsilon" declares one root where `ownMask` holds
(`epsE`, Johnson/Desc/K12/Law/MadeRounds.lean). So with a mask handed in the fold refuses, whatever
the view shows. The mask that the fold is handed is the record's in front: the front turns nothing,
and the batching keeps the mask where the masks come early (there the premise `p.early = true` is
spent).
Main names:
  `foldD_some_root`: a yes of `foldD` with a mask handed in: its first entry declares no root.
  `foldJ_some_root`: the same of the fold's part, at the first round of the cut that it is dealt.
  `second_entry`: where `ownMask` holds, the second declared round's entry declares one root.
  `oracles_len`: the place tells as many lists of oracle messages as its numbers give rounds (a
    clause of the frame's test on the plan).
  `hmask_of_step`: `ownMask = true`, the block's test on the plan and a yes of the step give
    `t0.mask = none`.
  `aloneAt_of_step_own`: `aloneAt_of_step` (Johnson/Desc/K12/Law/OwnSeatStep.lean) with `ownMask =
    true` in the place of its premise on the mask.
Limits: stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean), under `p.early = true`
(Johnson/Desc/K12/Law/EarlyStep.lean pays it from the same yes). The converse (no own mask: the
record names one) is `mask_of_step` (Johnson/Desc/K12/Law/MaskIffOwn.lean). No soundness is claimed,
and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.OwnSeatStep
import Johnson.Desc.K12.Law.MadeRounds

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok got_ok need_ok)
open H2K.First (aloneAt)
open H2K.Made (rounds_top lay_stage epsE)

theorem foldD_some_root {L : Type} (F : ℕ) (d d' : _root_.Desc.Plain.DState L) (Fs : FoldShape)
    (row : GroupRow) (id : ℕ) (eE : Fmt.Entry) (eR : List Fmt.Entry) (rs : List Fmt.RoundView)
    (out : SingleRows)
    (h : First.Close.foldD F d Fs row (some id) (eE :: eR) rs = .ok (out, d')) : eE.roots = 0 := by
  cases rs with
  | nil => cases h
  | cons rE rR =>
    rw [First.Close.foldD] at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨id', d1⟩, hq, h⟩ := bind_ok h
    cases hq
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨d2, _, h⟩ := bind_ok h
    obtain ⟨v, hv, _⟩ := bind_ok h
    unfold First.Close.heard at hv
    obtain ⟨_, _, hv⟩ := bind_ok hv
    obtain ⟨_, _, hv⟩ := bind_ok hv
    obtain ⟨_, h3, _⟩ := bind_ok hv
    have := need_ok h3
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.sub_self] at this
    exact this.1.1.1.2

theorem foldJ_some_root (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (t t1 : T12) (rs : List Fmt.RoundView) (gs : Gs) (id : ℕ) (hm : t.mask = some id)
    (c0 : Fmt.DeclaredRound) (hcut : cut.head? = some c0)
    (h : (foldJ p j cur cut).decide t rs gs = .ok t1) : c0.entry.roots = 0 := by
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
      exact foldD_some_root _ _ _ _ _ _ _ _ _ _ hf'
    · cases h

/-- Where the first fold sends its own mask, the second declared round (the first "FOLD epsilon")
declares one root. -/
theorem second_entry (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some rds) (ho : N.ownMask = true) :
    ∃ d0 d1 R s next rest, rds = d0 :: d1 :: R ∧ d1.entry.roots = 1 ∧
      N.stages = s :: next :: rest := by
  obtain ⟨s, next, rest, R, hs, hl, rfl⟩ := rounds_top N rds h
  obtain ⟨x, t, R', _, _, _, rfl⟩ := lay_stage _ _ _ _ _ _ _ _ _ _ hl
  refine ⟨_, _, _, s, next, rest, rfl, ?_, hs⟩
  simp [epsE, ho]

/-- The place tells as many lists of oracle messages as its numbers give rounds. -/
theorem oracles_len (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ds : List Fmt.DeclaredRound) (hd : H2U.roundsOfNums p.nums = some ds) :
    p.oracles.length = ds.length := by
  unfold proximityTestKind at hp
  split at hp
  · rename_i first rest rs os hs hr ho
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [hr] at hd
    cases hd
    exact hp.1.1.2
  · simp at hp

/-- **Where the place's first fold sends its own mask, a yes of the step holds that the record in
front names no mask.** -/
theorem hmask_of_step (p : P12) (he : p.early = true) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (ho : p.nums.ownMask = true) : t0.mask = none := by
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
  obtain ⟨d0, d1, R, s, next, rest', rfl, hroot, hs⟩ := second_entry p.nums ds e2 ho
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
  cases hm : tF.mask with
  | none => rfl
  | some id =>
    exfalso
    have hcut : (((((d0 :: d1 :: R).zip p.oracles).drop 1).take (1 + s.k)).map (·.1)).head? =
        some d1 := by
      rw [hor]
      simp [Nat.add_comm 1, List.take_succ_cons]
    have := foldJ_some_root p 0 s _ { tF with st := S', pass := .claim row L } _ _ _ id hm d1 hcut
      hfj
    omega

/-- aloneAt from the step's yes at a place whose first fold sends its own mask. -/
theorem aloneAt_of_step_own (p : P12) (he : p.early = true) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB))
    (ho : p.nums.ownMask = true) :
    aloneAt p { t0 with st := SB, pass := .claim rowB LB } = some true :=
  aloneAt_of_step p he t0 tE F n r0 rs' cols hp hstep eB rowB LB SB hbB
    (hmask_of_step p he t0 tE F n r0 rs' cols hp hstep ho)

end H2K.JointK

#print axioms H2K.JointK.hmask_of_step
#print axioms H2K.JointK.aloneAt_of_step_own
