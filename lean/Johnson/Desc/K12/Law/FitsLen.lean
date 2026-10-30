-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FitsLen.lean: a yes of the proximity test's block gives all four numbers of the
group's layout: `k`, `h`, `2 ^ logEll` and `2 ^ logEllZk` are the first stage's `k`, `h`, `C.l` and
`Z.l`. Statements and proofs.

Why it holds: the frame's guard "the group is the first stage's" (`firstFits`,
Johnson/Desc/K12/Frame.lean) compares the group's two codes with the stage's, not only `k` and `h`;
the layout's `logEll` is `ceilLog2` of the message length of the group's main code; `sizesOk`
(Johnson/Desc/K12/Sizes.lean) asks that both lengths be powers of two.
The walk to the guard follows `k12_fits` (Johnson/Desc/K12/Coin/YesHolds.lean),
which takes `k` and `h` off the same guard; that proof's first lines are
taken over.
What it is for: two clauses that the count on the batching's converse asks of the record (`2 ^
Ly.logEll = C.l`, `2 ^ Ly.logEllZk = Z.l`; Johnson/Desc/K12/Law/TupleVals.lean) follow from the yes.
Main names:
  `pow2_ceil`: `pow2 n` gives `2 ^ ceilLog2 n = n` (over `ceilLog2_two_pow`,
    OnBytes/Slice/ProgCodes.lean).
  `first_sizes`: the frame's own test on the plan, whatever the parts, holds at the first stage `a`:
    `pow2 a.C.l`, `pow2 a.Z.l`, `a.h ≤ a.k` (clauses of `sizesOk`).
  `begun_group`: the group under test behind the beginning is the group in front, marked and without
    open rows.
  `k12_lens`: `p.early = true`, the block's test on the plan, and a yes of its decision give the
    first stage and the batching's return `(row, L, S')` with `L.k = first.k`, `L.h = first.h`, `2 ^
    L.logEll = first.C.l`, `2 ^ L.logEllZk = first.Z.l`.
Limits: Stated of `proximityTestKind guardedProximityTestParts p` (Johnson/Desc/K12/JoinGuarded.lean). Where no view has met a yes it
says nothing. No soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.TopH
import OnBytes.Slice.ProgCodes
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok got_ok)

theorem pow2_ceil (n : ℕ) (h : pow2 n = true) : 2 ^ ceilLog2 n = n := by
  have h1 : 2 ^ Nat.log2 n = n := beq_iff_eq.1 h
  rw [← h1, ceilLog2_two_pow]

theorem first_sizes {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) : pow2 a.C.l = true ∧ pow2 a.Z.l = true ∧ a.h ≤ a.k := by
  simp only [proximityTestKind] at hp
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have h := hp.1.1.1.1
    unfold sizesOk at h
    simp only [Bool.and_eq_true] at h
    have h2 := h.2
    rw [hs] at h2
    simp only [stagesOk, K12.stageOk, Bool.and_eq_true, decide_eq_true_eq] at h2
    exact ⟨h2.1.1.1.1.1.1.1.2, h2.1.1.1.1.1.1.2, h2.1.1.1.2⟩
  · cases hp

theorem begun_group (S : Statement) (g : ℕ) (G : Group) (hG : S.groups[g]? = some G) :
    (begun S g G).groups[g]? = some { G with inRun := true, rows := #[] } := by
  show ((closeLedgers S G.members.toList).groups.modify g _)[g]? = _
  rw [Array.getElem?_modify, if_pos rfl, closeLedgers_groups, hG]
  rfl

theorem k12_lens (p : P12) (he : p.early = true) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (e : Fmt.Entry) (r : Fmt.RoundView)
      (row : GroupRow) (L : GroupLayout) (S' : Statement), p.nums.stages = first :: rest ∧
      First.Close.bat t0.st t0.g e r = .ok (row, L, S') ∧ L.k = first.k ∧ L.h = first.h ∧
      2 ^ L.logEll = first.C.l ∧ 2 ^ L.logEllZk = first.Z.l := by
  obtain ⟨first, rest, ds, tF, t1, e1, e2, hfr, hbat, hgrp, _⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  obtain ⟨first', rest', ds', e1', e2', l1, _⟩ := H2K.FrameLens.lens_top (Cl := Unit) guardedProximityTestParts p hp
  obtain rfl := Option.some.inj (e2'.symm.trans e2)
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
  have nB : (batAt guardedProximityTestParts p (ds'.zip p.oracles) : Blk').rounds.length = 1 := by
    show (((ds'.zip p.oracles).take 1).map (·.1)).length = 1
    rw [List.length_map, l1]
  rw [nB] at hbat
  obtain ⟨hbat', _, _⟩ := batK_ok p _ _ _ _ _ hbat
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ hbat'
  obtain ⟨pC, pZ, _⟩ := first_sizes guardedProximityTestParts p hp first rest e1
  obtain ⟨G0, hG0, hL, rfl⟩ := bat_front _ _ _ _ _ _ _ hb
  refine ⟨first, rest, e, r, row, L, _, e1, hb, ?_⟩
  obtain ⟨g, hg, hf⟩ := (Option.any_eq_true _ _).1 hgrp
  simp only [firstFits, Bool.and_eq_true, beq_iff_eq] at hf
  simp only [guardedProximityTestParts] at hg
  split at hg
  · rename_i x L' G hpass hG
    obtain ⟨_, rfl⟩ := Passing.claim.inj hpass
    split at hg
    · rename_i c z hc hz
      obtain rfl := Option.some.inj hg
      have hG' : G = { G0 with inRun := true, rows := #[] } :=
        Option.some.inj (hG.symm.trans (begun_group _ _ _ hG0))
      subst hG'
      have hc' : tF.st.codes.base[G0.code]? = some c := by
        have := hc
        rwa [show (begun tF.st tF.g G0).codes = tF.st.codes from closeLedgers_codes _ _] at this
      have hz' : tF.st.codes.mask[G0.maskCode]? = some z := by
        have := hz
        rwa [show (begun tF.st tF.g G0).codes = tF.st.codes from closeLedgers_codes _ _] at this
      unfold Statement.layout at hL
      rw [hG0] at hL
      obtain rfl := Option.some.inj hL
      have hl : c.ell = first.C.l := congrArg Fmt.M1.Code.l hf.1.1.1
      have hzl : z.ell = first.Z.l := congrArg Fmt.M1.Code.l hf.1.1.2
      refine ⟨hf.1.2, hf.2, ?_, ?_⟩
      · show 2 ^ ceilLog2 (tF.st.codes.base.getD G0.code default).ell = _
        rw [Array.getD_eq_getD_getElem?, hc', Option.getD_some, hl]
        exact pow2_ceil _ pC
      · show 2 ^ ceilLog2 (tF.st.codes.mask.getD G0.maskCode default).ell = _
        rw [Array.getD_eq_getD_getElem?, hz', Option.getD_some, hzl]
        exact pow2_ceil _ pZ
    · cases hg
  · cases hg

end H2K.JointK

#print axioms H2K.JointK.pow2_ceil
#print axioms H2K.JointK.first_sizes
#print axioms H2K.JointK.begun_group
#print axioms H2K.JointK.k12_lens
