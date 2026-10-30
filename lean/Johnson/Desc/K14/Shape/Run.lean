-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/Run.lean: the shared chain's shape (Johnson/Desc/K14/Shape/Lin.lean): THE ONE
UPDATE at each of the linear claim's eight sub-protocols; the law at their own steps (where what
goes out with o_u can be said, the plan has two codes and the kind's text makes its eight); and from
the test in front (Johnson/Desc/K14/Shape/Facts.lean) to the step's return (under PlanFacts, the two
sendings' test on the plan and the library's Block.Fits, at the eight of Eight P; at "(rec_gamma)"
beside: no seed of the key has the factor 0).

Main names:
  updS                **the one update at the sub-protocol number b**
  stepCarries         **WHEREVER THE STEP OF ONE OF THE EIGHT RETURNS .ok, WHERE WHAT GOES OUT WITH
                      o_u CAN BE SAID AND THE PLAN HAS TWO CODES, THE SHAPE BEHIND IS THE UPDATE OF
                      THE SHAPE IN FRONT.** Asks: what goes out with o_u (withU P.S = some sentU);
                      two codes; the kind's text makes its eight at P (Eight P). Nothing on the
                      state, on a round or on a column. THE STEPS ARE THOSE OF THE EIGHT AT THE
                      KIND's OWN TYPE OF CLAIMS (below)
  modAt_read, groupB_congr, msgB_congr, kindsAt_rowsUp, kindsAt_joinUp and their like   laws on
                      shapes: what the tests read through the updates
  kinds_up            **a law on shapes, no state is named**: what lies on the two groups is handed
                      on by the update, border by border; at 3, 4 and 8 it asks the facts' half too
  state9_up           **a law on shapes**: the facts' half in front of "SPLIT" gives the facts' half
                      behind it
  state_next          **a law on states**: UNDER PlanFacts AND THE TWO SENDINGS' TEST ON THE PLAN
                      (planOkOwn), at the eight of Eight P: the facts' half in front, and
                      Block.Fits: the step returns, and (at 1 to 7) the facts' half behind holds. AT
                      "(rec_gamma)" BESIDE: no seed of the key has the factor 0
  first_shape, facts_start   all keys whose sizes fit have one shape at the chain's first state
                      (that of the written example, Johnson/Desc/K14/Honest/ChainWitness.lean), and
                      it passes the test at the border 1. The files of this folder that stand over
                      this one and the library alone (Up.lean, End.lean, Comp.lean, EndToy.lean) do
                      not call the two. facts_start gives the premise that End.lean's facts_upTo
                      asks, at the first state's shape; the two are laid together in no theorem
                      there

WITH WHAT THE TEST SUFFICES. state_next asks beside the test: PlanFacts; at the two sendings their
kind's test on the plan (Johnson/Desc/K1/Own.lean: planOkOwn); Eight P; Block.Fits; at "(rec_gamma)"
the test on the key's seeds. Block.Fits (the step's own tests on rounds and columns) ASKS SOMETHING
OF THE VERIFIER's OWN RANDOM VALUES: at the two sendings no sampled seed has the factor 0 as machine
words; at "LOC" every sampled location is below 2 ^ logN.

PlanFacts (Johnson/Desc/K14/Honest/YesChain.lean), spelled out: every code's message length is a
power of two; the linear claim's public sizes meet their conditions; the two groups' codes are
there; THE PLAN HAS TWO CODES (sharedSplitNeeded); THE MASKS GO AHEAD (masksAhead); with o_u just
two messages go out; both sendings' notices pass the library's test; o_sp has a free mask entry;
o_omega gets a tree that o_sp does not share. A plan with one code, or whose masks do not go ahead,
is served by no law here that names PlanFacts. stepCarries reaches further: of these it asks two:
what goes out with o_u, and two codes.

The facts' half at 1 to 7 is handed on here along a state's step. The law at every shape stands in
Johnson/Desc/K14/Shape/Up.lean.

AT WHICH TYPE THE STEPS ARE. Eight P holds the eight sub-protocols that the kind's text makes
(blocks P) AT THE KIND's OWN TYPE OF CLAIMS (Block St Unit). A proof file's IOP as written in Lean
holds them carried to another type (Johnson/Desc/K14/Honest/StepsBack.lean says so at Eight). So a
caller at the IOP carries the steps across first; the library's laws for that:
Johnson/Desc/K14/Honest/FlatSteps.lean: Like.step, step_retype. No law here names the other type.
That the eight are there wherever what goes out with o_u can be said is the library's blocks_eight
(Johnson/Desc/K14/Law/BlocksEight.lean), as an existence; it is not called here: Eight P is taken as
a premise, so that the steps can be named.

What is not claimed. That every word shown is below the prime: the chain's decision asks it in front
of its fold (Johnson/Desc/Block.lean: viewWordsBelowPrime): a test on sent and sampled values that is in no
step, so in none of the test, the tests on values and Block.Fits. Anything at the sub-protocols
behind the eight. That updS is what the sub-protocols do at a plan with one code: by a reading of
Johnson/Desc/K14/Text.lean it is not, at "LIN point", the second sending, the joinings and "SPLIT".
Nothing on soundness or on hiding. This is not completeness of the protocol or of a program.
-/
import Johnson.Desc.K14.Shape.Facts
import Johnson.Desc.K14.Shape.Sends
import Johnson.Desc.K14.Honest.ChainWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open Desc.K14.Law (parU parO)
open Desc.K14.Honest (Eight PlanFacts Carried)

/-! ## The update at each of the eight, and the law at their own steps -/

/-- **THE ONE UPDATE OF THE SHAPE AT THE SUB-PROTOCOL NUMBER b** (1: "LIN point", …, 8: "SPLIT"),
where the plan has two codes: a function with code of the plan, of sentU and of the state's shape
alone. sentU is a free letter: it is the chain's update only where withU P.S = some sentU. At 0 (the
front sub-protocol, which leaves the state: a reading; no law here names that sub-protocol) and from
9 on: the shape as it is: FROM 9 ON THAT IS NO LAW: the sub-protocols there change the state. -/
def updS (P : P14) (sentU : Array OracleNotice) : Nat → Sh2 → Sh2
  | 1, a => pointUp P a
  | 2, a => sendUUp P sentU a
  | 3, a => recUp P a
  | 4, a => locUp P a
  | 5, a => sendOUp P a
  | 6, a => joinsUp a
  | 7, a => zetaUp P a
  | 8, a => splitUp a
  | _, a => a

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- **WHEREVER THE STEP OF ONE OF THE EIGHT RETURNS .ok, THE SHAPE BEHIND IS THE UPDATE OF THE SHAPE
IN FRONT**, under three premises, all on the plan. hU: what goes out with o_u can be said (withU P.S
= some sentU). hS: two codes. B: the kind's text makes its eight at P (Eight P). No premise on the
state, on a round or on a column. The steps are those of the eight at the kind's own type of claims
(Block St Unit); the IOP as written in Lean holds the eight carried to another type, and the way
across is the library's (Johnson/Desc/K14/Honest/FlatSteps.lean: Like.step, step_retype). -/
theorem stepCarries (hU : withU P.S = some sentU) (hS : P.S.sharedSplitNeeded = true) (B : Eight P)
    (ft : Nat) (d d' : St) (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) :
    (B.b1.step ft d rs c = .ok (d', n) → sh2 d' = updS P sentU 1 (sh2 d)) ∧
    (B.b2.step ft d rs c = .ok (d', n) → sh2 d' = updS P sentU 2 (sh2 d)) ∧
    (B.b3.step ft d rs c = .ok (d', n) → sh2 d' = updS P sentU 3 (sh2 d)) ∧
    (B.b4.step ft d rs c = .ok (d', n) → sh2 d' = updS P sentU 4 (sh2 d)) ∧
    (B.b5.step ft d rs c = .ok (d', n) → sh2 d' = updS P sentU 5 (sh2 d)) ∧
    (B.b6.step ft d rs c = .ok (d', n) → sh2 d' = updS P sentU 6 (sh2 d)) ∧
    (B.b7.step ft d rs c = .ok (d', n) → sh2 d' = updS P sentU 7 (sh2 d)) ∧
    (B.b8.step ft d rs c = .ok (d', n) → sh2 d' = updS P sentU 8 (sh2 d)) := by
  obtain ⟨_, ⟨n2, f2, g2, e2⟩, n5, f5, g5, e5⟩ := B.fronts hU
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_⟩
  · obtain ⟨R, _, _, k, hpt⟩ := B.back1 hU ft d d' rs c n h
    exact point_carries hS d d' _ hpt k
  · obtain ⟨Ra, Rb, _, _, _, k⟩ := B.back2 hU ft d d' rs c n h
    rw [e2] at k
    exact sendU_carries n2 f2 g2 d d' _ _ k
  · obtain ⟨_, _, k⟩ := B.back3 hU ft d d' rs c n h
    exact rec_carries d d' _ k
  · obtain ⟨R, _, hn, _, _, k⟩ := B.back4 hU ft d d' rs c n h
    exact loc_carries d d' _ _ hn k
  · obtain ⟨Ra, Rb, _, _, _, k⟩ := B.back5 hU ft d d' rs c n h
    rw [e5] at k
    exact sendO_carries hS n5 f5 g5 d d' _ _ k
  · obtain ⟨_, _, k⟩ := B.back6 hU ft d d' rs c n h
    exact joins_carries hS d d' _ k
  · obtain ⟨R, _, _, k, hz⟩ := B.back7 hU ft d d' rs c n h
    exact zeta_carries d d' _ hz k
  · obtain ⟨R, _, _, k⟩ := B.back8 hU hS ft d d' rs c n h
    exact split_carries hS d d' _ k

/-! ## Laws on shapes: a change of one entry of a list -/

/-- A change of one entry leaves the others. It follows from modAt_at
(Johnson/Desc/Ground/Shape/Claims.lean: the changed list at any number), a file that this one does
not import. -/
theorem modAt_get_ne {α : Type} (l : List α) (i j : Nat) (f : α → α) (h : j ≠ i) :
    (modAt l i f)[j]? = l[j]? := by
  unfold modAt
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases l[j]? with
  | none => rfl
  | some x =>
    show some (if 0 + j = i then f x else x) = some x
    rw [if_neg (by omega)]

/-- It leaves the length. -/
theorem modAt_length {α : Type} (l : List α) (i : Nat) (f : α → α) :
    (modAt l i f).length = l.length := by
  simp [modAt]

/-- A reader that a change does not turn reads the same at every entry. -/
theorem modAt_read {α β : Type} (l : List α) (i j : Nat) (f : α → α) (r : α → β)
    (h : ∀ x, r (f x) = r x) : ((modAt l i f)[j]?).map r = (l[j]?).map r := by
  by_cases e : j = i
  · subst e
    rw [modAt_get, Option.map_map]
    exact congrArg (fun q => Option.map q l[j]?) (funext h)
  · rw [modAt_get_ne _ _ _ _ e]

/-! ## Laws on shapes: what the tests read -/

/-- The test on a group reads four of its fields. -/
theorem groupB_congr {h h' : StSh} {g : Nat}
    (e : (h'.groups[g]?).map (fun G => (G.code, G.maskCode, G.inRun, G.members)) =
      (h.groups[g]?).map fun G => (G.code, G.maskCode, G.inRun, G.members))
    (code maskCode : Nat) (ms : List Nat) :
    groupB h' g code maskCode ms = groupB h g code maskCode ms := by
  unfold groupB
  cases h1 : h'.groups[g]? with
  | none =>
    cases h2 : h.groups[g]? with
    | none => rfl
    | some G =>
      rw [h1, h2] at e
      cases e
  | some G' =>
    cases h2 : h.groups[g]? with
    | none =>
      rw [h1, h2] at e
      cases e
    | some G =>
      rw [h1, h2] at e
      have e' := Option.some.inj e
      simp only [Prod.mk.injEq] at e'
      obtain ⟨a, b, c, d⟩ := e'
      simp only [a, b, c, d]

/-- The test on a message reads the codes and three of its fields. -/
theorem msgB_congr {h h' : StSh} {o : Nat} (hc : h'.codes = h.codes)
    (e : (h'.oracles[o]?).map (fun x => (x.shape, x.sampled, x.pad)) =
      (h.oracles[o]?).map fun x => (x.shape, x.sampled, x.pad)) (s : OracleShape) :
    msgB h' o s = msgB h o s := by
  unfold msgB
  rw [hc]
  cases h1 : h'.oracles[o]? with
  | none =>
    cases h2 : h.oracles[o]? with
    | none => rfl
    | some x =>
      rw [h1, h2] at e
      cases e
  | some x' =>
    cases h2 : h.oracles[o]? with
    | none =>
      rw [h1, h2] at e
      cases e
    | some x =>
      rw [h1, h2] at e
      have e' := Option.some.inj e
      simp only [Prod.mk.injEq] at e'
      obtain ⟨a, b, c⟩ := e'
      simp only [a, b, c]

/-- Where the test on a group passes, the group is there. -/
theorem groupB_some {h : StSh} {g code maskCode : Nat} {ms : List Nat}
    (e : groupB h g code maskCode ms = true) : ∃ G, h.groups[g]? = some G := by
  unfold groupB at e
  cases hG : h.groups[g]? with
  | none =>
    rw [hG] at e
    cases e
  | some G => exact ⟨G, rfl⟩

/-- The groups behind the laying of constraints. -/
theorem rowsUp_groups (c : CoreSh) (g : Nat) (ks : List RowKind) :
    (rowsUp c g ks).st.groups = modAt c.st.groups g fun G => { G with kinds := G.kinds ++ ks } :=
  rfl

/-- The groups behind a joining. -/
theorem joinUp_groups (c : CoreSh) (g o : Nat) (k : Bool) :
    (joinUp c g o k).st.groups = modAt c.st.groups g fun G =>
      { G with
        members := insAt G.members
          ((((c.st.groups[g]?).map (·.members)).getD []).filter (· < o)).length o
        kept := insAt G.kept
          ((((c.st.groups[g]?).map (·.members)).getD []).filter (· < o)).length k } :=
  rfl

/-- The messages behind the taking of a mask entry. -/
theorem maskUp_oracles (c : CoreSh) (o : Nat) :
    (maskUp c o).st.oracles =
      modAt c.st.oracles o fun x => { x with ledger := x.ledger.map ledNext } :=
  rfl

/-- Constraints laid on a group leave the tests on groups. -/
theorem groupB_rowsUp (c : CoreSh) (g' : Nat) (ks : List RowKind) (g code maskCode : Nat)
    (ms : List Nat) :
    groupB (rowsUp c g' ks).st g code maskCode ms = groupB c.st g code maskCode ms :=
  groupB_congr (by rw [rowsUp_groups]; exact modAt_read _ _ _ _ _ fun _ => rfl) _ _ _

/-- The taking of a mask entry leaves the tests on messages. -/
theorem msgB_maskUp (c : CoreSh) (o' o : Nat) (s : OracleShape) :
    msgB (maskUp c o').st o s = msgB c.st o s :=
  msgB_congr (h := c.st) (h' := (maskUp c o').st) rfl
    (by rw [maskUp_oracles]; exact modAt_read _ _ _ _ _ fun _ => rfl) _

/-- On the group itself the kinds are laid behind. -/
theorem kindsAt_rowsUp (c : CoreSh) (g : Nat) (ks : List RowKind) {G : GrpSh}
    (hG : c.st.groups[g]? = some G) : kindsAt (rowsUp c g ks) g = kindsAt c g ++ ks := by
  unfold kindsAt
  rw [rowsUp_groups, modAt_get, hG]
  rfl

/-- On another group nothing turns. -/
theorem kindsAt_rowsUp_ne (c : CoreSh) (g g' : Nat) (ks : List RowKind) (h : g' ≠ g) :
    kindsAt (rowsUp c g ks) g' = kindsAt c g' := by
  unfold kindsAt
  rw [rowsUp_groups, modAt_get_ne _ _ _ _ h]

/-- A joining lays no constraint. -/
theorem kindsAt_joinUp (c : CoreSh) (g o : Nat) (k : Bool) (g' : Nat) :
    kindsAt (joinUp c g o k) g' = kindsAt c g' := by
  unfold kindsAt
  rw [joinUp_groups]
  exact congrArg (fun q => Option.getD q []) (modAt_read _ _ _ _ _ fun _ => rfl)

/-- A group that is there is there behind a joining. -/
theorem some_joinUp (c : CoreSh) (g o : Nat) (k : Bool) (g' : Nat) {G : GrpSh}
    (hG : c.st.groups[g']? = some G) : ∃ G', (joinUp c g o k).st.groups[g']? = some G' := by
  have e : ((joinUp c g o k).st.groups[g']?).map (fun _ => ()) =
      (c.st.groups[g']?).map fun _ => () := by
    rw [joinUp_groups]
    exact modAt_read _ _ _ _ _ fun _ => rfl
  rw [hG] at e
  obtain ⟨G', hG', _⟩ := Option.map_eq_some_iff.1 e
  exact ⟨G', hG'⟩

/-- What the tests from 2 to 8 give on the two groups: they are two, and both are there. -/
theorem carriedB_groups {a : Sh2} {mU mO : List Nat} (h : carriedB P a mU mO = true) :
    a.lin.gU ≠ a.lin.gOmega ∧ (∃ G, a.core.st.groups[a.lin.gU]? = some G) ∧
      ∃ G, a.core.st.groups[a.lin.gOmega]? = some G := by
  unfold carriedB at h
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨h.1.1.2, groupB_some h.1.2, groupB_some h.2⟩

/-- From 2 to 8 the test on the state holds Carried's. -/
theorem stateB_carried {b : Nat} {a : Sh2} (h2 : 2 ≤ b) (h8 : b ≤ 8) (h : stateB P b a = true) :
    ∃ mU mO, carriedB P a mU mO = true := by
  match b, h2, h8, h with
  | 2, _, _, h => exact ⟨_, _, (Bool.and_eq_true _ _ ▸ h).1⟩
  | 3, _, _, h =>
    have h' : (carriedB P a [] [] && hasUB P a && keyB a.lin _) = true := h
    simp only [Bool.and_eq_true] at h'
    exact ⟨_, _, h'.1.1⟩
  | 4, _, _, h => exact ⟨_, _, (Bool.and_eq_true _ _ ▸ h).1⟩
  | 5, _, _, h => exact ⟨_, _, (Bool.and_eq_true _ _ ▸ h).1⟩
  | 6, _, _, h =>
    have h' : (carriedB P a [a.lin.oU] [] && hasUB P a && hasOB P a) = true := h
    simp only [Bool.and_eq_true] at h'
    exact ⟨_, _, h'.1.1⟩
  | 7, _, _, h =>
    have h' : (carriedB P a [a.lin.oU, a.lin.oSp] [a.lin.oOmega, a.lin.oSp] && hasUB P a &&
      hasOB P a) = true := h
    simp only [Bool.and_eq_true] at h'
    exact ⟨_, _, h'.1.1⟩
  | 8, _, _, h =>
    have h' : (carriedB P a [a.lin.oU, a.lin.oSp] [a.lin.oOmega, a.lin.oSp] && hasUB P a &&
      hasOB P a && a.lin.zFd == P.par.S.kRow) = true := h
    simp only [Bool.and_eq_true] at h'
    exact ⟨_, _, h'.1.1.1⟩

/-! ## Laws on shapes: what lies on the two groups, and what stands behind "SPLIT" -/

/-- **What lies on the two groups, handed on by the update**: a law on shapes: no state is named. At
3, 4 and 8 it asks the facts' half of the test too. -/
theorem kinds_up (a : Sh2) :
    (kindsB P 2 (updS P sentU 1 a) = true) ∧
    (kindsB P 2 a = true → kindsB P 3 (updS P sentU 2 a) = true) ∧
    (stateB P 3 a = true → kindsB P 3 a = true → kindsB P 4 (updS P sentU 3 a) = true) ∧
    (stateB P 4 a = true → kindsB P 4 a = true → kindsB P 5 (updS P sentU 4 a) = true) ∧
    (kindsB P 5 a = true → kindsB P 6 (updS P sentU 5 a) = true) ∧
    (kindsB P 6 a = true → kindsB P 7 (updS P sentU 6 a) = true) ∧
    (kindsB P 7 a = true → kindsB P 8 (updS P sentU 7 a) = true) ∧
    (stateB P 8 a = true → kindsB P 8 a = true → kindsB P 9 (updS P sentU 8 a) = true) := by
  unfold kindsB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, fun h => ?_, fun hs h => ?_, fun hs h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun hs h => ?_⟩
  · constructor
    · show kindsAt (groupUp (groupUp a.core _ _) _ _) a.core.st.groups.length = _
      simp [kindsAt, groupUp, kindsU]
    · show kindsAt (groupUp (groupUp a.core _ _) _ _) (a.core.st.groups.length + 1) = _
      simp [kindsAt, groupUp, kindsO]
  · exact ⟨h.1.trans (by simp [kindsU]), h.2⟩
  · obtain ⟨mU, mO, hc⟩ := stateB_carried (by omega) (by omega) hs
    obtain ⟨hne, ⟨GU, hU⟩, _⟩ := carriedB_groups hc
    obtain ⟨G', hG'⟩ := some_joinUp a.core a.lin.gU a.lin.oU false a.lin.gU hU
    constructor
    · show kindsAt (rowsUp (joinUp a.core a.lin.gU a.lin.oU false) a.lin.gU _) a.lin.gU = _
      rw [kindsAt_rowsUp _ _ _ hG', kindsAt_joinUp, h.1]
      simp [kindsU]
    · show kindsAt (rowsUp (joinUp a.core a.lin.gU a.lin.oU false) a.lin.gU _) a.lin.gOmega = _
      rw [kindsAt_rowsUp_ne _ _ _ _ (Ne.symm hne), kindsAt_joinUp, h.2]
      rfl
  · obtain ⟨mU, mO, hc⟩ := stateB_carried (by omega) (by omega) hs
    obtain ⟨hne, ⟨GU, hU⟩, _⟩ := carriedB_groups hc
    constructor
    · show kindsAt (rowsUp a.core a.lin.gU _) a.lin.gU = _
      rw [kindsAt_rowsUp _ _ _ hU, h.1]
      simp [kindsU]
    · show kindsAt (rowsUp a.core a.lin.gU _) a.lin.gOmega = _
      rw [kindsAt_rowsUp_ne _ _ _ _ (Ne.symm hne), h.2]
      rfl
  · exact ⟨h.1.trans (by simp [kindsU]), h.2⟩
  · constructor
    · show kindsAt (joinUp (joinUp (joinUp a.core _ _ _) _ _ _) _ _ _) a.lin.gU = _
      rw [kindsAt_joinUp, kindsAt_joinUp, kindsAt_joinUp, h.1]
      simp [kindsU]
    · show kindsAt (joinUp (joinUp (joinUp a.core _ _ _) _ _ _) _ _ _) a.lin.gOmega = _
      rw [kindsAt_joinUp, kindsAt_joinUp, kindsAt_joinUp, h.2]
      rfl
  · exact ⟨h.1.trans (by simp [kindsU]), h.2⟩
  · obtain ⟨mU, mO, hc⟩ := stateB_carried (by omega) (by omega) hs
    obtain ⟨hne, ⟨GU, hU⟩, GO, hO⟩ := carriedB_groups hc
    have hO' : (maskUp a.core a.lin.oSp).st.groups[a.lin.gOmega]? = some GO := hO
    have hU' : (rowsUp (maskUp a.core a.lin.oSp) a.lin.gOmega [.plain]).st.groups[a.lin.gU]? =
        some GU := by
      rw [rowsUp_groups, modAt_get_ne _ _ _ _ hne]
      exact hU
    constructor
    · show kindsAt (rowsUp (rowsUp (maskUp a.core a.lin.oSp) a.lin.gOmega _) a.lin.gU _)
        a.lin.gU = _
      rw [kindsAt_rowsUp _ _ _ hU', kindsAt_rowsUp_ne _ _ _ _ hne]
      show kindsAt a.core a.lin.gU ++ _ = _
      rw [h.1]
      simp [kindsU]
    · show kindsAt (rowsUp (rowsUp (maskUp a.core a.lin.oSp) a.lin.gOmega _) a.lin.gU _)
        a.lin.gOmega = _
      rw [kindsAt_rowsUp_ne _ _ _ _ (Ne.symm hne), kindsAt_rowsUp _ _ _ hO']
      show kindsAt a.core a.lin.gOmega ++ _ = _
      rw [h.2]
      rfl

/-- **What stands behind "SPLIT"**: a law on shapes. -/
theorem state9_up (a : Sh2) (h : stateB P 8 a = true) : stateB P 9 (splitUp a) = true := by
  have h' : (carriedB P a [a.lin.oU, a.lin.oSp] [a.lin.oOmega, a.lin.oSp] && hasUB P a &&
    hasOB P a && a.lin.zFd == P.par.S.kRow) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨hc, hu⟩, ho⟩, hz⟩ := h'
  unfold hasOB at ho
  rw [Bool.and_eq_true] at ho
  obtain ⟨hom, hl⟩ := ho
  have gB : ∀ g code z ms, groupB (splitUp a).core.st g code z ms = groupB a.core.st g code z ms :=
    fun g code z ms => by
      show groupB (rowsUp (rowsUp (maskUp a.core a.lin.oSp) _ _) _ _).st g code z ms = _
      rw [groupB_rowsUp, groupB_rowsUp]
      rfl
  have mB : ∀ o s, msgB (splitUp a).core.st o s = msgB a.core.st o s := fun o s =>
    msgB_maskUp a.core a.lin.oSp o s
  show (carriedB P (splitUp a) [a.lin.oU, a.lin.oSp] [a.lin.oOmega, a.lin.oSp] &&
    hasUB P (splitUp a) && hasOmB P (splitUp a) &&
    ledB (splitUp a) ((Slice.freshLedger a.core.st.codes P.par.S.sharedSplit).map ledNext) &&
    a.lin.zFd == P.par.S.kRow) = true
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hz⟩
  · unfold carriedB at hc ⊢
    rw [gB, gB]
    have hlen : (splitUp a).core.st.oracles.length = a.core.st.oracles.length := by
      show (maskUp a.core a.lin.oSp).st.oracles.length = _
      rw [maskUp_oracles, modAt_length]
    rw [hlen]
    exact hc
  · unfold hasUB at hu ⊢
    rw [mB]
    exact hu
  · unfold hasOmB at hom ⊢
    rw [mB, mB]
    exact hom
  · unfold ledB at hl ⊢
    show (match (maskUp a.core a.lin.oSp).st.oracles[a.lin.oSp]? with
      | some x => decide (x.ledger = _)
      | none => true) = true
    rw [maskUp_oracles, modAt_get]
    cases hx : a.core.st.oracles[a.lin.oSp]? with
    | none => rfl
    | some x =>
      rw [hx] at hl
      have e : x.ledger = Slice.freshLedger a.core.st.codes P.par.S.sharedSplit := by
        simpa using hl
      exact decide_eq_true (congrArg (Option.map ledNext) e)

/-! ## Laws on states: from the test in front to the step's return and the test behind -/

open Desc.K14.Honest (returns1 returns2 returns3 returns4 returns5 returns6 returns7 returns8
  facts_first firstW keyW key_fits)

/-- **Under PlanFacts (hP) and the two sendings' test on the plan (hBU, hBO: planOkOwn): the facts'
half of the test in front, and the library's Block.Fits: the step returns, and at 1 to 7 the facts'
half behind is passed.** At "(rec_gamma)" beside: no seed of the key has the factor 0. B (Eight P):
that the eight are there follows from hP's clause on what goes out with o_u, by the library's
blocks_eight (Johnson/Desc/K14/Law/BlocksEight.lean), which is not called here; B is taken so that
the steps can be named. -/
theorem state_next (hP : PlanFacts P.par P.codes sentU layO)
    (hBU : planOkOwn (parU P sentU) = true) (hBO : planOkOwn (parO P) = true) (B : Eight P)
    (ft : Nat) (d : St) (rs : List Fmt.RoundView) (c : List OpenedColumn) :
    (stateB P 1 (sh2 d) = true → B.b1.Fits ft rs c →
      ∃ d', B.b1.step ft d rs c = .ok (d', (B.b1.want ft rs).length) ∧
        stateB P 2 (sh2 d') = true) ∧
    (stateB P 2 (sh2 d) = true → B.b2.Fits ft rs c →
      ∃ d', B.b2.step ft d rs c = .ok (d', (B.b2.want ft rs).length) ∧
        stateB P 3 (sh2 d') = true) ∧
    (stateB P 3 (sh2 d) = true → (d.loc.key.seeds.all (!allZero ·.beta)) = true →
      B.b3.Fits ft rs c →
      ∃ d', B.b3.step ft d rs c = .ok (d', (B.b3.want ft rs).length) ∧
        stateB P 4 (sh2 d') = true) ∧
    (stateB P 4 (sh2 d) = true → B.b4.Fits ft rs c →
      ∃ d', B.b4.step ft d rs c = .ok (d', (B.b4.want ft rs).length) ∧
        stateB P 5 (sh2 d') = true) ∧
    (stateB P 5 (sh2 d) = true → B.b5.Fits ft rs c →
      ∃ d', B.b5.step ft d rs c = .ok (d', (B.b5.want ft rs).length) ∧
        stateB P 6 (sh2 d') = true) ∧
    (stateB P 6 (sh2 d) = true → B.b6.Fits ft rs c →
      ∃ d', B.b6.step ft d rs c = .ok (d', (B.b6.want ft rs).length) ∧
        stateB P 7 (sh2 d') = true) ∧
    (stateB P 7 (sh2 d) = true → B.b7.Fits ft rs c →
      ∃ d', B.b7.step ft d rs c = .ok (d', (B.b7.want ft rs).length) ∧
        stateB P 8 (sh2 d') = true) ∧
    (stateB P 8 (sh2 d) = true → B.b8.Fits ft rs c →
      ∃ d', B.b8.step ft d rs c = .ok (d', (B.b8.want ft rs).length)) := by
  refine ⟨fun g hF => ?_, fun g hF => ?_, fun g hbeta hF => ?_, fun g hF => ?_, fun g hF => ?_,
    fun g hF => ?_, fun g hF => ?_, fun g hF => ?_⟩
  · obtain ⟨hf, hk⟩ := (stateB_iff P d).1.1 g
    obtain ⟨d', hs, C⟩ := returns1 hP B ft d rs c hf hF
    have e : d'.loc.key = d.loc.key := Carried.key C
    refine ⟨d', hs, (stateB_iff P d').2.1.2 ?_⟩
    rw [e]
    exact ⟨C, hk⟩
  · obtain ⟨hf, hk⟩ := (stateB_iff P d).2.1.1 g
    obtain ⟨d', hs, C⟩ := returns2 hP hBU B ft d rs c hf hF
    have e : d'.loc.key = d.loc.key := Carried.key C.1
    refine ⟨d', hs, (stateB_iff P d').2.2.1.2 ?_⟩
    rw [e]
    exact ⟨C, hk⟩
  · obtain ⟨hf, hk⟩ := (stateB_iff P d).2.2.1.1 g
    obtain ⟨d', hs, C⟩ := returns3 hP B ft d rs c hf hk hbeta hF
    have e : d'.loc.key = d.loc.key := Carried.key C.1
    refine ⟨d', hs, (stateB_iff P d').2.2.2.1.2 ?_⟩
    rw [e]
    exact C
  · have hf := (stateB_iff P d).2.2.2.1.1 g
    obtain ⟨d', hs, C⟩ := returns4 hP B ft d rs c hf hF
    have e : d'.loc.key = d.loc.key := Carried.key C.1
    refine ⟨d', hs, (stateB_iff P d').2.2.2.2.1.2 ?_⟩
    rw [e]
    exact C
  · have hf := (stateB_iff P d).2.2.2.2.1.1 g
    obtain ⟨d', hs, C⟩ := returns5 hP hBO B ft d rs c hf hF
    have e : d'.loc.key = d.loc.key := Carried.key C.1
    refine ⟨d', hs, (stateB_iff P d').2.2.2.2.2.1.2 ?_⟩
    rw [e]
    exact C
  · have hf := (stateB_iff P d).2.2.2.2.2.1.1 g
    obtain ⟨d', hs, C⟩ := returns6 hP B ft d rs c hf hF
    have e : d'.loc.key = d.loc.key := Carried.key C.1
    refine ⟨d', hs, (stateB_iff P d').2.2.2.2.2.2.1.2 ?_⟩
    rw [e]
    exact C
  · have hf := (stateB_iff P d).2.2.2.2.2.2.1.1 g
    obtain ⟨d', hs, C⟩ := returns7 hP B ft d rs c hf hF
    have e : d'.loc.key = d.loc.key := Carried.key C.1
    refine ⟨d', hs, (stateB_iff P d').2.2.2.2.2.2.2.2 ?_⟩
    rw [e]
    exact C
  · exact returns8 hP B ft d rs c ((stateB_iff P d).2.2.2.2.2.2.2.1 g) hF

/-! ## The first shape -/

/-- **All keys whose sizes fit have one shape at the chain's first state**: the written
example's. -/
theorem first_shape (P : P14) (key : TableKey) (hk : keyFits key P.par.S.fold.index = true) :
    sh2 (first P.codes key) = sh2 (firstW P) := by
  have hw := key_fits P.par.S.fold.index
  unfold keyFits at hk hw
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hk hw
  have e1 : key.record.size = (keyW P.par.S.fold.index).record.size := hk.1.1.trans hw.1.1.symm
  have e2 : key.seeds.map (·.z.length) = (keyW P.par.S.fold.index).seeds.map (·.z.length) := by
    rw [List.eq_replicate_of_mem (l := key.seeds.map (·.z.length))
        (a := P.par.S.fold.index.cubeBits) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hk.2 y hy),
      List.eq_replicate_of_mem (l := (keyW P.par.S.fold.index).seeds.map (·.z.length))
        (a := P.par.S.fold.index.cubeBits) (by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact hw.2 y hy), List.length_map, List.length_map, hk.1.2, hw.1.2]
  show Sh2.mk _ { linSh (first P.codes key).loc with
      record := key.record.size, seeds := key.seeds.map (·.z.length) } =
    Sh2.mk _ { linSh (firstW P).loc with
      record := (keyW P.par.S.fold.index).record.size
      seeds := (keyW P.par.S.fold.index).seeds.map (·.z.length) }
  rw [e1, e2]
  rfl

/-- The chain's first state passes the test at the border 1, where the key's sizes fit. -/
theorem facts_start (P : P14) (key : TableKey) (hk : keyFits key P.par.S.fold.index = true) :
    factsB P 1 (sh2 (first P.codes key)) = true :=
  (factsB_iff P 1 _).2 ⟨(stateB_iff P (first P.codes key)).1.2 ⟨facts_first P key, hk⟩,
    fun h => by omega⟩

end Desc.K14.Shape

#print axioms Desc.K14.Shape.stepCarries
#print axioms Desc.K14.Shape.modAt_get_ne
#print axioms Desc.K14.Shape.modAt_length
#print axioms Desc.K14.Shape.modAt_read
#print axioms Desc.K14.Shape.groupB_congr
#print axioms Desc.K14.Shape.msgB_congr
#print axioms Desc.K14.Shape.groupB_some
#print axioms Desc.K14.Shape.rowsUp_groups
#print axioms Desc.K14.Shape.joinUp_groups
#print axioms Desc.K14.Shape.maskUp_oracles
#print axioms Desc.K14.Shape.groupB_rowsUp
#print axioms Desc.K14.Shape.msgB_maskUp
#print axioms Desc.K14.Shape.kindsAt_rowsUp
#print axioms Desc.K14.Shape.kindsAt_rowsUp_ne
#print axioms Desc.K14.Shape.kindsAt_joinUp
#print axioms Desc.K14.Shape.some_joinUp
#print axioms Desc.K14.Shape.carriedB_groups
#print axioms Desc.K14.Shape.stateB_carried
#print axioms Desc.K14.Shape.kinds_up
#print axioms Desc.K14.Shape.state9_up
#print axioms Desc.K14.Shape.state_next
#print axioms Desc.K14.Shape.first_shape
#print axioms Desc.K14.Shape.facts_start
