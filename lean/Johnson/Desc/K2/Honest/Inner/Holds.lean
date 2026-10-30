-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/Holds.lean: EVERY ROW THAT A CODE SWITCH BETWEEN TWO SEGMENTS LAYS SAYS
TRUE OF THE HONEST NEW MESSAGES: the proof of `SwitchRowsHold`
(Johnson/Desc/K2/Honest/Inner/Statement.lean). Statements and proofs.

  `mem_keptFrom`    which kept row a row of the list of kept rows' generator rows is
  `copies_in`       each copy's number names a message of the statement
  `listed_at`       a draw's number in the list of positions
  `keptList_len`    the list of kept rows has as many entries as the single rows count
  `switchRowsHold`  `SwitchRowsHold`

The five sorts of rows: Inner/CarriedHold.lean, SampleHold.lean, GenRows.lean (two), KeptHold.lean.
Which row is of which sort: `laid_of` (Johnson/Top/H0/K2Hands/RowsAt.lean), `switchCarried_iff`
(RowsOrder.lean), `switchGenerators_all` (Johnson/Top/H0/H2K/GenRowsAt.lean).

Limits. What the statement's head says. It is a lemma on rows and words: no coin, no round, no
frame, no decision. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.CarriedHold
import Johnson.Desc.K2.Honest.Inner.SampleHold
import Johnson.Desc.K2.Honest.Inner.KeptHold
import OnBytes.Slice.BlkCsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE readE codeOf genMain genMask symAtB)
open OnBytes.Means (Says)
open Johnson.Prover.Send (Rows)
open Johnson.Prover.Link (symG)
open H2K.Lift (genKept keptFrom)

/-- Which kept row a row of the list of kept rows' generator rows is. -/
theorem mem_keptFrom (Fr : SwitchFrame) (x : Nat) (sy : Nat → E) (r : OnBytes.Row) :
    ∀ (ks : List KeptPlace) (n : Nat), r ∈ keptFrom Fr x sy ks n →
      ∃ (a : Nat) (k : KeptPlace) (b : Nat), ks[a]? = some k ∧ b < k.rows ∧
        r = genKept Fr k b (n + (((ks.take a).map (·.rows)).sum + b)) x
          (sy (1 + (n + (((ks.take a).map (·.rows)).sum + b))))
  | [], _, h => by simp [keptFrom] at h
  | k :: ks, n, h => by
    rw [keptFrom, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
      exact ⟨0, k, b, rfl, List.mem_range.1 hb, by simp⟩
    · obtain ⟨a, k', b, hk, hb, rfl⟩ := mem_keptFrom Fr x sy r ks (n + k.rows) h
      refine ⟨a + 1, k', b, hk, hb, ?_⟩
      have e : n + k.rows + (((ks.take a).map (·.rows)).sum + b) =
          n + ((((k :: ks).take (a + 1)).map (·.rows)).sum + b) := by
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega
      rw [e]

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- Each copy's number names a message of the statement. -/
theorem copies_in (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) : ∀ o ∈ anew.toList, o < S.oracles.size := by
  intro o ho
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 ho
  obtain ⟨_, _, _, hsz, _⟩ := _root_.Tw.K2.frame_inv hFr
  have hsz' : anew.size = (switchKept old).size := by simpa using hsz
  have hlt : a < anew.size := by
    have := (List.getElem?_eq_some_iff.1 ha).1
    rwa [Array.length_toList] at this
  have hk : a < T.kept.size := by
    have := A.target.keptCount
    omega
  have hc := A.seated.copies a T.kept[a] (Array.getElem?_eq_getElem hk)
  have ha' : anew[a]? = some o := by rw [← Array.getElem?_toList]; exact ha
  rw [ha'] at hc
  obtain ⟨x, hx, _⟩ := Option.map_eq_some_iff.1 hc
  exact (Array.getElem?_eq_some_iff.1 hx).1

/-- A draw's number in the list of positions. -/
theorem listed_at (pos : Positions) (x : Nat) (h : (pos.indexOf x).isSome = true) :
    ∃ i, pos.indexOf x = some i ∧ i < pos.all.size ∧ pos.all.getD i 0 = x := by
  have hx : x ∈ pos.all := by
    unfold Positions.indexOf at h
    simpa using h
  exact OnBytes.Slice.indexOf_some pos x hx

/-- The list of kept rows has as many entries as the single rows count. -/
theorem keptList_len (A : AtSwitch S old T g anew W V) :
    ((sizesAt S old T).kept.zipIdx.flatMap fun s =>
      (List.range s.1.mainRows).map fun b => (s.2, b)).length = old.keptRows := by
  rw [List.length_flatMap, A.fits.rows]
  have e : ((sizesAt S old T).kept.zipIdx.map fun s : OracleShape × Nat =>
      ((List.range s.1.mainRows).map fun b => (s.2, b)).length) =
      (sizesAt S old T).kept.zipIdx.map fun s => (fun t : OracleShape => t.mainRows) s.1 := by
    apply List.map_congr_left
    intro s _
    simp
  rw [e, Lists.map_zipIdx_fst]
  show (((switchKept old).toList.map fun o => (S.oracles.getD o default).shape).map
    fun t : OracleShape => t.mainRows).sum = _
  rw [List.map_map]
  rfl

/-- **Every row that the switch lays says true of the honest new messages.** -/
theorem switchRowsHold : SwitchRowsHold := by
  intro S old T g anew pos y rows W V hcheck hrest hfits hpos hseat hlen hlogC hlogZ hx hrows
    hhonest hclaim hsamples hsym r hr
  have A : AtSwitch S old T g anew W V := ⟨hcheck, hrest, hfits, hpos, hseat, hlen, hhonest⟩
  obtain ⟨Fr, carried, L⟩ := VerifiableInference.Desc.First.K2Hands.laid_of
    (show switchRows S old T g anew pos y = some rows from hrows)
  have hFr := L.frame
  have hn := copies_in A hFr
  have hm := A.target.masks
  rw [L.rows, List.cons_append, List.mem_cons, List.mem_append] at hr
  rcases hr with hr | hr | hr
  · -- the claim carried over
    obtain ⟨ks, hks, hc⟩ :=
      (VerifiableInference.Desc.First.K2Hands.switchCarried_iff Fr old carried).1 L.claim
    rw [hr, hc]
    exact carried_holds A hn hFr ks hks hclaim
  · -- a stored sample row carried over
    obtain ⟨k, hk, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨sample, hsm, rfl⟩ := List.mem_map.1 hr
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hk
    obtain ⟨_, _, _, _, _, _, _, _, _, e6, _⟩ := kept_at hFr a k ha
    exact sample_holds A hn hFr a k ha sample hsm (L.reads k hk sample hsm)
      (hsamples k.old (List.mem_of_getElem? e6) sample hsm)
  · -- a draw's generator rows
    obtain ⟨x, hxm, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨i, hi, hlt, hget⟩ := listed_at pos x (L.listed x hxm)
    have hxin : x ∈ pos.all.toList := by
      rw [← hget, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
      exact Array.getElem_mem_toList hlt
    have hxlt := hx x hxin
    have hsy : ∀ j, symAtB old pos y x j = y.getD (i * old.rows + j) zeroE := by
      intro j
      unfold symAtB
      rw [hi]
      rfl
    rw [H2K.Lift.switchGenerators_all, List.cons_append, List.mem_cons, List.mem_append] at hr
    rcases hr with hr | hr | hr
    · -- the main row
      rw [hr]
      apply main_holds A hn hFr hlogC x hxlt
      rw [hsy 0]
      have h := hsym i 0 hlt (by unfold SingleRows.rows; omega)
      rw [if_pos (by unfold SingleRows.rows; omega), hget] at h
      exact h
    · -- a kept row
      obtain ⟨a, k, b, hk, hb, hr⟩ := mem_keptFrom Fr x _ r Fr.kept 0 hr
      rw [hr]
      simp only [Nat.zero_add]
      apply keptGen_holds A hn hFr hlogC a k hk b hb x hxlt
      rw [hsy]
      have hno := keptNo_lt A hFr a k hk b hb
      have h := hsym i (1 + (((Fr.kept.take a).map (·.rows)).sum + b)) hlt
        (by unfold SingleRows.rows; omega)
      rw [if_pos (by unfold SingleRows.rows; omega), hget] at h
      have hrow : rowOfComplex (sizesAt S old T) W
          (1 + (((Fr.kept.take a).map (·.rows)).sum + b)) =
          (codeOf (S.codes.base.getD old.code default), (W.kept a).main b, (W.kept a).tail b) := by
        unfold rowOfComplex
        simp only
        rw [if_neg (by simp), Nat.add_sub_cancel_left, keptRow_at hFr a k hk b hb]
        rfl
      rw [hrow] at h
      exact h
    · -- a mask row
      obtain ⟨jj, hjj, hr⟩ := List.mem_map.1 hr
      have hj2 : jj < 2 := by
        have := List.mem_range.1 hjj
        omega
      rw [← hr]
      apply mask_holds A hn hFr hlogZ jj hj2 x
      rw [hsy]
      have h := hsym i (old.maskRow jj) hlt
        (by unfold SingleRows.rows SingleRows.maskRow; omega)
      rw [if_neg (by unfold SingleRows.rows SingleRows.maskRow; omega), hget] at h
      have hrow : rowOfComplex (sizesAt S old T) W (old.maskRow jj) =
          (codeOf (S.codes.mask.getD old.maskCode default), W.mask jj, W.maskTail jj) := by
        unfold rowOfComplex SingleRows.maskRow
        simp only
        rw [if_neg (by simp), List.getElem?_eq_none (by rw [keptList_len A]; omega),
          keptList_len A]
        have e : 1 + old.keptRows + jj - 1 - old.keptRows = jj := by omega
        simp only [e]
        rfl
      rw [hrow] at h
      exact h

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.switchRowsHold
