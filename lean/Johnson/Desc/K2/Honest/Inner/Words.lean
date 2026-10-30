-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/Words.lean: WHICH WORD STANDS WHERE IN THE HONEST NEW MESSAGES OF A
CODE SWITCH BETWEEN TWO SEGMENTS: the words of Johnson/Desc/K2/Honest/Inner/Statement.lean's
`newWords`, at the indices that the switch's rows read. Statements and proofs. No coin, no round, no
frame.

  `AtSwitch`, `AtSwitch.target`   the public premises of `SwitchRowsHold`, with `HonestMain`, as one
                 structure; what the program's test on the target means
  `Lists.idxOf_at`     the number of an entry of a list without repeats
  `word_g`       the carrying message's word at an index of a real row, a real place and no pad:
                 what Carrying.lean lays there
  `main_no_pad`, `rest_fits`   no index in the main block is a pad's; the rest is no longer than
                 its places
  `word_main`    at `cutIndex`'s index of j: entry j of the folded main row
  `word_rest`    at `SwitchPlaces.get`'s index of i: entry i of the rest
  `word_copy`    a copy's word at an index of its table that is no pad's: the kept member's own
                 entry

By: Inner/LaidBackProof.lean's two theorems; what the program's test on a target means
(`targetOk_means`, Johnson/Top/H0/Tw/K2/TargetMeans.lean); `places_of_check`, `padPlaces_eq`,
`cutIndex_mod`, `cutIndex_div` (OnBytes/Slice/SwitchPlacesLaws.lean).

Limits. Nothing on the rows. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.Statement
import Johnson.Desc.K2.Honest.Inner.LaidBackProof
import Johnson.Desc.K2.Honest.Inner.RestIsPartsProof
import Johnson.Top.H0.Tw.K2.TargetMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE)
open Johnson.Prover.Send (Rows)

/-- The public premises of `SwitchRowsHold`, with `HonestMain`. -/
structure AtSwitch (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (W : Left) (V : Nat → Rows) : Prop where
  check : switchTargetCheck S old T = true
  restMain : T.rest.part = .main
  fits : OldFits S old
  keptPos : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows
  seated : SeatedAt S old T g anew
  lengths : S.codes.lengthsOk = true
  honest : HonestMain (sizesAt S old T) W V

/-- What the program's test on the target means. -/
theorem AtSwitch.target {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {W : Left} {V : Nat → Rows} (A : AtSwitch S old T g anew W V) :
    _root_.Tw.K2.TargetFits S old T :=
  (_root_.Tw.K2.targetOk_means S old T).1 ((_root_.Tw.K2.targetOk_eq S old T).trans A.check)

/-- The number of an entry of a list without repeats. -/
theorem Lists.idxOf_at : ∀ (l : List Nat) (a o : Nat), l.Nodup → l[a]? = some o →
    l.idxOf? o = some a
  | [], _, _, _, h => by simp at h
  | x :: l, 0, o, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [List.idxOf?_cons]
  | x :: l, a + 1, o, hn, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.nodup_cons] at hn
    have hne : x ≠ o := fun e => hn.1 (e ▸ List.mem_of_getElem? h)
    rw [List.idxOf?_cons, Lists.idxOf_at l a o hn.2 h]
    simp [hne]

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- The carrying message's word at an index of a real row, a real place and no pad. -/
theorem word_g (A : AtSwitch S old T g anew W V) (J : Nat)
    (hb : J % 2 ^ ceilLog2 T.shape.mainRows < T.shape.mainRows)
    (hj : J / 2 ^ ceilLog2 T.shape.mainRows < (S.codes.base.getD T.shape.code default).ell)
    (hp : J ∉ ((padPlaces S.codes T.shape).filter fun p => p.part == .main).map (·.index)) :
    newWords (sizesAt S old T) g anew V g .main J =
      carryingAt (sizesAt S old T) W (fun _ _ _ => zeroG) .main J := by
  have h := A.honest 0 (Nat.zero_le _) (J % 2 ^ ceilLog2 T.shape.mainRows)
    (J / 2 ^ ceilLog2 T.shape.mainRows) hb hj
    (by
      have e : J % 2 ^ ceilLog2 T.shape.mainRows +
          J / 2 ^ ceilLog2 T.shape.mainRows * 2 ^ ceilLog2 T.shape.mainRows = J := by
        rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
      show J % 2 ^ ceilLog2 T.shape.mainRows +
          J / 2 ^ ceilLog2 T.shape.mainRows * 2 ^ ceilLog2 T.shape.mainRows ∉ _
      rw [e]
      exact hp)
  show (if g = g then (V 0).word T.shape .main J else _) = _
  rw [if_pos rfl]
  show (if J % 2 ^ ceilLog2 T.shape.mainRows < T.shape.mainRows then
    (V 0).main (T.shape.mainDeg == 3) (J % 2 ^ ceilLog2 T.shape.mainRows)
      (J / 2 ^ ceilLog2 T.shape.mainRows) else 0) = _
  rw [if_pos hb]
  exact h

/-- No index in the main block is a pad's. -/
theorem main_no_pad (A : AtSwitch S old T g anew W V) (J : Nat)
    (hr : J % 2 ^ ceilLog2 T.shape.mainRows < 2 ^ T.main.bits) :
    J ∉ ((padPlaces S.codes T.shape).filter fun p => p.part == .main).map (·.index) := by
  have F := A.target
  have fill := F.fill
  unfold _root_.Tw.K2.BlocksFill at fill
  rw [A.restMain] at fill
  obtain ⟨_, _, _, hsum⟩ := fill
  have hpos : 0 < 2 ^ T.rest.bits := Nat.two_pow_pos _
  intro hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
  obtain ⟨hp, hpm⟩ := List.mem_filter.1 hp
  have hpm : p.part = .main := by simpa using hpm
  obtain ⟨part, base, h | h⟩ := SwitchPlaces.padPlaces_eq S.codes T.shape F.degree
  · rw [h] at hp; simp at hp
  · rw [h] at hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
    simp only at hpm hr
    subst hpm
    have hlt : T.shape.mainRows - 1 < 2 ^ ceilLog2 T.shape.mainRows := by
      have := SwitchPlaces.le_two_pow_ceilLog2' T.shape.mainRows
      have := F.rows
      omega
    have e : (T.shape.rows .main - 1 + (base + i) * 2 ^ ceilLog2 (T.shape.rows .main)) %
        2 ^ ceilLog2 T.shape.mainRows = T.shape.mainRows - 1 := by
      show (T.shape.mainRows - 1 + (base + i) * 2 ^ ceilLog2 T.shape.mainRows) % _ = _
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    rw [e] at hr
    omega

/-- At `cutIndex`'s index of j: entry j of the folded main row. -/
theorem word_main (A : AtSwitch S old T g anew W V) (j : Nat)
    (hj : j < (S.codes.base.getD old.code default).ell) :
    newWords (sizesAt S old T) g anew V g .main
      (cutIndex T.main (switchRowBits T .main) j) = W.main j := by
  have F := A.target
  obtain ⟨_, _, hM⟩ := SwitchPlaces.of_check A.check
  rw [F.mainPart] at hM
  have fill := F.fill
  unfold _root_.Tw.K2.BlocksFill at fill
  rw [A.restMain] at fill
  obtain ⟨_, h0, _, hsum⟩ := fill
  have hmod := cutIndex_mod hM j
  have hdiv := cutIndex_div hM j
  have hlt : j % 2 ^ T.main.bits < 2 ^ T.main.bits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpos : 0 < 2 ^ T.rest.bits := Nat.two_pow_pos _
  have hrb : switchRowBits T .main = ceilLog2 T.shape.mainRows := rfl
  rw [hrb] at hmod hdiv
  rw [word_g A _ (by rw [hrb, hmod, h0]; omega)
    (by
      rw [hrb, hdiv]
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact Nat.lt_of_lt_of_le hj F.mainRoom))
    (main_no_pad A _ (by rw [hrb, hmod, h0]; omega))]
  exact carrying_main (sizesAt S old T) W _ hM j hj

/-- The rest is no longer than its places. -/
theorem rest_fits (A : AtSwitch S old T g anew W V) :
    (rest (sizesAt S old T) W).length ≤ (SwitchPlaces.make S.codes T).size := by
  have h := (restIsParts S old T W A.target.masks A.fits).1
  rw [h]
  exact A.target.restRoom

/-- At `SwitchPlaces.get`'s index of i: entry i of the rest. -/
theorem word_rest (A : AtSwitch S old T g anew W V) (i : Nat)
    (hi : i < (rest (sizesAt S old T) W).length) :
    newWords (sizesAt S old T) g anew V g .main ((SwitchPlaces.make S.codes T).get i) =
      (rest (sizesAt S old T) W).getD i zeroG := by
  have F := A.target
  obtain ⟨_, hR, _⟩ := SwitchPlaces.of_check A.check
  obtain ⟨_, hrow, hplace, hpad⟩ := SwitchPlaces.places_of_check A.check
  have fill := F.fill
  unfold _root_.Tw.K2.BlocksFill at fill
  rw [A.restMain] at fill
  obtain ⟨_, h0, h1, hsum⟩ := fill
  have hr := hrow i
  have hpl := hplace i (Nat.lt_of_lt_of_le hi (rest_fits A))
  rw [A.restMain] at hr hpl
  have hrb : switchRowBits T .main = ceilLog2 T.shape.mainRows := rfl
  rw [hrb] at hr hpl
  rw [word_g A _ (by omega) hpl
    (by
      intro hm
      obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
      obtain ⟨hp, hpm⟩ := List.mem_filter.1 hp
      have hpm : p.part = .main := by simpa using hpm
      exact hpad i p hp (hpm.trans A.restMain.symm) e.symm)]
  have h := carrying_rest (sizesAt S old T) W (fun _ _ _ => zeroG) hR
    (SwitchPlaces.make_pad_rises S.codes T F.degree) (fun _ => Or.inl (by
      show T.main.firstRow + 2 ^ T.main.bits ≤ T.rest.firstRow
      rw [h0, h1]; omega)) i hi
  have e : (sizesAt S old T).target.rest.part = .main := A.restMain
  rw [e] at h
  exact h

/-- A copy's word at an index of its table that is no pad's: the kept member's own entry. -/
theorem word_copy (A : AtSwitch S old T g anew W V) (a : Nat) (s : OracleShape) (o : Nat)
    (hs : (sizesAt S old T).kept[a]? = some s) (ho : anew.toList[a]? = some o) (J : Nat)
    (hJ : J < 2 ^ (ceilLog2 s.mainRows + (S.codes.base.getD old.code default).logEll))
    (hp : J ∉ ((padPlaces S.codes s).filter fun p => p.part == .main).map (·.index)) :
    newWords (sizesAt S old T) g anew V o .main J = (W.kept a).entryIn s J := by
  have F := A.target
  have hap := A.seated.apart
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hap
  have hmem : o ∈ anew.toList := List.mem_of_getElem? ho
  have hne : o ≠ g := fun e => hap.1 (List.mem_append_left _ (e ▸ hmem))
  have hidx := Lists.idxOf_at anew.toList a o hap.2.1 ho
  have hget : (sizesAt S old T).kept.getD a {} = s := by
    rw [List.getD_eq_getElem?_getD, hs]
    rfl
  have hlen : a + 1 ≤ (sizesAt S old T).kept.length := (List.getElem?_eq_some_iff.1 hs).1
  -- the member's code is the old main code
  have hcode : s.code = old.code := by
    have hs' : ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape)[a]? =
        some s := hs
    rw [List.getElem?_map] at hs'
    obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 hs'
    exact A.fits.keptCode o' (List.mem_of_getElem? ho')
  show (if o = g then _ else
    match anew.toList.idxOf? o with
    | some a => (V (1 + a)).word ((sizesAt S old T).kept.getD a {}) .main J
    | none => 0) = _
  rw [if_neg hne, hidx]
  show (V (1 + a)).word ((sizesAt S old T).kept.getD a {}) .main J = _
  rw [hget]
  show (if J % 2 ^ ceilLog2 s.mainRows < s.mainRows then
    (V (1 + a)).main (s.mainDeg == 3) (J % 2 ^ ceilLog2 s.mainRows) (J / 2 ^ ceilLog2 s.mainRows)
    else 0) = _
  unfold Held.entryIn
  by_cases hb : J % 2 ^ ceilLog2 s.mainRows < s.mainRows
  · rw [if_pos hb, if_pos hb]
    have hj : J / 2 ^ ceilLog2 s.mainRows < (S.codes.base.getD s.code default).ell := by
      rw [hcode, ← F.power.2]
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add]
      exact hJ
    have h := A.honest (a + 1) hlen
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, hget] at h
    have h2 := h (J % 2 ^ ceilLog2 s.mainRows) (J / 2 ^ ceilLog2 s.mainRows) hb hj
      (by
        have e : J % 2 ^ ceilLog2 s.mainRows +
            J / 2 ^ ceilLog2 s.mainRows * 2 ^ ceilLog2 s.mainRows = J := by
          rw [Nat.mul_comm]; exact Nat.mod_add_div _ _
        rw [e]
        exact hp)
    rw [Nat.add_comm 1 a, h2]
    unfold mainRows
    rw [if_neg (by simp), if_pos hlen]
    rfl
  · rw [if_neg hb, if_neg hb]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.word_main
#print axioms VerifiableInference.Desc.K2.Honest.word_rest
#print axioms VerifiableInference.Desc.K2.Honest.word_copy
