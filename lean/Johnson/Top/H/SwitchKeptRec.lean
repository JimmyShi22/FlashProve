-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchKeptRec.lean: the record that the program's frame of a code switch holds
of a kept member (`KeptPlace`, OnBytes/Iop/Cs.lean), behind the program's test on the public sizes.

Statements and proofs.
Main names:
  `pad_index_at`: a place of the pad of a message without mask rows lies in the last main row.
  `kept_rec`: the record's fields, off the statement: the member's number, its rows, its row bits,
    its pad.
  `nodup_of_frame`, `pad_of_check`, `entry_of_check`, `rows_le_of_frame`: see their docstrings.
  `RecOK k rows ell`: the record has so many rows; its pad's indices differ; each place of its pad
    lies in a row of the member, at a place below ell. `recOK_of_check`: so it is at a frame of the
    program behind the test.
Limits: two premises of `recOK_of_check` are given by no test named here: the member has a row (it
follows where the target's shape for its new copy has one: Johnson/Top/H/SwitchNamed.lean), and its
rows are just as long as the old main row. Nothing on soundness.

-/
import Johnson.Top.H.SwitchFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

/-- A place of the pad of a message without mask rows: in the last main row, at a place of the
row. -/
theorem pad_index_at (codes : Codes) (s : OracleShape) (hm : s.maskRows = 0)
    (hr : 0 < s.mainRows) (p : PadPlace) (hp : p ∈ padPlaces codes s) :
    ∃ place, place < (codes.base.getD s.code default).ell ∧
      p.index = s.mainRows - 1 + place * 2 ^ ceilLog2 s.mainRows := by
  have hh : (Send.cube codes s).hasMask = false := by
    unfold Send.cube
    simp [hm]
  have hb : (Send.cube codes s).mainRowBits = ceilLog2 s.mainRows := by
    unfold Send.cube
    simp [hr]
  unfold padPlaces Send.pad at hp
  obtain ⟨h1, h2⟩ := mem_getD_ite _ _ p hp
  obtain ⟨m, m1, m2, -⟩ := pad_form_mem _ _ _ _ _ _ _ p h2
  simp only [hh, hb, Bool.false_eq_true, if_false, Bool.false_or] at h1 m1 m2
  refine ⟨_, ?_, m2⟩
  generalize (if (s.mainDeg == 3) = true then 1 else 3) * s.answers = Ea at h1 m1
  omega

theorem getD_mem (pad : List PadPlace) (q : ℕ) (hq : q < pad.length) :
    pad.getD q default ∈ pad := by
  rw [List.getD_eq_getElem _ _ hq]
  exact List.getElem_mem hq

section
variable (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ) (anew : Array ℕ)
  (W : SwitchFrame) (hW : switchFrame S old T g anew = some W)
include hW

/-- The record of the kept member number a in a frame. -/
theorem kept_rec (a : ℕ) (k : KeptPlace) (h : W.kept[a]? = some k) :
    ∃ hi : a < (switchKept old).size, k.old = (switchKept old)[a] ∧
      k.rows = (S.oracles.getD (switchKept old)[a] default).shape.mainRows ∧
      k.rowBits = ceilLog2 (S.oracles.getD (switchKept old)[a] default).shape.mainRows ∧
      k.pad = padPlaces S.codes (S.oracles.getD (switchKept old)[a] default).shape := by
  obtain ⟨-, -, -, -, -, -, -, f8⟩ := frame_fields S old T g anew W hW
  obtain ⟨hi, e⟩ := range_map_at _ _ _ _ (f8 ▸ h)
  have ko : (switchKept old).getD a noId = (switchKept old)[a] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rfl
  have e1 : k.old = (switchKept old).getD a noId := congrArg KeptPlace.old e
  have e2 : k.rows = (S.oracles.getD ((switchKept old).getD a noId) default).shape.mainRows :=
    congrArg KeptPlace.rows e
  have e3 : k.rowBits = S.rowBits ((switchKept old).getD a noId) .main :=
    congrArg KeptPlace.rowBits e
  have e4 : k.pad = padOf S ((switchKept old).getD a noId) := congrArg KeptPlace.pad e
  rw [ko] at e1 e2 e3 e4
  rw [rowBits_main] at e3
  exact ⟨hi, e1, e2, e3, e4⟩

variable (hc : switchTargetCheck S old T = true) (s : Sg) (hC : s.C = codeOf W.code)
  (a : ℕ) (k : KeptPlace) (hk : W.kept[a]? = some k)
  (hEll : (S.codes.base.getD (S.oracles.getD k.old default).shape.code default).ell = W.code.ell)
include hk

/-- The indices of the record's pad differ. -/
theorem nodup_of_frame : (k.pad.map (·.index)).Nodup := by
  obtain ⟨_, _, _, _, e4⟩ := kept_rec S old T g anew W hW a k hk
  rw [e4]
  exact padPlaces_nodup _ _

include hc hC hEll

/-- Each place of the record's pad lies in a row of the member, at a place of the row. -/
theorem pad_of_check (hpos : 0 < k.rows) (q : ℕ) (hq : q < k.pad.length) :
    (k.pad.getD q default).index % 2 ^ k.rowBits < k.rows ∧
      (k.pad.getD q default).index / 2 ^ k.rowBits < s.C.l := by
  obtain ⟨hi, e1, e2, e3, e4⟩ := kept_rec S old T g anew W hW a k hk
  obtain ⟨-, -, -, -, -, -, c7, -⟩ := check_facts hc
  have hm := (check_kept hc a hi (by rw [c7]; exact hi)).1
  obtain ⟨p, hmem, hpe⟩ : ∃ p, p ∈ k.pad ∧ k.pad.getD q default = p :=
    ⟨_, getD_mem k.pad q hq, rfl⟩
  rw [hpe]
  rw [e4] at hmem
  obtain ⟨place, p1, p2⟩ := pad_index_at S.codes _ hm (by rw [← e2]; exact hpos) _ hmem
  rw [← e1, hEll] at p1
  rw [← e3, ← e2] at p2
  have hR : k.rows ≤ 2 ^ k.rowBits := by
    rw [e2, e3]
    exact le_two_pow_ceilLog2 _
  have hl : s.C.l = W.code.ell := by rw [hC]; rfl
  rw [p2, hl]
  constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega), Nat.zero_add]
    exact p1

variable (l : List (OracleShape × ℕ))
  (hl : ∀ i (hi : i < T.kept.size), ∃ h : 1 + i < l.length,
    (l.get ⟨1 + i, h⟩).1 = T.kept[i].shape)
include hl

/-- Each entry of the main table of the member's new copy lies in a row of the member, at a place of
the row. -/
theorem entry_of_check (n : (sigOf S.codes l).Ent) (h0 : (entAt S.codes l n).1 = 1 + a)
    (hp : (entAt S.codes l n).2.1 = Part.main) :
    (entAt S.codes l n).2.2 % 2 ^ k.rowBits < k.rows ∧
      (entAt S.codes l n).2.2 / 2 ^ k.rowBits < s.C.l := by
  obtain ⟨hi, e1, e2, e3, _⟩ := kept_rec S old T g anew W hW a k hk
  obtain ⟨-, -, -, -, -, -, c7, c8⟩ := check_facts hc
  have hi' : a < T.kept.size := by rw [c7]; exact hi
  obtain ⟨m1, m2⟩ := c8 a hi hi'
  obtain ⟨h, hs⟩ := hl a hi'
  obtain ⟨ho, h1, h2⟩ := inTab_entAt S.codes l n
  generalize entAt S.codes l n = t at h0 hp ho h1 h2
  obtain ⟨o, part, J⟩ := t
  have h0' : o = 1 + a := h0
  have hp' : part = Part.main := hp
  subst h0' hp'
  have h1' : J % 2 ^ ceilLog2 (l.get ⟨1 + a, h⟩).1.mainRows < (l.get ⟨1 + a, h⟩).1.mainRows := h1
  have h2' : J / 2 ^ ceilLog2 (l.get ⟨1 + a, h⟩).1.mainRows <
      (S.codes.base.getD (l.get ⟨1 + a, h⟩).1.code default).ell := h2
  rw [hs, m1, ← e3, ← e2] at h1'
  rw [hs, m1, m2, ← e3, ← e1, hEll] at h2'
  have hl' : s.C.l = W.code.ell := by rw [hC]; rfl
  rw [hl']
  exact ⟨h1', h2'⟩

end

/-- What is asked of the frame's record of a kept member. -/
structure RecOK (k : KeptPlace) (rows ell : ℕ) : Prop where
  rows : k.rows = rows
  nodup : (k.pad.map (·.index)).Nodup
  pad : ∀ q, q < k.pad.length → (k.pad.getD q default).index % 2 ^ k.rowBits < k.rows ∧
    (k.pad.getD q default).index / 2 ^ k.rowBits < ell

section
variable (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ) (anew : Array ℕ)
  (W : SwitchFrame) (hW : switchFrame S old T g anew = some W)
  (a : ℕ) (k : KeptPlace) (hk : W.kept[a]? = some k)
include hW hk

theorem rows_le_of_frame : k.rows ≤ 2 ^ k.rowBits := by
  obtain ⟨_, _, e2, e3, _⟩ := kept_rec S old T g anew W hW a k hk
  rw [e2, e3]
  exact le_two_pow_ceilLog2 _

/-- **The record of a kept member at a frame of the program, behind the test.** -/
theorem recOK_of_check (hc : switchTargetCheck S old T = true) (s : Sg) (hC : s.C = codeOf W.code)
    (hEll : (S.codes.base.getD (S.oracles.getD k.old default).shape.code default).ell = W.code.ell)
    (hpos : 0 < k.rows) : RecOK k (S.oracles.getD k.old default).shape.mainRows s.C.l := by
  obtain ⟨_, e1, e2, _, _⟩ := kept_rec S old T g anew W hW a k hk
  exact ⟨by rw [e1]; exact e2, nodup_of_frame S old T g anew W hW a k hk,
    pad_of_check S old T g anew W hW hc s hC a k hk hEll hpos⟩

end

end Johnson.Top.H

#print axioms Johnson.Top.H.kept_rec
#print axioms Johnson.Top.H.pad_of_check
#print axioms Johnson.Top.H.entry_of_check
#print axioms Johnson.Top.H.recOK_of_check
