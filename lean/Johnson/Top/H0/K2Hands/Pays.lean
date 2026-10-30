-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/Pays.lean: the premises of the code switch's last join
(RowsJoin.lean) that speak of the frame and of public numbers, paid at a frame that the program
makes behind its own test.

Johnson/Top/H0/K2Hands/RowsJoin.lean joins the rows of the program's code switch with the rows of
the typed caller, under records of premises. Here the clauses of four of these records that speak of
the frame W and of public numbers are shown where `switchFrame S old T g anew = some W` and
`switchTargetCheck S old T = true` (OnBytes/Iop/Cs.lean). Statements and proofs.
Main names: `check_more`, `frame_more`: further clauses of the test and further fields of the frame.
Tools: `switchBox_room`, `getD_map_lt`, `size_startsFrom`, `rest_lt_bits`, `lt_pow_of`.
`places_inc`: the places of the rest increase. `frameOK_of_check`: `FrameOK` (GenJoin.lean) at the
frame's own numbers, with `maskAt_of_check`. `mainIn_of_check`, `restIn_of_check`: two clauses of
`Names` (GenJoin.lean). `rowLt_of_frame`, `padIn_of_check`, `keptIn_of_check`,
`tailPieces_of_frame`: clauses of `NamesK` (KeptJoin.lean). Its clause padNodup and the clauses pad
and entry of `Slots` (KeptFormJoin.lean) are `nodup_of_frame`, `pad_of_check`, `entry_of_check` of
Johnson/Top/H/SwitchKeptRec.lean. Limits: the premises of each statement; among them, shown of no
run here: g stands in the statement with the target's shape; both old codes have at most 2 ^ 32
positions; a kept member's rows are just as long as the main row; the old rows' count of kept rows
is the sum of the frame's members' rows; a kept member has a row (hpos, in `padIn_of_check`).
(Brought further, not paid: AtYes.lean's atSwitch_of makes the first at a yes of the kind's
decision, and the main code's bound from the premise logN ≤ 32.) The test and the frame are taken at
one statement (`check_congr`, Johnson/Top/H/SwitchPads.lean, carries the test). Whether the premises
can be met together has not been evaluated. Nothing on soundness.
-/
import Johnson.Top.H0.K2Hands.KeptFormJoin
import Johnson.Top.H.SwitchTie
import Johnson.Top.H.SwitchKeptRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

/-- Further clauses of the program's test on the public sizes. -/
theorem check_more {S : Statement} {old : SingleRows} {T : SwitchTarget}
    (h : switchTargetCheck S old T = true) :
    powerOfTwo (S.codes.base.getD old.code default).ell = true ∧ T.main.firstRow = 0 ∧
      2 ^ T.main.bits ≤ (S.codes.base.getD old.code default).ell ∧
      ∀ i (h1 : i < (switchKept old).size) (_ : i < T.kept.size),
        (S.oracles.getD (switchKept old)[i] default).shape.maskRows = 0 := by
  unfold switchTargetCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hp⟩, _⟩, _⟩, hb⟩, hle⟩, _⟩, _⟩,
    _⟩, hall⟩ := h
  have first : T.main.firstRow = 0 := by
    cases hq : T.rest.part with
    | mask =>
      rw [hq] at hb
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      omega
    | main =>
      rw [hq] at hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      omega
  refine ⟨hp, first, hle, fun i h1 h2 => ?_⟩
  rw [Array.all_eq_true] at hall
  have hz : i < ((switchKept old).zip T.kept).size := by
    rw [Array.size_zip]
    omega
  have hi := hall i hz
  rw [Array.getElem_zip] at hi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
  exact hi.1.1.1.1.1.1.1

/-- Further fields of a frame. -/
theorem frame_more (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (anew : Array ℕ) (W : SwitchFrame) (h : switchFrame S old T g anew = some W) :
    W.mainTail = switchPieces W.places W.parts.mainTailAt W.code.r ∧
    W.keptTail = W.parts.keptTailAt.map (fun a => switchPieces W.places a W.code.r) ∧
    W.maskTail = W.parts.maskTailAt.map (fun a => switchPieces W.places a W.zk.r) ∧
    W.box = (Array.range old.masks).map (fun j =>
      if powerOfTwo W.zk.ell then switchBox W.places (W.parts.maskAt.getD j 0) (ceilLog2 W.zk.ell)
      else none) ∧
    W.maskMessage = (Array.range old.masks).map (fun j =>
      if (W.box.getD j none).isSome then []
      else switchPieces W.places (W.parts.maskAt.getD j 0) W.zk.ell) := by
  unfold switchFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨code, hc, zk, hz, nc, -, -, -, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The places of the rest increase, at a frame behind the test. -/
theorem places_inc (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (anew : Array ℕ) (W : SwitchFrame) (hW : switchFrame S old T g anew = some W)
    (hc : switchTargetCheck S old T = true) (a n : ℕ) :
    ∀ i j, i < j → j < n → W.places.get (a + i) < W.places.get (a + j) := by
  intro i j hij _
  rw [(frame_fields S old T g anew W hW).2.2.2.2.2.1]
  exact (SwitchPlaces.places_of_check hc).1 _ _ (by omega)

/-- What a yes of `switchBox` says beside `switchBox_yes`: there is a variable, and the places
do not end before the box's last entry. -/
theorem switchBox_room (places : SwitchPlaces) (first vars : ℕ) (b : SwitchBox)
    (h : switchBox places first vars = some b) :
    vars ≠ 0 ∧ first + 2 ^ vars ≤ places.size := by
  unfold switchBox at h
  dsimp only at h
  split_ifs at h with c1 c2 c3 c4
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, not_lt] at c1
  exact c1

/-- An entry of an array that is made entry by entry from another. -/
theorem getD_map_lt {α β : Type} (a : Array α) (f : α → β) (j : ℕ) (hj : j < a.size) (d : β)
    (d0 : α) : (a.map f).getD j d = f (a.getD j d0) := by
  simp [Array.getD, hj]

theorem size_startsFrom (start step count : ℕ) : (startsFrom start step count).size = count := by
  simp [startsFrom]

section
variable (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ) (anew : Array ℕ)
  (W : SwitchFrame) (hW : switchFrame S old T g anew = some W)
  (hc : switchTargetCheck S old T = true)
include hW hc

/-- An entry of the rest below the places' number has its index below 2 ^ (the rest's table's index
bits), if g stands in the statement with the target's shape. -/
theorem rest_lt_bits (x : Oracle) (hx : S.oracles[g]? = some x) (hxs : x.shape = T.shape) (i : ℕ)
    (hi : i < W.places.size) : W.places.get i < 2 ^ W.restBits := by
  obtain ⟨-, -, -, -, -, f6, -, -⟩ := frame_fields S old T g anew W hW
  obtain ⟨-, -, -, c4, -, -, -, -⟩ := check_facts hc
  obtain ⟨-, p2, p3, -⟩ := SwitchPlaces.places_of_check hc
  obtain ⟨nc, -, -, b2⟩ := frame_bits S old T g anew W hW
  have hr : x.shape.rows T.rest.part ≠ 0 := by
    rw [hxs]
    have := Nat.two_pow_pos T.rest.bits
    omega
  rw [b2, tableBits_of_shape S g x hx T.rest.part hr, hxs, ellOf_eq, Nat.pow_add]
  rw [f6] at hi ⊢
  refine lt_of_lt_of_le (lt_of_mod_div _ _ (T.shape.rows T.rest.part) _
    (lt_of_lt_of_le (p2 i).2 c4) (le_two_pow_ceilLog2 _) (p3 i hi)) ?_
  exact Nat.mul_le_mul_left _ (le_two_pow_ceilLog2 _)

/-- `MaskAt` (Johnson/Top/H0/H2K/GenRowsAt.lean) at the frame's own numbers. -/
theorem maskAt_of_check (x : Oracle) (hx : S.oracles[g]? = some x) (hxs : x.shape = T.shape)
    (hZ32 : W.zk.logN ≤ 32) (j : ℕ) (hj : j < 2) :
    MaskAt W j (W.parts.maskAt.getD j 0) (W.parts.maskTailAt.getD j 0) := by
  obtain ⟨-, -, -, -, -, -, f7, -⟩ := frame_fields S old T g anew W hW
  obtain ⟨c1, -⟩ := check_facts hc
  obtain ⟨-, -, m3, m4, m5⟩ := frame_more S old T g anew W hW
  refine ⟨?_, ?_, ?_, places_inc S old T g anew W hW hc _ _, places_inc S old T g anew W hW hc _ _,
    hZ32⟩
  · intro hb
    rw [m5, getD_map_range, c1, if_pos hj, hb]
    rfl
  · intro b hb
    rw [m4, getD_map_range] at hb
    split_ifs at hb with k1 k2
    have hb' : switchBox W.places (W.parts.maskAt.getD j 0) W.zk.logEll = some b := hb
    obtain ⟨y1, -⟩ := switchBox_yes _ _ _ _ hb'
    obtain ⟨r1, r2⟩ := switchBox_room _ _ _ _ hb'
    have pos := Nat.two_pow_pos W.zk.logEll
    have s0 := y1 0 pos
    have t0 := y1 (2 ^ W.zk.logEll - 1) (by omega)
    have l0 := rest_lt_bits S old T g anew W hW hc x hx hxs (W.parts.maskAt.getD j 0 + 0) (by omega)
    have l1 := rest_lt_bits S old T g anew W hW hc x hx hxs
      (W.parts.maskAt.getD j 0 + (2 ^ W.zk.logEll - 1)) (by omega)
    rw [s0] at l0
    rw [t0] at l1
    refine ⟨hb', eq_of_powerOfTwo W.zk.ell k2, ?_, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, W.zk.logEll = v + 1 := ⟨W.zk.logEll - 1, by omega⟩
    have h2 : 2 ^ v ≤ 2 ^ W.zk.logEll - 1 := by
      rw [hv, Nat.pow_succ]
      have := Nat.two_pow_pos v
      omega
    have h3 : 2 ^ v * 2 ^ b.shift ≤ (2 ^ W.zk.logEll - 1) * 2 ^ b.shift :=
      Nat.mul_le_mul_right _ h2
    have h4 : 2 ^ (v + b.shift) < 2 ^ W.restBits := by
      rw [Nat.pow_add]
      omega
    have h5 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 h4
    omega
  · have hs : j < W.parts.maskTailAt.size := by
      rw [f7]
      show j < (startsFrom _ _ old.masks).size
      rw [size_startsFrom, c1]
      exact hj
    rw [m3]
    exact getD_map_lt _ _ _ hs _ _

end

section
variable (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ) (anew : Array ℕ)
  (W : SwitchFrame) (hW : switchFrame S old T g anew = some W)
  (hc : switchTargetCheck S old T = true)
include hW hc

/-- **`FrameOK` at the frame's own numbers.** x: g's record in the statement, with the target's
shape. The two bounds on the old codes' lengths are premises: the test does not ask them. -/
theorem frameOK_of_check (x : Oracle) (hx : S.oracles[g]? = some x) (hxs : x.shape = T.shape)
    (hC32 : W.code.logN ≤ 32) (hZ32 : W.zk.logN ≤ 32) :
    FrameOK W W.parts.mainTailAt (W.parts.maskAt.getD 0 0) (W.parts.maskTailAt.getD 0 0)
      (W.parts.maskAt.getD 1 0) (W.parts.maskTailAt.getD 1 0) := by
  obtain ⟨f1, -, -, f4, f5, -, -, -⟩ := frame_fields S old T g anew W hW
  obtain ⟨-, c2, -, -, c5, -, -, -⟩ := check_facts hc
  obtain ⟨q1, q2, q3, -⟩ := check_more hc
  obtain ⟨-, -, o3⟩ := SwitchPlaces.of_check hc
  obtain ⟨m1, -⟩ := frame_more S old T g anew W hW
  obtain ⟨nc, hn, b1, -⟩ := frame_bits S old T g anew W hW
  have g1 : S.codes.base.getD old.code default = W.code := by
    rw [Array.getD_eq_getD_getElem?, f1]
    rfl
  have gn : S.codes.base.getD T.shape.code default = nc := by
    rw [Array.getD_eq_getD_getElem?, hn]
    rfl
  rw [g1] at q1 q3 c5
  rw [gn] at c5
  have hpow : W.code.ell = 2 ^ W.code.logEll := eq_of_powerOfTwo _ q1
  have hbits : T.main.bits ≤ W.code.logEll := by
    rw [hpow] at q3
    exact (Nat.pow_le_pow_iff_right (by decide)).1 q3
  have hrow : T.main.bits ≤ switchRowBits T .main := by
    have h := o3.le
    rw [c2] at h
    exact (Nat.pow_le_pow_iff_right (by decide)).1 h
  have htab : W.code.logEll ≤ nc.logEll + T.main.bits := by
    have h1 : nc.ell * 2 ^ T.main.bits ≤ 2 ^ nc.logEll * 2 ^ T.main.bits :=
      Nat.mul_le_mul_right _ (le_two_pow_ceilLog2 _)
    rw [← Nat.pow_add] at h1
    rw [hpow] at c5
    exact (Nat.pow_le_pow_iff_right (by decide)).1 (le_trans c5 h1)
  refine ⟨m1, places_inc S old T g anew W hW hc _ _, hC32, hpow, ?_, ?_, ?_, ?_, ?_,
    maskAt_of_check S old T g anew W hW hc x hx hxs hZ32 0 (by decide),
    maskAt_of_check S old T g anew W hW hc x hx hxs hZ32 1 (by decide)⟩
  · rw [f4]
    exact hbits
  · rw [f4, f5]
    exact hrow
  · rw [b1, f4, f5]
    omega
  · rw [f4, q2]
    exact Nat.dvd_zero _
  · rw [f4, q2, Nat.zero_div]
    exact Nat.two_pow_pos _

variable (l : List (OracleShape × ℕ)) (g0 : 0 < l.length) (hg : (l.get ⟨0, g0⟩).1 = T.shape)
include hg

omit hc in
/-- `Names.mainIn`. -/
theorem mainIn_of_check (n : (sigOf S.codes l).Ent) (h0 : (entAt S.codes l n).1 = 0)
    (hp : (entAt S.codes l n).2.1 = Part.main) : (entAt S.codes l n).2.2 < 2 ^ W.tableBits := by
  obtain ⟨-, -, -, -, f5, -, -, -⟩ := frame_fields S old T g anew W hW
  obtain ⟨nc, hn, b1, -⟩ := frame_bits S old T g anew W hW
  have gn : pMain S.codes T.shape = nc := by
    show S.codes.base.getD T.shape.code default = nc
    rw [Array.getD_eq_getD_getElem?, hn]
    rfl
  obtain ⟨ho, h⟩ := (inTab_entAt S.codes l n).lt_pow
  generalize entAt S.codes l n = t at h0 hp ho h
  obtain ⟨o, part, J⟩ := t
  have h0' : o = 0 := h0
  have hp' : part = Part.main := hp
  subst h0' hp'
  have h' : J < 2 ^ (ceilLog2 (l.get ⟨0, g0⟩).1.mainRows +
      ceilLog2 (pMain S.codes (l.get ⟨0, g0⟩).1).ell) := h
  rw [hg, gn] at h'
  rw [b1, f5]
  exact h'

/-- `Names.restIn`. -/
theorem restIn_of_check (x : Oracle) (hx : S.oracles[g]? = some x) (hxs : x.shape = T.shape)
    (n : (sigOf S.codes l).Ent) (h0 : (entAt S.codes l n).1 = 0)
    (hp : (entAt S.codes l n).2.1 = W.restPart) : (entAt S.codes l n).2.2 < 2 ^ W.restBits := by
  obtain ⟨-, -, f3, -, -, -, -, -⟩ := frame_fields S old T g anew W hW
  obtain ⟨-, -, -, c4, -, -, -, -⟩ := check_facts hc
  obtain ⟨nc, -, -, b2⟩ := frame_bits S old T g anew W hW
  have hr : x.shape.rows T.rest.part ≠ 0 := by
    rw [hxs]
    have := Nat.two_pow_pos T.rest.bits
    omega
  obtain ⟨ho, h⟩ := (inTab_entAt S.codes l n).lt_pow
  generalize entAt S.codes l n = t at h0 hp ho h
  obtain ⟨o, part, J⟩ := t
  have h0' : o = 0 := h0
  have hp' : part = W.restPart := hp
  subst h0' hp'
  have h' : J < 2 ^ (ceilLog2 ((l.get ⟨0, g0⟩).1.rows W.restPart) +
      ceilLog2 (ellOf S.codes (l.get ⟨0, g0⟩).1 W.restPart)) := h
  rw [hg, f3] at h'
  rw [b2, tableBits_of_shape S g x hx T.rest.part hr, hxs]
  exact h'

end
theorem lt_pow_of (rb J rows ell logE : ℕ) (h1 : J % 2 ^ rb < rows) (hR : rows ≤ 2 ^ rb)
    (h2 : J / 2 ^ rb < ell) (hE : ell ≤ 2 ^ logE) : J < 2 ^ (rb + logE) := by
  rw [Nat.pow_add]
  exact lt_of_lt_of_le (lt_of_mod_div _ _ _ _ h1 hR h2) (Nat.mul_le_mul_left _ hE)

section
variable (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ) (anew : Array ℕ)
  (W : SwitchFrame) (hW : switchFrame S old T g anew = some W)
  (a : ℕ) (k : KeptPlace) (hk : W.kept[a]? = some k)
include hW hk

/-- `NamesK.rowLt`. -/
theorem rowLt_of_frame (b : ℕ) (hb : b < k.rows) : b < 2 ^ k.rowBits :=
  lt_of_lt_of_le hb (rows_le_of_frame S old T g anew W hW a k hk)

/-- `NamesK.tailPieces`, with the tail's beginning read off the frame's list. -/
theorem tailPieces_of_frame (hkr : old.keptRows = (W.kept.map (·.rows)).sum) (b : ℕ)
    (hb : b < k.rows) :
    W.keptTail.getD (rowsBefore W.kept a + b) [] =
      switchPieces W.places (W.parts.keptTailAt.getD (keptNo W a b) 0) W.code.r := by
  obtain ⟨-, -, -, -, -, -, f7, -⟩ := frame_fields S old T g anew W hW
  obtain ⟨-, m2, -⟩ := frame_more S old T g anew W hW
  have e : rowsBefore W.kept a + b = keptNo W a b := rfl
  have hs : keptNo W a b < W.parts.keptTailAt.size := by
    rw [f7]
    show _ < (startsFrom _ _ old.keptRows).size
    rw [size_startsFrom, hkr]
    unfold keptNo
    rw [List.map_take]
    exact sum_take_lt _ _ _ k.rows (by rw [List.getElem?_map, hk]; rfl) hb
  rw [e, m2]
  exact getD_map_lt _ _ _ hs _ _

variable (hc : switchTargetCheck S old T = true) (s : Sg) (hC : s.C = codeOf W.code)
  (hEll : (S.codes.base.getD (S.oracles.getD k.old default).shape.code default).ell = W.code.ell)
include hc hC hEll

/-- `NamesK.padIn`. -/
theorem padIn_of_check (hpos : 0 < k.rows) (q : ℕ) (hq : q < k.pad.length) :
    (k.pad.getD q default).index < 2 ^ (k.rowBits + W.code.logEll) := by
  obtain ⟨h1, h2⟩ := pad_of_check S old T g anew W hW hc s hC a k hk hEll hpos q hq
  have hl : s.C.l = W.code.ell := by rw [hC]; rfl
  exact lt_pow_of _ _ _ _ _ h1 (rows_le_of_frame S old T g anew W hW a k hk) h2
    (by rw [hl]; exact le_two_pow_ceilLog2 _)

/-- `NamesK.keptIn`. -/
theorem keptIn_of_check (l : List (OracleShape × ℕ))
    (hl : ∀ i (hi : i < T.kept.size), ∃ h : 1 + i < l.length,
      (l.get ⟨1 + i, h⟩).1 = T.kept[i].shape)
    (n : (sigOf S.codes l).Ent) (h0 : (entAt S.codes l n).1 = 1 + a)
    (hp : (entAt S.codes l n).2.1 = Part.main) :
    (entAt S.codes l n).2.2 < 2 ^ (k.rowBits + W.code.logEll) := by
  obtain ⟨h1, h2⟩ := entry_of_check S old T g anew W hW hc s hC a k hk hEll l hl n h0 hp
  have hl' : s.C.l = W.code.ell := by rw [hC]; rfl
  exact lt_pow_of _ _ _ _ _ h1 (rows_le_of_frame S old T g anew W hW a k hk) h2
    (by rw [hl']; exact le_two_pow_ceilLog2 _)

end

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.check_more
#print axioms VerifiableInference.Desc.First.K2Hands.frame_more
#print axioms VerifiableInference.Desc.First.K2Hands.rest_lt_bits
#print axioms VerifiableInference.Desc.First.K2Hands.maskAt_of_check
#print axioms VerifiableInference.Desc.First.K2Hands.frameOK_of_check
#print axioms VerifiableInference.Desc.First.K2Hands.mainIn_of_check
#print axioms VerifiableInference.Desc.First.K2Hands.restIn_of_check
#print axioms VerifiableInference.Desc.First.K2Hands.rowLt_of_frame
#print axioms VerifiableInference.Desc.First.K2Hands.tailPieces_of_frame
#print axioms VerifiableInference.Desc.First.K2Hands.padIn_of_check
#print axioms VerifiableInference.Desc.First.K2Hands.keptIn_of_check
