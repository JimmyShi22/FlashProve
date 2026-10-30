-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchFront.lean: what a code switch says of a kept member's two copies, on
plain tables: the new copy is the old message outside the old pad's places, and the old pad lies in
g.

A kept member of the old group is sent a second time, with a pad of its own (the head of
OnBytes/Iop/Cs.lean). A table is a function of (mask row or main row, row, place). Definitions,
statements and proofs.
Main names:
  `Tab`, `isMask`.
  `KeptIs W k ell m new g`: the relation between the old copy's table m, the new copy's table and
    g's table: `off`: at a row and place of the member outside the old pad, m is the new copy;
    `pad`: at place number q of the old pad, m is g's entry number oldPadAt + q of the rest.
  `padRaw cs s row place`: the library's `padP` (Johnson/Pack/PortZ.lean) at a main row's entry, on
    plain numbers. `padRaw_iff`: it is `padP`.
  `mem_pad_index`: which indices the program's pad has, for a message without mask rows.
  `padRaw_iff_mem`: at one answer the library's pad is the program's.
  `KeptIs.hoff`: if the new copy's table is a table msg outside its pad, and both copies have one
    shape's numbers, then msg is the old copy's table outside the pad.
  `tabOf cs l n o`: message number o of a sending's typed messages n, as a table. `ents_tab`.
  `iJ_off`, `iJ_pad`: what is read along iJ (Johnson/Top/H/SwitchMaps.lean) at a kept slot, in the
    new messages' tables. `padNoOf_getD`.
  `keptIs_of_iJ`: a table that holds, row by row, what is read along iJ at a member's slots stands
    in `KeptIs` to the tables of the member's new copy and of g.
  `check_kept`, `padRaw_same`, `fit_of_pad`: behind the program's test on the public sizes a copy's
    pad stands where its original's stood, and the rows are long enough for the pad.
Limits: nothing on decoding, on a witness or on what fixes a copy's pad. That a kept member has one
answer is a premise (`padRaw_iff_mem`, `KeptIs.hoff`) that no test named here gives. Nothing on
soundness.

-/
import Johnson.Top.H.SwitchPadsAt
import Johnson.Top.H.SwitchTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

/-- A message as a table: mask row or main row (true: mask), row, place. -/
abbrev Tab : Type := Bool → ℕ → ℕ → GE

def isMask : Part → Bool
  | .main => false
  | .mask => true

/-- **The two copies of a kept member, and g.** k: the member's record in the frame. ell: the length
of its rows. -/
structure KeptIs (W : SwitchFrame) (k : KeptPlace) (ell : ℕ) (m new g : Tab) : Prop where
  /-- the new copy is the old message outside the old pad's places -/
  off : ∀ b j, b < k.rows → j < ell → b + 2 ^ k.rowBits * j ∉ k.pad.map (·.index) →
    m false b j = new false b j
  /-- the old pad lies in g's rest -/
  pad : ∀ q, q < k.pad.length →
    m false ((k.pad.getD q default).index % 2 ^ k.rowBits)
        ((k.pad.getD q default).index / 2 ^ k.rowBits) =
      g (isMask W.restPart) (W.places.get (k.oldPadAt + q) % 2 ^ W.places.rowBits)
        (W.places.get (k.oldPadAt + q) / 2 ^ W.places.rowBits)

/-- The library's test on a pad's place, at a main row's entry, on plain numbers. -/
def padRaw (cs : Codes) (s : OracleShape) (row place : ℕ) : Prop :=
  s.maskRows = 0 ∧ row + 1 = s.mainRows ∧ (pMain cs s).ell ≤ place + eachZ s

theorem padRaw_iff (cs : Codes) (s : OracleShape) (x : Fin s.mainRows × Fin (pMain cs s).ell) :
    padRaw cs s x.1.val x.2.val ↔ padP cs s (.inl x) := Iff.rfl

theorem pad_form_index (part : Part) (c0 base e a rb : ℕ) (bs : ℕ → E) :
    (((List.range a).flatMap fun i => (List.range e).map fun t =>
      ({ part := part, index := c0 + (base + e * i + t) * 2 ^ rb, answer := i, basis := bs t } :
        PadPlace)).map (·.index)) =
      (List.range (e * a)).map fun m => c0 + (base + m) * 2 ^ rb := by
  rw [← flat_range e (fun m => c0 + (base + m) * 2 ^ rb) a, List.map_flatMap]
  simp only [List.map_map, Function.comp_def, Nat.add_assoc]

theorem getD_ite_neg (c : Prop) [Decidable c] (L : List PadPlace) (h : ¬ c) :
    (if c then none else some L : Option (List PadPlace)).getD [] = L := by
  rw [if_neg h]
  rfl

theorem map_getD_ite_neg (c : Prop) [Decidable c] (L : List PadPlace) (h : ¬ c) :
    ((if c then none else some L : Option (List PadPlace)).getD []).map (·.index) =
      L.map (·.index) := by
  rw [getD_ite_neg c L h]

/-- **The indices of the program's pad**, for a message without mask rows whose rows are long enough
for the pad. -/
theorem mem_pad_index (codes : Codes) (s : OracleShape) (hm : s.maskRows = 0)
    (hr : 0 < s.mainRows) (hfit : eachZ s * s.answers ≤ (codes.base.getD s.code default).ell)
    (J : ℕ) :
    J ∈ (padPlaces codes s).map (·.index) ↔ ∃ m, m < eachZ s * s.answers ∧
      J = s.mainRows - 1 +
        ((codes.base.getD s.code default).ell - eachZ s * s.answers + m) *
          2 ^ ceilLog2 s.mainRows := by
  have hh : (Send.cube codes s).hasMask = false := by
    unfold Send.cube
    simp [hm]
  have hb : (Send.cube codes s).mainRowBits = ceilLog2 s.mainRows := by
    unfold Send.cube
    simp [hr]
  have he : (if (s.mainDeg == 3) = true then 1 else 3) = eachZ s := by
    unfold eachZ
    simp
  have e : (padPlaces codes s).map (·.index) =
      (List.range (eachZ s * s.answers)).map fun m => s.mainRows - 1 +
        ((codes.base.getD s.code default).ell - eachZ s * s.answers + m) *
          2 ^ ceilLog2 s.mainRows := by
    unfold padPlaces Send.pad
    refine Eq.trans (map_getD_ite_neg _ _ ?_) (Eq.trans (pad_form_index _ _ _ _ _ _ _) ?_)
    · simp only [hh, Bool.false_eq_true, if_false, Bool.false_or, he]
      omega
    · simp only [hh, hb, Bool.false_eq_true, if_false, Bool.false_or, he]
  rw [e, List.mem_map]
  constructor
  · rintro ⟨m, h1, rfl⟩
    exact ⟨m, List.mem_range.1 h1, rfl⟩
  · rintro ⟨m, h1, rfl⟩
    exact ⟨m, List.mem_range.2 h1, rfl⟩

/-- **At one answer the library's pad is the program's**: a row and place of a message without mask
rows is a place of the library's pad just where its index is one of the program's pad's. -/
theorem padRaw_iff_mem (codes : Codes) (s : OracleShape) (hm : s.maskRows = 0)
    (h1 : s.answers = 1) (hfit : eachZ s ≤ (codes.base.getD s.code default).ell) (row place : ℕ)
    (hrow : row < s.mainRows) (hpl : place < (codes.base.getD s.code default).ell) :
    padRaw codes s row place ↔
      row + 2 ^ ceilLog2 s.mainRows * place ∈ (padPlaces codes s).map (·.index) := by
  have hr : 0 < s.mainRows := by omega
  have hR := le_two_pow_ceilLog2 s.mainRows
  rw [mem_pad_index codes s hm hr (by rw [h1, Nat.mul_one]; exact hfit), h1, Nat.mul_one]
  unfold padRaw
  show s.maskRows = 0 ∧ row + 1 = s.mainRows ∧
    (codes.base.getD s.code default).ell ≤ place + eachZ s ↔ _
  generalize (codes.base.getD s.code default).ell = ell at hfit hpl ⊢
  generalize eachZ s = ea at hfit ⊢
  constructor
  · rintro ⟨-, a, b⟩
    refine ⟨place + ea - ell, by omega, ?_⟩
    have e1 : ell - ea + (place + ea - ell) = place := by omega
    rw [e1, Nat.mul_comm]
    omega
  · rintro ⟨m, hm1, e⟩
    have k1 := congrArg (· % 2 ^ ceilLog2 s.mainRows) e
    have k2 := congrArg (· / 2 ^ ceilLog2 s.mainRows) e
    simp only at k1 k2
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at k1
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)] at k2
    exact ⟨hm, by omega, by omega⟩

/-- **What the pin of the old copy wants outside the pad.** so, sn: the shapes of the old and of the
new copy. msg: a table that the new copy's table is outside the new copy's pad. If the two shapes
have the same numbers where the pad's places are told, msg is the old copy's table outside the old
copy's pad. -/
theorem KeptIs.hoff {W : SwitchFrame} {k : KeptPlace} {m new g : Tab} (codes : Codes)
    (so sn : OracleShape) (K : KeptIs W k (codes.base.getD so.code default).ell m new g)
    (hrows : k.rows = so.mainRows) (hbits : k.rowBits = ceilLog2 so.mainRows)
    (hpad : k.pad = padPlaces codes so) (hm : so.maskRows = 0) (h1 : so.answers = 1)
    (hfit : eachZ so ≤ (codes.base.getD so.code default).ell)
    (same : ∀ row place, padRaw codes sn row place ↔ padRaw codes so row place) (msg : Tab)
    (hnew : ∀ row place, row < so.mainRows → place < (codes.base.getD so.code default).ell →
      ¬ padRaw codes sn row place → new false row place = msg false row place)
    (row place : ℕ) (hrow : row < so.mainRows)
    (hpl : place < (codes.base.getD so.code default).ell) (hno : ¬ padRaw codes so row place) :
    msg false row place = m false row place := by
  rw [K.off row place (by rw [hrows]; exact hrow) hpl (by
    rw [hbits, hpad, ← padRaw_iff_mem codes so hm h1 hfit row place hrow hpl]
    exact hno)]
  exact (hnew row place hrow hpl (fun h => hno ((same row place).1 h))).symm

/-! ## The typed side: what is read along iJ -/

section
variable (cs : Codes) (l : List (OracleShape × ℕ)) (n : (sigOf cs l).Msg)

/-- Message number o of a sending's typed messages, as a table; 0 outside its ranges. -/
def tabOf (o : ℕ) : Tab := fun mask row place =>
  if ho : o < l.length then
    if mask then
      if h : row < (l.get ⟨o, ho⟩).1.maskRows ∧ place < (pMask cs (l.get ⟨o, ho⟩).1).ell then
        n ⟨o, ho⟩ (.inr (⟨row, h.1⟩, ⟨place, h.2⟩)) else 0
    else
      if h : row < (l.get ⟨o, ho⟩).1.mainRows ∧ place < (pMain cs (l.get ⟨o, ho⟩).1).ell then
        n ⟨o, ho⟩ (.inl (⟨row, h.1⟩, ⟨place, h.2⟩)) else 0
  else 0

/-- The value at an entry, read in the table by the entry's three numbers. rb: the row bits of that
table. -/
theorem ents_tab (e : (sigOf cs l).Ent) (rb : ℕ)
    (hrb : rb = ceilLog2 ((l.get e.1).1.rows (entAt cs l e).2.1)) :
    (sigOf cs l).ents n e = tabOf cs l n (entAt cs l e).1 (isMask (entAt cs l e).2.1)
      ((entAt cs l e).2.2 % 2 ^ rb) ((entAt cs l e).2.2 / 2 ^ rb) := by
  obtain ⟨i, c⟩ := e
  change (Fin (l.get i).1.mainRows × Fin (pMain cs (l.get i).1).ell) ⊕
    (Fin (l.get i).1.maskRows × Fin (pMask cs (l.get i).1).ell) at c
  subst hrb
  rcases c with x | x
  · show n i (.inl x) = tabOf cs l n i.val false
      (idxOf _ _ x % 2 ^ ceilLog2 (l.get i).1.mainRows)
      (idxOf _ _ x / 2 ^ ceilLog2 (l.get i).1.mainRows)
    rw [idxOf_mod, idxOf_div]
    unfold tabOf
    rw [dif_pos i.isLt, if_neg (by decide), dif_pos ⟨x.1.isLt, x.2.isLt⟩]
    rfl
  · show n i (.inr x) = tabOf cs l n i.val true
      (idxOf _ _ x % 2 ^ ceilLog2 (l.get i).1.maskRows)
      (idxOf _ _ x / 2 ^ ceilLog2 (l.get i).1.maskRows)
    rw [idxOf_mod, idxOf_div]
    unfold tabOf
    rw [dif_pos i.isLt, if_pos rfl, dif_pos ⟨x.1.isLt, x.2.isLt⟩]
    rfl

end

/-- In a pad whose places have different indices, place number q has the number q. -/
theorem padNoOf_getD : ∀ (pad : List PadPlace), (pad.map (·.index)).Nodup → ∀ q, q < pad.length →
    padNoOf pad (pad.getD q default).index = q
  | [], _, q, h => absurd h (by simp)
  | a :: l, _, 0, _ => by
    simp [padNoOf]
  | a :: l, hn, q + 1, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    have hq : q < l.length := by simpa using h
    have hm : (l.getD q default).index ∈ l.map (·.index) := by
      rw [List.getD_eq_getElem _ _ hq]
      exact List.mem_map_of_mem (List.getElem_mem hq)
    have hne : a.index ≠ (l.getD q default).index := fun e => hn.1 (e ▸ hm)
    rw [List.getD_cons_succ]
    unfold padNoOf
    rw [if_neg hne, padNoOf_getD l hn.2 q hq]

section
variable {cs : Codes} {l : List (OracleShape × ℕ)} {s : Sg} {K : Type} [Fintype K] [DecidableEq K]
  {W : SwitchFrame} {mem row : K → ℕ} {pl : K → KeptPlace} (Ft : Fit cs l s W mem row pl)
  (n : (sigOf cs l).Msg)

/-- **Outside the old pad**: along iJ a kept slot's entry is read in the member's new copy, at the
same row and place. -/
theorem iJ_off (κ : K) (j : Fin s.C.l)
    (h : row κ + 2 ^ (pl κ).rowBits * j.val ∉ (pl κ).pad.map (·.index)) :
    (sigOf cs l).ents n (iJ s W mem row pl cs l Ft.nameJ (.inl (some κ, j))) =
      tabOf cs l n (1 + mem κ) false (row κ) j.val := by
  have he : entAt cs l (iJ s W mem row pl cs l Ft.nameJ (.inl (some κ, j))) =
      (1 + mem κ, Part.main, row κ + 2 ^ (pl κ).rowBits * j.val) := by
    rw [entAt_iJ]
    show keptNm W (mem κ) (pl κ) (row κ + 2 ^ (pl κ).rowBits * j.val) = _
    unfold keptNm
    rw [if_neg h]
  obtain ⟨hl, hb, -, -⟩ := Ft.keptMsg κ
  have h1 : (iJ s W mem row pl cs l Ft.nameJ (.inl (some κ, j))).1 = ⟨1 + mem κ, hl⟩ :=
    Fin.ext (congrArg Prod.fst he)
  have h2 := Ft.row_lt κ
  rw [ents_tab cs l n _ (pl κ).rowBits (by rw [h1, he]; exact hb), he]
  show tabOf cs l n (1 + mem κ) false ((row κ + 2 ^ (pl κ).rowBits * j.val) % 2 ^ (pl κ).rowBits)
    ((row κ + 2 ^ (pl κ).rowBits * j.val) / 2 ^ (pl κ).rowBits) = _
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt h2, Nat.zero_add]

/-- **At the old pad**: along iJ the entry at place number q of the old pad is read in g's rest, at
entry number oldPadAt + q. -/
theorem iJ_pad (κ : K) (j : Fin s.C.l) (hn : ((pl κ).pad.map (·.index)).Nodup) (q : ℕ)
    (hq : q < (pl κ).pad.length)
    (h : row κ + 2 ^ (pl κ).rowBits * j.val = ((pl κ).pad.getD q default).index) :
    (sigOf cs l).ents n (iJ s W mem row pl cs l Ft.nameJ (.inl (some κ, j))) =
      tabOf cs l n 0 (isMask W.restPart)
        (W.places.get ((pl κ).oldPadAt + q) % 2 ^ W.places.rowBits)
        (W.places.get ((pl κ).oldPadAt + q) / 2 ^ W.places.rowBits) := by
  have hm : ((pl κ).pad.getD q default).index ∈ (pl κ).pad.map (·.index) := by
    rw [List.getD_eq_getElem _ _ hq]
    exact List.mem_map_of_mem (List.getElem_mem hq)
  have he : entAt cs l (iJ s W mem row pl cs l Ft.nameJ (.inl (some κ, j))) =
      (0, W.restPart, W.places.get ((pl κ).oldPadAt + q)) := by
    rw [entAt_iJ]
    show keptNm W (mem κ) (pl κ) (row κ + 2 ^ (pl κ).rowBits * j.val) = _
    unfold keptNm restAt
    rw [h, if_pos hm, padNoOf_getD _ hn q hq]
  have h1 : (iJ s W mem row pl cs l Ft.nameJ (.inl (some κ, j))).1 = ⟨0, Ft.g⟩ :=
    Fin.ext (congrArg Prod.fst he)
  rw [ents_tab cs l n _ W.places.rowBits (by rw [h1, he]; exact Ft.restBits), he]

/-- **The table of what is read along iJ at a member's slots stands in `KeptIs`.** a: the member's
number; k: its record. m: a table that holds at (row κ, place) what is read along iJ at the slot κ,
for each slot κ of the member. cover: each row of the member has a slot. -/
theorem keptIs_of_iJ (a : ℕ) (k : KeptPlace) (hk : ∀ κ, mem κ = a → pl κ = k) (m : Tab)
    (hm : ∀ κ (j : Fin s.C.l), mem κ = a → m false (row κ) j.val =
      (sigOf cs l).ents n (iJ s W mem row pl cs l Ft.nameJ (.inl (some κ, j))))
    (cover : ∀ b, b < k.rows → ∃ κ, mem κ = a ∧ row κ = b)
    (hn : (k.pad.map (·.index)).Nodup)
    (hpad : ∀ q, q < k.pad.length → (k.pad.getD q default).index % 2 ^ k.rowBits < k.rows ∧
      (k.pad.getD q default).index / 2 ^ k.rowBits < s.C.l) :
    KeptIs W k s.C.l m (tabOf cs l n (1 + a)) (tabOf cs l n 0) := by
  constructor
  · intro b j hb hj hoff
    obtain ⟨κ, rfl, rfl⟩ := cover b hb
    have e := hk κ rfl
    subst e
    rw [hm κ ⟨j, hj⟩ rfl]
    exact iJ_off Ft n κ ⟨j, hj⟩ hoff
  · intro q hq
    obtain ⟨p1, p2⟩ := hpad q hq
    obtain ⟨κ, rfl, hr⟩ := cover _ p1
    have e := hk κ rfl
    subst e
    rw [← hr, hm κ ⟨_, p2⟩ rfl]
    exact iJ_pad Ft n κ ⟨_, p2⟩ hn q hq (by
      show row κ + 2 ^ (pl κ).rowBits * (((pl κ).pad.getD q default).index / 2 ^ (pl κ).rowBits) = _
      rw [hr]
      exact Nat.mod_add_div _ _)

end

/-! ## What the program's test on the public sizes gives for the two copies' shapes -/

/-- The clauses of the test on a kept member's old shape and on the shape of its new copy. -/
theorem check_kept {S : Statement} {old : SingleRows} {T : SwitchTarget}
    (h : switchTargetCheck S old T = true) (i : ℕ) (h1 : i < (switchKept old).size)
    (h2 : i < T.kept.size) :
    (S.oracles.getD (switchKept old)[i] default).shape.maskRows = 0 ∧
      T.kept[i].shape.maskRows = 0 ∧
      (Send.pad S.codes (S.oracles.getD (switchKept old)[i] default).shape).isSome = true ∧
      T.kept[i].shape.mainRows = (S.oracles.getD (switchKept old)[i] default).shape.mainRows ∧
      T.kept[i].shape.mainDeg = (S.oracles.getD (switchKept old)[i] default).shape.mainDeg ∧
      T.kept[i].shape.answers = (S.oracles.getD (switchKept old)[i] default).shape.answers ∧
      (S.codes.base.getD T.kept[i].shape.code default).ell =
        (S.codes.base.getD (S.oracles.getD (switchKept old)[i] default).shape.code default).ell
    := by
  unfold switchTargetCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hall := h.2
  rw [Array.all_eq_true] at hall
  have hz : i < ((switchKept old).zip T.kept).size := by
    rw [Array.size_zip]
    omega
  have hi := hall i hz
  rw [Array.getElem_zip] at hi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
  exact ⟨hi.1.1.1.1.1.1.1, hi.1.1.1.1.1.1.2, hi.1.1.1.1.2, hi.1.1.1.2, hi.1.1.2, hi.1.2, hi.2⟩

/-- **A copy's pad stands where its original's stood**, for two shapes with the same four
numbers. -/
theorem padRaw_same (codes : Codes) (so sn : OracleShape) (e1 : sn.maskRows = so.maskRows)
    (e2 : sn.mainRows = so.mainRows) (e3 : sn.mainDeg = so.mainDeg)
    (e4 : (codes.base.getD sn.code default).ell = (codes.base.getD so.code default).ell)
    (row place : ℕ) : padRaw codes sn row place ↔ padRaw codes so row place := by
  unfold padRaw eachZ
  show sn.maskRows = 0 ∧ row + 1 = sn.mainRows ∧
      (codes.base.getD sn.code default).ell ≤ place + (if sn.mainDeg = 3 then 1 else 3) ↔
    so.maskRows = 0 ∧ row + 1 = so.mainRows ∧
      (codes.base.getD so.code default).ell ≤ place + (if so.mainDeg = 3 then 1 else 3)
  rw [e1, e2, e3, e4]

/-- A shape without mask rows for which the program makes a pad has rows that are long enough for
it. -/
theorem fit_of_pad (codes : Codes) (s : OracleShape) (hm : s.maskRows = 0)
    (h : (Send.pad codes s).isSome = true) :
    eachZ s * s.answers ≤ (codes.base.getD s.code default).ell := by
  have hh : (Send.cube codes s).hasMask = false := by
    unfold Send.cube
    simp [hm]
  have he : (if (s.mainDeg == 3) = true then 1 else 3) = eachZ s := by
    unfold eachZ
    simp
  by_contra hlt
  have hn : Send.pad codes s = none := by
    unfold Send.pad
    simp only [hh, Bool.false_eq_true, if_false, Bool.false_or, he]
    rw [if_pos (by omega)]
  rw [hn] at h
  exact absurd h (by simp)

end Johnson.Top.H

#print axioms Johnson.Top.H.mem_pad_index
#print axioms Johnson.Top.H.padRaw_iff_mem
#print axioms Johnson.Top.H.KeptIs.hoff
#print axioms Johnson.Top.H.ents_tab
#print axioms Johnson.Top.H.iJ_off
#print axioms Johnson.Top.H.iJ_pad
#print axioms Johnson.Top.H.keptIs_of_iJ
#print axioms Johnson.Top.H.check_kept
#print axioms Johnson.Top.H.padRaw_same
#print axioms Johnson.Top.H.fit_of_pad
