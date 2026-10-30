-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchMaps.lean: the two maps of names of a code switch, written out of the
program's own frame, and what coefficients carried along them give at a table's index.

At the caller `switchSel` (Johnson/Top/H/SwitchSel.lean) two maps iJ and iQ say which entry of
which new message holds an entry of the open word's message, and of its randomness. There they are
letters. Here they are written out for the folded complex with kept slots (`Sg.cKept`,
OnBytes/Slice/CsRowKept.lean), from the record that the program computes once for a switch
(`SwitchFrame`, OnBytes/Iop/Cs.lean). An entry of a new message is named by three numbers
(`entAt`, Johnson/Top/H/SwitchNames.lean): which message of the sending, which table, the index.
The new oracle message g is message 0 of the sending; the message that takes the kept member
number i is message 1 + i (`switchVerify`: the notices' order). Definitions, statements and
proofs.

Where each entry lies, as the head of OnBytes/Iop/Cs.lean says it:
  the folded main row's message: in g's main table, at `cutIndex` of the main cut;
  a kept row's message: in the new message of its member, at row + 2^rowBits * place; but an entry
    at a place of the member's old pad: in the rest, from `oldPadAt` on, by its number in the pad;
  the two mask rows' messages, the main row's tail, the kept rows' tails, the mask rows' tails: in
    the rest, from `maskAt`, `mainTailAt`, `keptTailAt`, `maskTailAt` on.
Entry number i of the rest lies in g's table `restPart` at the index `places.get i`.

Main names:
  `Nm`: three numbers. `InTab cs l t`: t names an entry of the sending. `inTab_iff`: exactly then
    some entry has the numbers t.
  `mapOf nm h`: the map of names with the numbers nm. `entAt_mapOf`, `mapOf_unique`: it has these
    numbers, and it is the only map that has them.
  `readAt nm c t`: the sum of the c i with nm i = t. `pushTo_names`: coefficients carried along a
    map with the numbers nm, read at an entry, are `readAt` at the entry's numbers.
  `readAt_tab`, `readAt_rest`, `readAt_main`, `readAt_kept`: closed forms, in `stretchAt`
    (OnBytes/Slice/BlkCsStretch.lean) and `liftAt`. `sum_row`: the sum over one row's entries.
  `nameJ`, `nameQ`: the numbers of the entries of the message and of the randomness.
  `nameJ_read`, `nameQ_read`: `readAt` at them, table by table.
  `iJ`, `iQ`: the two maps. `pushTo_iJ`, `pushTo_iQ`: what is carried along them.
  `pushTo_inr`, `pushTo_inl`: a map into the second half of a sum of two families.
Limits: which slot holds which row of which kept member (mem, row, pl) are letters. That all names
lie in the tables of the sending is a premise of `iJ` and `iQ`. Where a part of the rest begins is
read off the frame's lists with 0 for a number that a list lacks, as `switchFrame` reads `maskAt`;
that the lists are long enough (two masks; one tail for each kept row) is not asked here, and where
one is too short the names are not the program's places. Nothing says that a program's rows
are the rows of `switchSel`. Nothing on soundness.

-/
import Johnson.Top.H.SwitchNames
import OnBytes.Slice.CsRowKept
import OnBytes.Slice.SwitchPlacesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

/-- An entry of a sending in the program's numbers: which message; which table; the index. -/
abbrev Nm : Type := ℕ × Part × ℕ

theorem nm_eq (a o : ℕ) (p part : Part) (x J : ℕ) :
    ((a, p, x) : Nm) = (o, part, J) ↔ (o = a ∧ part = p) ∧ x = J := by
  constructor
  · intro e
    exact ⟨⟨(congrArg (fun t : Nm => t.1) e).symm, (congrArg (fun t : Nm => t.2.1) e).symm⟩,
      congrArg (fun t : Nm => t.2.2) e⟩
  · rintro ⟨⟨rfl, rfl⟩, rfl⟩
    rfl

theorem ite_nm (a o : ℕ) (p part : Part) (x J : ℕ) (v : GE) :
    (if ((a, p, x) : Nm) = (o, part, J) then v else 0) =
      if o = a ∧ part = p then (if x = J then v else 0) else 0 := by
  by_cases h : o = a ∧ part = p
  · by_cases e : x = J
    · rw [if_pos h, if_pos e, if_pos ((nm_eq a o p part x J).2 ⟨h, e⟩)]
    · rw [if_pos h, if_neg e, if_neg fun k => e ((nm_eq a o p part x J).1 k).2]
  · rw [if_neg h, if_neg fun k => h ((nm_eq a o p part x J).1 k).1]

/-! ## The numbers that name an entry -/

section
variable (cs : Codes)

/-- The number of places in a row of a table of a shape. -/
def ellOf (s : OracleShape) : Part → ℕ
  | .main => (pMain cs s).ell
  | .mask => (pMask cs s).ell

/-- A coordinate of a shape's message in its main table, and in its mask table. -/
def jMain (s : OracleShape) (x : Fin s.mainRows × Fin (pMain cs s).ell) : (portCode cs s).J :=
  Sum.inl x
def jMask (s : OracleShape) (x : Fin s.maskRows × Fin (pMask cs s).ell) : (portCode cs s).J :=
  Sum.inr x

theorem idxOf_mk (rows ell n : ℕ) (h1 : n % 2 ^ ceilLog2 rows < rows)
    (h2 : n / 2 ^ ceilLog2 rows < ell) : idxOf rows ell (⟨_, h1⟩, ⟨_, h2⟩) = n :=
  Nat.mod_add_div n _

variable (l : List (OracleShape × ℕ))

/-- The entry of the message i at the coordinate j. -/
noncomputable def entMk (i : Fin l.length) (j : (portCode cs (l.get i).1).J) : (sigOf cs l).Ent :=
  ⟨i, j⟩

theorem entAt_entMk (i : Fin l.length) (j : (portCode cs (l.get i).1).J) :
    entAt cs l (entMk cs l i j) = (i.val, coordAt cs (l.get i).1 j) := rfl

/-- The three numbers name an entry of the sending: the message is there, the index's row is a row
of the table, and its place is a place of the row. -/
def InTab (t : Nm) : Prop :=
  ∃ h : t.1 < l.length,
    t.2.2 % 2 ^ ceilLog2 ((l.get ⟨t.1, h⟩).1.rows t.2.1) < (l.get ⟨t.1, h⟩).1.rows t.2.1 ∧
      t.2.2 / 2 ^ ceilLog2 ((l.get ⟨t.1, h⟩).1.rows t.2.1) < ellOf cs (l.get ⟨t.1, h⟩).1 t.2.1

theorem ent_of_inTab (t : Nm) (h : InTab cs l t) : ∃ e, entAt cs l e = t := by
  obtain ⟨o, part, n⟩ := t
  obtain ⟨ho, h1, h2⟩ := h
  cases part
  · refine ⟨entMk cs l ⟨o, ho⟩ (jMain cs _ (⟨_, h1⟩, ⟨_, h2⟩)), ?_⟩
    exact congrArg (fun v => ((o, Part.main, v) : Nm)) (Nat.mod_add_div n _)
  · refine ⟨entMk cs l ⟨o, ho⟩ (jMask cs _ (⟨_, h1⟩, ⟨_, h2⟩)), ?_⟩
    exact congrArg (fun v => ((o, Part.mask, v) : Nm)) (Nat.mod_add_div n _)

theorem inTab_entAt (e : (sigOf cs l).Ent) : InTab cs l (entAt cs l e) := by
  obtain ⟨i, j⟩ := e
  change (Fin (l.get i).1.mainRows × Fin (pMain cs (l.get i).1).ell) ⊕
    (Fin (l.get i).1.maskRows × Fin (pMask cs (l.get i).1).ell) at j
  rcases j with x | x
  · exact ⟨i.isLt, lt_of_eq_of_lt (idxOf_mod _ _ x) x.1.isLt,
      lt_of_eq_of_lt (idxOf_div _ _ x) x.2.isLt⟩
  · exact ⟨i.isLt, lt_of_eq_of_lt (idxOf_mod _ _ x) x.1.isLt,
      lt_of_eq_of_lt (idxOf_div _ _ x) x.2.isLt⟩

/-- The numbers that name an entry are exactly those of `InTab`. -/
theorem inTab_iff (t : Nm) : InTab cs l t ↔ ∃ e, entAt cs l e = t :=
  ⟨ent_of_inTab cs l t, fun ⟨e, h⟩ => h ▸ inTab_entAt cs l e⟩

/-- **The map of names with given numbers.** -/
noncomputable def mapOf {I : Type} (nm : I → Nm) (h : ∀ i, InTab cs l (nm i)) (i : I) :
    (sigOf cs l).Ent :=
  (ent_of_inTab cs l _ (h i)).choose

theorem entAt_mapOf {I : Type} (nm : I → Nm) (h : ∀ i, InTab cs l (nm i)) (i : I) :
    entAt cs l (mapOf cs l nm h i) = nm i :=
  (ent_of_inTab cs l _ (h i)).choose_spec

/-- No other map has these numbers. -/
theorem mapOf_unique {I : Type} (nm : I → Nm) (h : ∀ i, InTab cs l (nm i))
    (p : I → (sigOf cs l).Ent) (hp : ∀ i, entAt cs l (p i) = nm i) : p = mapOf cs l nm h :=
  funext fun i => entAt_inj cs l ((hp i).trans (entAt_mapOf cs l nm h i).symm)

theorem mapOf_inj {I : Type} (nm : I → Nm) (h : ∀ i, InTab cs l (nm i))
    (hn : Function.Injective nm) : Function.Injective (mapOf cs l nm h) := fun a b e =>
  hn (by rw [← entAt_mapOf cs l nm h a, ← entAt_mapOf cs l nm h b, e])

/-- The sum of the coefficients whose name has the numbers t. -/
def readAt {I : Type} [Fintype I] (nm : I → Nm) (c : I → GE) (t : Nm) : GE :=
  ∑ i, if nm i = t then c i else 0

/-- **Coefficients carried along a map of names, read at an entry.** -/
theorem pushTo_names {I : Type} [Fintype I] (p : I → (sigOf cs l).Ent) (nm : I → Nm)
    (hp : ∀ i, entAt cs l (p i) = nm i) (c : I → GE) (n : (sigOf cs l).Ent) :
    pushTo p c n = readAt nm c (entAt cs l n) := by
  unfold pushTo readAt
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases e : p i = n
  · rw [if_pos e, if_pos (by rw [← hp i, e])]
  · rw [if_neg e, if_neg fun k => e (entAt_inj cs l ((hp i).trans k))]

end

/-! ## Closed forms of `readAt` -/

theorem readAt_elim {I I' : Type} [Fintype I] [Fintype I'] (a : I → Nm) (b : I' → Nm)
    (c : I ⊕ I' → GE) (t : Nm) :
    readAt (Sum.elim a b) c t =
      readAt a (fun i => c (.inl i)) t + readAt b (fun i => c (.inr i)) t := by
  unfold readAt
  rw [Fintype.sum_sum_type]
  rfl

theorem readAt_opt {K F : Type} [Fintype K] [Fintype F] (a : Option K × F → Nm)
    (c : Option K × F → GE) (t : Nm) :
    readAt a c t = readAt (fun j => a (none, j)) (fun j => c (none, j)) t +
      ∑ k, readAt (fun j => a (some k, j)) (fun j => c (some k, j)) t := by
  unfold readAt
  rw [Fintype.sum_prod_type, Fintype.sum_option]

/-- Names that all lie in one table. -/
theorem readAt_tab {I : Type} [Fintype I] (o₀ : ℕ) (p₀ : Part) (f : I → ℕ) (c : I → GE)
    (o : ℕ) (part : Part) (J : ℕ) :
    readAt (fun i => ((o₀, p₀, f i) : Nm)) c (o, part, J) =
      if o = o₀ ∧ part = p₀ then ∑ i, if f i = J then c i else 0 else 0 := by
  unfold readAt
  simp only [ite_nm]
  by_cases h : o = o₀ ∧ part = p₀
  · simp only [if_pos h]
  · simp only [if_neg h]
    exact Finset.sum_const_zero

/-- Coefficients on finitely many numbers, as coefficients on all numbers. -/
def onNat {n : ℕ} (c : Fin n → GE) (i : ℕ) : GE := if h : i < n then c ⟨i, h⟩ else 0

/-- What coefficients on the entries of a vector that a cut places give on the index J. -/
def liftAt (cut : RowCut) (rowBits : ℕ) {n : ℕ} (c : Fin n → GE) (J : ℕ) : GE :=
  ∑ j : Fin n, if cutIndex cut rowBits j.val = J then c j else 0

/-- Entry number i of the rest. -/
def restAt (W : SwitchFrame) (i : ℕ) : Nm := (0, W.restPart, W.places.get i)

/-- Entry number j of the main row's message. -/
def mainNm (W : SwitchFrame) (j : ℕ) : Nm := (0, Part.main, cutIndex W.mainCut W.rowBits j)

/-- **A stretch of the rest.** -/
theorem readAt_rest (W : SwitchFrame) (a n : ℕ) (c : Fin n → GE) (o : ℕ) (part : Part) (J : ℕ) :
    readAt (fun j : Fin n => restAt W (a + j.val)) c (o, part, J) =
      if o = 0 ∧ part = W.restPart then stretchAt W.places a n (onNat c) J else 0 :=
  (readAt_tab 0 W.restPart (fun j : Fin n => W.places.get (a + j.val)) c o part J).trans
    (congrArg (fun v : GE => if o = 0 ∧ part = W.restPart then v else 0)
      (pushTo_stretch W.places a n c J))

/-- **The main row's message.** -/
theorem readAt_main (W : SwitchFrame) (n : ℕ) (c : Fin n → GE) (o : ℕ) (part : Part) (J : ℕ) :
    readAt (fun j : Fin n => mainNm W j.val) c (o, part, J) =
      if o = 0 ∧ part = Part.main then liftAt W.mainCut W.rowBits c J else 0 :=
  readAt_tab 0 Part.main (fun j : Fin n => cutIndex W.mainCut W.rowBits j.val) c o part J

/-- Where the cut's indices are one to one, the index of entry j₀ gets that entry's coefficient. -/
theorem liftAt_at (cut : RowCut) (rowBits : ℕ) (h : 2 ^ cut.bits ≤ 2 ^ rowBits) {n : ℕ}
    (c : Fin n → GE) (j₀ : Fin n) : liftAt cut rowBits c (cutIndex cut rowBits j₀.val) = c j₀ :=
  pushTo_one (fun j : Fin n => cutIndex cut rowBits j.val)
    (fun _ _ e => Fin.ext (cutIndex_inj h e)) c j₀

/-- An index that is no entry's gets 0. -/
theorem liftAt_off (cut : RowCut) (rowBits : ℕ) {n : ℕ} (c : Fin n → GE) (J : ℕ)
    (h : ∀ j : Fin n, cutIndex cut rowBits j.val ≠ J) : liftAt cut rowBits c J = 0 :=
  Finset.sum_eq_zero fun j _ => if_neg (h j)

/-- The entries of one row of a table, read at an index: the index's row must be that row, and then
the index's place says which entry it is. -/
theorem sum_row (rb b n : ℕ) (hb : b < 2 ^ rb) (c : Fin n → GE) (J : ℕ) :
    (∑ j : Fin n, if b + 2 ^ rb * j.val = J then c j else 0) =
      if J % 2 ^ rb = b then onNat c (J / 2 ^ rb) else 0 := by
  have key : ∀ j : ℕ, b + 2 ^ rb * j = J → J % 2 ^ rb = b ∧ J / 2 ^ rb = j := by
    intro j e
    subst e
    constructor
    · rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hb
    · rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hb, Nat.zero_add]
  by_cases h : J % 2 ^ rb = b
  · rw [if_pos h]
    unfold onNat
    by_cases hn : J / 2 ^ rb < n
    · rw [dif_pos hn, Finset.sum_eq_single (⟨J / 2 ^ rb, hn⟩ : Fin n)]
      · rw [if_pos]
        show b + 2 ^ rb * (J / 2 ^ rb) = J
        rw [← h]
        exact Nat.mod_add_div J _
      · intro j _ hj
        rw [if_neg]
        intro e
        exact hj (Fin.ext (key j.val e).2.symm)
      · intro hx
        exact absurd (Finset.mem_univ _) hx
    · rw [dif_neg hn]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro e
      exact hn ((key j.val e).2 ▸ j.isLt)
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    intro e
    exact h (key j.val e).1

/-! ## A kept row's message -/

/-- The number, in a pad, of the first place with the index x; the pad's length if there is none. -/
def padNoOf : List PadPlace → ℕ → ℕ
  | [], _ => 0
  | p :: ps, x => if p.index = x then 0 else padNoOf ps x + 1

/-- A sum over the numbers of a pad's places that at most one place hits. -/
theorem sum_padNo : ∀ (pad : List PadPlace), (pad.map (·.index)).Nodup → ∀ (x : ℕ) (F : ℕ → GE),
    (∑ q ∈ Finset.range pad.length, if x = (pad.getD q default).index then F q else 0) =
      if x ∈ pad.map (·.index) then F (padNoOf pad x) else 0
  | [], _, _, _ => by simp
  | a :: l, hn, x, F => by
    rw [List.map_cons, List.nodup_cons] at hn
    have e : (∑ q ∈ Finset.range l.length,
        if x = ((a :: l).getD (q + 1) default).index then F (q + 1) else 0) =
        ∑ q ∈ Finset.range l.length,
          if x = (l.getD q default).index then (fun q => F (q + 1)) q else 0 :=
      Finset.sum_congr rfl fun q _ => by rw [List.getD_cons_succ]
    rw [List.length_cons, Finset.sum_range_succ', e, sum_padNo l hn.2 x fun q => F (q + 1),
      List.getD_cons_zero]
    by_cases h : a.index = x
    · subst h
      simp [padNoOf, hn.1]
    · have h' : ¬ x = a.index := fun k => h k.symm
      simp [padNoOf, h, h']

/-- The entry with the index x of the main table of the kept member number i: it lies in the
member's new message at the same index; but at a place of the old pad it lies in the rest. -/
def keptNm (W : SwitchFrame) (i : ℕ) (k : KeptPlace) (x : ℕ) : Nm :=
  if x ∈ k.pad.map (·.index) then restAt W (k.oldPadAt + padNoOf k.pad x)
  else (1 + i, Part.main, x)

/-- Entry number j of the row b of the kept member number i. -/
def keptAt (W : SwitchFrame) (i : ℕ) (k : KeptPlace) (b j : ℕ) : Nm :=
  keptNm W i k (b + 2 ^ k.rowBits * j)

theorem keptNm_term (W : SwitchFrame) (i : ℕ) (k : KeptPlace) (x : ℕ) (v : GE) (o : ℕ)
    (part : Part) (J : ℕ) :
    (if keptNm W i k x = (o, part, J) then v else 0) =
      (if o = 1 + i ∧ part = Part.main then
        (if J ∈ k.pad.map (·.index) then 0 else if x = J then v else 0) else 0) +
      if o = 0 ∧ part = W.restPart then
        (if x ∈ k.pad.map (·.index) then
          (if W.places.get (k.oldPadAt + padNoOf k.pad x) = J then v else 0) else 0) else 0 := by
  unfold keptNm restAt
  by_cases hP : x ∈ k.pad.map (·.index)
  · have z : (if o = 1 + i ∧ part = Part.main then
        (if J ∈ k.pad.map (·.index) then (0 : GE) else if x = J then v else 0) else 0) = 0 := by
      by_cases h1 : o = 1 + i ∧ part = Part.main
      · rw [if_pos h1]
        by_cases hJ : J ∈ k.pad.map (·.index)
        · rw [if_pos hJ]
        · rw [if_neg hJ, if_neg fun e => hJ (by rw [← e]; exact hP)]
      · rw [if_neg h1]
    rw [z, zero_add]
    simp only [if_pos hP, ite_nm]
  · have y : (if J ∈ k.pad.map (·.index) then (0 : GE) else if x = J then v else 0) =
        if x = J then v else 0 := by
      by_cases hJ : J ∈ k.pad.map (·.index)
      · rw [if_pos hJ, if_neg fun e => hP (by rw [e]; exact hJ)]
      · rw [if_neg hJ]
    rw [y]
    simp only [if_neg hP, ite_nm, ite_self, add_zero]

/-- **A kept row's message**: on its member's new message the coefficients, but 0 at the places of
the old pad; on the rest the coefficients at these places, laid where the old pad is. -/
theorem readAt_kept (W : SwitchFrame) (i : ℕ) (k : KeptPlace) (b n : ℕ) (c : Fin n → GE)
    (hn : (k.pad.map (·.index)).Nodup) (o : ℕ) (part : Part) (J : ℕ) :
    readAt (fun j : Fin n => keptAt W i k b j.val) c (o, part, J) =
      (if o = 1 + i ∧ part = Part.main then
        (if J ∈ k.pad.map (·.index) then 0
          else ∑ j : Fin n, if b + 2 ^ k.rowBits * j.val = J then c j else 0) else 0) +
      if o = 0 ∧ part = W.restPart then
        stretchAt W.places k.oldPadAt k.pad.length
          (fun q => ∑ j : Fin n,
            if b + 2 ^ k.rowBits * j.val = (k.pad.getD q default).index then c j else 0) J
      else 0 := by
  unfold readAt keptAt
  simp only [keptNm_term]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases h1 : o = 1 + i ∧ part = Part.main
    · simp only [if_pos h1]
      by_cases hJ : J ∈ k.pad.map (·.index)
      · simp only [if_pos hJ]
        exact Finset.sum_const_zero
      · simp only [if_neg hJ]
    · simp only [if_neg h1]
      exact Finset.sum_const_zero
  · by_cases h2 : o = 0 ∧ part = W.restPart
    · simp only [if_pos h2]
      unfold stretchAt
      have e : (∑ q ∈ Finset.range k.pad.length,
          if W.places.get (k.oldPadAt + q) = J then
            ∑ j : Fin n, if b + 2 ^ k.rowBits * j.val = (k.pad.getD q default).index then c j
              else 0
          else 0) =
          ∑ q ∈ Finset.range k.pad.length, ∑ j : Fin n,
            if b + 2 ^ k.rowBits * j.val = (k.pad.getD q default).index then
              (if W.places.get (k.oldPadAt + q) = J then c j else 0) else 0 := by
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases g : W.places.get (k.oldPadAt + q) = J
        · simp only [if_pos g]
        · simp only [if_neg g, ite_self]
          exact Finset.sum_const_zero.symm
      rw [e, Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ =>
        (sum_padNo k.pad hn (b + 2 ^ k.rowBits * j.val)
          fun q => if W.places.get (k.oldPadAt + q) = J then c j else 0).symm
    · simp only [if_neg h2]
      exact Finset.sum_const_zero

/-! ## The two maps -/

section
variable (s : Sg) {K : Type} [Fintype K] [DecidableEq K] (W : SwitchFrame)
  (mem row : K → ℕ) (pl : K → KeptPlace)

/-- The running number of the row b of the kept member number i among all kept rows. -/
def keptNo (i b : ℕ) : ℕ := ((W.kept.take i).map (·.rows)).sum + b

/-- **The numbers of the entries of the open word's message.** mem k, row k, pl k: the slot k holds
the row number row k of the kept member number mem k, whose record in the frame is pl k. -/
def nameJ : (Option K × Fin s.C.l) ⊕ (Fin s.Z.l ⊕ Fin s.Z.l) → Nm :=
  Sum.elim
    (fun x => x.1.elim (mainNm W x.2.val) fun k => keptAt W (mem k) (pl k) (row k) x.2.val)
    (Sum.elim (fun j => restAt W (W.parts.maskAt.getD 0 0 + j.val))
      fun j => restAt W (W.parts.maskAt.getD 1 0 + j.val))

/-- **The numbers of the entries of the open word's randomness.** -/
def nameQ : (Option K × Fin s.C.r) ⊕ (Fin s.Z.r ⊕ Fin s.Z.r) → Nm :=
  Sum.elim
    (fun x => x.1.elim (restAt W (W.parts.mainTailAt + x.2.val)) fun k =>
      restAt W (W.parts.keptTailAt.getD (keptNo W (mem k) (row k)) 0 + x.2.val))
    (Sum.elim (fun q => restAt W (W.parts.maskTailAt.getD 0 0 + q.val))
      fun q => restAt W (W.parts.maskTailAt.getD 1 0 + q.val))

omit [DecidableEq K] in
/-- **Coefficients on the message's entries, table by table.** -/
theorem nameJ_read (c : (Option K × Fin s.C.l) ⊕ (Fin s.Z.l ⊕ Fin s.Z.l) → GE)
    (hn : ∀ k, ((pl k).pad.map (·.index)).Nodup) (o : ℕ) (part : Part) (J : ℕ) :
    readAt (nameJ s W mem row pl) c (o, part, J) =
      ((if o = 0 ∧ part = Part.main then
          liftAt W.mainCut W.rowBits (fun j => c (.inl (none, j))) J else 0) +
        ∑ k, ((if o = 1 + mem k ∧ part = Part.main then
            (if J ∈ (pl k).pad.map (·.index) then 0
              else ∑ j : Fin s.C.l,
                if row k + 2 ^ (pl k).rowBits * j.val = J then c (.inl (some k, j)) else 0)
            else 0) +
          if o = 0 ∧ part = W.restPart then
            stretchAt W.places (pl k).oldPadAt (pl k).pad.length
              (fun q => ∑ j : Fin s.C.l,
                if row k + 2 ^ (pl k).rowBits * j.val = ((pl k).pad.getD q default).index then
                  c (.inl (some k, j)) else 0) J
          else 0)) +
      ((if o = 0 ∧ part = W.restPart then
          stretchAt W.places (W.parts.maskAt.getD 0 0) s.Z.l
            (onNat fun j => c (.inr (.inl j))) J else 0) +
        if o = 0 ∧ part = W.restPart then
          stretchAt W.places (W.parts.maskAt.getD 1 0) s.Z.l
            (onNat fun j => c (.inr (.inr j))) J else 0) := by
  unfold nameJ
  rw [readAt_elim, readAt_opt, readAt_elim]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (readAt_main W s.C.l (fun j => c (.inl (none, j))) o part J)
      (Finset.sum_congr rfl fun k _ =>
        readAt_kept W (mem k) (pl k) (row k) s.C.l (fun j => c (.inl (some k, j))) (hn k) o part J))
    (congrArg₂ (· + ·)
      (readAt_rest W (W.parts.maskAt.getD 0 0) s.Z.l (fun j => c (.inr (.inl j))) o part J)
      (readAt_rest W (W.parts.maskAt.getD 1 0) s.Z.l (fun j => c (.inr (.inr j))) o part J))

omit [DecidableEq K] in
/-- **Coefficients on the randomness' entries**: all lie in the rest. -/
theorem nameQ_read (c : (Option K × Fin s.C.r) ⊕ (Fin s.Z.r ⊕ Fin s.Z.r) → GE) (o : ℕ)
    (part : Part) (J : ℕ) :
    readAt (nameQ s W mem row) c (o, part, J) =
      ((if o = 0 ∧ part = W.restPart then
          stretchAt W.places W.parts.mainTailAt s.C.r (onNat fun q => c (.inl (none, q))) J
          else 0) +
        ∑ k, if o = 0 ∧ part = W.restPart then
          stretchAt W.places (W.parts.keptTailAt.getD (keptNo W (mem k) (row k)) 0) s.C.r
            (onNat fun q => c (.inl (some k, q))) J else 0) +
      ((if o = 0 ∧ part = W.restPart then
          stretchAt W.places (W.parts.maskTailAt.getD 0 0) s.Z.r
            (onNat fun q => c (.inr (.inl q))) J else 0) +
        if o = 0 ∧ part = W.restPart then
          stretchAt W.places (W.parts.maskTailAt.getD 1 0) s.Z.r
            (onNat fun q => c (.inr (.inr q))) J else 0) := by
  unfold nameQ
  rw [readAt_elim, readAt_opt, readAt_elim]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·)
      (readAt_rest W W.parts.mainTailAt s.C.r (fun q => c (.inl (none, q))) o part J)
      (Finset.sum_congr rfl fun k _ =>
        readAt_rest W (W.parts.keptTailAt.getD (keptNo W (mem k) (row k)) 0) s.C.r
          (fun q => c (.inl (some k, q))) o part J))
    (congrArg₂ (· + ·)
      (readAt_rest W (W.parts.maskTailAt.getD 0 0) s.Z.r (fun q => c (.inr (.inl q))) o part J)
      (readAt_rest W (W.parts.maskTailAt.getD 1 0) s.Z.r (fun q => c (.inr (.inr q))) o part J))

variable (cs : Codes) (l : List (OracleShape × ℕ))

/-- **iJ**: which entry of which new message holds an entry of the open word's message. -/
noncomputable def iJ (h : ∀ x, InTab cs l (nameJ s W mem row pl x)) :
    (s.cKept K).J → (sigOf cs l).Ent :=
  mapOf cs l (nameJ s W mem row pl) h

/-- **iQ**: the same of the open word's randomness. -/
noncomputable def iQ (h : ∀ x, InTab cs l (nameQ s W mem row x)) :
    (s.cKept K).Q → (sigOf cs l).Ent :=
  mapOf cs l (nameQ s W mem row) h

theorem entAt_iJ (h : ∀ x, InTab cs l (nameJ s W mem row pl x)) (x : (s.cKept K).J) :
    entAt cs l (iJ s W mem row pl cs l h x) = nameJ s W mem row pl x :=
  entAt_mapOf cs l _ h x

theorem entAt_iQ (h : ∀ x, InTab cs l (nameQ s W mem row x)) (x : (s.cKept K).Q) :
    entAt cs l (iQ s W mem row cs l h x) = nameQ s W mem row x :=
  entAt_mapOf cs l _ h x

/-- **What is carried along iJ, read at an entry.** -/
theorem pushTo_iJ (h : ∀ x, InTab cs l (nameJ s W mem row pl x)) (c : (s.cKept K).J → GE)
    (n : (sigOf cs l).Ent) :
    pushTo (iJ s W mem row pl cs l h) c n = readAt (nameJ s W mem row pl) c (entAt cs l n) :=
  pushTo_names cs l _ _ (entAt_iJ s W mem row pl cs l h) c n

/-- **What is carried along iQ, read at an entry.** -/
theorem pushTo_iQ (h : ∀ x, InTab cs l (nameQ s W mem row x)) (c : (s.cKept K).Q → GE)
    (n : (sigOf cs l).Ent) :
    pushTo (iQ s W mem row cs l h) c n = readAt (nameQ s W mem row) c (entAt cs l n) :=
  pushTo_names cs l _ _ (entAt_iQ s W mem row cs l h) c n

end

/-! ## A map into the second half of a sum of two families -/

section
variable {I A B : Type} [Fintype I] {F : A ⊕ B → Type} (p : I → Σ b : B, F (.inr b)) (c : I → GE)

omit [Fintype I] in
theorem inr_inj : Function.Injective
    (fun m : Σ b : B, F (.inr b) => (⟨.inr m.1, m.2⟩ : Σ a, F a)) := by
  rintro ⟨a, x⟩ ⟨a', x'⟩ k
  have k' : (⟨.inr a, x⟩ : Σ a, F a) = ⟨.inr a', x'⟩ := k
  cases k'
  rfl

theorem pushTo_inr (n : Σ b : B, F (.inr b)) :
    pushTo (fun i => (⟨.inr (p i).1, (p i).2⟩ : Σ a, F a)) c ⟨.inr n.1, n.2⟩ = pushTo p c n := by
  unfold pushTo
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases e : p i = n
  · rw [if_pos e,
      if_pos (congrArg (fun m : Σ b : B, F (.inr b) => (⟨.inr m.1, m.2⟩ : Σ a, F a)) e)]
  · rw [if_neg e, if_neg fun k => e (inr_inj k)]

theorem pushTo_inl (a : A) (x : F (.inl a)) :
    pushTo (fun i => (⟨.inr (p i).1, (p i).2⟩ : Σ a, F a)) c ⟨.inl a, x⟩ = 0 := by
  unfold pushTo
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [if_neg]
  intro k
  cases k

end

end Johnson.Top.H

#print axioms Johnson.Top.H.inTab_iff
#print axioms Johnson.Top.H.mapOf_unique
#print axioms Johnson.Top.H.pushTo_names
#print axioms Johnson.Top.H.sum_row
#print axioms Johnson.Top.H.readAt_kept
#print axioms Johnson.Top.H.nameJ_read
#print axioms Johnson.Top.H.nameQ_read
#print axioms Johnson.Top.H.pushTo_iJ
#print axioms Johnson.Top.H.pushTo_iQ
#print axioms Johnson.Top.H.pushTo_inr
#print axioms Johnson.Top.H.pushTo_inl
