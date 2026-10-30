-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/SwitchPlacesLaws.lean: laws on the places at which a code switch lays «the
rest» into the new oracle message g: the program's pure functions `cutIndex`, `SwitchPlaces.get`
and `SwitchPlaces.make` (OnBytes/Iop/Cs.lean). Numbers and lists alone: no field, no oracle, no
run.

A cut lays entry j of a vector at row firstRow + j mod 2^bits, place j div 2^bits, of a table whose
rows are numbered by rowBits bits: index row + place * 2^rowBits. The rest steps over the entries of
the block that belong to the pad of g's sample: `get P i` is the cut's index of `skip P.pad i`.

Main statements. B: 2^bits; R: 2^rowBits.
  `skip_lt`, `le_skip`, `skip_le`: skip is strictly increasing; i ≤ skip pad i ≤ i + pad.length.
  `skip_not_mem`: for a strictly increasing pad, skip pad i is no entry of the pad.
  `cutIndex_mod`, `cutIndex_div`: where the block lies inside the table's rows (firstRow + B ≤ R):
    the index's row and place are those of the head of this file.
  `cutIndex_lt`, `cutIndex_inj`: where B ≤ R, cutIndex is strictly increasing, so one to one.
  `get_lt`, `get_inj`: so is get.
  `get_row`, `get_place_lt`: get stays in the block: its row lies in [firstRow, firstRow + B); its
    place lies below ell for every i below ell * B - pad.length.
  `make_get_ne_pad`: get of the places that the program makes is the index of no entry of the pad
    of g's sample in that table.
  `make_pad_rises`: the numbers of the pad that the program makes increase strictly, for a target
    whose main rows are over the extension field.
  `of_check`, `places_of_check`: under the program's own test on the public sizes
    (switchTargetCheck) both conditions below hold; so the places of the rest increase strictly,
    stay in the rest's block (the place: for every i below the places' number) and miss the pad of
    g's sample.
Conditions of the single laws, on public numbers: `Fits`: firstRow + B ≤ R.
`P.pad.Pairwise (· < ·)`: the pad's numbers increase strictly (`padRises`: the same as a test that
can be evaluated).
Limits: nothing on what is laid at the places, nor on `switchParts`.
-/
import OnBytes.Iop.Cs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes
namespace SwitchPlaces

/-- Entry i of the rest, numbered in the order in which the block is filled. -/
def skip (pad : List Nat) (i : Nat) : Nat := pad.foldl (fun j p => if p ≤ j then j + 1 else j) i

theorem get_eq (P : SwitchPlaces) (i : Nat) :
    P.get i = cutIndex P.cut P.rowBits (skip P.pad i) := rfl

theorem skip_nil (i : Nat) : skip [] i = i := rfl

theorem skip_cons (p : Nat) (ps : List Nat) (i : Nat) :
    skip (p :: ps) i = skip ps (if p ≤ i then i + 1 else i) := rfl

/-- skip is strictly increasing. -/
theorem skip_lt : ∀ (pad : List Nat) {i i' : Nat}, i < i' → skip pad i < skip pad i'
  | [], _, _, h => h
  | p :: ps, i, i', h => by
      rw [skip_cons, skip_cons]
      apply skip_lt ps
      split <;> split <;> omega

theorem le_skip : ∀ (pad : List Nat) (i : Nat), i ≤ skip pad i
  | [], _ => Nat.le_refl _
  | p :: ps, i => by
      rw [skip_cons]
      by_cases hp : p ≤ i
      · rw [if_pos hp]
        have := le_skip ps (i + 1)
        omega
      · rw [if_neg hp]
        exact le_skip ps i

theorem skip_le : ∀ (pad : List Nat) (i : Nat), skip pad i ≤ i + pad.length
  | [], _ => Nat.le_refl _
  | p :: ps, i => by
      rw [skip_cons, List.length_cons]
      by_cases hp : p ≤ i
      · rw [if_pos hp]
        have := skip_le ps (i + 1)
        omega
      · rw [if_neg hp]
        have := skip_le ps i
        omega

/-- Below all entries of the pad nothing is stepped over. -/
theorem skip_of_lt : ∀ (pad : List Nat) (i : Nat), (∀ p ∈ pad, i < p) → skip pad i = i
  | [], _, _ => rfl
  | p :: ps, i, h => by
      have hp : i < p := h p (List.mem_cons_self ..)
      rw [skip_cons, if_neg (by omega)]
      exact skip_of_lt ps i fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- **skip misses the pad.** -/
theorem skip_not_mem : ∀ (pad : List Nat), pad.Pairwise (· < ·) → ∀ i : Nat, skip pad i ∉ pad
  | [], _, _ => by simp
  | p :: ps, h, i => by
      rw [List.pairwise_cons] at h
      rw [skip_cons]
      intro hm
      rcases List.mem_cons.1 hm with he | hin
      · by_cases hpi : p ≤ i
        · rw [if_pos hpi] at he
          have := le_skip ps (i + 1)
          omega
        · rw [if_neg hpi] at he
          rw [skip_of_lt ps i fun q hq => by have := h.1 q hq; omega] at he
          omega
      · exact skip_not_mem ps h.2 _ hin

end SwitchPlaces

/-- The block lies inside the table's rows. -/
def RowCut.Fits (cut : RowCut) (rowBits : Nat) : Prop := cut.firstRow + 2 ^ cut.bits ≤ 2 ^ rowBits

theorem cutIndex_mod {cut : RowCut} {rb : Nat} (h : cut.Fits rb) (j : Nat) :
    cutIndex cut rb j % 2 ^ rb = cut.firstRow + j % 2 ^ cut.bits := by
  unfold cutIndex
  have hm : j % 2 ^ cut.bits < 2 ^ cut.bits := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by unfold RowCut.Fits at h; omega)

theorem cutIndex_div {cut : RowCut} {rb : Nat} (h : cut.Fits rb) (j : Nat) :
    cutIndex cut rb j / 2 ^ rb = j / 2 ^ cut.bits := by
  unfold cutIndex
  have hm : j % 2 ^ cut.bits < 2 ^ cut.bits := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (by unfold RowCut.Fits at h; omega), Nat.zero_add]

/-- **cutIndex is strictly increasing** where a block's rows are at most the table's. -/
theorem cutIndex_lt {cut : RowCut} {rb : Nat} (h : 2 ^ cut.bits ≤ 2 ^ rb) {j j' : Nat}
    (hj : j < j') : cutIndex cut rb j < cutIndex cut rb j' := by
  unfold cutIndex
  have hB : 0 < 2 ^ cut.bits := Nat.two_pow_pos _
  have hm : j % 2 ^ cut.bits < 2 ^ cut.bits := Nat.mod_lt _ hB
  have hq : j / 2 ^ cut.bits ≤ j' / 2 ^ cut.bits := Nat.div_le_div_right (Nat.le_of_lt hj)
  rcases Nat.eq_or_lt_of_le hq with he | hl
  · have e1 := Nat.div_add_mod j (2 ^ cut.bits)
    have e2 := Nat.div_add_mod j' (2 ^ cut.bits)
    rw [he] at e1
    rw [he]
    omega
  · have hmul : (j / 2 ^ cut.bits + 1) * 2 ^ rb ≤ (j' / 2 ^ cut.bits) * 2 ^ rb :=
      Nat.mul_le_mul_right _ hl
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega

/-- **cutIndex is one to one.** -/
theorem cutIndex_inj {cut : RowCut} {rb : Nat} (h : 2 ^ cut.bits ≤ 2 ^ rb) {j j' : Nat}
    (he : cutIndex cut rb j = cutIndex cut rb j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with hl | hl | hl
  · have := cutIndex_lt (cut := cut) h hl; omega
  · exact hl
  · have := cutIndex_lt (cut := cut) h hl; omega

theorem RowCut.Fits.le {cut : RowCut} {rb : Nat} (h : cut.Fits rb) : 2 ^ cut.bits ≤ 2 ^ rb := by
  unfold RowCut.Fits at h; omega

namespace SwitchPlaces

/-- **get is strictly increasing.** -/
theorem get_lt (P : SwitchPlaces) (h : 2 ^ P.cut.bits ≤ 2 ^ P.rowBits) {i i' : Nat} (hi : i < i') :
    P.get i < P.get i' := by
  rw [get_eq, get_eq]
  exact cutIndex_lt h (skip_lt P.pad hi)

theorem get_inj (P : SwitchPlaces) (h : 2 ^ P.cut.bits ≤ 2 ^ P.rowBits) {i i' : Nat}
    (he : P.get i = P.get i') : i = i' := by
  rcases Nat.lt_trichotomy i i' with hl | hl | hl
  · have := P.get_lt h hl; omega
  · exact hl
  · have := P.get_lt h hl; omega

/-- **get stays in the block**: its row. -/
theorem get_row (P : SwitchPlaces) (h : P.cut.Fits P.rowBits) (i : Nat) :
    P.cut.firstRow ≤ P.get i % 2 ^ P.rowBits ∧
      P.get i % 2 ^ P.rowBits < P.cut.firstRow + 2 ^ P.cut.bits := by
  rw [get_eq, cutIndex_mod h]
  have := Nat.mod_lt (skip P.pad i) (Nat.two_pow_pos P.cut.bits)
  omega

/-- **get stays in the block**: its place. ell: the places of a row. -/
theorem get_place_lt (P : SwitchPlaces) (h : P.cut.Fits P.rowBits) (ell : Nat) {i : Nat}
    (hi : i < ell * 2 ^ P.cut.bits - P.pad.length) : P.get i / 2 ^ P.rowBits < ell := by
  rw [get_eq, cutIndex_div h]
  have := skip_le P.pad i
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)

/-- The pad's numbers increase strictly: as a test. -/
def padRises (P : SwitchPlaces) : Bool := (P.pad.zip (P.pad.drop 1)).all fun x => decide (x.1 < x.2)

/-- **get misses the pad of g's sample.** -/
theorem make_get_ne_pad (codes : Codes) (T : SwitchTarget)
    (h : T.rest.Fits (switchRowBits T T.rest.part))
    (hp : (make codes T).pad.Pairwise (· < ·)) (i : Nat) (p : PadPlace)
    (hm : p ∈ padPlaces codes T.shape) (hpart : p.part = T.rest.part) :
    (make codes T).get i ≠ p.index := by
  intro he
  have hcut : (make codes T).cut = T.rest := rfl
  have hrb : (make codes T).rowBits = switchRowBits T T.rest.part := rfl
  have hfit : (make codes T).cut.Fits (make codes T).rowBits := by rw [hcut, hrb]; exact h
  have hrow := (make codes T).get_row hfit i
  have hmod := cutIndex_mod hfit (skip (make codes T).pad i)
  have hdiv := cutIndex_div hfit (skip (make codes T).pad i)
  rw [← get_eq, he] at hmod hdiv
  rw [he] at hrow
  rw [hcut, hrb] at hmod hdiv hrow
  apply skip_not_mem _ hp i
  show skip (make codes T).pad i ∈ List.mergeSort _ _
  rw [List.mem_mergeSort, List.mem_filterMap]
  refine ⟨p, hm, ?_⟩
  have hc : (p.part == T.rest.part &&
      decide (T.rest.firstRow ≤ p.index % 2 ^ switchRowBits T T.rest.part) &&
      decide (p.index % 2 ^ switchRowBits T T.rest.part < T.rest.firstRow + 2 ^ T.rest.bits)) =
        true := by
    simp [hpart, hrow.1, hrow.2]
  simp only [hc, if_true]
  have e := Nat.div_add_mod (skip (make codes T).pad i) (2 ^ T.rest.bits)
  rw [hmod, hdiv, Nat.mul_comm (skip (make codes T).pad i / 2 ^ T.rest.bits)]
  congr 1
  omega

/-! ### The pad's numbers increase strictly -/

/-- The pad of a shape whose sample takes one entry an answer: one row, places one after the
other. -/
theorem padPlaces_eq (codes : Codes) (s : OracleShape) (h3 : s.mainDeg = 3) :
    ∃ (part : Part) (base : Nat), padPlaces codes s = [] ∨
      padPlaces codes s = (List.range s.answers).map fun i =>
        { part := part, index := (s.rows part - 1) + (base + i) * 2 ^ ceilLog2 (s.rows part),
          answer := i, basis := thetaE 0 } := by
  unfold padPlaces Send.pad
  by_cases hm : 0 < s.maskRows
  · refine ⟨.mask, (codes.mask.getD s.maskCode default).ell - 1 * s.answers, ?_⟩
    simp only [Send.cube, hm, decide_true, if_true, Bool.true_or]
    split
    · left; rfl
    · right
      rw [List.map_eq_flatMap]
      simp [OracleShape.rows, List.range_succ, Nat.add_assoc]
  · refine ⟨.main, (codes.base.getD s.code default).ell - 1 * s.answers, ?_⟩
    simp only [Send.cube, hm, decide_false, if_false, Bool.false_or, h3, beq_self_eq_true, if_true,
      Bool.false_eq_true]
    split
    · left; rfl
    · right
      by_cases h0 : 0 < s.mainRows
      · rw [List.map_eq_flatMap]
        simp [OracleShape.rows, List.range_succ, Nat.add_assoc, h0]
      · have : s.mainRows = 0 := by omega
        rw [List.map_eq_flatMap]
        simp [OracleShape.rows, List.range_succ, Nat.add_assoc, this, ceilLog2]

/-- **The numbers of the pad that the program makes increase strictly**, for a target whose main
rows are over the extension field (switchTargetCheck asks that). -/
theorem make_pad_rises (codes : Codes) (T : SwitchTarget) (h3 : T.shape.mainDeg = 3) :
    (make codes T).pad.Pairwise (· < ·) := by
  have key : ((padPlaces codes T.shape).filterMap fun p =>
      let row := p.index % 2 ^ switchRowBits T T.rest.part
      let place := p.index / 2 ^ switchRowBits T T.rest.part
      if p.part == T.rest.part && T.rest.firstRow ≤ row && row < T.rest.firstRow + 2 ^ T.rest.bits
      then some (row - T.rest.firstRow + place * 2 ^ T.rest.bits) else none).Pairwise (· < ·) := by
    obtain ⟨part, base, h | h⟩ := padPlaces_eq codes T.shape h3
    · rw [h]; simp
    · rw [h]
      by_cases hp : part = T.rest.part
      · subst hp
        have hrow : T.shape.rows T.rest.part - 1 < 2 ^ ceilLog2 (T.shape.rows T.rest.part) := by
          have h1 : T.shape.rows T.rest.part ≤ 2 ^ ceilLog2 (T.shape.rows T.rest.part) := by
            unfold ceilLog2
            split
            · simpa using ‹_›
            · have := Nat.lt_log2_self (n := T.shape.rows T.rest.part - 1)
              omega
          have := Nat.two_pow_pos (ceilLog2 (T.shape.rows T.rest.part))
          omega
        apply List.Pairwise.filterMap (R := fun a b => a.index % 2 ^ switchRowBits T T.rest.part =
          b.index % 2 ^ switchRowBits T T.rest.part ∧
          a.index / 2 ^ switchRowBits T T.rest.part < b.index / 2 ^ switchRowBits T T.rest.part)
        · intro a a' hR b hb b' hb'
          have hb : _ = some b := hb
          have hb' : _ = some b' := hb'
          simp only at hb hb'
          split at hb <;> split at hb' <;> simp at hb hb'
          subst hb; subst hb'
          rw [hR.1]
          have := Nat.mul_le_mul_right (2 ^ T.rest.bits) (Nat.succ_le_of_lt hR.2)
          have hB := Nat.two_pow_pos T.rest.bits
          rw [Nat.succ_mul] at this
          omega
        · rw [List.pairwise_map]
          apply List.Pairwise.imp _ List.pairwise_lt_range
          intro i j hij
          simp only [switchRowBits]
          rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
            Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
            Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
            Nat.div_eq_of_lt hrow]
          exact ⟨rfl, by omega⟩
      · rw [List.filterMap_map]
        have : ∀ i ∈ List.range T.shape.answers, (((fun p : PadPlace =>
            let row := p.index % 2 ^ switchRowBits T T.rest.part
            let place := p.index / 2 ^ switchRowBits T T.rest.part
            if p.part == T.rest.part && T.rest.firstRow ≤ row &&
              row < T.rest.firstRow + 2 ^ T.rest.bits
            then some (row - T.rest.firstRow + place * 2 ^ T.rest.bits) else none) ∘ fun i =>
              ({ part := part, index := (T.shape.rows part - 1) +
                  (base + i) * 2 ^ ceilLog2 (T.shape.rows part), answer := i, basis := thetaE 0 } :
                PadPlace)) i) = none := by
          intro i _
          simp [hp]
        rw [List.filterMap_eq_nil_iff.2 this]
        simp
  show (List.mergeSort _ _).Pairwise (· < ·)
  rw [List.mergeSort_of_pairwise]
  · exact key
  · exact key.imp fun h => by simpa using Nat.le_of_lt h

/-! ### Under the program's own test on the public sizes -/

theorem le_two_pow_ceilLog2' (n : Nat) : n ≤ 2 ^ ceilLog2 n := by
  unfold ceilLog2
  split
  · simpa using ‹_›
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- What switchTargetCheck gives for the places: g's main rows are over the extension field, and
both blocks lie inside their tables' rows. -/
theorem of_check {S : Statement} {old : SingleRows} {T : SwitchTarget}
    (h : switchTargetCheck S old T = true) :
    T.shape.mainDeg = 3 ∧ T.rest.Fits (switchRowBits T T.rest.part) ∧
      T.main.Fits (switchRowBits T T.main.part) := by
  unfold switchTargetCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h3⟩, _⟩, _⟩, hmp⟩, _⟩, _⟩, _⟩, hb⟩, _⟩, _⟩, _⟩, _⟩,
    _⟩ := h
  refine ⟨h3, ?_, ?_⟩
  · unfold RowCut.Fits switchRowBits
    cases hp : T.rest.part with
    | mask =>
      rw [hp] at hb
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      have := le_two_pow_ceilLog2' (T.shape.rows .mask)
      simp only [OracleShape.rows] at this ⊢
      omega
    | main =>
      rw [hp] at hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      have := le_two_pow_ceilLog2' (T.shape.rows .main)
      simp only [OracleShape.rows] at this ⊢
      omega
  · unfold RowCut.Fits switchRowBits
    rw [hmp]
    have := le_two_pow_ceilLog2' (T.shape.rows .main)
    simp only [OracleShape.rows] at this ⊢
    cases hp : T.rest.part with
    | mask =>
      rw [hp] at hb
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      omega
    | main =>
      rw [hp] at hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      omega

/-- **Under the program's own test: the places of the rest increase strictly, stay in the rest's
block, and miss the pad of g's sample.** -/
theorem places_of_check {S : Statement} {old : SingleRows} {T : SwitchTarget}
    (h : switchTargetCheck S old T = true) :
    (∀ i i', i < i' → (make S.codes T).get i < (make S.codes T).get i') ∧
    (∀ i, T.rest.firstRow ≤ (make S.codes T).get i % 2 ^ switchRowBits T T.rest.part ∧
      (make S.codes T).get i % 2 ^ switchRowBits T T.rest.part <
        T.rest.firstRow + 2 ^ T.rest.bits) ∧
    (∀ i, i < (make S.codes T).size →
      (make S.codes T).get i / 2 ^ switchRowBits T T.rest.part <
        switchRowLength S.codes T T.rest.part) ∧
    (∀ i p, p ∈ padPlaces S.codes T.shape → p.part = T.rest.part →
      (make S.codes T).get i ≠ p.index) := by
  obtain ⟨h3, hr, _⟩ := of_check h
  refine ⟨fun i i' hi => (make S.codes T).get_lt hr.le hi, fun i => (make S.codes T).get_row hr i,
    fun i hi => ?_, fun i p hm hp =>
      make_get_ne_pad S.codes T hr (make_pad_rises S.codes T h3) i p hm hp⟩
  apply (make S.codes T).get_place_lt hr
  have : (make S.codes T).pad.length = ((padPlaces S.codes T.shape).filterMap fun p =>
      let row := p.index % 2 ^ switchRowBits T T.rest.part
      let place := p.index / 2 ^ switchRowBits T T.rest.part
      if p.part == T.rest.part && T.rest.firstRow ≤ row && row < T.rest.firstRow + 2 ^ T.rest.bits
      then some (row - T.rest.firstRow + place * 2 ^ T.rest.bits) else none).length :=
    List.length_mergeSort _
  rw [this]
  exact hi

end SwitchPlaces
end OnBytes

#print axioms OnBytes.SwitchPlaces.places_of_check
#print axioms OnBytes.SwitchPlaces.make_pad_rises
#print axioms OnBytes.SwitchPlaces.skip_not_mem
#print axioms OnBytes.cutIndex_inj
#print axioms OnBytes.SwitchPlaces.get_lt
#print axioms OnBytes.SwitchPlaces.get_row
#print axioms OnBytes.SwitchPlaces.get_place_lt
#print axioms OnBytes.SwitchPlaces.make_get_ne_pad
