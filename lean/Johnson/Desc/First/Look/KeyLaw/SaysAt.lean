-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/SaysAt.lean: what a lookup's row says, AT THE LEVEL OF VALUES: a row
over the field has one value at values of the mask entries and of the bits (valueF). The typed row
made of it (rdRow) applied to typed entries has that value; and so has the row of the program's type
that a caller builds of it (target, mask form, then the terms on the planes by the program's own
Wf.planesAt) applied to words (OnBytes.Means.value). So where the typed entries are read off the
words, the typed row holds exactly if the program's row says its claim.

No place of a typed entry in a table is named, and nothing is asked coefficient by coefficient: the
law on Wf.planesAt that is used is a law on sums (Planes.planesAt_value,
OnBytes/Slice/BlkPlanesAt.lean), whose conditions are tests of the program.

Main names:
  valueF mu d r mv bit: the mask form at the values mv, plus for each term its scalar times the sum
    over planes and rows of the vector's entry times the bit.
  typed_value: the typed row applied to typed entries.
  value_bare, value_addMasks, value_planesAt, value_terms: a row of the program applied to words.
  TablesFit: the statement has the message's main table, of the size that the layout reckons with.
  program_value: the row that a caller builds, applied to words.
  Tied: the typed entries are read off the words: a mask entry's value; a real plane's bit.
  bitsOf_none: a plane that is not real has the bit 0: no block of the layout holds it.
  says_iff_typed: where the entries are tied to the words: the program's row says its claim of the
    words exactly if the typed row holds of the entries.

Limits. Tied and TablesFit are premises. Nothing on RowIn, nor on Padded.

-/
import Johnson.Desc.First.Look.KeyLaw.RowsRead
import Johnson.Desc.Means.Says
import Johnson.Desc.First.Look.KeyLaw.RowCoef
import OnBytes.Slice.BlkPlanesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice Finset
open OnBytes.Model (Reading)
open OnBytes.Params (WfLookup WfPublic)
open Lk6 (Dat)
open Lk6.PortSim (rdMF)
open Lk6.Mid (RowF rdRow onCell)

/-- The value of a row over the field at values of the mask entries and of the bits. -/
def valueF (mu d : ℕ) (r : RowF) (mv : Slot → GE) (bit : ℕ → ℕ → GE) : GE :=
  (r.masks.map fun p => p.2 * mv p.1).sum +
    (r.maps.map fun a : GE × List (GE × GE) => a.1 * ∑ j ∈ range (2 ^ mu), ∑ t ∈ range (2 ^ d),
      Lk6.Mid.pairsAt a.2 (j + 2 ^ mu * t) * bit t j).sum

/-! ## The typed row -/

section Typed
variable (A : Dat GE) (sl : Slot → A.J) (μ : A.J → GE)

theorem sum_rdMF : ∀ m : PscF.MaskForm,
    ∑ j, rdMF sl m j * μ j = (m.map fun p => p.2 * μ (sl p.1)).sum
  | [] => by
    simp [Lk6.PortSim.rdMF_nil]
  | p :: m => by
    simp only [Lk6.PortSim.rdMF_cons, add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [sum_rdMF m]
    congr 1
    unfold Lk6.Parts.one
    simp [ite_mul]

theorem sum_onCell (hr : A.pl ≤ 2 ^ A.mu) (ps : List (GE × GE)) :
    ∑ j, onCell A ps j * μ j = ∑ j ∈ range (2 ^ A.mu), ∑ t ∈ range (2 ^ A.d),
      Lk6.Mid.pairsAt ps (j + 2 ^ A.mu * t) * (if j < A.pl then μ (A.bAt t j) else 0) := by
  have e1 : ∑ j, onCell A ps j * μ j = ∑ u ∈ range (2 ^ A.d), ∑ p ∈ range A.pl,
      Lk6.Mid.pairsAt ps (p + 2 ^ A.mu * u) * μ (A.bAt u p) := by
    unfold onCell
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [ite_mul]
  rw [e1, Finset.sum_comm]
  have e2 : ∀ j ∈ range (2 ^ A.mu), (∑ t ∈ range (2 ^ A.d),
      Lk6.Mid.pairsAt ps (j + 2 ^ A.mu * t) * (if j < A.pl then μ (A.bAt t j) else 0)) =
      if j < A.pl then ∑ t ∈ range (2 ^ A.d), Lk6.Mid.pairsAt ps (j + 2 ^ A.mu * t) * μ (A.bAt t
          j)
      else 0 := by
    intro j _
    split
    · rfl
    · simp
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- **The typed row applied to typed entries.** -/
theorem typed_value (hr : A.pl ≤ 2 ^ A.mu) (r : RowF) :
    ∑ j, (rdRow A sl r).cf j * μ j =
      valueF A.mu A.d r (fun s => μ (sl s)) fun t j => if j < A.pl then μ (A.bAt t j) else 0 := by
  show ∑ j, (rdMF sl r.masks j + (r.maps.map fun a => a.1 * onCell A a.2 j).sum) * μ j = _
  simp only [add_mul, Finset.sum_add_distrib]
  unfold valueF
  rw [sum_rdMF A sl μ]
  congr 1
  induction r.maps with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
    rw [ih, ← sum_onCell A μ hr, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

end Typed

/-! ## The program's row -/

section Program
variable (St : Statement) (w : Means.Words GE)

/-- The share of one place of one table in a sum over all tables. -/
theorem share_one (c : ℕ → Part → ℕ → GE) (x : ℕ × Part × ℕ) (v : GE)
    (h1 : x.1 < St.oracles.size) (h2 : x.2.2 < Means.tableSize St x.1 x.2.1) :
    (∑ o ∈ Finset.range St.oracles.size,
      ((∑ i ∈ Finset.range (Means.tableSize St o .main),
          c o .main i * (if x = (o, Part.main, i) then v else 0)) +
        ∑ i ∈ Finset.range (Means.tableSize St o .mask),
          c o .mask i * (if x = (o, Part.mask, i) then v else 0))) = c x.1 x.2.1 x.2.2 * v := by
  obtain ⟨o0, p0, i0⟩ := x
  rw [Finset.sum_eq_single o0]
  · cases p0 with
    | main =>
      rw [Finset.sum_eq_single i0, Finset.sum_eq_zero, add_zero, if_pos rfl]
      · intro i _
        rw [if_neg (by simp), mul_zero]
      · intro i _ hi
        rw [if_neg (by simp; exact fun e => hi e.symm), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 h2) h
    | mask =>
      rw [Finset.sum_eq_zero, zero_add, Finset.sum_eq_single i0, if_pos rfl]
      · intro i _ hi
        rw [if_neg (by simp; exact fun e => hi e.symm), mul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 h2) h
      · intro i _
        rw [if_neg (by simp), mul_zero]
  · intro o _ ho
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro i _
      rw [if_neg (by simp; exact fun e => absurd e.symm ho), mul_zero]
    · intro i _
      rw [if_neg (by simp; exact fun e => absurd e.symm ho), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 h1) h

/-- Two rows whose coefficients differ by delta: so do their values. -/
theorem value_add (R R' : GRow) (δ : ℕ → Part → ℕ → GE)
    (h : ∀ o part i, readE (R'.coefficient o part i) = readE (R.coefficient o part i) + δ o part i)
        :
    Means.value Reading.gl St R' w = Means.value Reading.gl St R w +
      ∑ o ∈ range St.oracles.size,
        ((∑ i ∈ range (Means.tableSize St o .main), δ o .main i * w o .main i) +
          ∑ i ∈ range (Means.tableSize St o .mask), δ o .mask i * w o .mask i) := by
  unfold Means.value Means.onTable
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  have e : ∀ part, ∑ i ∈ range (Means.tableSize St o part),
      Reading.gl.val (R'.coefficient o part i) * w o part i =
      ∑ i ∈ range (Means.tableSize St o part), Reading.gl.val (R.coefficient o part i) * w o part i
          +
        ∑ i ∈ range (Means.tableSize St o part), δ o part i * w o part i := by
    intro part
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    show readE _ * _ = readE _ * _ + _
    rw [h, add_mul]
  rw [e, e]
  ring

theorem value_bare (t : E) : Means.value Reading.gl St ({ target := t } : GRow) w = 0 := by
  unfold Means.value Means.onTable
  refine Finset.sum_eq_zero fun o _ => ?_
  have e : ∀ part, ∑ i ∈ range (Means.tableSize St o part),
      Reading.gl.val (({ target := t } : GRow).coefficient o part i) * w o part i = 0 := by
    intro part
    refine Finset.sum_eq_zero fun i _ => ?_
    show readE _ * _ = 0
    rw [Lk6.Mid.rd_bare, zero_mul]
  rw [e, e, add_zero]

/-- A mask form's entries stand inside mask tables that the statement has. -/
def MasksIn (m : MaskForm) : Prop :=
  ∀ p ∈ m, p.1.oracle < St.oracles.size ∧ p.1.index < Means.tableSize St p.1.oracle .mask

/-- Shares that are added member by member of a list. -/
theorem sum_list_delta {α : Type} (δ : α → ℕ → Part → ℕ → GE) (v : α → GE) : ∀ m : List α,
    (∀ p ∈ m, ∑ o ∈ range St.oracles.size,
      ((∑ i ∈ range (Means.tableSize St o .main), δ p o .main i * w o .main i) +
        ∑ i ∈ range (Means.tableSize St o .mask), δ p o .mask i * w o .mask i) = v p) →
    ∑ o ∈ range St.oracles.size,
      ((∑ i ∈ range (Means.tableSize St o .main), (m.map fun p => δ p o .main i).sum * w o .main i)
          +
        ∑ i ∈ range (Means.tableSize St o .mask), (m.map fun p => δ p o .mask i).sum * w o .mask i)
            =
      (m.map v).sum
  | [], _ => by simp
  | p :: m, h => by
    have h1 := h p List.mem_cons_self
    have h2 := sum_list_delta δ v m fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2

theorem value_addMasks (m : MaskForm) (R : GRow) (hm : MasksIn St m) :
    Means.value Reading.gl St (R.addMasks m) w = Means.value Reading.gl St R w +
      (m.map fun p => readE p.2 * w p.1.oracle .mask p.1.index).sum := by
  rw [value_add St w R (R.addMasks m) (fun o part idx =>
    (m.map fun p => if p.1.oracle = o ∧ Part.mask = part then
      (if p.1.index = idx then readE p.2 else 0) else 0).sum)
    (fun o part i => Lk6.Mid.rd_addMasks m R o part i)]
  congr 1
  refine sum_list_delta St w (fun (p : Slot × E) o part idx =>
    if p.1.oracle = o ∧ Part.mask = part then (if p.1.index = idx then readE p.2 else 0) else 0)
    (fun p => readE p.2 * w p.1.oracle .mask p.1.index) m fun p hp => ?_
  have h1 := hm p hp
  have e := share_one St w (p.1.oracle, Part.mask, p.1.index) (readE p.2) h1.1 h1.2
  have c : ∀ (o : ℕ) (part : Part) (i : ℕ),
      (if p.1.oracle = o ∧ Part.mask = part then (if p.1.index = i then readE p.2 else 0) else 0) *
        w o part i =
      w o part i * (if (p.1.oracle, Part.mask, p.1.index) = (o, part, i) then readE p.2 else 0) :=
          by
    intro o part i
    by_cases h : (p.1.oracle, Part.mask, p.1.index) = (o, part, i)
    · obtain ⟨h1, h2, h3⟩ : p.1.oracle = o ∧ Part.mask = part ∧ p.1.index = i := by
        simpa using h
      rw [if_pos h, if_pos ⟨h1, h2⟩, if_pos h3, mul_comm]
    · rw [if_neg h, mul_zero]
      by_cases h4 : p.1.oracle = o ∧ Part.mask = part
      · rw [if_pos h4, if_neg, zero_mul]
        intro h5
        exact h (by rw [h4.1, h4.2, h5])
      · rw [if_neg h4, zero_mul]
  refine Eq.trans ?_ (e.trans (mul_comm _ _))
  refine Finset.sum_congr rfl fun o _ => ?_
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => c o _ i

variable (x : WfPublic) (codes : Codes) (i : ℕ)

/-- The statement has the message's main table, of the size that the layout reckons with. -/
structure TablesFit : Prop where
  there : x.messageId < St.oracles.size
  size : Means.tableSize St x.messageId .main =
    2 ^ ((Planes.codeOf x codes).logEll + ceilLog2 x.message.shape.mainRows)

/-- What the program's routine for the planes adds to a row's value. -/
theorem value_planesAt (hT : TablesFit St x codes) (l : WfLookup) (R : GRow) (v : Tensor)
    (hi : x.lookups[i]? = some l) (hl : Wf.lookupOk Wf.fBits l = true)
    (hh : ((Wf.layout x.lookups (Planes.codeOf x codes).ell).head?.any fun b =>
      decide (2 ^ b.bits ≤ (Planes.codeOf x codes).ell)) = true)
    (hv : v.denseVars = []) (hn : v.pairs.length = l.mu + l.d) :
    Means.value Reading.gl St (Wf.planesAt x codes i R v) w = Means.value Reading.gl St R w +
      ∑ j ∈ range (2 ^ l.mu), ∑ t ∈ range (2 ^ l.d),
        readE (v.entry (j + 2 ^ l.mu * t)) * Planes.bitsOf x codes i (w x.messageId .main) t j := by
  have hval := Planes.planesAt_value Reading.gl x codes i l R v hi hl hh hv hn (w x.messageId .main)
  rw [← hT.size] at hval
  unfold Means.value
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hT.there),
    ← Finset.add_sum_erase (range St.oracles.size) (fun o => Means.onTable Reading.gl St R w o .main
        +
      Means.onTable Reading.gl St R w o .mask) (Finset.mem_range.2 hT.there)]
  have e1 : Means.onTable Reading.gl St (Wf.planesAt x codes i R v) w x.messageId .main =
      Means.onTable Reading.gl St R w x.messageId .main +
        ∑ j ∈ range (2 ^ l.mu), ∑ t ∈ range (2 ^ l.d),
          readE (v.entry (j + 2 ^ l.mu * t)) *
            Planes.bitsOf x codes i (w x.messageId .main) t j := hval
  have e2 : ∀ o part, ¬ (x.messageId = o ∧ Part.main = part) →
      Means.onTable Reading.gl St (Wf.planesAt x codes i R v) w o part =
        Means.onTable Reading.gl St R w o part := by
    intro o part hne
    unfold Means.onTable
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [Planes.planesAt_coefficient, if_neg hne, add_zero]
  rw [e1, e2 x.messageId .mask (by simp)]
  have e3 : ∑ o ∈ (range St.oracles.size).erase x.messageId,
      (Means.onTable Reading.gl St (Wf.planesAt x codes i R v) w o .main +
        Means.onTable Reading.gl St (Wf.planesAt x codes i R v) w o .mask) =
      ∑ o ∈ (range St.oracles.size).erase x.messageId,
        (Means.onTable Reading.gl St R w o .main + Means.onTable Reading.gl St R w o .mask) := by
    refine Finset.sum_congr rfl fun o ho => ?_
    have hne : x.messageId ≠ o := fun e => (Finset.mem_erase.1 ho).1 e.symm
    rw [e2 o .main (fun h => hne h.1), e2 o .mask (fun h => hne h.1)]
  rw [e3]
  ring

/-- Terms on the planes, added one after another. -/
theorem value_terms (hT : TablesFit St x codes) (l : WfLookup) (hi : x.lookups[i]? = some l)
    (hl : Wf.lookupOk Wf.fBits l = true)
    (hh : ((Wf.layout x.lookups (Planes.codeOf x codes).ell).head?.any fun b =>
      decide (2 ^ b.bits ≤ (Planes.codeOf x codes).ell)) = true) :
    ∀ (maps : List (E × List (E × E))) (R : GRow), (∀ a ∈ maps, a.2.length = l.mu + l.d) →
    Means.value Reading.gl St
        (maps.foldl (fun row a => Wf.planesAt x codes i row { scalar := a.1, pairs := a.2 }) R) w =
      Means.value Reading.gl St R w +
        (maps.map fun a => readE a.1 * ∑ j ∈ range (2 ^ l.mu), ∑ t ∈ range (2 ^ l.d),
          Lk6.Mid.pairsAt (pairsF a.2) (j + 2 ^ l.mu * t) *
            Planes.bitsOf x codes i (w x.messageId .main) t j).sum
  | [], R, _ => by simp
  | a :: maps, R, h => by
    rw [List.foldl_cons, value_terms hT l hi hl hh maps _ fun b hb => h b (List.mem_cons_of_mem _
        hb),
      value_planesAt St w x codes i hT l R _ hi hl hh rfl (h a List.mem_cons_self), List.map_cons,
      List.sum_cons, add_assoc]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Lk6.Mid.entry_read _ rfl]
    show readE a.1 * Lk6.Mid.pairsAt (pairsF a.2) _ * _ = _
    ring

/-- **The row that a caller builds (target, mask form, then the terms on the planes), applied to
words.** -/
theorem program_value (hT : TablesFit St x codes) (l : WfLookup) (hi : x.lookups[i]? = some l)
    (hl : Wf.lookupOk Wf.fBits l = true)
    (hh : ((Wf.layout x.lookups (Planes.codeOf x codes).ell).head?.any fun b =>
      decide (2 ^ b.bits ≤ (Planes.codeOf x codes).ell)) = true)
    (m : MaskForm) (maps : List (E × List (E × E))) (t : E) (hm : MasksIn St m)
    (hps : ∀ a ∈ maps, a.2.length = l.mu + l.d) :
    Means.value Reading.gl St
        (maps.foldl (fun row a => Wf.planesAt x codes i row { scalar := a.1, pairs := a.2 })
          (({ target := t } : GRow).addMasks m)) w =
      valueF l.mu l.d ⟨readForm m, maps.map fun a => (readE a.1, pairsF a.2), readE t⟩
        (fun s => w s.oracle .mask s.index)
        fun t j => Planes.bitsOf x codes i (w x.messageId .main) t j := by
  rw [value_terms St w x codes i hT l hi hl hh maps _ hps, value_addMasks St w m _ hm,
    value_bare, zero_add]
  unfold valueF readForm
  simp only [List.map_map]
  rfl

theorem target_terms : ∀ (maps : List (E × List (E × E))) (R : GRow),
    (maps.foldl (fun row a => Wf.planesAt x codes i row { scalar := a.1, pairs := a.2 }) R).target =
      R.target
  | [], _ => rfl
  | a :: maps, R => by
    rw [List.foldl_cons, target_terms maps, Planes.planesAt_target]

end Program

/-! ## The two together -/

/-- The value hangs on the mask entries that the row names and on the bits below the bounds. -/
theorem valueF_congr (mu d : ℕ) (r : RowF) {mv mv' : Slot → GE} {bit bit' : ℕ → ℕ → GE}
    (h1 : ∀ p ∈ r.masks, mv p.1 = mv' p.1)
    (h2 : ∀ j < 2 ^ mu, ∀ t < 2 ^ d, bit t j = bit' t j) :
    valueF mu d r mv bit = valueF mu d r mv' bit' := by
  unfold valueF
  congr 1
  · exact congrArg List.sum (List.map_congr_left fun p hp => by rw [h1 p hp])
  · refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
    congr 1
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun t ht => ?_
    rw [h2 j (Finset.mem_range.1 hj) t (Finset.mem_range.1 ht)]

/-- **The typed entries are read off the words**: at the homes in hs; at the real planes. -/
structure Tied (A : Dat GE) (sl : Slot → A.J) (μ : A.J → GE) (w : Means.Words GE) (x : WfPublic)
    (codes : Codes) (i : ℕ) (hs : List Slot) : Prop where
  mask : ∀ s ∈ hs, μ (sl s) = w s.oracle .mask s.index
  bit : ∀ t < 2 ^ A.d, ∀ j < A.pl,
    μ (A.bAt t j) = Planes.bitsOf x codes i (w x.messageId .main) t j

/-- **A plane that is not real has the bit 0**, whatever the table holds: no block of the layout
holds it. -/
theorem bitsOf_none (x : WfPublic) (codes : Codes) (i : ℕ) (l : WfLookup)
    (hi : x.lookups[i]? = some l) (T : ℕ → GE) (t j : ℕ) (hj : Wf.planesOf l ≤ j) :
    Planes.bitsOf x codes i T t j = 0 := by
  unfold Planes.bitsOf Planes.bitAt
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
  have hb' := List.mem_filter.1 hb
  obtain ⟨l', h1, h2, -⟩ := Planes.layout_mem _ _ b hb'.1
  have hbi : b.lookup = i := by simpa using hb'.2
  rw [hbi, hi] at h1
  obtain rfl := Option.some.inj h1
  have h3 := (Planes.liveLoop_spec (Wf.planesOf l) 64 0 _ h2).2
  have h3' : b.first + 2 ^ b.logPlanes ≤ Wf.planesOf l := h3
  rw [if_neg]
  omega

/-- **The program's row says its claim of the words exactly if the typed row holds of the entries.**
-/
theorem says_iff_typed {A : Dat GE} {sl : Slot → A.J} {μ : A.J → GE} {w : Means.Words GE}
    {x : WfPublic} {codes : Codes} {i : ℕ} {hs : List Slot} (St : Statement)
    (hr : A.pl ≤ 2 ^ A.mu) (hTd : Tied A sl μ w x codes i hs) (hT : TablesFit St x codes)
    (l : WfLookup) (hi : x.lookups[i]? = some l) (hl : Wf.lookupOk Wf.fBits l = true)
    (hh : ((Wf.layout x.lookups (Planes.codeOf x codes).ell).head?.any fun b =>
      decide (2 ^ b.bits ≤ (Planes.codeOf x codes).ell)) = true)
    (hmu : l.mu = A.mu) (hd : l.d = A.d) (hpl : Wf.planesOf l = A.pl)
    (m : MaskForm) (maps : List (E × List (E × E))) (t : E) (hm : MasksIn St m)
    (hms : ∀ p ∈ m, p.1 ∈ hs) (hps : ∀ a ∈ maps, a.2.length = l.mu + l.d) :
    Means.Says Reading.gl St
        (maps.foldl (fun row a => Wf.planesAt x codes i row { scalar := a.1, pairs := a.2 })
          (({ target := t } : GRow).addMasks m)) w ↔
      (rdRow A sl ⟨readForm m, maps.map fun a => (readE a.1, pairsF a.2), readE t⟩).Holds μ := by
  have e : valueF A.mu A.d ⟨readForm m, maps.map fun a => (readE a.1, pairsF a.2), readE t⟩
      (fun s => μ (sl s)) (fun t j => if j < A.pl then μ (A.bAt t j) else 0) =
      valueF A.mu A.d ⟨readForm m, maps.map fun a => (readE a.1, pairsF a.2), readE t⟩
        (fun s => w s.oracle .mask s.index)
        fun t j => Planes.bitsOf x codes i (w x.messageId .main) t j := by
    refine valueF_congr A.mu A.d _ (fun p hp => ?_) fun j hj t ht => ?_
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact hTd.mask q.1 (hms q hq)
    · by_cases hjp : j < A.pl
      · rw [if_pos hjp]
        exact hTd.bit t ht j hjp
      · rw [if_neg hjp]
        exact (bitsOf_none x codes i l hi _ t j (by rw [hpl]; exact Nat.le_of_not_lt hjp)).symm
  unfold Means.Says Cb.LdLkp.Row.Holds
  rw [program_value St w x codes i hT l hi hl hh m maps t hm hps, target_terms,
    Lk6.Mid.target_addMasks, hmu, hd, typed_value A sl μ hr, e]
  exact Iff.rfl

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.typed_value
#print axioms VerifiableInference.Desc.K3.KeyLaw.program_value
#print axioms VerifiableInference.Desc.K3.KeyLaw.says_iff_typed
