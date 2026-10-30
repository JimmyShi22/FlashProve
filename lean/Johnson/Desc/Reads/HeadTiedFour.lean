-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadTiedFour.lean: at the output head's link: the tie of the uses to the text,
clause (T) of Reads/Stated.lean, for all four forms of the acceptance policy, under named premises.

What is shown is a step of the row at the head: it speaks of the kind's written forms mean, count,
clip and table, at letters.
  `tied_head`, `tied_of_reading`: `Tied P.letters () s`. Every use's number is a form's; every entry
    of U3 in the four forms lies inside its row; and form by form, for all values at the places of
    U3, the form's part in U3 is the value of the uses of that number.

The premises, at a state s. K is a commutative ring.
  hval: the letter val is the map of a reading (OnBytes/Model/HideLaws.lean); in `tied_of_reading`:
    `IsReading P.letters` (Reads/Stated.lean).
  hcols: a row of U3 has an entry.
  hC: the clip C of the relation's own request is, in K, the C of the kind's policy.
  hJV: the relation's vocabulary and the kind's padded vocabulary have the same number of blocks.
None of them is shown here of any description. Without hC the form mean is not tied; no failing case
is typed for that.

The premises can be met together, at a toy that bears the kind's full numbers and the library's
reading. It names no description, and it is not a run's object.
  `fullToy`: letters with 1,024 positions, blocks of 64 features, 5,120 features, 202,048 vocabulary
    entries; the reading `Reading.gl` into the library's field; rows of 64 entries; every read from
    place 0 on; an empty request, no heard point, no table. `verify-on-bytes`'s records h and L are
    defaults there. So `NumH` fails of it, and with it `Sane`, `HeadClaim` and `HeadClaimByDecls`
    (Reads/HeadStated.lean); and clause (A) fails at every use, for want of a table.
  `tied_full`: these letters are tied. It says that the four premises of `tied_head` can be met
    together. It does not say that (T) holds at the full size, at the release's plan or at a run's
    letters.
  `tooth_full`: with the bytes of paid turned in clip (Reads/HeadTied.lean) they are not.
Neither says anything of clauses (A) and (L) or of `NotEmpty` there.

Tools, for all forms, readings and worlds.
  `part`: what turns in a form's value between two worlds. `part_add` and the like: its laws under
    the kinds' signs for sums and multiples. `u3Value_part`: a form's part in U3 is such a
    difference.
  `Inside`: the entries of one array lie inside their rows. `inside_addMul` and the like.
  `bytesAt`: the sum over l below m of 256 ^ l times the value at the place st + (NR + d + l).
  `summed_part`, `mean_part`, `count_part`, `clip_part`, `wide_part`, `table_part`: the text's side.
  `uses_zero`, `uses_one`, `uses_three`, `byte_sum`, `flat_sum`: the relation's side.

Of OnBytes/Model/ this file names `Aff`, `Ent`, `Reading`, `World` and `Aff.value`, as
Reads/Value.lean does.

Limits. Clauses (A) and (L) of the row, and `NotEmpty`, are not shown. The other 31 forms of the
link are not read. Both sides of (T) take the place from one seat: a form's entry through
`Seat.reads`, a use's place through `Use.index` (both in Reads/HeadStated.lean), which is copied off
the same text. So `tied_head` shows which numbers stand in which clause, with which coefficients,
and how many blocks. It shows nothing on which cells stand at a place: that is clause (A). It holds
of every seat; if a description's frame seats a read otherwise than `Seat.reads` does, it is not
about that frame. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtHead

open Finset
open OnBytes (E mulE oneE zeroE subE)
open OnBytes.Model (Aff Ent Reading World)
open VerifiableInference.Desc.Kinds
open Inst.Model.Head (nV)

variable {K : Type} [CommRing K] {ρ : Reading K}

/-! ## 1. What turns in a form's value between two worlds -/

/-- The form's value in the world W less its value in the world W0. -/
def part (ρ : Reading K) (W W0 : World K) (f : Aff) : K := f.value ρ W - f.value ρ W0

section Part
variable (W W0 : World K)

theorem part_const (x : E) : part ρ W W0 (Aff.ofConst x) = 0 := by
  unfold part
  rw [Aff.value_ofConst, Aff.value_ofConst, sub_self]

theorem part_add (f g : Aff) : part ρ W W0 (f + g) = part ρ W W0 f + part ρ W W0 g := by
  unfold part
  rw [Aff.value_add, Aff.value_add]
  ring

theorem part_sub (f g : Aff) : part ρ W W0 (f - g) = part ρ W W0 f - part ρ W W0 g := by
  unfold part
  rw [Aff.value_sub, Aff.value_sub]
  ring

theorem part_smulNat (ρ : Reading K) (k : ℕ) (f : Aff) :
    part ρ W W0 (k • f) = (k : K) * part ρ W W0 f := by
  unfold part
  rw [value_smulNat ρ, value_smulNat ρ]
  ring

theorem part_addE (f : Aff) (x : E) :
    part ρ W W0 (HAdd.hAdd (α := Aff) (β := E) (γ := Aff) f x) = part ρ W W0 f := by
  show part ρ W W0 (f + Aff.ofConst x) = _
  rw [part_add, part_const, add_zero]

theorem part_subE (f : Aff) (x : E) :
    part ρ W W0 (HSub.hSub (α := Aff) (β := E) (γ := Aff) f x) = part ρ W W0 f := by
  show part ρ W W0 (f - Aff.ofConst x) = _
  rw [part_sub, part_const, sub_zero]

theorem part_Eadd (x : E) (f : Aff) :
    part ρ W W0 (HAdd.hAdd (α := E) (β := Aff) (γ := Aff) x f) = part ρ W W0 f := by
  show part ρ W W0 (Aff.ofConst x + f) = _
  rw [part_add, part_const, zero_add]

theorem part_addN (f : Aff) (n : ℕ) :
    part ρ W W0 (HAdd.hAdd (α := Aff) (β := ℕ) (γ := Aff) f n) = part ρ W W0 f := by
  show part ρ W W0 (f + Aff.ofConst (natE n)) = _
  rw [part_add, part_const, add_zero]

theorem part_subN (f : Aff) (n : ℕ) :
    part ρ W W0 (HSub.hSub (α := Aff) (β := ℕ) (γ := Aff) f n) = part ρ W W0 f := by
  show part ρ W W0 (f - Aff.ofConst (natE n)) = _
  rw [part_sub, part_const, sub_zero]

theorem part_natCast (n : ℕ) : part ρ W W0 ((n : ℕ) : Form) = 0 := part_const W W0 (natE n)

theorem part_sumTo (ρ : Reading K) (n : ℕ) (f : ℕ → Aff) :
    part ρ W W0 (sumTo n f) = ∑ i ∈ range n, part ρ W W0 (f i) := by
  unfold part
  rw [value_sumTo ρ, value_sumTo ρ, Finset.sum_sub_distrib]

end Part

/-- A form's part in U3 is what turns in its value between the world of v and the world of 0. -/
theorem u3Value_part (iU3 cols : ℕ) (v : ℕ → K) (f : Aff) :
    u3Value ρ.val iU3 cols f v = part ρ (worldOf iU3 cols v) (worldOf iU3 cols fun _ => 0) f :=
  u3Value_diff ρ iU3 cols v f

/-- At a seat, entry i of a read turns by the value at the read's first entry plus i. -/
theorem seat_part (S : Seat) (v : ℕ → K) (r : Head.Read) (i : ℕ) :
    part ρ (worldOf S.iU3 S.cols v) (worldOf S.iU3 S.cols fun _ => 0) (S.reads.entry r i) =
      v (S.start r + i) := by
  have e1 : (S.reads.entry r i).value ρ (worldOf S.iU3 S.cols v) = v (S.start r + i) :=
    value_place ρ S.iU3 S.cols v _
  have e2 : (S.reads.entry r i).value ρ (worldOf S.iU3 S.cols fun _ => (0 : K)) = 0 :=
    value_place ρ S.iU3 S.cols (fun _ => 0) _
  unfold part
  rw [e1, e2, sub_zero]

/-! ## 2. The entries of one array lie inside their rows -/

/-- Every entry of array number iU3 in the form has an index below cols. -/
def Inside (iU3 cols : ℕ) (f : Aff) : Prop := ∀ x ∈ f.ents.toList, x.tree = iU3 → x.idx < cols

section In
variable {iU3 cols : ℕ}

theorem inside_const (x : E) : Inside iU3 cols (Aff.ofConst x) := by
  intro y hy _
  have hy' : y ∈ ([] : List Ent) := hy
  exact absurd hy' List.not_mem_nil

theorem inside_addMul {a b : Aff} (k : E) (ha : Inside iU3 cols a) (hb : Inside iU3 cols b) :
    Inside iU3 cols (Aff.addMul a b k) := by
  intro x hx ht
  have hx' : x ∈ a.ents.toList ++ b.ents.toList.map fun y => { y with coef := mulE y.coef k } := by
    rw [← OnBytes.Model.foldl_push_toList]
    exact hx
  rcases List.mem_append.1 hx' with h | h
  · exact ha x h ht
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
    exact hb y hy ht

theorem inside_add {f g : Aff} (hf : Inside iU3 cols f) (hg : Inside iU3 cols g) :
    Inside iU3 cols (f + g) := inside_addMul oneE hf hg

theorem inside_sub {f g : Aff} (hf : Inside iU3 cols f) (hg : Inside iU3 cols g) :
    Inside iU3 cols (f - g) := inside_addMul (subE zeroE oneE) hf hg

theorem inside_smulNat (k : ℕ) {f : Aff} (hf : Inside iU3 cols f) : Inside iU3 cols (k • f) :=
  inside_addMul (a := {}) (natE k) (inside_const zeroE) hf

theorem inside_addE {f : Aff} (x : E) (hf : Inside iU3 cols f) :
    Inside iU3 cols (HAdd.hAdd (α := Aff) (β := E) (γ := Aff) f x) :=
  inside_add hf (inside_const x)

theorem inside_subE {f : Aff} (x : E) (hf : Inside iU3 cols f) :
    Inside iU3 cols (HSub.hSub (α := Aff) (β := E) (γ := Aff) f x) :=
  inside_sub hf (inside_const x)

theorem inside_Eadd {f : Aff} (x : E) (hf : Inside iU3 cols f) :
    Inside iU3 cols (HAdd.hAdd (α := E) (β := Aff) (γ := Aff) x f) :=
  inside_add (inside_const x) hf

theorem inside_addN {f : Aff} (n : ℕ) (hf : Inside iU3 cols f) :
    Inside iU3 cols (HAdd.hAdd (α := Aff) (β := ℕ) (γ := Aff) f n) :=
  inside_add hf (inside_const (natE n))

theorem inside_subN {f : Aff} (n : ℕ) (hf : Inside iU3 cols f) :
    Inside iU3 cols (HSub.hSub (α := Aff) (β := ℕ) (γ := Aff) f n) :=
  inside_sub hf (inside_const (natE n))

theorem inside_natCast (n : ℕ) : Inside iU3 cols ((n : ℕ) : Form) := inside_const (natE n)

theorem inside_sumTo (n : ℕ) {f : ℕ → Aff} (hf : ∀ i, Inside iU3 cols (f i)) :
    Inside iU3 cols (sumTo n f) := by
  induction n with
  | zero => exact inside_const (natE 0)
  | succ n ih =>
    have e : sumTo (n + 1) f = sumTo n f + f n := by
      unfold sumTo
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e]
    exact inside_add ih (hf n)

end In

/-- At a seat whose rows have an entry, an entry of a read lies inside its row. -/
theorem inside_seat (S : Seat) (hcols : 0 < S.cols) (r : Head.Read) (i : ℕ) :
    Inside S.iU3 S.cols (S.reads.entry r i) := by
  intro x hx _
  have hx' : x ∈ [(⟨S.iU3, (S.start r + i) / S.cols, (S.start r + i) % S.cols, oneE⟩ : Ent)] := hx
  rw [List.mem_singleton.1 hx']
  exact Nat.mod_lt _ hcols

/-! ## 3. The text's side -/

/-- The sum over l below m of 256 ^ l times the value at the place st + (NR + d + l). -/
def bytesAt (v : ℕ → K) (st d m : ℕ) : K :=
  ∑ l ∈ range m, ((256 ^ l : ℕ) : K) * v (st + (NR + d + l))

/-- The world in which v stands at the places of U3, at a seat. -/
abbrev Seat.world (S : Seat) (v : ℕ → K) : World K := worldOf S.iU3 S.cols v

theorem summed_part [iS : Head.Sizes] [iR : Head.Request] (ρ : Reading K) (S : Seat) (v : ℕ → K)
    (n : Head.Number) :
    part ρ (S.world v) (S.world fun _ => 0) (letI := S.reads; Head.summed n) =
      bytesAt v (S.start .rowCount) n.digits.1 n.digits.2 := by
  unfold Head.summed bytesAt
  rw [part_sumTo _ _ ρ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [part_smulNat _ _ ρ, part_addN, seat_part]

theorem atCosts_part [iS : Head.Sizes] [iR : Head.Request] [iI : FinalNorm.In] (ρ : Reading K)
    (S : Seat) (v : ℕ → K) (n : Head.Number) :
    part ρ (S.world v) (S.world fun _ => 0) (letI := S.reads; Head.atCosts n) =
      bytesAt v (S.start .rowAtCosts) n.digits.1 n.digits.2 := by
  unfold Head.atCosts bytesAt
  rw [part_sumTo _ _ ρ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [part_smulNat _ _ ρ, part_addE, seat_part]

theorem mean_part [iS : Head.Sizes] [iP : Head.Policy] [iR : Head.Request] (ρ : Reading K)
    (S : Seat) (v : ℕ → K) :
    part ρ (S.world v) (S.world fun _ => 0) (letI := S.reads; Head.mean) =
      bytesAt v (S.start .rowCount) 0 5 + (Head.C : K) * bytesAt v (S.start .rowCount) 5 1 +
        bytesAt v (S.start .rowCount) 6 5 := by
  have h1 : _ = bytesAt v (S.start .rowCount) 0 5 := summed_part ρ S v .paid
  have h2 : _ = bytesAt v (S.start .rowCount) 5 1 := summed_part ρ S v .over
  have h3 : _ = bytesAt v (S.start .rowCount) 6 5 := summed_part ρ S v .slackMean
  unfold Head.mean
  rw [part_subN, part_add, part_add, part_smulNat _ _ ρ, h1, h2, h3]

theorem count_part [iS : Head.Sizes] [iP : Head.Policy] [iR : Head.Request] (ρ : Reading K)
    (S : Seat) (v : ℕ → K) :
    part ρ (S.world v) (S.world fun _ => 0) (letI := S.reads; Head.count) =
      bytesAt v (S.start .rowCount) 5 1 + bytesAt v (S.start .rowCount) 16 2 := by
  have h1 : _ = bytesAt v (S.start .rowCount) 5 1 := summed_part ρ S v .over
  have h2 : _ = bytesAt v (S.start .rowCount) 16 2 := summed_part ρ S v .slackCap
  unfold Head.count
  rw [part_sub, part_add, part_natCast, h1, h2, sub_zero]

theorem clip_part [iS : Head.Sizes] [iP : Head.Policy] [iR : Head.Request] [iI : FinalNorm.In]
    (ρ : Reading K) (S : Seat) (v : ℕ → K) :
    part ρ (S.world v) (S.world fun _ => 0) (letI := S.reads; Head.clip) =
      bytesAt v (S.start .rowAtCosts) 0 5 + bytesAt v (S.start .rowAtCosts) 11 5 := by
  have h1 : _ = bytesAt v (S.start .rowAtCosts) 0 5 := atCosts_part ρ S v .paid
  have h2 : _ = bytesAt v (S.start .rowAtCosts) 11 5 := atCosts_part ρ S v .slackClip
  unfold Head.clip
  rw [part_subE, part_add, h1, h2]

theorem wide_part [iS : Head.Sizes] [iR : Head.Request] [iI : FinalNorm.In] (ρ : Reading K)
    (S : Seat) (v : ℕ → K) :
    part ρ (S.world v) (S.world fun _ => 0) (letI := S.reads; Head.tableValuesAtCosts) =
      ∑ l ∈ range 3, ∑ i ∈ range (Head.JV / Norm.S2), ((256 ^ l : ℕ) : K) *
        v (S.start .wideAtCosts + ((4 * Norm.d + (3 + l) * Head.JV) / Norm.S2 + i)) := by
  unfold Head.tableValuesAtCosts
  rw [part_Eadd, part_sumTo _ _ ρ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [part_sumTo _ _ ρ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [part_smulNat _ _ ρ, seat_part]

theorem table_part [iS : Head.Sizes] [iR : Head.Request] [iI : FinalNorm.In] (ρ : Reading K)
    (S : Seat) (v : ℕ → K) :
    part ρ (S.world v) (S.world fun _ => 0) (letI := S.reads; Head.table) =
      bytesAt v (S.start .rowAtCosts) 18 3 +
        ∑ l ∈ range 3, ∑ i ∈ range (Head.JV / Norm.S2), ((256 ^ l : ℕ) : K) *
          v (S.start .wideAtCosts + ((4 * Norm.d + (3 + l) * Head.JV) / Norm.S2 + i)) := by
  have h1 : _ = bytesAt v (S.start .rowAtCosts) 18 3 := atCosts_part ρ S v .slackTable
  unfold Head.table
  rw [part_subE, part_add, h1, wide_part ρ S v]

/-! The four forms' entries lie inside their rows. -/

theorem inside_summed [iS : Head.Sizes] [iR : Head.Request] (S : Seat) (hcols : 0 < S.cols)
    (n : Head.Number) : Inside S.iU3 S.cols (letI := S.reads; Head.summed n) :=
  inside_sumTo _ fun _ => inside_smulNat _ (inside_addN _ (inside_seat S hcols _ _))

theorem inside_atCosts [iS : Head.Sizes] [iR : Head.Request] [iI : FinalNorm.In] (S : Seat)
    (hcols : 0 < S.cols) (n : Head.Number) :
    Inside S.iU3 S.cols (letI := S.reads; Head.atCosts n) :=
  inside_sumTo _ fun _ => inside_smulNat _ (inside_addE _ (inside_seat S hcols _ _))

theorem inside_mean [iS : Head.Sizes] [iP : Head.Policy] [iR : Head.Request] (S : Seat)
    (hcols : 0 < S.cols) : Inside S.iU3 S.cols (letI := S.reads; Head.mean) :=
  inside_subN _ (inside_add (inside_add (inside_summed S hcols _)
    (inside_smulNat _ (inside_summed S hcols _))) (inside_summed S hcols _))

theorem inside_count [iS : Head.Sizes] [iP : Head.Policy] [iR : Head.Request] (S : Seat)
    (hcols : 0 < S.cols) : Inside S.iU3 S.cols (letI := S.reads; Head.count) :=
  inside_sub (inside_add (inside_summed S hcols _) (inside_summed S hcols _)) (inside_natCast _)

theorem inside_clip [iS : Head.Sizes] [iP : Head.Policy] [iR : Head.Request] [iI : FinalNorm.In]
    (S : Seat) (hcols : 0 < S.cols) : Inside S.iU3 S.cols (letI := S.reads; Head.clip) :=
  inside_subE _ (inside_add (inside_atCosts S hcols _) (inside_atCosts S hcols _))

theorem inside_table [iS : Head.Sizes] [iR : Head.Request] [iI : FinalNorm.In] (S : Seat)
    (hcols : 0 < S.cols) : Inside S.iU3 S.cols (letI := S.reads; Head.table) :=
  inside_subE _ (inside_add (inside_atCosts S hcols _)
    (inside_Eadd _ (inside_sumTo _ fun _ => inside_sumTo _ fun _ =>
      inside_smulNat _ (inside_seat S hcols _ _))))

/-! ## 4. The relation's side -/

/-- No use of a table value has a number below 3. -/
theorem ex_out [iS : Head.Sizes] (n : ℕ) (hn : n < 3) :
    (((List.range 3).flatMap fun l =>
      (List.range (nV / Norm.S2)).map fun blk => Use.ex l blk).filter
        fun u => u.clause.no == n) = [] := by
  refine List.filter_eq_nil_iff.2 fun u hu => ?_
  obtain ⟨l, -, hu⟩ := List.mem_flatMap.1 hu
  obtain ⟨blk, -, rfl⟩ := List.mem_map.1 hu
  intro h
  have h' : (3 : ℕ) = n := beq_iff_eq.1 h
  omega

/-- The uses of form number 0: the bytes of c, b and u in (B2). -/
theorem uses_zero [iS : Head.Sizes] : (usesH.filter fun u => u.clause.no == 0) =
    (List.range 5).map (Use.byte .B2 .c) ++ ((List.range 1).map (Use.byte .B2 .b) ++
      (List.range 5).map (Use.byte .B2 .u)) := by
  unfold usesH
  rw [List.filter_append, ex_out 0 (by decide), List.append_nil]
  rfl

/-- The uses of form number 1: the bytes of b and z in (B3). -/
theorem uses_one [iS : Head.Sizes] : (usesH.filter fun u => u.clause.no == 1) =
    (List.range 1).map (Use.byte .B3 .b) ++ (List.range 2).map (Use.byte .B3 .z) := by
  unfold usesH
  rw [List.filter_append, ex_out 1 (by decide), List.append_nil]
  rfl

/-- The uses of form number 3: the bytes of zs in (Z), and all table values. -/
theorem uses_three [iS : Head.Sizes] : (usesH.filter fun u => u.clause.no == 3) =
    (List.range 3).map (Use.byte .Z .zs) ++ (List.range 3).flatMap fun l =>
      (List.range (nV / Norm.S2)).map fun blk => Use.ex l blk := by
  have hB : (((List.range 3).flatMap fun l =>
      (List.range (nV / Norm.S2)).map fun blk => Use.ex l blk).filter
        fun u => u.clause.no == 3) = (List.range 3).flatMap fun l =>
      (List.range (nV / Norm.S2)).map fun blk => Use.ex l blk := by
    refine List.filter_eq_self.2 fun u hu => ?_
    obtain ⟨l, -, hu⟩ := List.mem_flatMap.1 hu
    obtain ⟨blk, -, rfl⟩ := List.mem_map.1 hu
    rfl
  unfold usesH
  rw [List.filter_append, hB]
  rfl

/-- A sum over a list that is laid in n runs of m items. -/
theorem flat_sum {α : Type} (h : ℕ → ℕ → α) (g : α → K) (n m : ℕ) :
    (((List.range n).flatMap fun l => (List.range m).map (h l)).map g).sum =
      ∑ l ∈ range n, ∑ i ∈ range m, g (h l i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, range_sum,
      Function.comp_def]

/-- What a use adds to its clause's value. -/
def HeadLetters.term (P : HeadLetters K) (s : P.State) (v : ℕ → K) (u : Use) : K :=
  u.coef (P.req s) * v (P.seat.start u.read + @Use.index P.sizes u)

theorem clause_at (P : HeadLetters K) (s : P.State) (n : ℕ) (v : ℕ → K) :
    P.letters.clauseValue () s n v =
      (((@usesH P.sizes).filter fun u => u.clause.no == n).map (P.term s v)).sum := rfl

/-- The m low bytes of a hidden number in a clause. -/
theorem byte_sum (P : HeadLetters K) (s : P.State) (v : ℕ → K) (cl : Clause) (x : Hid) (m : ℕ) :
    (((List.range m).map (Use.byte cl x)).map (P.term s v)).sum =
      cl.factor (P.req s) x * bytesAt v (P.seat.start cl.read) x.number.digits.1 m := by
  rw [List.map_map, range_sum]
  unfold bytesAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show cl.factor (P.req s) x * (256 : K) ^ l *
      v (P.seat.start cl.read + (NR + x.number.digits.1 + l)) =
    cl.factor (P.req s) x * (((256 ^ l : ℕ) : K) *
      v (P.seat.start cl.read + (NR + x.number.digits.1 + l)))
  push_cast
  ring

/-! ## 5. The two together -/

/-- The kind's four forms at the head's letters and a state. -/
def HeadLetters.form (P : HeadLetters K) (s : P.State) (cl : Clause) : Form :=
  letI := P.sizes
  letI := P.policy
  letI := P.request s
  letI := P.points s
  letI := P.seat.reads
  cl.form

theorem forms_are (P : HeadLetters K) (s : P.State) :
    P.letters.forms () s = [P.form s .B2, P.form s .B3, P.form s .B4, P.form s .Z] := rfl

theorem no_lt (cl : Clause) : cl.no < 4 := by cases cl <;> decide

/-- **(T) at the head's link, for the four forms of the policy.** -/
theorem tied_head (P : HeadLetters K) (hval : P.val = ρ.val) (s : P.State)
    (hcols : 0 < P.seat.cols) (hC : ((P.req s).pol.C : K) = (P.policy.C : K))
    (hJV : letI := P.sizes; nV / Norm.S2 = Head.JV / Norm.S2) :
    Tied P.letters () s := by
  refine ⟨fun u _ => no_lt _, fun n f hf => ?_⟩
  have hf' : [P.form s .B2, P.form s .B3, P.form s .B4, P.form s .Z][n]? = some f := hf
  show Inside P.seat.iU3 P.seat.cols f ∧
    ∀ v : ℕ → K, u3Value P.val P.seat.iU3 P.seat.cols f v = P.letters.clauseValue () s n v
  rw [hval]
  rcases n with _ | _ | _ | _ | n
  · obtain rfl : P.form s .B2 = f := Option.some.inj hf'
    refine ⟨inside_mean (iS := P.sizes) (iP := P.policy) (iR := P.request s) P.seat hcols,
      fun v => ?_⟩
    rw [u3Value_part, clause_at, uses_zero (iS := P.sizes), List.map_append, List.map_append,
      List.sum_append, List.sum_append, byte_sum, byte_sum, byte_sum]
    refine (mean_part (iS := P.sizes) (iP := P.policy) (iR := P.request s) ρ P.seat v).trans ?_
    show _ = 1 * bytesAt v (P.seat.start .rowCount) 0 5 +
      (((P.req s).pol.C : K) * bytesAt v (P.seat.start .rowCount) 5 1 +
        1 * bytesAt v (P.seat.start .rowCount) 6 5)
    rw [hC]
    ring
  · obtain rfl : P.form s .B3 = f := Option.some.inj hf'
    refine ⟨inside_count (iS := P.sizes) (iP := P.policy) (iR := P.request s) P.seat hcols,
      fun v => ?_⟩
    rw [u3Value_part, clause_at, uses_one (iS := P.sizes), List.map_append, List.sum_append,
      byte_sum, byte_sum]
    refine (count_part (iS := P.sizes) (iP := P.policy) (iR := P.request s) ρ P.seat v).trans ?_
    show _ = 1 * bytesAt v (P.seat.start .rowCount) 5 1 +
      1 * bytesAt v (P.seat.start .rowCount) 16 2
    ring
  · obtain rfl : P.form s .B4 = f := Option.some.inj hf'
    refine ⟨inside_clip (iS := P.sizes) (iP := P.policy) (iR := P.request s) (iI := P.points s)
      P.seat hcols, fun v => ?_⟩
    rw [u3Value_part, clause_at, uses_two (iS := P.sizes), List.map_append, List.sum_append,
      byte_sum, byte_sum]
    refine (clip_part (iS := P.sizes) (iP := P.policy) (iR := P.request s) (iI := P.points s) ρ
      P.seat v).trans ?_
    show _ = 1 * bytesAt v (P.seat.start .rowAtCosts) 0 5 +
      1 * bytesAt v (P.seat.start .rowAtCosts) 11 5
    ring
  · obtain rfl : P.form s .Z = f := Option.some.inj hf'
    refine ⟨inside_table (iS := P.sizes) (iR := P.request s) (iI := P.points s) P.seat hcols,
      fun v => ?_⟩
    rw [u3Value_part, clause_at, uses_three (iS := P.sizes), List.map_append, List.sum_append,
      byte_sum, flat_sum, hJV]
    refine (table_part (iS := P.sizes) (iR := P.request s) (iI := P.points s) ρ P.seat v).trans ?_
    refine congrArg₂ (· + ·) (one_mul _).symm (Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => ?_)
    have e : ((256 ^ l : ℕ) : K) = (256 : K) ^ l := by rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [e]
    rfl
  · simp at hf'

/-- The same, in the words of Reads/Stated.lean. -/
theorem tied_of_reading (P : HeadLetters K) (hR : IsReading P.letters) (s : P.State)
    (hcols : 0 < P.seat.cols) (hC : ((P.req s).pol.C : K) = (P.policy.C : K))
    (hJV : letI := P.sizes; nV / Norm.S2 = Head.JV / Norm.S2) :
    Tied P.letters () s := by
  obtain ⟨ρ, h⟩ := hR
  exact tied_head P h.symm s hcols hC hJV

/-! ## 6. The premises can be met -/

/-- A toy: letters with the kind's full numbers and the library's reading. h and L are defaults and
there is no table, so the statements at the head fail of it. -/
noncomputable def fullToy : HeadLetters Cb.Gl.E where
  val := Reading.gl.val
  h := default
  L := {}
  sizes :=
    { lt := 10, ls := 6, d := 5120, MF := 0, KF := 0, epsF := 0, V := 202048, sh := 7, F := 24 }
  policy := ⟨128, 128, 0⟩
  seat := ⟨5, 64, fun _ => some 0, fun _ => 0, fun _ => (0, 1)⟩
  State := Unit
  AtClose := fun _ => True
  req := fun _ => ⟨0, 0, fun _ => 0, ⟨128, 128, 0⟩⟩
  request := fun _ => ⟨fun _ => 0, 0, 0⟩
  points := fun _ => ⟨#[], #[], fun _ _ => zeroE, fun _ _ => zeroE, fun _ => zeroE⟩
  heard := fun _ => ⟨{}⟩
  tl := fun _ => {}
  funs := fun _ => #[]

/-- At these letters the four forms are tied. -/
theorem tied_full : Tied fullToy.letters () () :=
  tied_head (ρ := Reading.gl) fullToy rfl () (by show 0 < 64; decide) rfl
    (by show 202048 / 2 ^ 6 = (202048 + 2 ^ 6 - 1) / 2 ^ 6 * 2 ^ 6 / 2 ^ 6; decide)

/-- With the bytes of paid turned in clip they are not. -/
theorem tooth_full : ¬ Tied (fullToy.lettersWith fun l => 256 ^ (4 - l)) () () :=
  tooth_clip_turned (ρ := Reading.gl) fullToy rfl one_ne_zero ()

end VerifiableInference.Reads.AtHead

#print axioms VerifiableInference.Reads.AtHead.part_const
#print axioms VerifiableInference.Reads.AtHead.part_add
#print axioms VerifiableInference.Reads.AtHead.part_sub
#print axioms VerifiableInference.Reads.AtHead.part_smulNat
#print axioms VerifiableInference.Reads.AtHead.part_addE
#print axioms VerifiableInference.Reads.AtHead.part_subE
#print axioms VerifiableInference.Reads.AtHead.part_Eadd
#print axioms VerifiableInference.Reads.AtHead.part_addN
#print axioms VerifiableInference.Reads.AtHead.part_subN
#print axioms VerifiableInference.Reads.AtHead.part_natCast
#print axioms VerifiableInference.Reads.AtHead.part_sumTo
#print axioms VerifiableInference.Reads.AtHead.u3Value_part
#print axioms VerifiableInference.Reads.AtHead.seat_part
#print axioms VerifiableInference.Reads.AtHead.inside_const
#print axioms VerifiableInference.Reads.AtHead.inside_addMul
#print axioms VerifiableInference.Reads.AtHead.inside_add
#print axioms VerifiableInference.Reads.AtHead.inside_sub
#print axioms VerifiableInference.Reads.AtHead.inside_smulNat
#print axioms VerifiableInference.Reads.AtHead.inside_addE
#print axioms VerifiableInference.Reads.AtHead.inside_subE
#print axioms VerifiableInference.Reads.AtHead.inside_Eadd
#print axioms VerifiableInference.Reads.AtHead.inside_addN
#print axioms VerifiableInference.Reads.AtHead.inside_subN
#print axioms VerifiableInference.Reads.AtHead.inside_natCast
#print axioms VerifiableInference.Reads.AtHead.inside_sumTo
#print axioms VerifiableInference.Reads.AtHead.inside_seat
#print axioms VerifiableInference.Reads.AtHead.summed_part
#print axioms VerifiableInference.Reads.AtHead.atCosts_part
#print axioms VerifiableInference.Reads.AtHead.mean_part
#print axioms VerifiableInference.Reads.AtHead.count_part
#print axioms VerifiableInference.Reads.AtHead.clip_part
#print axioms VerifiableInference.Reads.AtHead.wide_part
#print axioms VerifiableInference.Reads.AtHead.table_part
#print axioms VerifiableInference.Reads.AtHead.inside_summed
#print axioms VerifiableInference.Reads.AtHead.inside_atCosts
#print axioms VerifiableInference.Reads.AtHead.inside_mean
#print axioms VerifiableInference.Reads.AtHead.inside_count
#print axioms VerifiableInference.Reads.AtHead.inside_clip
#print axioms VerifiableInference.Reads.AtHead.inside_table
#print axioms VerifiableInference.Reads.AtHead.ex_out
#print axioms VerifiableInference.Reads.AtHead.uses_zero
#print axioms VerifiableInference.Reads.AtHead.uses_one
#print axioms VerifiableInference.Reads.AtHead.uses_three
#print axioms VerifiableInference.Reads.AtHead.flat_sum
#print axioms VerifiableInference.Reads.AtHead.clause_at
#print axioms VerifiableInference.Reads.AtHead.byte_sum
#print axioms VerifiableInference.Reads.AtHead.forms_are
#print axioms VerifiableInference.Reads.AtHead.no_lt
#print axioms VerifiableInference.Reads.AtHead.tied_head
#print axioms VerifiableInference.Reads.AtHead.tied_of_reading
#print axioms VerifiableInference.Reads.AtHead.tied_full
#print axioms VerifiableInference.Reads.AtHead.tooth_full
