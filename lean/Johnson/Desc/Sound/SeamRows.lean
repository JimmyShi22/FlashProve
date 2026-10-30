-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamRows.lean: **THE SEAM AT THE SHARED CHAIN's TWO PROXIMITY TESTS, ITS HALF ON THE ROWS (s4): WHAT THE TEST TAKES IN HOLDS OF THE WORDS ⟹ EVERY CLASS THAT THE TEST CLOSES SAYS ITS CLAIM, AT THE FILLING rowW (Johnson/Desc/K14/Law/LedgerSay.lean).** Statements
and proofs. NO NEW MATHEMATICS.

The kind's law ends in "AllSay rdE (begun S g G) (runRows S G).toList W": every row that the test takes in (the group's open rows; each member's sample rows) says its claim of the words W, AT THE STATEMENT BEHIND THE TEST's BEGINNING. The ledger's clause
wants, class by class, rowW (Johnson/Desc/K14/Law/LedgerSay.lean): slices of the group's list as it lies in the record IN FRONT, said at a statement that has grown out of the record's ((rec_gamma), (loc_x): RowsUL; a message's sample's
rows: SmpSay) or at the record's own ((fold_u), (fold_omega): RowsU | RowsO).
  slice_mem        a row of a slice of a group's list is a row of the group.
  open_says        each open row of the group says its claim at the begun statement: open_taken (where no open row is of the kind "sample": OpenKinds, a part of Tidy).
  rows_nine        the four classes that the test on G_u closes: [sample o_u, (rec_gamma), (loc_x), (fold_u)].
  rows_ten         the three that the test on G_omega closes: [sample o_omega, sample o_sp, (fold_omega)].
By: grows_begun (Johnson/Desc/Grows.lean) · open_taken | samples_taken (Johnson/Desc/Means/Holds.lean) · allSay_same (Johnson/Desc/K14/Law/Shapes.lean: the beginning brings no message).
WHAT IS NOT HERE: that W are the words built of a tuple of typed messages (s5) · the candidates (s1 · s2 · s3).
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K14.Law.LedgerSay
import Johnson.Desc.Means.Holds
import Johnson.Desc.K12.Law.OutK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words AllSay Says OpenKinds open_taken samples_taken)
open VerifiableInference.Desc (Grows grows_begun)
open VerifiableInference.Desc.Shared
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law (rowW RowsU RowsUL RowsO SmpSay rowsOn allSay_same)

/-- A row of a slice of a group's list is a row of the group. -/
theorem slice_mem (s : St) (g : ℕ) (G0 : Group) (hG : s.st.groups[g]? = some G0) (i n : ℕ)
    (r : OnBytes.Row) (hr : r ∈ ((rowsOn s g).drop i).take n) : r ∈ G0.rows.toList := by
  have h1 : r ∈ rowsOn s g := List.mem_of_mem_drop (List.mem_of_mem_take hr)
  unfold rowsOn at h1
  rw [hG] at h1
  exact h1

/-- Each open row of the group says its claim at the begun statement. -/
theorem open_says (s : St) (g : ℕ) (G0 : Group) (hG : s.st.groups[g]? = some G0)
    (hK : OpenKinds s.st) (W : Words GE)
    (h : AllSay OnBytes.Model.Reading.gl (begun s.st g G0) (runRows s.st G0).toList W) (i n : ℕ) :
    AllSay OnBytes.Model.Reading.gl (begun s.st g G0) (((rowsOn s g).drop i).take n) W :=
  fun r hr => h r (open_taken hK g G0 hG r (slice_mem s g G0 hG i n r hr))

/-- The same at the record's own statement: the beginning brings no message. -/
theorem open_says_own (s : St) (g : ℕ) (G0 : Group) (hG : s.st.groups[g]? = some G0)
    (hK : OpenKinds s.st) (W : Words GE)
    (h : AllSay OnBytes.Model.Reading.gl (begun s.st g G0) (runRows s.st G0).toList W) (i n : ℕ) :
    AllSay OnBytes.Model.Reading.gl s.st (((rowsOn s g).drop i).take n) W :=
  allSay_same OnBytes.Model.Reading.gl s.st (begun s.st g G0) (grows_begun _ _ _)
    (H2K.Out.closeLedgers_size _ _) _ W (open_says s g G0 hG hK W h i n)

/-- A member's sample's rows. -/
theorem smp_says (s : St) (g : ℕ) (G0 : Group) (W : Words GE)
    (h : AllSay OnBytes.Model.Reading.gl (begun s.st g G0) (runRows s.st G0).toList W) (o : ℕ)
    (ho : o ∈ G0.members.toList) (x : OnBytes.Oracle) (hx : s.st.oracles[o]? = some x) :
    SmpSay o s W :=
  ⟨x, begun s.st g G0, hx, grows_begun _ _ _, fun r hr => h r (samples_taken s.st G0 ho hx r hr)⟩

/-- **THE FOUR CLASSES THAT THE TEST ON G_u CLOSES.** -/
theorem rows_nine (P : Par) (n : ℕ) (num : Msg2 → ℕ) (s : St) (G0 : Group)
    (hG : s.st.groups[s.loc.gU]? = some G0) (hK : OpenKinds s.st) (W : Words GE)
    (h : AllSay OnBytes.Model.Reading.gl (begun s.st s.loc.gU G0) (runRows s.st G0).toList W)
    (hU : num .oU ∈ G0.members.toList) (xU : OnBytes.Oracle)
    (hxU : s.st.oracles[num .oU]? = some xU) :
    ∀ q ∈ [RowS.sample .oU, .recG, .loc, .foldU], rowW P n num q s W := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact smp_says s _ G0 W h _ hU xU hxU
  · exact ⟨_, grows_begun _ _ _, open_says s _ G0 hG hK W h _ _⟩
  · exact ⟨_, grows_begun _ _ _, open_says s _ G0 hG hK W h _ _⟩
  · exact open_says_own s _ G0 hG hK W h _ _

/-- **THE THREE THAT THE TEST ON G_omega CLOSES.** -/
theorem rows_ten (P : Par) (n : ℕ) (num : Msg2 → ℕ) (s : St) (G0 : Group)
    (hG : s.st.groups[s.loc.gOmega]? = some G0) (hK : OpenKinds s.st) (W : Words GE)
    (h : AllSay OnBytes.Model.Reading.gl (begun s.st s.loc.gOmega G0) (runRows s.st G0).toList W)
    (hO : num .oOmega ∈ G0.members.toList) (xO : OnBytes.Oracle)
    (hxO : s.st.oracles[num .oOmega]? = some xO)
    (hS : num .oSp ∈ G0.members.toList) (xS : OnBytes.Oracle)
    (hxS : s.st.oracles[num .oSp]? = some xS) :
    ∀ q ∈ [RowS.sample .oOmega, .sample .oSp, .foldOmega], rowW P n num q s W := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact smp_says s _ G0 W h _ hO xO hxO
  · exact smp_says s _ G0 W h _ hS xS hxS
  · exact open_says_own s _ G0 hG hK W h _ _

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.open_says
#print axioms Desc.K14.Law.Fence.open_says_own
#print axioms Desc.K14.Law.Fence.smp_says
#print axioms Desc.K14.Law.Fence.rows_nine
#print axioms Desc.K14.Law.Fence.rows_ten
