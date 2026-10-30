-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedMembers.lean: **THE SHARED TABLE's LETTERS ms · N.tenant · N.lo · oNo, FILLED FROM THE PLAN's TWO LAYOUTS: AN OFFER.** Definitions with code; statements and proofs.

What for. The shared chain's table speaks of three sampled messages by TENANT (a tree's number through the file; the part in the tree): N.tenant; of members of sendings that SIT at tenants: ms; and the reading of a
sample (smpSt, Johnson/Desc/Sound/SmpShared.lean) goes by a member's NUMBER in the chain's statement: oNo. All are letters. What this file offers is the correspondence between the rows' letters and the members on the plan: SeatIs is
paid at (lo + m.t, lay.part i), and that THIS is the letter's seat needs one equation.
  tenantSh lo layU layO    o_u: (lo + layU.tree 0, layU.part 0) · o_omega: (lo + layU.shapes.size + layO.tree 0, layO.part 0) · o_sp: (lo + layU.shapes.size + layO.tree 1, layO.part 1).
  numbersSh                the table's numbers at these. numbersSh_sorted: the table's own test, from "the slot's own two trees lie below lo".
  sendingU · sendingO · msSh   the two sendings' SAMPLED members (the first fold's mask bears no sample: no member), seated so; the radii: letters.
  numSh sU                 o_u 0 · o_omega sU · o_sp sU + 1 (membX's numbers).   oNoSh sU: a member's number: by its sending's length and its place in it.
  msSh_all                 the members, one by one.
  hms_sh                   NineAt | TenAt's hms, by make.     hsit_sh: at each tenant a member sits.
  tenants_apart            the three tenants are three, where the layouts are the planner's (a tree of o_u's sending lies below those of o_omega's; two messages in one tree have two parts: layTrees_part).
  **number_of_seat**       a member of msSh that sits at m's tenant bears m's number: keep5_paid's premise "a member at o_u's seat bears o_u's number", by make.
  **place_of_tenant**      under the one X at the borders 6 … 12: the chain's book places m's number at m's tenant less lo: book.place[numSh sU m]? = some ((tenant m).1 - lo, (tenant m).2), and (tenant m).1 = lo + that place.
Limits. AN OFFER: whether the table's letters are laid so is left to the table's files. The members' shapes are the plan's S.fold.u | S.omega | S.sharedSplit: that the record's messages have them is shapedUB | shapedOB.
With a split. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedX
import Johnson.Desc.Sound.MeaningSig
import Johnson.Desc.Shared.BordersShared
import Johnson.Desc.K12.Coin.LaySymbols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Sound (Sending Mem membersOf SitsAt)
open VerifiableInference.Desc.Shared (Msg2 NumbersS)
open OnBytes.LayTreesLaws (inTree)

/-- The three tenants. -/
def tenantSh (lo : ℕ) (layU layO : TreeLay) : Msg2 → ℕ × ℕ
  | .oU => (lo + layU.tree.getD 0 0, layU.part.getD 0 0)
  | .oOmega => (lo + layU.shapes.size + layO.tree.getD 0 0, layO.part.getD 0 0)
  | .oSp => (lo + layU.shapes.size + layO.tree.getD 1 0, layO.part.getD 1 0)

/-- The table's numbers. w, index: the slot's own two tenants. -/
def numbersSh (lo : ℕ) (layU layO : TreeLay) (w index : ℕ × ℕ) : NumbersS :=
  ⟨lo, tenantSh lo layU layO, w, index⟩

theorem numbersSh_sorted (lo : ℕ) (layU layO : TreeLay) (w index : ℕ × ℕ) (hw : w.1 < lo)
    (hi : index.1 < lo) : (numbersSh lo layU layO w index).sorted = true := by
  simp [NumbersS.sorted, numbersSh, tenantSh, hw, hi, Nat.add_assoc]

/-- o_u's sending's one sampled member. -/
def sendingU (S : LinShape) (rU lo : ℕ) (layU layO : TreeLay) : Sending :=
  ⟨[(S.fold.u, rU)], fun _ => tenantSh lo layU layO .oU⟩

/-- o_omega's sending's two. -/
def sendingO (S : LinShape) (rO rSp lo : ℕ) (layU layO : TreeLay) : Sending :=
  ⟨[(S.omega, rO), (S.sharedSplit, rSp)], fun i =>
    if i.val = 0 then tenantSh lo layU layO .oOmega else tenantSh lo layU layO .oSp⟩

/-- The shared chain's sampled members. -/
def msSh (S : LinShape) (rU rO rSp lo : ℕ) (layU layO : TreeLay) : List Mem :=
  membersOf [sendingU S rU lo layU layO, sendingO S rO rSp lo layU layO]

/-- The messages' numbers in the chain's statement. sU: how many messages o_u's sending has. -/
def numSh (sU : ℕ) : Msg2 → ℕ
  | .oU => 0
  | .oOmega => sU
  | .oSp => sU + 1

/-- A member's number. -/
def oNoSh (sU : ℕ) (x : Mem) : ℕ := if x.1.l.length = 1 then 0 else sU + x.2.val

section
variable (S : LinShape) (rU rO rSp lo sU : ℕ) (layU layO : TreeLay)

/-- The members, one by one. -/
theorem msSh_all : msSh S rU rO rSp lo layU layO =
    [⟨sendingU S rU lo layU layO, ⟨0, Nat.one_pos⟩⟩,
      ⟨sendingO S rO rSp lo layU layO, ⟨0, Nat.two_pos⟩⟩,
      ⟨sendingO S rO rSp lo layU layO, ⟨1, Nat.one_lt_two⟩⟩] := rfl

/-- Of each member: which message it is: its seat and its number. -/
theorem msSh_is (z : Mem) (hz : z ∈ msSh S rU rO rSp lo layU layO) :
    ∃ m : Msg2, z.1.seat z.2 = tenantSh lo layU layO m ∧ oNoSh sU z = numSh sU m := by
  rw [msSh_all] at hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨.oU, rfl, rfl⟩
  · exact ⟨.oOmega, rfl, rfl⟩
  · exact ⟨.oSp, rfl, rfl⟩

/-- NineAt | TenAt's premise on the members' numbers. -/
theorem hms_sh : ∀ z ∈ msSh S rU rO rSp lo layU layO,
    oNoSh sU z = 0 ∨ oNoSh sU z = sU ∨ oNoSh sU z = sU + 1 := by
  intro z hz
  obtain ⟨m, _, e⟩ := msSh_is S rU rO rSp lo sU layU layO z hz
  rw [e]
  cases m
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- At each tenant a member sits. -/
theorem hsit_sh (m : Msg2) : ∃ y ∈ msSh S rU rO rSp lo layU layO,
    SitsAt y (tenantSh lo layU layO m).1 (tenantSh lo layU layO m).2 := by
  rw [msSh_all]
  cases m
  · exact ⟨_, List.mem_cons_self, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

end

/-- **The three tenants are three.** -/
theorem tenants_apart (codes : Codes) (sentU sentO : Array OracleNotice) (layU layO : TreeLay)
    (hlU : layTrees codes sentU = some layU) (hlO : layTrees codes sentO = some layO)
    (hU : 0 < sentU.size) (hO : 1 < sentO.size) (lo : ℕ) (m m' : Msg2)
    (h : tenantSh lo layU layO m = tenantSh lo layU layO m') : m = m' := by
  have l0 := OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlU hU
  have p0 := layTrees_part codes sentO layO hlO 0 (by omega)
  have p1 := layTrees_part codes sentO layO hlO 1 hO
  have key : (layO.tree.getD 0 0, layO.part.getD 0 0) ≠ (layO.tree.getD 1 0, layO.part.getD 1 0) := by
    intro e
    have e1 : layO.tree.getD 0 0 = layO.tree.getD 1 0 := congrArg Prod.fst e
    have e2 : layO.part.getD 0 0 = layO.part.getD 1 0 := congrArg Prod.snd e
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, p0, p1, ← e1] at e2
    simp [inTree, List.range_succ] at e2
  cases m <;> cases m' <;> first
    | rfl
    | (exfalso
       have e1 := congrArg Prod.fst h
       simp only [tenantSh] at e1
       omega)
    | (exfalso
       have e1 := congrArg Prod.fst h
       have e2 := congrArg Prod.snd h
       simp only [tenantSh] at e1 e2
       first
         | exact key (Prod.ext (by omega) e2)
         | exact key (Prod.ext (by omega) e2.symm))

/-- **A member that sits at m's tenant bears m's number.** -/
theorem number_of_seat (codes : Codes) (sentU sentO : Array OracleNotice) (layU layO : TreeLay)
    (hlU : layTrees codes sentU = some layU) (hlO : layTrees codes sentO = some layO)
    (hU : 0 < sentU.size) (hO : 1 < sentO.size) (S : LinShape) (rU rO rSp lo sU : ℕ) (m : Msg2)
    (z : Mem) (hz : z ∈ msSh S rU rO rSp lo layU layO)
    (hs : SitsAt z (tenantSh lo layU layO m).1 (tenantSh lo layU layO m).2) :
    oNoSh sU z = numSh sU m := by
  obtain ⟨m', e1, e2⟩ := msSh_is S rU rO rSp lo sU layU layO z hz
  have e : tenantSh lo layU layO m' = tenantSh lo layU layO m := e1.symm.trans hs
  rw [e2, tenants_apart codes sentU sentO layU layO hlU hlO hU hO lo m' m e]

/-- **Under the one X the chain's book places m's number at m's tenant less lo.** -/
theorem place_of_tenant (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (k : ℕ)
    (hk : 5 < k ∧ k ≤ 12) (d : St) (hX : sharedX P sentU layU layO k d = true)
    (hU : 0 < sentU.size) (hO : 1 < (withOmega P.S).size) (lo : ℕ) (m : Msg2) :
    ∃ z, d.book.place[numSh sentU.size m]? = some (z, (tenantSh lo layU layO m).2) ∧
      (tenantSh lo layU layO m).1 = lo + z ∧ z < d.book.trees.size := by
  obtain ⟨pU, pO⟩ := seatX_place P sentU layU layO k d hk
    ((sharedX_parts P sentU layU layO k d).1 hX).2.1
  have lt : ∀ z (T : TreeShape), (d.book.trees[z]?).map (·.shape) = some T →
      z < d.book.trees.size := fun z T h => by
    obtain ⟨T', hT', _⟩ := Option.map_eq_some_iff.1 h
    exact (Array.getElem?_eq_some_iff.1 hT').1
  cases m
  · exact ⟨_, (pU 0 hU).1, rfl, lt _ _ (pU 0 hU).2⟩
  · exact ⟨_, (pO 0 (by omega)).1, Nat.add_assoc _ _ _, lt _ _ (pO 0 (by omega)).2⟩
  · exact ⟨_, (pO 1 hO).1, Nat.add_assoc _ _ _, lt _ _ (pO 1 hO).2⟩

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.numbersSh_sorted
#print axioms Desc.K14.Law.Fence.hms_sh
#print axioms Desc.K14.Law.Fence.hsit_sh
#print axioms Desc.K14.Law.Fence.tenants_apart
#print axioms Desc.K14.Law.Fence.number_of_seat
#print axioms Desc.K14.Law.Fence.place_of_tenant
