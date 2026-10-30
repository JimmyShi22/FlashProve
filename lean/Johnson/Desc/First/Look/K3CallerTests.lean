-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallerTests.lean: THE TESTS ON PUBLIC DATA UNDER THE CLOSED CALLER OF A
LINK's DIGITS' LOOKUP (DigOK, K3Caller.lean) AS ONE Bool THAT A PROGRAM CAN RUN IN A MOMENT, and the
theorem that its yes gives DigOK. Definitions with code, statements and proofs. NO SOUNDNESS IS
CLAIMED. Nothing is evaluated in this file.

Main names.
  findJ_cell, findJ_mask: a cell inside its array, a slot below the number of slots, has an entry.
  digAddrB x tl D l: the digits' array ZZ is in the link's written list with at least tau rows and
    2 mz columns; the array BZ of the counts' bits with at least bzColumns columns and room for
    2^(kT + cK + 5) bits; both pass arrB (K3CallerLaid.lean: the link's own; laid; the blocks cover
    them inside their message's table); the lookup's mask entries lie below the number of slots, and
    in the link's mask row (maskB).
  dig_resolves: its yes, with NC ≤ 2^cK, gives Resolves at ReadsDig.
  digB set x tl D rad pp: that, the planner's yes, the library's shapeTest2, and one answer at every
    message of the signature.
  digOK_of: its yes, with «the kind's parameters make tl.f9», gives DigOK.
  digAt X i: link i's place and record, the lookup's record laid anew as digCallerAt lays it.
  digOK_at: so at digAt's value the one Bool gives DigOK: NO PREMISE IS LEFT BUT THE Bool.
  sameNums: the record that the kind's parameters make has the plan's own numbers, field by field
    (needed by no theorem: for the run).
Limits. An evaluation of digB at an example's public files speaks of that example. D is an argument.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Caller
import Johnson.Desc.First.Look.K3CallerLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)

theorem findJ_cell {S : Road.Rows.Shape} {t r c : ℕ} {T : Road.Rows.Arr}
    (hT : S.arrays[t]? = some T) (hr : r < T.R) (hc : c < T.K) :
    (findJ S (.cell t r c)).isSome = true := by
  obtain ⟨ht, eT⟩ := List.getElem?_eq_some_iff.1 hT
  have h1 : r < (S.arrays.get ⟨t, ht⟩).R := by
    rw [List.get_eq_getElem, eT]
    exact hr
  have h2 : c < (S.arrays.get ⟨t, ht⟩).K := by
    rw [List.get_eq_getElem, eT]
    exact hc
  simp only [findJ, dif_pos ht]
  rw [finOf_some h1, finOf_some h2]
  rfl

theorem findJ_mask {S : Road.Rows.Shape} {j : ℕ} (hj : j < S.ns) :
    (findJ S (.mask j)).isSome = true := by
  simp only [findJ]
  rw [finOf_some hj]
  rfl

/-- **The test on the addresses that the digits' lookup reads.** l: the signature's list. -/
def digAddrB (x : Place) (tl : HTailF2) (D : Sent) (l : List (OracleShape × Nat)) : Bool :=
  (match x.arrays.arrays[tl.ix.ZZ]? with
    | some T => decide (tl.tau ≤ T.R) && decide (tl.mz + tl.mz ≤ T.K)
    | none => false) &&
  (match x.arrays.arrays[tl.ix.BZ]? with
    | some T => decide (tl.bzColumns ≤ T.K) &&
        decide (2 ^ tl.f9.kT * 2 ^ tl.f9.cK * 2 ^ 5 ≤ tl.bzColumns * T.R)
    | none => false) &&
  arrB x.arrays D l x.link tl.ix.ZZ && arrB x.arrays D l x.link tl.ix.BZ &&
  decide (x.F.next + FoNums.nMasks tl.f9 ≤ x.arrays.ns) &&
  maskB D l x.link (x.F.next + FoNums.nMasks tl.f9)

/-- **Its yes gives Resolves.** -/
theorem dig_resolves {x : Place} {tl : HTailF2} {D : Sent} {l : List (OracleShape × Nat)}
    (h : digAddrB x tl D l = true) (hN : tl.f9.NC ≤ 2 ^ tl.f9.cK) :
    Resolves x.arrays D.codes l (seatOf D x.link) (ReadsDig tl x.F.next) := by
  simp only [digAddrB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hZ, hB⟩, aZ⟩, aB⟩, hs⟩, hm⟩ := h
  intro a ha
  cases ha with
  | low i =>
    split at hZ
    · rename_i T hT
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hZ
      have hj := findJ_cell hT (Nat.lt_of_lt_of_le i.2.isLt hZ.1)
        (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le i.1.isLt (Nat.le_add_right _ _)) hZ.2)
      exact ⟨hj, cell_resolves aZ hj⟩
    · cases hZ
  | high i =>
    split at hZ
    · rename_i T hT
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hZ
      have hj := findJ_cell hT (Nat.lt_of_lt_of_le i.2.isLt hZ.1)
        (Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.1.isLt tl.mz) hZ.2)
      exact ⟨hj, cell_resolves aZ hj⟩
    · cases hZ
  | bit t c j ht hc hj =>
    split at hB
    · rename_i T hT
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
      have hY : t * 2 ^ tl.f9.cK + c < 2 ^ tl.f9.kT * 2 ^ tl.f9.cK :=
        lt_mul_of (Nat.lt_of_lt_of_le hc hN) ht
      have hX : (t * 2 ^ tl.f9.cK + c) * 2 ^ 5 + j < 2 ^ tl.f9.kT * 2 ^ tl.f9.cK * 2 ^ 5 :=
        lt_mul_of hj hY
      have hpos : 0 < tl.bzColumns := by
        unfold HTailF2.bzColumns
        positivity
      have e := findJ_cell (c := ((t * 2 ^ tl.f9.cK + c) * 2 ^ 5 + j) % tl.bzColumns) hT
        (Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hX hB.2))
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) hB.1)
      exact ⟨e, cell_resolves aB e⟩
    · cases hB
  | mask s hs' =>
    exact ⟨findJ_mask (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hs' _) hs),
      mask_resolves hm (Nat.add_lt_add_left hs' _)⟩

/-- **The one Bool.** -/
def digB (set : Params.Setting) (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → Nat)
    (pp : Nat) : Bool :=
  (P.ofPlace set true x).entries.isSome && DgP.shapeTest2 tl pp &&
    (digList x D rad).all (fun o => o.1.answers == 1) && digAddrB x tl D (digList x D rad)

/-- **Its yes gives DigOK.** -/
theorem digOK_of {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} {pp : ℕ} (hs : (P.ofPlace set true x).shape = some tl.f9)
    (h : digB set x tl D rad pp = true) : DigOK set x tl D rad pp := by
  simp only [digB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨h₀, a, b, e⟩ := shape_made hs
  have hok : FoNums.ok tl.f9 = true := by
    rw [e]
    exact Cb.Fo.shape_ok a b
  exact ⟨hs, h2, h1, h3, dig_resolves h4 (Cb.Fo.ok_parts hok).1.2.2.1⟩

/-- Link i's place and the record of its smallness test, the lookup's record laid anew as the one
that the kind's own parameters make. -/
def digAt (X : Verify.Public) (i : Nat) : Option (Place × HTailF2) :=
  (lookAt X i true).bind fun x => (tlAt X i).bind fun tl =>
    (P.ofPlace (Params.settingOf X.P.frame) true x).shape.map fun h => (x, { tl with f9 := h })

/-- **At a link of the public record the one Bool is all that is asked.** -/
theorem digOK_at {X : Verify.Public} {i : ℕ} {x : Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → Nat} {pp : ℕ} (hx : digAt X i = some (x, tl))
    (h : digB (Params.settingOf X.P.frame) x tl D rad pp = true) :
    DigOK (Params.settingOf X.P.frame) x tl D rad pp := by
  refine digOK_of ?_ h
  unfold digAt at hx
  obtain ⟨x', -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', hh, hx⟩ := Option.map_eq_some_iff.1 hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  exact hh

/-- The numbers of two records of a lookup are the same, field by field; of a call its four numbers.
-/
def sameNums (h g : Forest.Shape) : Bool :=
  h.dT == g.dT && h.kT == g.kT && h.NT == g.NT && h.rK == g.rK && h.NC == g.NC && h.cK == g.cK &&
    h.iota == g.iota && h.first == g.first && h.callOf == g.callOf && h.pub == g.pub &&
    h.calls.map (fun c => (c.n, c.k, c.t0, c.kappa)) ==
      g.calls.map fun c => (c.n, c.k, c.t0, c.kappa)

/-- For a run: at every link of X: is there a place; the one Bool; the plan's own numbers. -/
def digRun (X : Verify.Public) (D : Sent) (pp : Nat) : List (Nat × Bool × Bool × Bool) :=
  (List.range ((if X.p4 then 2 else 1) * X.NGr + 1)).map fun i =>
    match digAt X i, tlAt X i with
    | some (x, tl), some tl₀ =>
      (i, true, digB (Params.settingOf X.P.frame) x tl D (fun _ => 0) pp, sameNums tl.f9 tl₀.f9)
    | _, _ => (i, false, false, false)

#print axioms dig_resolves
#print axioms digOK_of
#print axioms digOK_at

end VerifiableInference.Desc.First.Look
