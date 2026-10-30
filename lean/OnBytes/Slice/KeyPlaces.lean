-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyPlaces.lean: seats by row numbers, and what a group is asked, from plain
inequalities.

OnBytes/Slice/KeyGroup.lean places the rows of a sent message among the rows of a stage by maps into
two cubes. Here the maps are given by numbers: row r of a message stands at the vertex whose digits
are those of (first row) + r, the lowest first (vtx). This is how the written link places its two
members (OnBytes/Slice/BatSem.lean: memRow).

The result (Gp.ok_of): what the exit asks of a group (OnBytes/Slice/KeyExit.lean: Gp.OK) follows
from inequalities on sizes and radii:
 the stage's and the members' sizes (Sg.Sized, Mb.Sized);
 each member's rows have room in the stage's tables, and the members' blocks of rows do not overlap
 (Gp.Numbered);
 twice a member's radius is below the distance of each kind of row that it has;
 the stage's radius fits each member's, and is below the stage's distance.

Main definitions: vtx, Site.byNo, Gp.Numbered.

Main theorems: vtx_inj, Gp.Numbered.apart, Gp.numbered_one, numbered_two, numbered_three, Gp.ok_of,
Mb.fix_enc.

Not claimed. That a given verifier numbers its rows so.

-/
import OnBytes.Slice.KeyExit
import OnBytes.Slice.Cells

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- The vertex of the cube of k variables with the number i: its digit at t is the digit of i at
2^t. -/
def vtx (k i : ℕ) : Fin k → Bool := fun u => i.testBit u.val

/-- Different numbers below 2^k have different vertices. -/
theorem vtx_inj {k i j : ℕ} (hi : i < 2 ^ k) (hj : j < 2 ^ k) (h : vtx k i = vtx k j) : i = j := by
  have h1 : i % 2 ^ k = j % 2 ^ k := by
    rw [← rowNo_testBit k i, ← rowNo_testBit k j]
    exact congrArg Sz.rowNo h
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h1

/-- **A seat by numbers**: the message's main rows stand from row oM on, its mask rows from row oZ
on. -/
def Site.byNo (s : Sg) (M : Mb) (oM oZ : ℕ) (ha : M.a ≤ s.C.a)
    (hC : 0 < M.nM → M.C = s.C ∧ M.a = s.C.a) (hZ : 0 < M.nZ → M.Z = s.Z ∧ M.Z.a ≤ M.a) :
    Site s M where
  pM r := vtx _ (oM + r.val)
  pZ r := vtx _ (oZ + r.val)
  ha := ha
  hC r := (hC r.pos).1
  hM r := (hC r.pos).2
  hZ r := (hZ r.pos).1
  hz r := (hZ r.pos).2

namespace Gp
variable {s : Sg} (G : Gp s)

/-- **The group's seats are by numbers.** Member i has its main rows from row oM i on and its mask
rows from row oZ i on. The rows have room in the stage's tables, and two members' blocks of rows do
not overlap. -/
structure Numbered (oM oZ : G.ι → ℕ) : Prop where
  pM : ∀ i r, (G.seat i).pM r = vtx _ (oM i + r.val)
  pZ : ∀ i r, (G.seat i).pZ r = vtx _ (oZ i + r.val)
  roomM : ∀ i, oM i + (G.mb i).nM ≤ 2 ^ (s.h + s.g)
  roomZ : ∀ i, oZ i + (G.mb i).nZ ≤ 2 ^ s.h
  apartM : ∀ i i', i ≠ i' → oM i + (G.mb i).nM ≤ oM i' ∨ oM i' + (G.mb i').nM ≤ oM i
  apartZ : ∀ i i', i ≠ i' → oZ i + (G.mb i).nZ ≤ oZ i' ∨ oZ i' + (G.mb i').nZ ≤ oZ i

variable {G}

/-- No two rows of a group with seats by numbers have the same place. -/
theorem Numbered.apart {oM oZ : G.ι → ℕ} (h : G.Numbered oM oZ) : G.Apart where
  main := by
    rintro ⟨i, r⟩ ⟨i', r'⟩ heq
    have h0 : (G.seat i).pM r = (G.seat i').pM r' := heq
    rw [h.pM, h.pM] at h0
    have hr := r.isLt
    have hr' := r'.isLt
    have h1 := vtx_inj (lt_of_lt_of_le (Nat.add_lt_add_left hr _) (h.roomM i))
      (lt_of_lt_of_le (Nat.add_lt_add_left hr' _) (h.roomM i')) h0
    by_cases hii : i = i'
    · subst hii
      have h2 : r = r' := Fin.ext (Nat.add_left_cancel h1)
      rw [h2]
    · rcases h.apartM i i' hii with h2 | h2 <;> omega
  mask := by
    rintro ⟨i, r⟩ ⟨i', r'⟩ heq
    have h0 : (G.seat i).pZ r = (G.seat i').pZ r' := heq
    rw [h.pZ, h.pZ] at h0
    have hr := r.isLt
    have hr' := r'.isLt
    have h1 := vtx_inj (lt_of_lt_of_le (Nat.add_lt_add_left hr _) (h.roomZ i))
      (lt_of_lt_of_le (Nat.add_lt_add_left hr' _) (h.roomZ i')) h0
    by_cases hii : i = i'
    · subst hii
      have h2 : r = r' := Fin.ext (Nat.add_left_cancel h1)
      rw [h2]
    · rcases h.apartZ i i' hii with h2 | h2 <;> omega

/-- A group of one member with a seat by numbers. -/
theorem numbered_one {M : Mb} (σ : Site s M) {oM oZ : ℕ}
    (p : ∀ r, σ.pM r = vtx _ (oM + r.val)) (q : ∀ r, σ.pZ r = vtx _ (oZ + r.val))
    (rM : oM + M.nM ≤ 2 ^ (s.h + s.g)) (rZ : oZ + M.nZ ≤ 2 ^ s.h) :
    (Gp.one M σ).Numbered (fun _ => oM) fun _ => oZ where
  pM _ := p
  pZ _ := q
  roomM _ := rM
  roomZ _ := rZ
  apartM _ _ h := absurd rfl h
  apartZ _ _ h := absurd rfl h

/-- A group of two members with seats by numbers. -/
theorem numbered_two {A B : Mb} (σa : Site s A) (σb : Site s B) {oMa oZa oMb oZb : ℕ}
    (pa : ∀ r, σa.pM r = vtx _ (oMa + r.val)) (qa : ∀ r, σa.pZ r = vtx _ (oZa + r.val))
    (pb : ∀ r, σb.pM r = vtx _ (oMb + r.val)) (qb : ∀ r, σb.pZ r = vtx _ (oZb + r.val))
    (rMa : oMa + A.nM ≤ 2 ^ (s.h + s.g)) (rMb : oMb + B.nM ≤ 2 ^ (s.h + s.g))
    (rZa : oZa + A.nZ ≤ 2 ^ s.h) (rZb : oZb + B.nZ ≤ 2 ^ s.h)
    (dM : oMa + A.nM ≤ oMb ∨ oMb + B.nM ≤ oMa) (dZ : oZa + A.nZ ≤ oZb ∨ oZb + B.nZ ≤ oZa) :
    (Gp.two A B σa σb).Numbered (Duo.pick (T := fun _ => ℕ) oMa oMb)
      (Duo.pick (T := fun _ => ℕ) oZa oZb) where
  pM i := by cases i <;> assumption
  pZ i := by cases i <;> assumption
  roomM i := by cases i <;> assumption
  roomZ i := by cases i <;> assumption
  apartM i i' h := by
    cases i <;> cases i'
    · exact absurd rfl h
    · exact dM
    · exact dM.symm
    · exact absurd rfl h
  apartZ i i' h := by
    cases i <;> cases i'
    · exact absurd rfl h
    · exact dZ
    · exact dZ.symm
    · exact absurd rfl h

/-- A group of three members with seats by numbers. -/
theorem numbered_three {A B D : Mb} (σa : Site s A) (σb : Site s B) (σc : Site s D)
    {oMa oZa oMb oZb oMc oZc : ℕ}
    (pa : ∀ r, σa.pM r = vtx _ (oMa + r.val)) (qa : ∀ r, σa.pZ r = vtx _ (oZa + r.val))
    (pb : ∀ r, σb.pM r = vtx _ (oMb + r.val)) (qb : ∀ r, σb.pZ r = vtx _ (oZb + r.val))
    (pc : ∀ r, σc.pM r = vtx _ (oMc + r.val)) (qc : ∀ r, σc.pZ r = vtx _ (oZc + r.val))
    (rMa : oMa + A.nM ≤ 2 ^ (s.h + s.g)) (rMb : oMb + B.nM ≤ 2 ^ (s.h + s.g))
    (rMc : oMc + D.nM ≤ 2 ^ (s.h + s.g)) (rZa : oZa + A.nZ ≤ 2 ^ s.h)
    (rZb : oZb + B.nZ ≤ 2 ^ s.h) (rZc : oZc + D.nZ ≤ 2 ^ s.h)
    (dMab : oMa + A.nM ≤ oMb ∨ oMb + B.nM ≤ oMa) (dMac : oMa + A.nM ≤ oMc ∨ oMc + D.nM ≤ oMa)
    (dMbc : oMb + B.nM ≤ oMc ∨ oMc + D.nM ≤ oMb) (dZab : oZa + A.nZ ≤ oZb ∨ oZb + B.nZ ≤ oZa)
    (dZac : oZa + A.nZ ≤ oZc ∨ oZc + D.nZ ≤ oZa) (dZbc : oZb + B.nZ ≤ oZc ∨ oZc + D.nZ ≤ oZb) :
    (Gp.three A B D σa σb σc).Numbered (Tri.pick (T := fun _ => ℕ) oMa oMb oMc)
      (Tri.pick (T := fun _ => ℕ) oZa oZb oZc) where
  pM i := by cases i <;> assumption
  pZ i := by cases i <;> assumption
  roomM i := by cases i <;> assumption
  roomZ i := by cases i <;> assumption
  apartM i i' h := by
    cases i <;> cases i'
    · exact absurd rfl h
    · exact dMab
    · exact dMac
    · exact dMab.symm
    · exact absurd rfl h
    · exact dMbc
    · exact dMac.symm
    · exact dMbc.symm
    · exact absurd rfl h
  apartZ i i' h := by
    cases i <;> cases i'
    · exact absurd rfl h
    · exact dZab
    · exact dZac
    · exact dZab.symm
    · exact absurd rfl h
    · exact dZbc
    · exact dZac.symm
    · exact dZbc.symm
    · exact absurd rfl h

/-- **What the exit asks of a group, from inequalities on sizes and radii.** -/
theorem ok_of (hs : s.Sized) {oM oZ : G.ι → ℕ} (hN : G.Numbered oM oZ)
    (hm : ∀ i, (G.mb i).Sized) (h2M : ∀ i, 0 < (G.mb i).nM → 2 * (G.mb i).e < (G.mb i).dM)
    (h2Z : ∀ i, 0 < (G.mb i).nZ → 2 * (G.mb i).e < (G.mb i).dZ) {e : ℕ}
    (hfit : ∀ i, e < ((G.mb i).e + 1) * 2 ^ (s.C.a - (G.mb i).a)) (he : e < s.d) : G.OK e s.d :=
  ⟨hN.apart, hfit, fun i => ⟨_, Mb.uniq_of (hm i) (h2M i) (h2Z i)⟩, (Sg.fit_cM hs).dist,
    (Sg.fit_cZ hs).dist, he⟩

end Gp

/-- **An encoding decodes to its message.** -/
theorem Mb.fix_enc {M : Mb} {d : ℕ} (hU : M.Uniq d) (m : M.cd.J → GE) (r : M.cd.Q → GE) :
    M.fix (M.cd.enc m r) = some m :=
  Mb.fix_eq hU ⟨r, by
    show cnt _ ≤ M.e
    rw [cnt_false fun _ h => h rfl]
    exact Nat.zero_le _⟩

end OnBytes.Slice
