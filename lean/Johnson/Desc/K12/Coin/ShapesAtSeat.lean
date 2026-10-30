-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/ShapesAtSeat.lean: when do the members of a proximity test's group (the kind
K12) have a seat in the first stage at the format that their own shapes give (`siteL`,
Johnson/Desc/K12/Law/SiteOk.lean)? What of its yes follows from the conclusion's own test, and what
is left to the member's shape. Statements and proofs; no definition.

Why. The seam from the game's conclusion to a table's relation asks «ok (siteL cs a m) = true» of
each member. No guard of the running text asks it. But the conclusion «one tuple for all rows»
holds, under its own «there is», the yes of `gpL` (Johnson/Desc/K12/Law/FirstOk.lean), and with it
the yes of `memL` at each member: the stage's two codes at the parts that have rows, and bounds on
the tree's depth.
What it is not, first.
  (1) It pays that clause at no member: the facts on the member's shape (has it main rows, has it
    mask rows, where the index of the code of a part without rows points) and, at a member of mask
    rows alone, on its tree's depth are premises.
  (2) That the record's message at the member's number has the plan's shape is not said here.
  (3) Nothing is evaluated: no closed place, no number.
Main names.
  `site_at`: `siteL` reads of the member its shape and its tree's shape alone: a congruence.
  `site_of_mem`: the yes of `memL` gives the yes of `siteL` under three premises, each on a part
    without rows.
  `mem_of_ok`: the yes of `gpL` holds the yes of `memL` at each member.
  `maskB_idle`, `mainB_idle`: an index beyond the table gives the default code.
  `site_long`: a member with main rows. `site_mask`: a member of mask rows alone.
  `maskB_of_ok`, `site_maskB`: the same with the tree's depth held against the member's own mask
    code.
Limits: those of the files called. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.SiteOk
import Johnson.Desc.K12.Law.FirstOkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Pin
open OnBytes OnBytes.Params
open H2K.First (Seat1 memL gpL Plain)

/-- `siteL` reads of the member its shape and its tree's shape alone. -/
theorem site_at (cs cs₀ : Codes) (a : Fmt.M1.Stage) (m : Seat1) (sh₀ : OracleShape)
    (T₀ : TreeShape) (h1 : m.sh = sh₀) (h2 : m.tsh = T₀) (h3 : cs = cs₀)
    (hk : ok (siteL cs₀ a ⟨0, sh₀, 0, 0, T₀, 0⟩) = true) : ok (siteL cs a m) = true := by
  subst h1 h2 h3
  exact hk

/-- What of siteL's yes the member's clauses of gpL's yes already hold: ALL, but for what is asked
of the code of a part WITHOUT ROWS, and, at a member without main rows, that the tree is no deeper
than the shape's own depth. At a member with rows of both kinds the three premises are idle. -/
theorem site_of_mem (K : Codes) (a : Fmt.M1.Stage) (L : GroupLayout) (w : Nat) (m : Seat1)
    (h : ok (memL K a L w m) = true)
    (hM : m.sh.mainRows = 0 → (mainB K m.sh).logN ≤ m.tsh.logN)
    (hZ : m.sh.maskRows = 0 → (maskB K m.sh).logN ≤ m.tsh.logN)
    (hd : m.sh.mainRows = 0 → m.tsh.logN ≤ aOfB K m.sh) :
    ok (siteL K a m) = true := by
  simp only [memL, ok, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := h
  have cM : 0 < m.sh.mainRows → mainB K m.sh = ⟨a.C.a, a.C.l, a.C.r⟩ := by
    intro hp
    rcases h4 with h4 | h4
    · omega
    · unfold H2K.First.codeB at h4
      have e := of_decide_eq_true h4
      unfold mainB
      rw [Array.getD_eq_getD_getElem?, e]
      rfl
  have cZ : 0 < m.sh.maskRows → maskB K m.sh = ⟨a.Z.a, a.Z.l, a.Z.r⟩ := by
    intro hp
    rcases h5 with h5 | h5
    · omega
    · unfold H2K.First.codeB at h5
      have e := of_decide_eq_true h5
      unfold maskB
      rw [Array.getD_eq_getD_getElem?, e]
      rfl
  have zT : (maskB K m.sh).logN ≤ m.tsh.logN := by
    rcases Nat.eq_zero_or_pos m.sh.maskRows with q | q
    · exact hZ q
    · rw [cZ q]
      exact h3 q
  simp only [siteL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, codeIs]
  rcases Nat.eq_zero_or_pos m.sh.mainRows with q | q
  · have mT := hM q
    have dT := hd q
    have hA : aOfB K m.sh ≤ m.tsh.logN := Nat.max_le.2 ⟨mT, zT⟩
    refine ⟨by omega, Or.inl q, Or.inl q, ?_, Or.inr (Nat.le_max_right _ _), by omega⟩
    rcases Nat.eq_zero_or_pos m.sh.maskRows with z | z
    · exact Or.inl z
    · exact Or.inr (cZ z)
  · have eT := h2 q
    have eM : (mainB K m.sh).logN = a.C.a := by rw [cM q]
    have hA : aOfB K m.sh = a.C.a := by
      unfold aOfB
      rw [eM]
      exact Nat.max_eq_left (by omega)
    refine ⟨by omega, Or.inr (cM q), Or.inr hA, ?_, Or.inr (Nat.le_max_right _ _), by omega⟩
    rcases Nat.eq_zero_or_pos m.sh.maskRows with z | z
    · exact Or.inl z
    · exact Or.inr (cZ z)

/-- The yes of `gpL` holds the yes of `memL` at each member. -/
theorem mem_of_ok (π : VerifiableInference.Desc.K12.P12) (a : Fmt.M1.Stage) (row : GroupRow)
    (D : Plain) (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length) :
    ok (memL D.st.codes a D.L j.val (D.mems.get j)) = true := by
  unfold H2K.First.ok gpL at hok
  dsimp only at hok
  rw [List.all_append, Bool.and_eq_true, List.all_flatMap] at hok
  exact List.all_eq_true.1 hok.1 (D.mems.get j, j.val) (H2K.First.mem_zipIdx_get D.mems j)

/-- An index beyond the table gives the default code. -/
theorem maskB_idle (K : Codes) (sh : OracleShape) (h : K.mask.size ≤ sh.maskCode) :
    (maskB K sh).logN = 0 := by
  unfold maskB
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

theorem mainB_idle (K : Codes) (sh : OracleShape) (h : K.base.size ≤ sh.code) :
    (mainB K sh).logN = 0 := by
  unfold mainB
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

/-- **A member with main rows.** -/
theorem site_long (π : VerifiableInference.Desc.K12.P12) (a : Fmt.M1.Stage) (row : GroupRow)
    (D : Plain) (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length)
    (h0 : 0 < (D.mems.get j).sh.mainRows)
    (hz : (D.mems.get j).sh.maskRows = 0 → D.st.codes.mask.size ≤ (D.mems.get j).sh.maskCode) :
    ok (siteL D.st.codes a (D.mems.get j)) = true :=
  site_of_mem D.st.codes a D.L j.val (D.mems.get j) (mem_of_ok π a row D hok j)
    (fun q => absurd q (Nat.pos_iff_ne_zero.1 h0))
    (fun q => by rw [maskB_idle _ _ (hz q)]; exact Nat.zero_le _)
    (fun q => absurd q (Nat.pos_iff_ne_zero.1 h0))

/-- **A member of mask rows alone.** -/
theorem site_mask (π : VerifiableInference.Desc.K12.P12) (a : Fmt.M1.Stage) (row : GroupRow)
    (D : Plain) (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length)
    (h1 : 0 < (D.mems.get j).sh.maskRows)
    (hc : D.st.codes.base.size ≤ (D.mems.get j).sh.code)
    (hd : (D.mems.get j).tsh.logN ≤ a.Z.a) :
    ok (siteL D.st.codes a (D.mems.get j)) = true := by
  have hm := mem_of_ok π a row D hok j
  refine site_of_mem D.st.codes a D.L j.val (D.mems.get j) hm
    (fun _ => by rw [mainB_idle _ _ hc]; exact Nat.zero_le _)
    (fun q => absurd q (Nat.pos_iff_ne_zero.1 h1)) fun _ => ?_
  have hm' := hm
  simp only [memL, ok, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hm'
  obtain ⟨_, _, _, _, h5, _⟩ := hm'
  have cZ : maskB D.st.codes (D.mems.get j).sh = ⟨a.Z.a, a.Z.l, a.Z.r⟩ := by
    rcases h5 with h5 | h5
    · omega
    · unfold H2K.First.codeB at h5
      have e := of_decide_eq_true h5
      unfold maskB
      rw [Array.getD_eq_getD_getElem?, e]
      rfl
  have : a.Z.a ≤ aOfB D.st.codes (D.mems.get j).sh := by
    unfold aOfB
    rw [cZ]
    exact Nat.le_max_right _ _
  omega

/-- Where a member has mask rows, the code at its mask index is the stage's mask code. -/
theorem maskB_of_ok (π : VerifiableInference.Desc.K12.P12) (a : Fmt.M1.Stage) (row : GroupRow)
    (D : Plain) (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length)
    (h1 : 0 < (D.mems.get j).sh.maskRows) :
    maskB D.st.codes (D.mems.get j).sh = ⟨a.Z.a, a.Z.l, a.Z.r⟩ := by
  have hm' := mem_of_ok π a row D hok j
  simp only [memL, ok, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hm'
  obtain ⟨_, _, _, _, h5, _⟩ := hm'
  rcases h5 with h5 | h5
  · omega
  · unfold H2K.First.codeB at h5
    have e := of_decide_eq_true h5
    unfold maskB
    rw [Array.getD_eq_getD_getElem?, e]
    rfl

/-- `site_mask` with the tree's depth held against the member's own mask code. -/
theorem site_maskB (π : VerifiableInference.Desc.K12.P12) (a : Fmt.M1.Stage) (row : GroupRow)
    (D : Plain) (hok : H2K.First.ok (gpL π a row D) = true) (j : Fin D.mems.length)
    (h1 : 0 < (D.mems.get j).sh.maskRows)
    (hc : D.st.codes.base.size ≤ (D.mems.get j).sh.code)
    (hd : (D.mems.get j).tsh.logN ≤ (maskB D.st.codes (D.mems.get j).sh).logN) :
    ok (siteL D.st.codes a (D.mems.get j)) = true :=
  site_mask π a row D hok j h1 hc (by rw [maskB_of_ok π a row D hok j h1] at hd; exact hd)

end H2K.Pin

#print axioms H2K.Pin.site_at
#print axioms H2K.Pin.site_of_mem
#print axioms H2K.Pin.mem_of_ok
#print axioms H2K.Pin.maskB_idle
#print axioms H2K.Pin.mainB_idle
#print axioms H2K.Pin.site_long
#print axioms H2K.Pin.site_mask
#print axioms H2K.Pin.maskB_of_ok
#print axioms H2K.Pin.site_maskB
