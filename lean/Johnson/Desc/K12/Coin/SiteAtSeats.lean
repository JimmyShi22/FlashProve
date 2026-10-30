-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/SiteAtSeats.lean: at the shared chain's two proximity tests every member of
the group under test has a seat in the first stage at the format that its own shape gives (the yes
of `siteL`, Johnson/Desc/K12/Law/SiteOk.lean), under named facts on the plan. One definition;
statements and proofs; each proof is a row of calls.

Why. The seam from the game's conclusion to a table's relation asks «ok (siteL cs a (D.mems.get j))
= true» of each member.
Whose is what. Called: `site_long`, `site_mask` (ShapesAtSeat.lean); `member_shape`
(MemberShape.lean: a member's shape is the shape of the record in front's own message at its
number); `mems_at_nine`, `mems_at_ten` (MembersLaid.lean: at the two seats the group has two
members, with their numbers and their trees' shapes as their sendings laid them).
What it is not, first.
  (1) THE FACTS ON THE PLAN ARE PREMISES: which kind of rows each of the three messages' shapes has;
    that the index of the code of a part without rows lies beyond the codes' table; that the tree of
    the message of mask rows alone is no deeper than the stage's mask code.
  (2) That the record's message at the number has that shape is a premise (mU, mO, mSp).
  (3) That the record carries where each message was laid and which messages are the members
    (`seatX`, `membX`) are premises.
  (4) It is one clause of the seven that the seam asks of a member.
Main names.
  `ShapeFits cs a sh lg`: what the yes of `siteL` wants of a message's shape, of two sizes of the
    codes and of its tree's depth.
  `site_of_fits`, `site_of_tuple`: at one member, general in the chain and the arm.
  `site_nine`, `site_ten`: at the test on G_u; at the test on G_omega.
  `site_of_split`, `site_nineP`, `site_tenP`: the same at the plan's own codes and shapes, the
    plan's facts field by field; the depth of the split's mask message's tree is no premise
    (`split_depth`, Johnson/Desc/K12/Law/SplitDepth.lean).
Limits: those of the files called. With a split and the masks ahead. No soundness is claimed.
Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.ShapesAtSeat
import Johnson.Desc.K12.Coin.MemberShape
import Johnson.Desc.K12.Coin.MembersLaid
import Johnson.Desc.K12.Law.BatValsPay
import Johnson.Desc.K12.Law.SplitDepth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.First (Plain gpL)
open H2K.Pin (NTuple siteL)
open _root_.Desc.K14 (St P14 withOmega)
open _root_.Desc.K14.Law.Fence (seatX membX)

/-- What the yes of `siteL` wants of a message's shape, of two sizes of the codes and of its tree's
depth: main rows, and the mask code's index beyond the table where there is no mask row; or mask
rows, the main code's index beyond the table, and a tree no deeper than the stage's mask code. -/
def ShapeFits (cs : Codes) (a : Fmt.M1.Stage) (sh : OracleShape) (lg : ℕ) : Prop :=
  (0 < sh.mainRows ∧ (sh.maskRows = 0 → cs.mask.size ≤ sh.maskCode)) ∨
    (0 < sh.maskRows ∧ cs.base.size ≤ sh.code ∧ lg ≤ a.Z.a)

section
variable {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
  {Ly : GroupLayout} {D : Plain}

/-- **At one member, from the record in front's own message.** -/
theorem site_of_fits (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (hok : H2K.First.ok (gpL π a row₀ D) = true) (cs : Codes) (hcs : D.st.codes = cs)
    (j : Fin D.mems.length) (x : OnBytes.Oracle)
    (hx : t.st.oracles[(D.mems.get j).id]? = some x)
    (h : ShapeFits cs a x.shape (D.mems.get j).tsh.logN) :
    H2K.Pin.ok (siteL cs a (D.mems.get j)) = true := by
  have hlt : (D.mems.get j).id < t.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  obtain ⟨x₁, hx₁, hs⟩ := member_shape hf j hlt
  obtain rfl : x₁ = x := Option.some.inj (hx₁.symm.trans hx)
  subst hcs
  rcases h with ⟨h0, hz⟩ | ⟨h1, hc, hd⟩
  · exact H2K.Pin.site_long π a row₀ D hok j (by rw [hs]; exact h0) (by rw [hs]; exact hz)
  · exact H2K.Pin.site_mask π a row₀ D hok j (by rw [hs]; exact h1) (by rw [hs]; exact hc) hd

/-- The same from the conclusion "one tuple for all rows" itself. -/
theorem site_of_tuple {F : Frame} (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (y : F.E.Str)
    (hf : Fixes π t a rest G0 Ly D) (hN : NTuple F π no rad rd (t, y) a rest G0 Ly D)
    (cs : Codes) (hcs : D.st.codes = cs) (j : Fin D.mems.length) (x : OnBytes.Oracle)
    (hx : t.st.oracles[(D.mems.get j).id]? = some x)
    (h : ShapeFits cs a x.shape (D.mems.get j).tsh.logN) :
    H2K.Pin.ok (siteL cs a (D.mems.get j)) = true := by
  obtain ⟨row₀, hok, _⟩ := hN
  exact site_of_fits hf row₀ hok cs hcs j x hx h

end

/-- **AT THE TEST ON G_u.** shU, shSp: the shapes of o_u and of o_sp. -/
theorem site_nine (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hU : 0 < sentU.size) (hO : 1 < (withOmega P.S).size)
    (hX : seatX P sentU layU layO 9 d = true) (hM : membX sentU.size 9 d = true) (π : P12)
    (t : T12) (ht : Seat.enter (·.gU) (·.firstMask) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (hok : H2K.First.ok (gpL π a row₀ D) = true) (cs : Codes) (hcs : D.st.codes = cs)
    (shU shSp : OracleShape)
    (mU : ∃ x, d.st.oracles[0]? = some x ∧ x.shape = shU)
    (mSp : ∃ x, d.st.oracles[sentU.size + 1]? = some x ∧ x.shape = shSp)
    (fU : 0 < shU.mainRows ∧ (shU.maskRows = 0 → cs.mask.size ≤ shU.maskCode))
    (fSp : 0 < shSp.maskRows ∧ cs.base.size ≤ shSp.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a.Z.a) :
    ∀ j : Fin D.mems.length, H2K.Pin.ok (siteL cs a (D.mems.get j)) = true := by
  obtain ⟨_, hq⟩ := mems_at_nine P sentU layU layO d hU hO hX hM π t ht a rest G0 Ly D hf
  have est : t.st = d.st := by
    cases ht
    rfl
  intro j
  rcases hq j with ⟨_, hid, _⟩ | ⟨_, hid, hl⟩
  · obtain ⟨x, hx, hs⟩ := mU
    exact site_of_fits hf row₀ hok cs hcs j x (by rw [hid, est]; exact hx)
      (Or.inl (by rw [hs]; exact fU))
  · obtain ⟨x, hx, hs⟩ := mSp
    exact site_of_fits hf row₀ hok cs hcs j x (by rw [hid, est]; exact hx)
      (Or.inr (by rw [hs, hl.shape]; exact fSp))

/-- **AT THE TEST ON G_omega.** shO, shSp: the shapes of o_omega and of o_sp. -/
theorem site_ten (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 1 < (withOmega P.S).size)
    (hX : seatX P sentU layU layO 10 d = true) (hM : membX sentU.size 10 d = true) (π : P12)
    (t : T12) (ht : Seat.enter (·.gOmega) (fun _ => none) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (hok : H2K.First.ok (gpL π a row₀ D) = true) (cs : Codes) (hcs : D.st.codes = cs)
    (shO shSp : OracleShape)
    (mO : ∃ x, d.st.oracles[sentU.size]? = some x ∧ x.shape = shO)
    (mSp : ∃ x, d.st.oracles[sentU.size + 1]? = some x ∧ x.shape = shSp)
    (fO : 0 < shO.mainRows ∧ (shO.maskRows = 0 → cs.mask.size ≤ shO.maskCode))
    (fSp : 0 < shSp.maskRows ∧ cs.base.size ≤ shSp.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a.Z.a) :
    ∀ j : Fin D.mems.length, H2K.Pin.ok (siteL cs a (D.mems.get j)) = true := by
  obtain ⟨_, hq⟩ := mems_at_ten P sentU layU layO d hO hX hM π t ht a rest G0 Ly D hf
  have est : t.st = d.st := by
    cases ht
    rfl
  intro j
  rcases hq j with ⟨_, hid, _⟩ | ⟨_, hid, hl⟩
  · obtain ⟨x, hx, hs⟩ := mO
    exact site_of_fits hf row₀ hok cs hcs j x (by rw [hid, est]; exact hx)
      (Or.inl (by rw [hs]; exact fO))
  · obtain ⟨x, hx, hs⟩ := mSp
    exact site_of_fits hf row₀ hok cs hcs j x (by rw [hid, est]; exact hx)
      (Or.inr (by rw [hs, hl.shape]; exact fSp))

/-! ## The plan's facts, field by field -/

section
variable {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
  {Ly : GroupLayout} {D : Plain}

/-- At the mask message of the split: its tree is the second of what goes out with Omega. -/
theorem site_of_split (P : P14) (layO : TreeLay) (hf : Fixes π t a rest G0 Ly D)
    (row₀ : GroupRow) (hok : H2K.First.ok (gpL π a row₀ D) = true)
    (hcs : D.st.codes = P.codes) (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (hS : P.S.sharedSplitNeeded = true) (j : Fin D.mems.length) (x : OnBytes.Oracle)
    (hx : t.st.oracles[(D.mems.get j).id]? = some x) (hs : x.shape = P.S.sharedSplit)
    (ht : (D.mems.get j).tsh = layO.shapes.getD (layO.tree.getD 1 0) default)
    (oMain : 0 < P.S.omega.mainRows) (sMain : P.S.sharedSplit.mainRows = 0)
    (sMask : 0 < P.S.sharedSplit.maskRows) (sIdle : P.codes.base.size ≤ P.S.sharedSplit.code)
    (hcl : P.S.omegaLeafClass ≠ P.S.sharedSplitLeafClass) :
    H2K.Pin.ok (siteL P.codes a (D.mems.get j)) = true := by
  have hlt : (D.mems.get j).id < t.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  obtain ⟨x₁, hx₁, hsh⟩ := member_shape hf j hlt
  obtain rfl : x₁ = x := Option.some.inj (hx₁.symm.trans hx)
  have hsh' : (D.mems.get j).sh = P.S.sharedSplit := hsh.trans hs
  have hd := H2K.Pin.split_depth P.codes P.S layO hS hlO (Nat.pos_iff_ne_zero.1 oMain) sMain sMask
    hcl
  rw [← hcs]
  refine H2K.Pin.site_maskB π a row₀ D hok j (by rw [hsh']; exact sMask)
    (by rw [hsh', hcs]; exact sIdle) ?_
  rw [ht, hd, hsh', hcs]
  exact Nat.le_refl _

end

/-- **AT THE TEST ON G_u, from the plan's facts field by field.** -/
theorem site_nineP (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hU : 0 < sentU.size) (hO : 1 < (withOmega P.S).size)
    (hX : seatX P sentU layU layO 9 d = true) (hM : membX sentU.size 9 d = true) (π : P12)
    (t : T12) (ht : Seat.enter (·.gU) (·.firstMask) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (hok : H2K.First.ok (gpL π a row₀ D) = true) (hcs : D.st.codes = P.codes)
    (hlO : layTrees P.codes (withOmega P.S) = some layO) (hS : P.S.sharedSplitNeeded = true)
    (mU : ∃ x, d.st.oracles[0]? = some x ∧ x.shape = P.S.fold.u)
    (mSp : ∃ x, d.st.oracles[sentU.size + 1]? = some x ∧ x.shape = P.S.sharedSplit)
    (uMain : 0 < P.S.fold.u.mainRows) (uIdle : P.codes.mask.size ≤ P.S.fold.u.maskCode)
    (oMain : 0 < P.S.omega.mainRows) (sMain : P.S.sharedSplit.mainRows = 0)
    (sMask : 0 < P.S.sharedSplit.maskRows) (sIdle : P.codes.base.size ≤ P.S.sharedSplit.code)
    (hcl : P.S.omegaLeafClass ≠ P.S.sharedSplitLeafClass) :
    ∀ j : Fin D.mems.length, H2K.Pin.ok (siteL P.codes a (D.mems.get j)) = true := by
  obtain ⟨_, hq⟩ := mems_at_nine P sentU layU layO d hU hO hX hM π t ht a rest G0 Ly D hf
  have est : t.st = d.st := by
    cases ht
    rfl
  intro j
  rcases hq j with ⟨_, hid, _⟩ | ⟨_, hid, hl⟩
  · obtain ⟨x, hx, hs⟩ := mU
    exact site_of_fits hf row₀ hok P.codes hcs j x (by rw [hid, est]; exact hx)
      (Or.inl (by rw [hs]; exact ⟨uMain, fun _ => uIdle⟩))
  · obtain ⟨x, hx, hs⟩ := mSp
    exact site_of_split P layO hf row₀ hok hcs hlO hS j x (by rw [hid, est]; exact hx) hs hl.shape
      oMain sMain sMask sIdle hcl

/-- **AT THE TEST ON G_omega, from the plan's facts field by field.** -/
theorem site_tenP (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 1 < (withOmega P.S).size)
    (hX : seatX P sentU layU layO 10 d = true) (hM : membX sentU.size 10 d = true) (π : P12)
    (t : T12) (ht : Seat.enter (·.gOmega) (fun _ => none) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (hok : H2K.First.ok (gpL π a row₀ D) = true) (hcs : D.st.codes = P.codes)
    (hlO : layTrees P.codes (withOmega P.S) = some layO) (hS : P.S.sharedSplitNeeded = true)
    (mO : ∃ x, d.st.oracles[sentU.size]? = some x ∧ x.shape = P.S.omega)
    (mSp : ∃ x, d.st.oracles[sentU.size + 1]? = some x ∧ x.shape = P.S.sharedSplit)
    (oMain : 0 < P.S.omega.mainRows) (oIdle : P.codes.mask.size ≤ P.S.omega.maskCode)
    (sMain : P.S.sharedSplit.mainRows = 0)
    (sMask : 0 < P.S.sharedSplit.maskRows) (sIdle : P.codes.base.size ≤ P.S.sharedSplit.code)
    (hcl : P.S.omegaLeafClass ≠ P.S.sharedSplitLeafClass) :
    ∀ j : Fin D.mems.length, H2K.Pin.ok (siteL P.codes a (D.mems.get j)) = true := by
  obtain ⟨_, hq⟩ := mems_at_ten P sentU layU layO d hO hX hM π t ht a rest G0 Ly D hf
  have est : t.st = d.st := by
    cases ht
    rfl
  intro j
  rcases hq j with ⟨_, hid, _⟩ | ⟨_, hid, hl⟩
  · obtain ⟨x, hx, hs⟩ := mO
    exact site_of_fits hf row₀ hok P.codes hcs j x (by rw [hid, est]; exact hx)
      (Or.inl (by rw [hs]; exact ⟨oMain, fun _ => oIdle⟩))
  · obtain ⟨x, hx, hs⟩ := mSp
    exact site_of_split P layO hf row₀ hok hcs hlO hS j x (by rw [hid, est]; exact hx) hs hl.shape
      oMain sMain sMask sIdle hcl

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.site_of_fits
#print axioms VerifiableInference.Desc.K12.Coin.site_of_tuple
#print axioms VerifiableInference.Desc.K12.Coin.site_nine
#print axioms VerifiableInference.Desc.K12.Coin.site_ten
#print axioms VerifiableInference.Desc.K12.Coin.site_of_split
#print axioms VerifiableInference.Desc.K12.Coin.site_nineP
#print axioms VerifiableInference.Desc.K12.Coin.site_tenP
