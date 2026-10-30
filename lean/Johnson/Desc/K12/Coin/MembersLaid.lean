-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/MembersLaid.lean: **AT THE SHARED CHAIN's TWO PROXIMITY TESTS EVERY MEMBER OF THE GROUP UNDER TEST SITS WHERE ITS SENDING LAID IT.** Statements and proofs.

The law of the proximity test speaks of the members D.mems of the plain data that the record fixes (Fixes, Sheet.lean; Made, Law/FirstOkLaw.lean): each with its number, its tree's place in the book D.book, its
part and its tree's shape. The join on the plan's side (seatIs_of_laid, ToldAtFile.lean) asks four equations of such a member m, at the i-th message of a sending with the layout lay that
stands at the chain's tree number base: m.t = base + lay.tree i · m.part = lay.part i · the book's tree at m.t has the shape m.tsh · m.tsh = lay.shapes[lay.tree i]. Here they are fed from the two Bools that the
record carries: seatX (Johnson/Desc/Sound/SeatsCarried.lean) and membX (Johnson/Desc/Sound/MembersCarried.lean).
  fixes_bookKeeps    the book of what the record fixes keeps what lay in the record's book (it IS that book where the mask came ahead; else a receiving behind it).
  LaidIs B m base lay i   the four equations.
  member_laid        from "the book places the message number n so, and the tree there has that shape" and Made's word on a member with the number n.
  mems_ids           the members' numbers are the group's, in order.
  **mems_at_nine**   at Seat.onGu's door: under seatX 9 and membX 9: D has two members: o_u (number 0: the 0-th of o_u's sending, base 0) and o_sp (number sU + 1: the 1-st of o_omega's sending, base
                     layU.shapes.size), each with LaidIs.
  **mems_at_ten**    at Seat.onGomega's door: under seatX 10 and membX 10: o_omega (the 0-th of its sending) and o_sp (the 1-st).
  withU_size · withOmega_size   o_u's sending has two messages where the masks go ahead; o_omega's two where there is a split.
Limits. With a split and the masks ahead. At the chain's own record St. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Coin.FirstBookOwn
import Johnson.Desc.Sound.MembersCarried

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.First (gpOf Plain made_of entered Seat1 Made)
open H2K.Sw (recvP_ok bookSentP)
open _root_.Desc.K14 (St P14 withU withOmega)
open _root_.Desc.K14.Law.Fence (seatX membX memOf seatX_place membX_nine membX_ten bookKeeps_recv)

/-- The book of what the record fixes keeps what lay in the record's book. -/
theorem fixes_bookKeeps (π : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (G0 : Group) (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) :
    BookKeeps t.book D.book := by
  cases hm : t.mask with
  | some id =>
    rw [book_of_fixes π t (by rw [hm]; rfl) a rest G0 Ly D hf]
    exact BookKeeps.refl _
  | none =>
    obtain ⟨cu, _, he⟩ := (made_of π _ a Ly D (hf.2.2.2 default)).ent
    unfold entered at he
    dsimp only at he
    rw [hm] at he
    dsimp only at he
    obtain ⟨⟨ids, d1⟩, hr, he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨id, _, he⟩ := Option.map_eq_some_iff.1 he
    obtain ⟨lay, _, _, _, rfl⟩ := recvP_ok hr
    have ebk : recvBook π.nums.firstTree t.book #[foldMaskNotice (ioppFoldShape cu Ly)] lay
        (begun t.st t.g G0).oracles.size t.roots = D.book :=
      congrArg (fun q : ℕ × Statement × TreeBook => q.2.2) he
    rw [← ebk]
    exact bookKeeps_recv _ _ _ _ _ _

/-- The four equations that the plan's side asks of a member. -/
structure LaidIs (B : TreeBook) (m : Seat1) (base : ℕ) (lay : TreeLay) (i : ℕ) : Prop where
  tree : m.t = base + lay.tree.getD i 0
  part : m.part = lay.part.getD i 0
  inBook : (B.trees[m.t]?).map (·.shape) = some m.tsh
  shape : m.tsh = lay.shapes.getD (lay.tree.getD i 0) default

/-- From the record's word on the message and Made's word on the member. -/
theorem member_laid {p : P12} {t12 : T12} {a : Fmt.M1.Stage} {L : GroupLayout} {D : Plain}
    (hm : Made p t12 a L D) (B : TreeBook) (hk : BookKeeps B D.book) (q : Fin D.mems.length)
    (n base : ℕ) (lay : TreeLay) (i : ℕ) (hid : (D.mems.get q).id = n)
    (hp : B.place[n]? = some (base + lay.tree.getD i 0, lay.part.getD i 0))
    (hs : (B.trees[base + lay.tree.getD i 0]?).map (·.shape) =
      some (lay.shapes.getD (lay.tree.getD i 0) default)) :
    LaidIs D.book (D.mems.get q) base lay i := by
  obtain ⟨_, h2⟩ := hm.mem q
  have e := h2.place
  rw [hid, hk.place _ _ hp] at e
  have e1 : base + lay.tree.getD i 0 = (D.mems.get q).t := congrArg Prod.fst (Option.some.inj e)
  have e2 : lay.part.getD i 0 = (D.mems.get q).part := congrArg Prod.snd (Option.some.inj e)
  obtain ⟨T, hT, hsh, _⟩ := h2.tree
  obtain ⟨T0, hT0, es⟩ := Option.map_eq_some_iff.1 hs
  obtain ⟨T', hT', e3, _⟩ := hk.tree _ T0 hT0
  rw [e1, hT] at hT'
  obtain rfl := Option.some.inj hT'
  refine ⟨e1.symm, e2.symm, ?_, ?_⟩
  · rw [hT]
    show some T.shape = _
    rw [hsh]
  · rw [← hsh, e3, es]

/-- The members' numbers are the group's, in order. -/
theorem mems_ids (π : P12) (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = G0.members.size ∧
      ∀ q : Fin D.mems.length, G0.members[q.val]? = some (D.mems.get q).id := by
  have hmd := made_of π _ a Ly D (hf.2.2.2 default)
  have hLy : Ly.members = G0.members := by
    have e := (OnBytes.Means.layout_eq t.st t.g G0 hf.2.1).symm.trans hf.2.2.1
    rw [← Option.some.inj e]
    rfl
  refine ⟨by rw [← hLy]; exact hmd.size.symm, fun q => ?_⟩
  rw [← hLy]
  exact (hmd.mem q).1

/-- **AT THE TEST ON G_u.** t: the record behind Seat.onGu's door in. -/
theorem mems_at_nine (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hU : 0 < sentU.size) (hO : 1 < (withOmega P.S).size)
    (hX : seatX P sentU layU layO 9 d = true) (hM : membX sentU.size 9 d = true) (π : P12)
    (t : T12) (ht : Seat.enter (·.gU) (·.firstMask) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = 2 ∧ ∀ q : Fin D.mems.length,
      (q.val = 0 ∧ (D.mems.get q).id = 0 ∧ LaidIs D.book (D.mems.get q) 0 layU 0) ∨
      (q.val = 1 ∧ (D.mems.get q).id = sentU.size + 1 ∧
        LaidIs D.book (D.mems.get q) layU.shapes.size layO 1) := by
  cases ht
  have hmd := made_of π _ a Ly D (hf.2.2.2 default)
  have hk := fixes_bookKeeps π _ a rest G0 Ly D hf
  obtain ⟨hl, hq⟩ := mems_ids π _ a rest G0 Ly D hf
  have hG : G0.members = #[0, sentU.size + 1] := by
    have h1 := (membX_nine _ d hM).1
    unfold memOf at h1
    have h2 : d.st.groups[d.loc.gU]? = some G0 := hf.2.1
    rw [h2] at h1
    exact Option.some.inj h1
  obtain ⟨pU, pO⟩ := seatX_place P sentU layU layO 9 d ⟨by omega, by omega⟩ hX
  rw [hG] at hl hq
  refine ⟨hl, fun q => ?_⟩
  have hq2 : q.val < 2 := Nat.lt_of_lt_of_eq q.isLt hl
  have h3 := hq q
  rcases Nat.lt_or_ge q.val 1 with h0 | h1
  · have e0 : q.val = 0 := by omega
    rw [e0] at h3
    have hid : (D.mems.get q).id = 0 := (Option.some.inj h3).symm
    obtain ⟨p1, p2⟩ := pU 0 hU
    exact .inl ⟨e0, hid, member_laid hmd d.book hk q 0 0 layU 0 hid (by rw [Nat.zero_add]; exact p1)
      (by rw [Nat.zero_add]; exact p2)⟩
  · have e1 : q.val = 1 := by omega
    rw [e1] at h3
    have hid : (D.mems.get q).id = sentU.size + 1 := (Option.some.inj h3).symm
    obtain ⟨p1, p2⟩ := pO 1 hO
    exact .inr ⟨e1, hid, member_laid hmd d.book hk q _ _ layO 1 hid p1 p2⟩

/-- **AT THE TEST ON G_omega.** t: the record behind Seat.onGomega's door in. -/
theorem mems_at_ten (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (d : St)
    (hO : 1 < (withOmega P.S).size)
    (hX : seatX P sentU layU layO 10 d = true) (hM : membX sentU.size 10 d = true) (π : P12)
    (t : T12) (ht : Seat.enter (·.gOmega) (fun _ => none) d = .ok t) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    D.mems.length = 2 ∧ ∀ q : Fin D.mems.length,
      (q.val = 0 ∧ (D.mems.get q).id = sentU.size ∧
        LaidIs D.book (D.mems.get q) layU.shapes.size layO 0) ∨
      (q.val = 1 ∧ (D.mems.get q).id = sentU.size + 1 ∧
        LaidIs D.book (D.mems.get q) layU.shapes.size layO 1) := by
  cases ht
  have hmd := made_of π _ a Ly D (hf.2.2.2 default)
  have hk := fixes_bookKeeps π _ a rest G0 Ly D hf
  obtain ⟨hl, hq⟩ := mems_ids π _ a rest G0 Ly D hf
  have hG : G0.members = #[sentU.size, sentU.size + 1] := by
    have h1 := membX_ten _ d hM
    unfold memOf at h1
    have h2 : d.st.groups[d.loc.gOmega]? = some G0 := hf.2.1
    rw [h2] at h1
    exact Option.some.inj h1
  obtain ⟨_, pO⟩ := seatX_place P sentU layU layO 10 d ⟨by omega, by omega⟩ hX
  rw [hG] at hl hq
  refine ⟨hl, fun q => ?_⟩
  have hq2 : q.val < 2 := Nat.lt_of_lt_of_eq q.isLt hl
  have h3 := hq q
  rcases Nat.lt_or_ge q.val 1 with h0 | h1
  · have e0 : q.val = 0 := by omega
    rw [e0] at h3
    have hid : (D.mems.get q).id = sentU.size := (Option.some.inj h3).symm
    obtain ⟨p1, p2⟩ := pO 0 (by omega)
    exact .inl ⟨e0, hid, member_laid hmd d.book hk q _ _ layO 0 hid p1 p2⟩
  · have e1 : q.val = 1 := by omega
    rw [e1] at h3
    have hid : (D.mems.get q).id = sentU.size + 1 := (Option.some.inj h3).symm
    obtain ⟨p1, p2⟩ := pO 1 hO
    exact .inr ⟨e1, hid, member_laid hmd d.book hk q _ _ layO 1 hid p1 p2⟩

/-- o_u's sending has two messages where the masks go ahead. -/
theorem withU_size (S : LinShape) (sentU : Array OracleNotice) (hm : S.masksAhead = true)
    (h : withU S = some sentU) : sentU.size = 2 := by
  unfold withU linWithU at h
  simp only [hm, if_true, Option.bind_eq_bind, Option.pure_def, Option.map_eq_some_iff,
    Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨x, ⟨n, _, rfl⟩, rfl⟩ := h
  rfl

/-- o_omega's sending has two messages where there is a split. -/
theorem withOmega_size (S : LinShape) (hS : S.sharedSplitNeeded = true) :
    (withOmega S).size = 2 := by
  unfold withOmega linMessageOmega
  simp [hS]

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.fixes_bookKeeps
#print axioms VerifiableInference.Desc.K12.Coin.member_laid
#print axioms VerifiableInference.Desc.K12.Coin.mems_at_nine
#print axioms VerifiableInference.Desc.K12.Coin.mems_at_ten
#print axioms VerifiableInference.Desc.K12.Coin.withU_size
#print axioms VerifiableInference.Desc.K12.Coin.withOmega_size
