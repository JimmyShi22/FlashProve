--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesSplit.lean: the function of the place "SPLIT" of the linear claim's
shared rounds returns a state, whatever scalar is sent. The state is written out over the state
behind the taking of a mask entry, which is given by its equation.

The place makes the constraint (fold), takes the next free entry of the mask message o_sp, and lays
one constraint on each of the two groups.

The function is the own text of the IOP as written in Lean (Johnson/Desc/K14/Text.lean). The
sub-protocol's decide function is that function under the names of its tests. A decision is the
format's step (Johnson/Desc/Block.lean: Block.step), which tests the rounds' form and the columns in
front of the decide function. That the eight decide functions return .ok: Returned.decides
(Johnson/Desc/K14/Honest/YesChain.lean). That the eight steps do: eight_steps_hold
(Johnson/Desc/K14/Honest/ChainSteps.lean).

Main names: Front8 (the facts in front; "SPLIT" is the eighth of the eight sub-protocols; "ledger"
is the name of the statement's field that counts a message's free mask entries), nextRealRow_zero,
fold_names, take_first (the entry taken is o_sp's first), split_of_facts, split_returns.

What is not claimed. That a decision accepts. That the facts in front hold at any state. That the
two constraints hold of what was sent: that hangs on the scalar. Shapes with one code are not
served. Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesFacts
import Johnson.Desc.K14.Law.Tries
import Johnson.Desc.Key.Laid.Split

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (withRow)
open OnBytes.Means (addRowP_of_fits)
open VerifiableInference.Desc.Ground (takeMaskP ok)
open VerifiableInference.Desc.Key (withRow_groupOff)
open VerifiableInference.Desc.Own (linFits)
open Desc.K14.Law (onOmega onU)

/-- In front of "SPLIT", the eighth of the eight sub-protocols. -/
structure Front8 (p : Par) (d : St) : Prop where
  lin : linFits d.st.codes p.S = true
  psi : d.loc.psiSh.length = p.S.kCol
  zeta : d.loc.zFd.length = p.S.kRow
  lay : d.loc.oU.lay = vectorLay d.st.codes p.S.fold.u p.S.fold.rowsHigh
  two : d.loc.gU ≠ d.loc.gOmega
  gU : GroupIs d.st d.loc.gU p.S.fold.u.code p.S.sharedMaskCode [d.loc.oU.oracle, d.loc.oSp]
  gO : GroupIs d.st d.loc.gOmega p.S.omega.code p.S.sharedMaskCode [d.loc.oOmega, d.loc.oSp]
  u : MsgIs d.st d.loc.oU.oracle p.S.fold.u
  omega : MsgIs d.st d.loc.oOmega p.S.omega
  sp : MsgIs d.st d.loc.oSp p.S.sharedSplit
  /-- o_sp's ledger is as its sending left it -/
  ledger : ∀ x, d.st.oracles[d.loc.oSp]? = some x →
    x.ledger = Slice.freshLedger d.st.codes p.S.sharedSplit
  apart : d.loc.oOmega ≠ d.loc.oSp
  apartU : d.loc.oSp ≠ d.loc.oU.oracle
  apartOU : d.loc.oOmega ≠ d.loc.oU.oracle
  /-- the mask message has a free entry -/
  free : 0 < Send.freeMaskEntries p.S.sharedSplit.maskRows
    (d.st.codes.mask.getD p.S.sharedSplit.maskCode default).ell p.S.sharedSplit.answers

/-- The first number from 0 on whose low bits name a real row is 0. -/
theorem nextRealRow_zero (rows logRows : Nat) (h : 0 < rows) :
    Blk.nextRealRow rows logRows (2 ^ logRows) 0 = 0 := by
  obtain ⟨f, hf⟩ : ∃ f, 2 ^ logRows = f + 1 :=
    ⟨2 ^ logRows - 1, by have := Nat.two_pow_pos logRows; omega⟩
  rw [hf]
  unfold Blk.nextRealRow
  rw [if_pos (by rw [Nat.zero_mod]; exact h)]

/-- (fold) names o_omega and o_u alone. -/
theorem fold_names (S : LinShape) (l : Lin) (lay : VectorLay) (row : Row)
    (h : fold S l lay = some row) (o : Nat) (ho : o ∈ row.oracles) :
    o = l.oOmega ∨ o = l.oU.oracle := by
  obtain ⟨A, B, _, _, _, _, rfl⟩ := fold_made S l lay row h
  unfold FoldedRow.addAll at ho
  simp only [Row.oracles, units_addLaid, runs_addLaid, forms_addLaid, List.mem_append,
    Array.toList_map, List.mem_map, Array.mem_toList_iff] at ho
  rcases ho with ((⟨t, ht, rfl⟩ | ⟨t, ht, _⟩) | ⟨t, ht, _⟩) | ⟨t, ht, _⟩
  · rcases mem_addLaid _ _ _ _ _ ht with h1 | ⟨v, _, rfl⟩
    · rcases mem_addLaid _ _ _ _ _ h1 with h2 | ⟨v, _, rfl⟩
      · simp at h2
      · exact Or.inl rfl
    · exact Or.inr rfl
  · simp at ht
  · simp at ht
  · simp at ht

/-- **The first entry of o_sp is the one taken**; the statement behind the taking is like the one in
front, with the same groups. -/
theorem take_first (p : Par) (d : St) (hS : p.S.sharedSplitNeeded = true) (h : Front8 p d) :
    ∃ d₁, takeMaskP d d.loc.oSp = some (0, d₁) ∧ Alike d.st d₁.st ∧
      d₁.st.groups = d.st.groups := by
  obtain ⟨xS, hxS, _, _, _⟩ := h.sp
  obtain ⟨hsh, _⟩ := (VerifiableInference.Desc.Own.linFits_iff d.st.codes p.S).1 h.lin
  have hSp : VerifiableInference.Desc.Own.SplitMessageFits p.S.sharedSplit p.S.sharedMaskCode := by
    rcases hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
    · rw [hS] at e
      cases e
    · exact e
  have hk : 0 < p.S.sharedSplit.maskRows := Nat.pos_of_ne_zero hSp.2.1
  have hl : xS.ledger = some
      { next := 0
        left := Send.freeMaskEntries p.S.sharedSplit.maskRows
          (d.st.codes.mask.getD p.S.sharedSplit.maskCode default).ell p.S.sharedSplit.answers
        rows := max p.S.sharedSplit.maskRows 1, logRows := ceilLog2 p.S.sharedSplit.maskRows } := by
    rw [h.ledger xS hxS]
    unfold Slice.freshLedger
    rw [if_pos hk]
  have hk0 := takeMaskP_of d d.loc.oSp xS _ hxS hl rfl h.free
  rw [nextRealRow_zero (max p.S.sharedSplit.maskRows 1) (ceilLog2 p.S.sharedSplit.maskRows)
    (by omega)] at hk0
  exact ⟨_, hk0, alike_mod d.st d.st.groups d.loc.oSp _ (fun _ => ⟨rfl, rfl⟩), rfl⟩

/-- The function of "SPLIT" returns where its named tests hold, a mask entry is taken, and
SplitFacts holds at the statement behind the taking: one constraint more on each of the two
groups. -/
theorem split_of_facts (p : Par) (d d₁ : St) (r : Fmt.RoundView) (x : UInt64 × UInt64 × UInt64) (row : Row)
    (GU GO : Group) (kappa : Nat) (hS : p.S.sharedSplitNeeded = true) (hx : r.vals = [.e x])
    (hf : fold p.S d.loc (linLayOmega d.st.codes p.S) = some row)
    (hGO : d.st.groups[d.loc.gOmega]? = some GO) (hok : ok (splitL d row) = true)
    (hk : takeMaskP d d.loc.oSp = some (kappa, d₁))
    (hGO1 : d₁.st.groups[d.loc.gOmega]? = some GO) (hGU1 : d₁.st.groups[d.loc.gU]? = some GU)
    (hrunO : GO.inRun = false) (hrunU : GU.inRun = false) (two : d.loc.gU ≠ d.loc.gOmega)
    (facts : SplitFacts d₁.st p.S d.loc (linLayOmega d.st.codes p.S) GU GO kappa) :
    split p d [r] = some { d₁ with
      st := (withRow (withRow d₁.st d.loc.gOmega
          (onOmega row GO.members d.loc.oSp kappa (E.ofTriple x))) d.loc.gU
        (onU row GO.members d.loc.oSp kappa (E.ofTriple x))) } := by
  have a1 := addRowP_of_fits d₁ d.loc.gOmega GO _ hGO1 hrunO
    (onOmega_fits facts row hf (E.ofTriple x))
  have a2 := addRowP_of_fits ({ d₁ with
      st := (withRow d₁.st d.loc.gOmega (onOmega row GO.members d.loc.oSp kappa (E.ofTriple x))) } :
        St) d.loc.gU GU _ ((withRow_groupOff _ _ _ _ (Ne.symm two)).trans hGU1) hrunU
    ((onU_fits facts row hf (E.ofTriple x)).elsewhere _ _)
  exact Law.split_yes p d _ r row x GO kappa _ _ hS hf hx hGO hok hk a1 a2

/-- **The function of "SPLIT" returns**, whatever scalar is sent: o_sp's first entry is taken, and
one constraint more stands on each of the two groups. -/
theorem split_returns (p : Par) (d : St) (r : Fmt.RoundView) (x : UInt64 × UInt64 × UInt64)
    (hS : p.S.sharedSplitNeeded = true) (h : Front8 p d) (hx : r.vals = [.e x]) :
    ∃ row GO d₁, fold p.S d.loc (linLayOmega d.st.codes p.S) = some row ∧
      d.st.groups[d.loc.gOmega]? = some GO ∧ takeMaskP d d.loc.oSp = some (0, d₁) ∧
      split p d [r] = some { d₁ with
        st := (withRow (withRow d₁.st d.loc.gOmega
            (onOmega row GO.members d.loc.oSp 0 (E.ofTriple x))) d.loc.gU
          (onU row GO.members d.loc.oSp 0 (E.ofTriple x))) } := by
  obtain ⟨GU, hGU, _, _, hrunU, hmemU⟩ := h.gU
  obtain ⟨GO, hGO, _, _, hrunO, hmemO⟩ := h.gO
  obtain ⟨xS, hxS, hsS, _, hpS⟩ := h.sp
  have R := shapeSizes_of d.st.codes p.S h.lin
  obtain ⟨hsh, _⟩ := (VerifiableInference.Desc.Own.linFits_iff d.st.codes p.S).1 h.lin
  have hSp : VerifiableInference.Desc.Own.SplitMessageFits p.S.sharedSplit p.S.sharedMaskCode := by
    rcases hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
    · rw [hS] at e
      cases e
    · exact e
  obtain ⟨row, hf⟩ := fold_makes p.S d.loc (linLayOmega d.st.codes p.S) h.psi h.zeta
  -- the five named tests
  have hok : ok (splitL d row) = true := by
    simp only [ok, splitL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [hGO, hGU, hxS]
    refine ⟨by simpa using (Ne.symm h.two), ?_, contains_of hmemO _ (by simp),
      contains_of hmemU _ (by simp), ?_⟩
    · show (xS.shape.mainRows == 0) = true
      rw [hsS, hSp.1]
      rfl
    · rw [List.all_eq_true]
      intro o ho
      show (GO.members.contains o != GU.members.contains o) = true
      rcases fold_names _ _ _ _ hf o ho with rfl | rfl
      · rw [contains_of hmemO _ (by simp), not_contains_of hmemU _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨h.apartOU, h.apart⟩)]
        rfl
      · rw [not_contains_of hmemO _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨Ne.symm h.apartOU, Ne.symm h.apartU⟩), contains_of hmemU _ (by simp)]
        rfl
  -- the mask entry; the statement behind the taking is like the one in front
  obtain ⟨d₁, hk0, hA, hg⟩ := take_first p d hS h
  obtain ⟨ms1, ms2⟩ := mask_first d.st d.loc.oSp xS p.S.sharedSplit hxS hsS hpS h.free
  have sU := (sits_u h.lin h.u GU (contains_of hmemU _ (by simp))).mono R.matrix
  rw [← h.lay] at sU
  have sO := sits_omega h.lin h.omega GO (contains_of hmemO _ (by simp))
  have facts : SplitFacts d₁.st p.S d.loc (linLayOmega d.st.codes p.S) GU GO 0 :=
    { omega := sO.alike hA GO sO.member
      u := sU.alike hA GU sU.member
      uOut := not_contains_of hmemO _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Ne.symm h.apartOU, Ne.symm h.apartU⟩)
      spO := contains_of hmemO _ (by simp)
      spU := contains_of hmemU _ (by simp)
      mask := by rw [hA.has_eq]; exact ms1
      inside := Nat.two_pow_pos _
      free := fun y hy hq => by
        obtain ⟨y0, e1, _, e2⟩ := hA.there _ y hy
        obtain rfl : xS = y0 := Option.some.inj (hxS.symm.trans e1)
        exact ms2 (e2 ▸ hq)
      bitsOmega := R.kRow
      bitsU := by rw [h.lay]; exact R.kBoth }
  exact ⟨row, GO, d₁, hf, hGO, hk0, split_of_facts p d d₁ r x row GU GO 0 hS hx hf hGO hok hk0
    (by rw [hg]; exact hGO) (by rw [hg]; exact hGU) hrunO hrunU h.two facts⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.nextRealRow_zero
#print axioms Desc.K14.Honest.fold_names
#print axioms Desc.K14.Honest.take_first
#print axioms Desc.K14.Honest.split_of_facts
#print axioms Desc.K14.Honest.split_returns
