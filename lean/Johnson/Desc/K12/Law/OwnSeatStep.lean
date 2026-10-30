-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OwnSeatStep.lean: two tests on the record behind the batching of a proximity
test, from a yes of the block's step. Statements and proofs.

`lastOk` (Johnson/Desc/K12/Law/OwnSeat.lean) and `aloneAt` (Johnson/Desc/K12/Law/AloneOk.lean)
follow from a yes of `Block.step` of `proximityTestKind guardedProximityTestParts p`, under `p.early = true`, the block's test on
the plan, and the batching's yes at the first round (`k12_guards`, Johnson/Desc/K12/Law/TopH.lean,
pays the last from the others). So `accK_yes_real_own` (Johnson/Desc/K12/Law/AccKOwn.lean) need not
take them as premises, and the block need not ask them.
Why they hold: the front of the test asks that each member's tree is in the book ("front: each tree
is in the book", Johnson/Desc/K12/Front.lean); this one clause of the front is spent. Where the
record names no mask, `entered` (Johnson/Desc/K12/Law/FirstOk.lean) lays the first fold's own mask
by `Ground.recvP`. That function's own guard, at the record behind the batching, holds that
statement and book know as many messages (`recvP_ok`, Johnson/Desc/K12/Law/SwUnfold.lean). So the
mask's place is written behind the book's places, at the mask's own number, and its tree's index is
the book's number of trees or more. So every member's tree stands below the mask's.
Main names:
  `getLast_of_max`: a rising list that holds x and nothing greater ends in x.
  `entered_own`: where the record names no mask, the place of the mask that `entered` lays names a
    tree's index that is the book's number of trees or more, and the elder places are kept.
  `own_below`: at the plain data D that `gpOf` makes, where the record names no mask and each
    member's tree is in the book in front: every member's tree's index is below `D.fresh.t`.
  `refuse_all`, `frontJ_all`, `front_trees`: a yes of the front's part holds all the front's
    clauses; the clause on the trees, read off for the group's members.
  `step_plain`: from a yes of the step: the first stage, the plain data at the record behind the
    batching, each member's tree in the book in front.
  `lastOk_of_step`: under these three, a yes of the step gives `lastOk` at the record behind the
    batching. It has no premise on the mask: where the record names one, `lastOk` asks only that the
    plain data can be made.
  `aloneAt_of_step`: the same gives `aloneAt … = some true` where the record in front names no mask
    (the premise `t0.mask = none`; Johnson/Desc/K12/Law/OwnMaskStep.lean pays it where the first
    fold sends its own mask).
Limits: stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean), under `p.early = true`
(Johnson/Desc/K12/Law/EarlyStep.lean pays it from the same yes) and the block's test on the plan.
Where the record names a mask, `aloneAt` may be false in truth: the mask may share a member's tree.
No soundness is claimed, and nothing is said on hiding.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.AccKOwn

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok got_ok)
open H2K.First (gpOk gpOf Plain lastOk lastL lastOn aloneAt aloneOk plainAt seatOf entered Made
  made_of gpOk_inv)
open H2K.Sw (recvP_ok bookSentP)

theorem getLast_of_max : ∀ (l : List ℕ) (x : ℕ), l.Pairwise (· < ·) → x ∈ l → (∀ y ∈ l, y ≤ x) →
    l.getLast? = some x
  | [], _, _, hx, _ => by cases hx
  | [a], x, _, hx, _ => by
    simp only [List.mem_singleton] at hx
    subst hx
    rfl
  | a :: b :: l, x, hi, hx, hm => by
    rw [List.getLast?_cons_cons]
    have hi' := List.pairwise_cons.1 hi
    refine getLast_of_max (b :: l) x hi'.2 ?_ (fun y hy => hm y (List.mem_cons_of_mem _ hy))
    rcases List.mem_cons.1 hx with rfl | h
    · have h1 := hi'.1 b (List.mem_cons_self ..)
      have h2 := hm b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      omega
    · exact h

/-- Where the record names no mask, the mask that `entered` lays stands at a tree's index that is
the book's number of trees or more, and the elder places are kept. -/
theorem entered_own (p : P12) (t : T12) (cu : IoppStage) (L : GroupLayout) (id : ℕ) (st : Statement)
    (bk : TreeBook) (hm : t.mask = none) (h : entered p t cu L = some (id, st, bk)) :
    (∃ q, bk.place[id]? = some q ∧ t.book.trees.size ≤ q.1) ∧
      ∀ (o : ℕ) (q : ℕ × ℕ), t.book.place[o]? = some q → bk.place[o]? = some q := by
  unfold entered at h
  rw [hm] at h
  dsimp only at h
  obtain ⟨⟨ids, d₁⟩, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨i0, hi, h⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨lay, _, hstep, rfl, rfl⟩ := recvP_ok hr
  cases h
  dsimp only at hstep hi ⊢
  have e0 : id = t.st.oracles.size := by
    simp at hi
    omega
  subst e0
  constructor
  · refine ⟨(t.book.trees.size + lay.tree.getD 0 0, lay.part.getD 0 0), ?_, Nat.le_add_right _ _⟩
    unfold bookSentP
    dsimp only
    rw [hstep, Array.getElem?_append_right (Nat.le_refl _)]
    simp
  · intro o q ho
    unfold bookSentP
    dsimp only
    have hlt : o < t.book.place.size := by
      by_contra hc
      rw [Array.getElem?_eq_none (by omega)] at ho
      cases ho
    rw [Array.getElem?_append_left hlt]
    exact ho

/-- At gpOf's plain data, where the record names no mask and each member's tree is in the book in
front: every member's tree stands below the mask's. -/
theorem own_below (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (D : Plain)
    (hD : gpOf p t a L = some D) (hm : t.mask = none)
    (hin : ∀ o ∈ L.members.toList, ∃ q, t.book.place[o]? = some q ∧ q.1 < t.book.trees.size) :
    ∀ m ∈ D.mems, m.t < D.fresh.t := by
  have M := made_of p t a L D hD
  obtain ⟨cu, _, he⟩ := M.ent
  obtain ⟨⟨q, hq, hle⟩, hold⟩ := entered_own p t cu L _ _ _ hm he
  have hf : q.1 = D.fresh.t := by
    have := M.fresh.place
    rw [hq] at this
    exact congrArg Prod.fst (Option.some.inj this)
  intro m hmem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  obtain ⟨h1, h2⟩ := M.mem ⟨i, hi⟩
  have hmm : (D.mems.get ⟨i, hi⟩).id ∈ L.members.toList := by
    rw [← Array.getElem?_toList] at h1
    exact List.mem_of_getElem? h1
  obtain ⟨q', hq', hlt⟩ := hin _ hmm
  have := h2.place
  rw [hold _ _ hq'] at this
  have e : q'.1 = (D.mems.get ⟨i, hi⟩).t := congrArg Prod.fst (Option.some.inj this)
  show (D.mems.get ⟨i, hi⟩).t < D.fresh.t
  omega

/-- A list of named clauses that refuses nothing holds throughout. -/
theorem refuse_all (l : Ground.Clauses) (u : Unit) (h : Ground.refuse l = .ok u) :
    ∀ c ∈ l, c.2 = true := by
  unfold Ground.refuse at h
  split at h
  · cases h
  · rename_i hn
    simp only [List.find?_eq_none] at hn
    intro c hc
    simpa using hn c hc

/-- A yes of the front's part holds all the front's clauses. -/
theorem frontJ_all (p : P12) (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (frontJ p).decide t rs gs = .ok t') : ∀ c ∈ frontL t.st t.book t.g t.mask, c.2 = true := by
  unfold frontJ at h
  dsimp only at h
  split at h
  · obtain ⟨_, hf, _⟩ := bind_ok h
    unfold frontE at hf
    obtain ⟨u, h1, _⟩ := bind_ok hf
    exact refuse_all _ u h1
  · cases h

/-- The front's clause "each tree is in the book", read off for the group's members. -/
theorem front_trees {St : Statement} {B : TreeBook} {g : ℕ} {mask : Option ℕ}
    (h : ∀ c ∈ frontL St B g mask, c.2 = true) {G : Group} (hG : St.groups[g]? = some G) :
    ∀ o ∈ G.members.toList, ∃ q, B.place[o]? = some q ∧ q.1 < B.trees.size := by
  have := h ("front: each tree is in the book", Ground.on (St.groups[g]?) fun G =>
    (G.members.toList ++ mask.toList).all fun o =>
      ((B.place[o]?).bind fun p => B.trees[p.1]?).isSome) (by simp [frontL])
  simp only [Ground.on, hG, Option.map_some, Option.getD_some, List.all_eq_true] at this
  intro o ho
  have h1 := this o (List.mem_append_left _ ho)
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨q, hq, hT⟩ := Option.bind_eq_some_iff.1 hT
  refine ⟨q, hq, ?_⟩
  by_contra hc
  rw [Array.getElem?_eq_none (by omega)] at hT
  cases hT

/-- What both theorems below stand on: from a yes of the step: the first stage, the plain data at
the record behind the batching, and each member's tree in the book in front. -/
theorem step_plain (p : P12) (he : p.early = true) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB)) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : Plain), p.nums.stages = a :: rest ∧
      gpOf p { t0 with st := SB, pass := .claim rowB LB } a LB = some D ∧
      ∀ o ∈ LB.members.toList, ∃ q, t0.book.place[o]? = some q ∧ q.1 < t0.book.trees.size := by
  obtain ⟨_, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 hstep
  obtain ⟨_, _, e, r, row, L, S', hr, hb, hg⟩ := k12_guards p he t0 tE _ _ hp hdec
  obtain rfl : noDigest r0 = r := (List.cons.inj hr).1
  cases bat_unique _ _ _ _ _ _ _ hbB hb
  obtain ⟨a, rest, ds, tF, t1, e1, _, hfr, _⟩ := k12_ok guardedProximityTestParts p t0 tE _ _ hdec
  obtain ⟨D, hD, _⟩ := gpOk_inv p _ a rest rowB LB e1 rfl hg
  obtain ⟨hfr', _, _⟩ := frontK_ok p _ _ _ _ hfr
  have hcl := frontJ_all p _ _ _ _ hfr'
  obtain ⟨G0, hG0, hlay, _⟩ := bat_front _ _ _ _ _ _ _ hbB
  have eL : LB = Own.layoutOf t0.st G0 := by
    rw [Own.layout_of_group hG0] at hlay
    exact (Option.some.inj hlay).symm
  refine ⟨a, rest, D, e1, hD, ?_⟩
  rw [eL]
  exact front_trees hcl hG0

/-- **lastOk from the step's yes.** No premise on the mask: where the record names one, lastOk asks
only that the plain data can be made. -/
theorem lastOk_of_step (p : P12) (he : p.early = true) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB)) :
    lastOk p { t0 with st := SB, pass := .claim rowB LB } = true := by
  obtain ⟨a, rest, D, e1, hD, hin⟩ :=
    step_plain p he t0 tE F n r0 rs' cols hp hstep eB rowB LB SB hbB
  unfold lastOk lastL
  rw [e1]
  dsimp only
  rw [hD]
  dsimp only
  cases hm : t0.mask with
  | some id => simp [lastOn, H2K.First.ok]
  | none =>
    have hb := own_below p _ a LB D hD hm hin
    have M := made_of p _ a LB D hD
    have hl : D.ts.getLast? = some D.fresh.t := by
      rw [M.ts]
      refine getLast_of_max _ _ (Fmt.listOf_incr _) ((Fmt.listOf_mem _ _).2 (by simp)) ?_
      intro y hy
      rcases List.mem_append.1 ((Fmt.listOf_mem _ _).1 hy) with h | h
      · obtain ⟨m, hm', rfl⟩ := List.mem_map.1 h
        exact Nat.le_of_lt (hb m hm')
      · simp only [List.mem_singleton] at h
        omega
    simp [lastOn, H2K.First.ok, hl]

/-- **aloneAt from the step's yes, where the record in front names no mask.** -/
theorem aloneAt_of_step (p : P12) (he : p.early = true) (t0 tE : T12) (F n : ℕ) (r0 : Fmt.RoundView)
    (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (hstep : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 (r0 :: rs') cols = .ok (tE, n))
    (eB : Fmt.Entry) (rowB : GroupRow) (LB : GroupLayout) (SB : Statement)
    (hbB : First.Close.bat t0.st t0.g eB (noDigest r0) = .ok (rowB, LB, SB))
    (hmask : t0.mask = none) :
    aloneAt p { t0 with st := SB, pass := .claim rowB LB } = some true := by
  obtain ⟨a, rest, D, e1, hD, hin⟩ :=
    step_plain p he t0 tE F n r0 rs' cols hp hstep eB rowB LB SB hbB
  have hb := own_below p _ a LB D hD hmask hin
  unfold aloneAt plainAt
  rw [e1]
  dsimp only
  rw [hD]
  simp only [Option.map_some, Option.some.injEq]
  unfold aloneOk
  rw [List.all_eq_true]
  intro m hm
  have := hb m hm
  simp only [bne_iff_ne, ne_eq]
  omega

end H2K.JointK

#print axioms H2K.JointK.lastOk_of_step
#print axioms H2K.JointK.aloneAt_of_step
