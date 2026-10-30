-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/RoomFold.lean:
THE FACT ALONG THE FOLD THAT TAKES THE PLACE OF THE PUBLIC ITEM "pile.room": at every
state that the proof file's first chain's sub-protocols hand on, from behind link 0's first one to
in front of the chain's batching at its end, THE INDEX-MASK MESSAGE's LEDGER IS THERE, IS NOT
CLOSED, AND HAS JUST free0 ENTRIES LESS THE PENDING ROWS LAID SO FAR. A FORM WITH ITS DEBTS COUNTED.
THE INVARIANT HAS A SECOND CLAUSE: THE INDEX-MASK MESSAGE IS A MEMBER OF NO GROUP. Why: a link's
closing begins the proximity test on the link's group and closes the ledger of every member
(begun, OnBytes/Slice/BlkBegin.lean); it does not read which message the index masks' is. Without
the second clause the keeping could not be paid at a closing's number.

  bearing l, isTake k, isOurs k, takenAt k   which links leave a row; at which numbers an entry is
                    taken; which numbers are the frame's "laid" and "cleared"; how many entries are
                    taken in front of border k: tests and numbers with code
  taken_step_full, taken_three   takenAt steps by one just at a take; it is 0 at border 3: by Lean's
                    kernel
  outOfGroupsB s    the second clause, a test with code; outOfGroupsB_iff: what it says
  take_at           PAID: at the thirteen takes: one entry less (cleared_leftIs, FrameEntries.lean)
  keep_ours         PAID: at the frame's other 37 numbers the ledger is as it was
  ours_out          PAID: at the frame's fifty numbers the second clause is handed on
  reach_two         at border 2 the reached state is the first state itself
  opened_makes, make_at   THE MAKE, OUR HALF: "link 0: opened" leaves the statement and lays the
                    message's number: so the make at number 2 is cut down to a sentence on the
                    sending in front: "the message that the frame's test finds has the fresh ledger"
  opened_makes_out, make_out_at   the like for the second clause: "... is a member of no group"
  RoomOwes          WHAT IS LEFT: the make, at number 2; the keeping at the numbers of other kinds:
                    both clauses; the keeping has "reached" and both clauses in hand
  room_both         the invariant, both clauses
  room_at_reach     THE FACT: Reach 0 c.blocksInOrder start k (z, s) -> 3 <= k -> k <= 355 ->
                    leftIsB (free0 - takenAt k) s = true
  room_out_of_groups   the second clause at the same states
  roomPlacesB_full, room_places, rowsBefore_scope, room_field   THE FIELD "room" OF FoldFacts
                    (Johnson/Desc/First/FoldFacts.lean), in that structure's own letters: in front
                    of a sub-protocol of segment m behind its first: roomIsB free0 fvs m

Limits. RoomOwes is shown at nothing here. In the goals' scope, where every sub-protocol of the flat
list passes its test on the plan. No soundness statement.

-/
import Johnson.P1L20R.FrameFold
import Johnson.Top.H0.Walk.FrameEntries
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open Johnson.Desc.First.Walk (layFront clearWith)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- Link l leaves a row. -/
def bearing (l : ℕ) : Bool := decide (IM.subAt l ≠ ModelPart.attention)

/-- At number k an entry is taken. -/
def isTake (k : ℕ) : Bool := (List.range 25).any fun l => bearing l && clearIx l == k

/-- Number k is the frame's "laid" or "cleared". -/
def isOurs (k : ℕ) : Bool := (List.range 25).any fun l => 14 * l + 1 == k || clearIx l == k

/-- How many entries are taken in front of border k. -/
def takenAt (k : ℕ) : ℕ :=
  ((List.range 25).filter fun l => bearing l && decide (clearIx l < k)).length

set_option maxRecDepth 1000000 in
theorem taken_step_full : ((List.range 356).all fun k =>
    takenAt (k + 1) == takenAt k + (if isTake k then 1 else 0)) = true := by decide +kernel

theorem taken_step {k : ℕ} (hk : k < 356) :
    takenAt (k + 1) = takenAt k + (if isTake k then 1 else 0) :=
  eq_of_beq (List.all_eq_true.1 taken_step_full k (List.mem_range.2 hk))

theorem taken_three : takenAt 3 = 0 := by decide +kernel

theorem leftIsB_of_ledger {n : ℕ} {s s' : S}
    (h : Johnson.Desc.First.Walk.Law.ledgerAt s' = Johnson.Desc.First.Walk.Law.ledgerAt s) :
    leftIsB n s' = leftIsB n s := by
  unfold leftIsB
  rw [h]

/-- **The second clause: the index-mask message is a member of no group.** A test with code. -/
def outOfGroupsB (s : S) : Bool := s.st.groups.all fun G => !G.members.contains s.out.indexMasks

theorem outOfGroupsB_iff {s : S} :
    outOfGroupsB s = true ↔ ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members := by
  unfold outOfGroupsB
  rw [Array.all_eq_true_iff_forall_mem]
  refine forall₂_congr fun G _ => ?_
  simp

theorem outOfGroupsB_same {s t : S} (h1 : t.st.groups = s.st.groups)
    (h2 : t.out.indexMasks = s.out.indexMasks) : outOfGroupsB t = outOfGroupsB s := by
  unfold outOfGroupsB
  rw [h1, h2]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- What "cleared" at link l is, with the flag by the link's sort. -/
theorem clear_by_sort (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {b : Block S Cl}
    (hb : c.blocksInOrder[clearIx l]? = some b) {s s' : S} (hy : StepYes 0 b s s') :
    ∃ X counts left, X.fv = bearing l ∧
      clearWith X counts left (Johnson.Desc.First.Walk.Seat.rowOf Z.p.X Z.first) s = .ok s' := by
  obtain ⟨fs, hfs, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨f, _, _, _, _, _, bC, hf, _, _, _, _, _, _, _, _, _, _, _, iC, yC⟩ := hh l hl
  obtain rfl : bC = b := Option.some.inj (iC.symm.trans hb)
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  have h1 := yC s rs gs s' e
  obtain ⟨X, counts, left, X', e1, hX', hkk, _, _, hflag⟩ :=
    clear_with_flag hfs hf (plans_hold hS hR O hp hfs hl hf)
  rw [e1] at h1
  refine ⟨X, counts, left, ?_, h1⟩
  have hsub := kind_of_sort hS hR O hl hX'
  unfold bearing
  rcases hflag with ⟨g1, g2⟩ | ⟨g1, g2, _⟩
  · rw [hkk] at g1
    rw [g1] at hsub
    rw [g2, ← hsub]
    decide
  · rw [hkk] at g1
    rw [g2]
    have : IM.subAt l ≠ ModelPart.attention := by
      rw [← hsub]
      unfold ProofFile.subOf
      by_cases h0 : X'.kind = 0
      · simp [h0]
      · simp [h0, g1]
    simp [this]

/-- **PAID: at a take: one entry less.** -/
theorem take_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} (hk : isTake k = true) {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) {s s' : S} (hy : StepYes 0 b s s') {n : ℕ}
    (hn : leftIsB n s = true) : leftIsB (n - 1) s' = true := by
  unfold isTake at hk
  obtain ⟨l, hl, h2⟩ := List.any_eq_true.1 hk
  rw [Bool.and_eq_true] at h2
  obtain rfl : clearIx l = k := eq_of_beq h2.2
  obtain ⟨X, counts, left, hv, h1⟩ := clear_by_sort hS hR O hp (List.mem_range.1 hl) hb hy
  exact (cleared_leftIs h1 (hv.trans h2.1) hn).2

/-- **PAID: at the frame's other numbers the ledger is as it was.** -/
theorem keep_ours (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} (hk : isOurs k = true) (ht : isTake k = false)
    {b : Block S Cl} (hb : c.blocksInOrder[k]? = some b) {s s' : S} (hy : StepYes 0 b s s') {n : ℕ} :
    leftIsB n s' = leftIsB n s := by
  unfold isOurs at hk
  obtain ⟨l, hl, h2⟩ := List.any_eq_true.1 hk
  have hl' := List.mem_range.1 hl
  rw [Bool.or_eq_true] at h2
  rcases h2 with h3 | h3
  · obtain rfl : 14 * l + 1 = k := eq_of_beq h3
    obtain ⟨fs, _, hh⟩ := IM.frames_sit hS hR O
    obtain ⟨f, _, _, bL, _, _, _, _, hlay, iL, yL, _⟩ := hh l hl'
    obtain rfl : bL = b := Option.some.inj (iL.symm.trans hb)
    obtain ⟨rs, gs, e⟩ := stepYes_decide hy
    have h1 := yL s rs gs s' e
    rw [hlay] at h1
    rw [(Johnson.Desc.First.Walk.Law.layFront_ok h1).1]
  · obtain rfl : clearIx l = k := eq_of_beq h3
    obtain ⟨X, counts, left, hv, h1⟩ := clear_by_sort hS hR O hp hl' hb hy
    have hb0 : bearing l = false := by
      cases hbl : bearing l with
      | false => rfl
      | true =>
        have : isTake (clearIx l) = true := by
          unfold isTake
          exact List.any_eq_true.2 ⟨l, hl, by rw [hbl]; simp⟩
        rw [this] at ht
        cases ht
    exact cleared_leftIs_none h1 (hv.trans hb0)

/-- **PAID: at the frame's fifty numbers the second clause is handed on.** -/
theorem ours_out (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} (hk : isOurs k = true)
    {b : Block S Cl} (hb : c.blocksInOrder[k]? = some b) {s s' : S} (hy : StepYes 0 b s s') :
    outOfGroupsB s' = outOfGroupsB s := by
  unfold isOurs at hk
  obtain ⟨l, hl, h2⟩ := List.any_eq_true.1 hk
  have hl' := List.mem_range.1 hl
  rw [Bool.or_eq_true] at h2
  rcases h2 with h3 | h3
  · obtain rfl : 14 * l + 1 = k := eq_of_beq h3
    obtain ⟨fs, _, hh⟩ := IM.frames_sit hS hR O
    obtain ⟨f, _, _, bL, _, _, _, _, hlay, iL, yL, _⟩ := hh l hl'
    obtain rfl : bL = b := Option.some.inj (iL.symm.trans hb)
    obtain ⟨rs, gs, e⟩ := stepYes_decide hy
    have h1 := yL s rs gs s' e
    rw [hlay] at h1
    rw [(Johnson.Desc.First.Walk.Law.layFront_ok h1).1]
  · obtain rfl : clearIx l = k := eq_of_beq h3
    obtain ⟨X, counts, left, _, h1⟩ := clear_by_sort hS hR O hp hl' hb hy
    obtain ⟨_, _, _, _, _, _, _, _, _, hg, _, _, _, hi, _⟩ := clearedGives X counts left _ _ s s' h1
    exact outOfGroupsB_same hg hi

/-- **Half of the make**: "link 0: opened" leaves the statement and lays the index-mask message's
number: so where that message, behind the sending in front, has a ledger that is not closed with
just free0 entries left, the fact holds behind "opened". -/
theorem opened_makes {Q : Johnson.Desc.First.Walk.LayPar} {fvs : List Bool} {kCol : ℕ} {m u : S}
    (hy : Johnson.Desc.First.Walk.openLayZero Q fvs kCol m = .ok u) {free0 : ℕ}
    (hf : ∀ im, Johnson.Desc.First.Walk.Props.IndexMasksAt
        (Johnson.Desc.First.Walk.roomOf fvs kCol) m.check m.st.oracles im →
      ∃ l, (m.st.oracles[im]?).bind (·.ledger) = some l ∧ l.closed = false ∧ l.left = free0) :
    leftIsB free0 u = true := by
  obtain ⟨_, _, g3, ⟨im, hi, ho⟩, _⟩ := openedZeroGives Q fvs kCol m u hy
  obtain ⟨l, h1, h2, h3⟩ := hf im hi
  refine leftIsB_iff.2 ⟨l, ?_, h2, h3⟩
  show (u.st.oracles[u.out.indexMasks]?).bind (·.ledger) = some l
  rw [g3.2.2.1, ho]
  exact h1

/-- The like for the second clause: where that message, behind the sending in front, is a member of
no group, the second clause holds behind "opened". -/
theorem opened_makes_out {Q : Johnson.Desc.First.Walk.LayPar} {fvs : List Bool} {kCol : ℕ} {m u : S}
    (hy : Johnson.Desc.First.Walk.openLayZero Q fvs kCol m = .ok u)
    (hf : ∀ im, Johnson.Desc.First.Walk.Props.IndexMasksAt
        (Johnson.Desc.First.Walk.roomOf fvs kCol) m.check m.st.oracles im →
      ∀ G ∈ m.st.groups, im ∉ G.members) :
    outOfGroupsB u = true := by
  obtain ⟨_, _, g3, ⟨im, hi, ho⟩, _⟩ := openedZeroGives Q fvs kCol m u hy
  refine outOfGroupsB_iff.2 ?_
  rw [g3.2.2.1, ho]
  exact hf im hi

/-- **At border 2 the reached state is the first state itself**: the two sub-protocols in front (the
chain's idle front; "link 0: laid") hand the state on. -/
theorem reach_two (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Q : Type} {start : Q → S}
    {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start 2 (z, s)) : s = start z := by
  obtain ⟨b0, e0, _, _, _, _, hd⟩ := IM.front_of O
  obtain ⟨_, _, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨f, _, _, bL, _, _, _, _, hlay, iL, yL, _⟩ := hh 0 (by omega)
  cases h with
  | @succ _ _ s₁ _ b₁ h₁ hb₁ hy₁ =>
    cases h₁ with
    | @succ _ _ s₀ _ b₀ h₀ hb₀ hy₀ =>
      cases h₀
      obtain rfl : b0 = b₀ := Option.some.inj (e0.symm.trans hb₀)
      obtain rfl : bL = b₁ := Option.some.inj (iL.symm.trans hb₁)
      obtain ⟨rs, gs, e⟩ := stepYes_decide hy₀
      obtain rfl : s₁ = start z := (hd _ _ _ _).1 e
      obtain ⟨rs', gs', e'⟩ := stepYes_decide hy₁
      have h1 := yL _ rs' gs' s e'
      rw [hlay] at h1
      exact (Johnson.Desc.First.Walk.Law.layFront_ok h1).1

/-- **The make, at number 2**, cut down to a sentence on the sending in front of "opened": behind an
accepting step, FROM THE FIRST STATE, of link 0's first sub-protocol as its own lot's list has
it, the message that the frame's test on the index masks finds has the fresh ledger. -/
theorem make_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {free0 : ℕ} {s : S}
    (hK : ∀ (b' : Block S Cl) rs cols m n, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place.kind = VerifiableInference.Desc.KindName.K1 → b'.place.link = some 0 →
      b'.place.piece = 1 → b'.step 0 s rs cols = .ok (m, n) →
      ∀ room im, Johnson.Desc.First.Walk.Props.IndexMasksAt room m.check m.st.oracles im →
      ∃ l, (m.st.oracles[im]?).bind (·.ledger) = some l ∧ l.closed = false ∧ l.left = free0) :
    ∀ b s', c.blocksInOrder[2]? = some b → StepYes 0 b s s' → leftIsB free0 s' = true := by
  intro b s' hb hy
  obtain ⟨fs0, hfs0, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨_, _, kd, _, b0, b', _, _, _, _, _, _, _, ib, hkd, hlot, hpl, hj, _⟩ :=
    hh 0 (by omega)
  have hk1 : kd = VerifiableInference.Desc.KindName.K1 := by
    have e : (VerifiableInference.Desc.First.kindsBeforeBatching (IM.subAt 0) (0 == 0))[0]? =
        some VerifiableInference.Desc.KindName.K1 := by decide
    exact (Option.some.inj (e.symm.trans hkd)).symm
  obtain rfl : b0 = b := Option.some.inj (ib.symm.trans hb)
  obtain ⟨R, cc, _, e⟩ := hy
  obtain ⟨fs, f, m, hfs, hf, h3, _, h5, _⟩ := hj.step e
  rcases Johnson.Desc.First.Walk.Seat.framesOf_arms hfs hf with
    ⟨X, hX, hk, _⟩ | ⟨_, X, _, Q, _, _, _, _, _, e1, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
  · have e2 := kind_of_sort hS hR O (by omega) hX
    rw [hk] at e2
    exact absurd e2 (by decide)
  · rw [e1] at h5
    exact opened_makes h5 fun im hi =>
      hK b' R cc m cc.length hlot (by rw [hpl]; exact hk1) (by rw [hpl]) (by rw [hpl]) h3 _ im hi
  · exact absurd rfl h0
  · exact absurd rfl h0

/-- The like for the second clause, at number 2: behind an accepting step, from the first state, of
link 0's first sub-protocol as its own lot's list has it, the message that the frame's test on
the index masks finds is a member of no group. -/
theorem make_out_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hK : ∀ (b' : Block S Cl) rs cols m n, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place.kind = VerifiableInference.Desc.KindName.K1 → b'.place.link = some 0 →
      b'.place.piece = 1 → b'.step 0 s rs cols = .ok (m, n) →
      ∀ room im, Johnson.Desc.First.Walk.Props.IndexMasksAt room m.check m.st.oracles im →
      ∀ G ∈ m.st.groups, im ∉ G.members) :
    ∀ b s', c.blocksInOrder[2]? = some b → StepYes 0 b s s' → outOfGroupsB s' = true := by
  intro b s' hb hy
  obtain ⟨fs0, hfs0, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨_, _, kd, _, b0, b', _, _, _, _, _, _, _, ib, hkd, hlot, hpl, hj, _⟩ :=
    hh 0 (by omega)
  have hk1 : kd = VerifiableInference.Desc.KindName.K1 := by
    have e : (VerifiableInference.Desc.First.kindsBeforeBatching (IM.subAt 0) (0 == 0))[0]? =
        some VerifiableInference.Desc.KindName.K1 := by decide
    exact (Option.some.inj (e.symm.trans hkd)).symm
  obtain rfl : b0 = b := Option.some.inj (ib.symm.trans hb)
  obtain ⟨R, cc, _, e⟩ := hy
  obtain ⟨fs, f, m, hfs, hf, h3, _, h5, _⟩ := hj.step e
  rcases Johnson.Desc.First.Walk.Seat.framesOf_arms hfs hf with
    ⟨X, hX, hk, _⟩ | ⟨_, X, _, Q, _, _, _, _, _, e1, _⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
  · have e2 := kind_of_sort hS hR O (by omega) hX
    rw [hk] at e2
    exact absurd e2 (by decide)
  · rw [e1] at h5
    exact opened_makes_out h5 fun im hi =>
      hK b' R cc m cc.length hlot (by rw [hpl]; exact hk1) (by rw [hpl]) (by rw [hpl]) h3 _ im hi
  · exact absurd rfl h0
  · exact absurd rfl h0

/-- **What is left.** free0: the fresh ledger's free count. -/
structure RoomOwes {Q : Type} (c : Chain S Cl) (start : Q → S) (free0 : ℕ) : Prop where
  /-- the make: behind link 0's first sub-protocol, with "opened" joined behind it, FROM THE FIRST
  STATE (at every state in front it could not be paid): both clauses -/
  make : ∀ b z s', c.blocksInOrder[2]? = some b → StepYes 0 b (start z) s' →
    leftIsB free0 s' = true ∧ outOfGroupsB s' = true
  /-- the keeping, at the numbers of other kinds: AT A REACHED STATE at which both clauses hold
  (the count at any n): both are handed on. (The first clause is in hand for the second: whoever
  joins a fresh message to a group needs that the index masks' is there already.) -/
  keep : ∀ k, 3 ≤ k → k < 355 → isOurs k = false → ∀ b z s s', Reach 0 c.blocksInOrder start k (z, s) →
    c.blocksInOrder[k]? = some b → StepYes 0 b s s' → outOfGroupsB s = true →
    ∀ n, leftIsB n s = true → leftIsB n s' = true ∧ outOfGroupsB s' = true

/-- **The invariant along the fold, both clauses.** -/
theorem room_both (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {free0 : ℕ} {Q : Type} {start : Q → S}
    (H : RoomOwes c start free0) {k : ℕ} {a : Q × S} (h : Reach 0 c.blocksInOrder start k a) :
    3 ≤ k → k ≤ 355 → leftIsB (free0 - takenAt k) a.2 = true ∧ outOfGroupsB a.2 = true := by
  refine Reach.inv (Inv := fun k a => 3 ≤ k → k ≤ 355 →
      leftIsB (free0 - takenAt k) a.2 = true ∧ outOfGroupsB a.2 = true)
    (fun z h3 _ => absurd h3 (by omega)) (fun k z s s' b hr hb hy ih h3 h355 => ?_) h
  by_cases h2 : k = 2
  · subst h2
    show leftIsB (free0 - takenAt 3) s' = true ∧ outOfGroupsB s' = true
    rw [taken_three]
    obtain rfl := reach_two hS hR O hr
    exact H.make b z s' hb hy
  · obtain ⟨ih1, ih2⟩ := ih (by omega) (by omega)
    show leftIsB (free0 - takenAt (k + 1)) s' = true ∧ outOfGroupsB s' = true
    rw [taken_step (by omega)]
    cases ho : isOurs k with
    | true =>
      refine ⟨?_, by rw [ours_out hS hR O hp ho hb hy]; exact ih2⟩
      cases ht : isTake k with
      | true =>
        have := take_at hS hR O hp ht hb hy ih1
        simpa [Nat.sub_sub] using this
      | false =>
        simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        rw [keep_ours hS hR O hp ho ht hb hy]
        exact ih1
    | false =>
      have ht : isTake k = false := by
        cases ht : isTake k with
        | false => rfl
        | true =>
          unfold isTake at ht
          obtain ⟨l, hl, h4⟩ := List.any_eq_true.1 ht
          rw [Bool.and_eq_true] at h4
          have : isOurs k = true := by
            unfold isOurs
            exact List.any_eq_true.2 ⟨l, hl, by rw [h4.2]; simp⟩
          rw [this] at ho
          cases ho
      rw [ht]
      simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      exact H.keep k (by omega) (by omega) ho b z s s' hr hb hy ih2 _ ih1

/-- **THE FACT ALONG THE FOLD.** -/
theorem room_at_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {free0 : ℕ} {Q : Type} {start : Q → S}
    (H : RoomOwes c start free0) {k : ℕ} {a : Q × S} (h : Reach 0 c.blocksInOrder start k a)
    (h3 : 3 ≤ k) (h355 : k ≤ 355) : leftIsB (free0 - takenAt k) a.2 = true :=
  (room_both hS hR O hp H h h3 h355).1

/-- The second clause at the same states. -/
theorem room_out_of_groups (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {free0 : ℕ} {Q : Type} {start : Q → S}
    (H : RoomOwes c start free0) {k : ℕ} {a : Q × S} (h : Reach 0 c.blocksInOrder start k a)
    (h3 : 3 ≤ k) (h355 : k ≤ 355) : outOfGroupsB a.2 = true :=
  (room_both hS hR O hp H h h3 h355).2

/-! ### In the letters of the field "room" of FoldFacts -/

/-- The links' flags, written. -/
def bearingList : List Bool := (List.range 25).map bearing

/-- A test with code on the written list: in front of a sub-protocol of segment m behind its first,
the border's number lies in the fact's stretch, and as many entries are taken in front of it as
bearing segments stand in front of m. -/
def roomPlacesB : Bool :=
  (List.range 358).all fun k =>
    match (flatPlacesOf linksFull true)[k]? with
    | some p =>
      match p.link with
      | some m =>
        !decide (2 ≤ p.piece) ||
          (decide (3 ≤ k) && decide (k ≤ 355) && decide (m < 25) &&
            takenAt k == rowsBefore bearingList m)
      | none => true
    | none => true

set_option maxRecDepth 1000000 in
theorem roomPlacesB_full : roomPlacesB = true := by decide +kernel

theorem room_places {k m : ℕ} {p : VerifiableInference.Desc.Place}
    (hk : (flatPlacesOf linksFull true)[k]? = some p) (hm : p.link = some m) (h2 : 2 ≤ p.piece) :
    3 ≤ k ∧ k ≤ 355 ∧ m < 25 ∧ takenAt k = rowsBefore bearingList m := by
  have hlt : k < 358 := by
    rw [← places_length_full]
    exact (List.getElem?_eq_some_iff.1 hk).1
  have h := List.all_eq_true.1 roomPlacesB_full k (List.mem_range.2 hlt)
  simp only [hk, hm, h2, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem take_congr {α : Type} {l₁ l₂ : List α} {m : ℕ} (h : ∀ i, i < m → l₁[i]? = l₂[i]?) :
    l₁.take m = l₂.take m := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_take]
  split
  · exact h i ‹_›
  · rfl

/-- In scope the planner's flags count as the written ones do. -/
theorem rowsBefore_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {m : ℕ} (hm : m < 25) :
    rowsBefore (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) m =
      rowsBefore bearingList m := by
  unfold rowsBefore
  rw [take_congr (l₂ := bearingList) fun i hi => ?_]
  rw [fvs_bearing hS hR O hp (by omega : i < 25)]
  unfold bearingList
  rw [List.getElem?_map, List.getElem?_range (by omega : i < 25)]
  rfl

/-- **THE FIELD "room" OF FoldFacts** (Johnson/Desc/First/FoldFacts.lean), in the structure's own
letters, general in Rch and at_ with one premise hR, at the written list and at
d.fvs := the planner's flags. -/
theorem room_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {free0 : ℕ} {Q : Type} {start : Q → S}
    (H : RoomOwes c start free0) {X : Type} {Rch : ℕ → X → Prop} {at_ : X → Q × S}
    (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder start k (at_ a)) :
    ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf linksFull true)[k]? = some p → p.link = some m → 2 ≤ p.piece →
      roomIsB free0 (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) m (at_ a).2 = true := by
  intro k a p m hr _ hk hm h2
  obtain ⟨g1, g2, g3, g4⟩ := room_places hk hm h2
  unfold roomIsB
  rw [rowsBefore_scope hS hR O hp g3, ← g4]
  exact room_at_reach hS hR O hp H (hRch k a hr) g1 g2

end

end P1L20

#print axioms P1L20.roomPlacesB_full
#print axioms P1L20.room_field
#print axioms P1L20.taken_step_full
#print axioms P1L20.take_at
#print axioms P1L20.keep_ours
#print axioms P1L20.reach_two
#print axioms P1L20.make_at
#print axioms P1L20.room_at_reach
#print axioms P1L20.ours_out
#print axioms P1L20.make_out_at
#print axioms P1L20.room_both
#print axioms P1L20.room_out_of_groups
