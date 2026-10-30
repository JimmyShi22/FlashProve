-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/OwnSitsLast.lean: no soundness is claimed.
The test ownSitsB V (Johnson/Desc/Last/OwnSits.lean: the own group that the first chain hands on has just two members, the index masks' message and W, at the plan's places and with the plan's shapes) at the first chain's last reached state: the join. By position, not by a relation that every sub-protocol keeps: the last two steps of the fold are W's sending (with the own group and the row (Eval) behind it) and the seal.
  atM4_two          an accept of the sub-protocol at W's sending is an accept at two rounds (the cut is that of kind K13's files, inside atM4_roots, Johnson/Desc/K13/Law/RootsBehind.lean)
  group_there       behind that accept the own group is there
  FrontM4 idx s     what is asked of the state in front: one row lies on the table, all its mask entries are of the message idx, it has one; idx is there
  BehindM4 V idx s  what is asked of the state behind: the places of idx and of W in the book, and their shapes, are V's
  **ownSitsB_atM4** (a) the join at W's sending, in letters: the accept · no split's message · FrontM4 idx s · BehindM4 V idx s' ⇒ ownSitsB V s' = true (ownMembers_atM4_there and ownSitsB_of_members, Johnson/Desc/Last/ShapeOwnSitsEarned.lean)
  reach_two         Reach opened twice from behind (called by nothing here)
  HandsBack bs Rc   what is asked of a family of reached states: what is reached at border n + 1 comes by an accepting step of sub-protocol number n from something reached at border n · handsBack_reach (Reach, Johnson/Top/H0/Walk/Reach.lean, over the list itself) · step_of_below · **handsBack_below** (Reach over the sub-protocols with the test «every word is below the prime» in front: the wrapped family: what a run makes)
  **ownSitsB_last_of** (b) in the goals' scope, at the full size's numbers, general in the family: HandsBack c.blocksInOrder Rc · Rc 358 (z, s) ⇒ ownSitsB V s = true, by at_356 | at_357 (Johnson/IMR/LastFour.lean), under: no split's message at the seat's shape · FrontM4 at every state of the family at border 356 · BehindM4 at border 357.
  **ownSitsB_last**  the same at the wrapped family.
Left, by name. hsp : (K13.whereOf Z).lin.ownSplitNeeded = false (left to kind K13's files) · hF: FrontM4: FoldFacts' oneRow | pileMasks at border 356, and the table's «the index masks' message is there» · hB: BehindM4: FoldFacts' seatsCarried | msgShapes at border 357, at two tests on the plan that tie V to the listed seats and shapes, with «W's number is the count of messages in front» (w_fresh_atM4).
Does not show. Anything at a border in front of the last: there the test is true for nothing, but that wants «W's number is not laid yet», a fact on where the chain stands. Nothing at the small size's numbers (76 | 77). No member. Nothing on soundness.
-/
import Johnson.IMR.LastFour
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.Last.ShapeOwnSitsEarned
import Johnson.Desc.K13.Law.RootsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Last (OwnSeats ownSitsB ownMembers_atM4_there ownSitsB_of_members)
open VerifiableInference.Desc.K13.Law (OnLedger linAt)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

section
variable {Cl : Type} {P : K13.Where} {P' : K1.Par} {s s' : S} {rs : List Fmt.RoundView}
  {gs : List (List (Nat × List UInt64))}

/-- An accept of the sub-protocol at W's sending is an accept at two rounds. -/
theorem atM4_two (h : (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s rs gs = .ok s') :
    ∃ r₁ r₂, (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s' := by
  have h' : ((K1.sendAtS P' : Block S Cl).decide s (rs.take 2) _).bind (fun m =>
      (K13.rowsB (Cl := Cl) K13.atS P).decide m (rs.drop 2) _) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := K13.Law.ebind_ok.1 h'
  obtain ⟨r₁, r₂, e⟩ := K13.Law.sendAtS_two P' h1
  refine ⟨r₁, r₂, ?_⟩
  show ((K1.sendAtS P' : Block S Cl).decide s [r₁, r₂] _).bind (fun m =>
    (K13.rowsB (Cl := Cl) K13.atS P).decide m [] _) = .ok s'
  rw [← e, h1]
  exact h2

/-- Behind that accept the own group is there. -/
theorem group_there {r₁ r₂ : Fmt.RoundView}
    (h : (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') :
    ∀ l, linAt s' = some l → (s'.st.groups[l.own]?).isSome = true := by
  obtain ⟨s₁, g₁, rs₂, g₂, -, h2⟩ := K13.Law.atM4_mid h
  obtain ⟨m₀, l₀, o, owed, -, -, hrows, rfl⟩ := K13.Law.rowsB_at h2
  obtain ⟨d₃, row, G, -, -, -, hG, -, hst, -⟩ := K13.Law.rows_ok hrows
  intro l hl
  obtain rfl : o.1 = l := Option.some.inj hl
  obtain ⟨G', hG', -⟩ := K13.Law.mem_withRow row hG
  show (o.2.st.groups[o.1.own]?).isSome = true
  rw [hst, hG']
  rfl

end

/-- **What is asked of the state in front of W's sending.** -/
structure FrontM4 (idx : ℕ) (s : S) : Prop where
  row : ∃ r, s.rows = [r] ∧ OnLedger idx r ∧ r.masks ≠ []
  there : idx < s.st.oracles.size

/-- **What is asked of the state behind it.** -/
structure BehindM4 (V : OwnSeats) (idx : ℕ) (s : S) : Prop where
  pI : s.book.place[idx]? = some V.index
  pW : ∀ l, linAt s = some l → s.book.place[l.w]? = some V.w
  sI : (s.st.oracles[idx]?).map (·.shape) = some V.indexShape
  sW : ∀ l, linAt s = some l → (s.st.oracles[l.w]?).map (·.shape) = some V.wShape

/-- **(a) The join at W's sending.** -/
theorem ownSitsB_atM4 {Cl : Type} {P : K13.Where} {P' : K1.Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Cl) P (K1.sendAtS P')).decide s rs gs = .ok s')
    (hsp : P.lin.ownSplitNeeded = false) {V : OwnSeats} {idx : ℕ} (F : FrontM4 idx s)
    (B : BehindM4 V idx s') : ownSitsB V s' = true := by
  obtain ⟨r₁, r₂, h2⟩ := atM4_two h
  obtain ⟨r, hr, hon, hne⟩ := F.row
  exact ownSitsB_of_members (group_there h2)
    (ownMembers_atM4_there h2 hsp hr hon hne F.there) B.pI B.pW B.sI B.sW

/-- `Reach`, opened twice from behind. -/
theorem reach_two {T Cl Pp : Type} {ft : ℕ} {bs : List (Block T Cl)} {start : Pp → T} {n : ℕ}
    {z : Pp} {s : T} (h : Reach ft bs start (n + 2) (z, s)) :
    ∃ s₁ s₂ b₁ b₂, Reach ft bs start n (z, s₁) ∧ Reach ft bs start (n + 1) (z, s₂) ∧
      bs[n]? = some b₁ ∧ bs[n + 1]? = some b₂ ∧ StepYes ft b₁ s₁ s₂ ∧ StepYes ft b₂ s₂ s := by
  cases h with
  | succ h2 hb2 hy2 =>
    cases h2 with
    | succ h1 hb1 hy1 => exact ⟨_, _, _, _, h1, .succ h1 hb1 hy1, hb1, hb2, hy1, hy2⟩

/-- **What is asked of a family of reached states**: whatever is reached at border n + 1 comes, by an
accepting step of the sub-protocol number n of the list, from something reached at border n. -/
def HandsBack {T Cl Pp : Type} (bs : List (Block T Cl)) (Rc : ℕ → Pp × T → Prop) : Prop :=
  ∀ (n : ℕ) (z : Pp) (s : T), Rc (n + 1) (z, s) → ∃ (s₀ : T) (b : Block T Cl) (ft : ℕ)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (m : ℕ), Rc n (z, s₀) ∧ bs[n]? = some b ∧
      b.step ft s₀ rs cols = .ok (s, m)

/-- `Reach` over the list itself hands back. -/
theorem handsBack_reach {T Cl Pp : Type} (ft : ℕ) (bs : List (Block T Cl)) (start : Pp → T) :
    HandsBack bs (Reach ft bs start) := by
  intro n z s h
  cases h with
  | succ h1 hb hy =>
    obtain ⟨R, c, -, y⟩ := hy
    exact ⟨_, _, ft, R, c, _, h1, hb, y⟩

/-- An accepting step of a sub-protocol with the test "every word is below the prime" in front is
an accepting step of the sub-protocol. -/
theorem step_of_below {T Cl : Type} {ft : ℕ} {b : Block T Cl} {s s' : T} {R : List Fmt.RoundView}
    {c : List OpenedColumn} {k : ℕ} (h : (Sound.below b).step ft s R c = .ok (s', k)) :
    b.step ft s R c = .ok (s', k) := by
  obtain ⟨h1, h2, h3, h4⟩ := (Sound.step_ok_iff ft _ s s' R c k).1 h
  refine (Sound.step_ok_iff ft b s s' R c k).2 ⟨h1, h2, h3, ?_⟩
  have h5 := h4
  unfold Sound.below at h5
  dsimp only at h5
  split at h5
  · exact h5
  · cases h5

/-- **The wrapped family**: `Reach` over the sub-protocols with that test in front hands back over
the list itself. -/
theorem handsBack_below {T Cl Pp : Type} (ft : ℕ) (bs : List (Block T Cl)) (start : Pp → T) :
    HandsBack bs (Reach ft (bs.map Sound.below) start) := by
  intro n z s h
  cases h with
  | succ h1 hb hy =>
    obtain ⟨R, c, -, y⟩ := hy
    rw [List.getElem?_map] at hb
    obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1 hb
    exact ⟨_, b, ft, R, c, _, h1, hb', step_of_below y⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **(b) At the first chain's last reached state, in the goals' scope, at the full size's numbers:
GENERAL IN THE FAMILY OF REACHED STATES.** -/
theorem ownSitsB_last_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pp : Type}
    {Rc : ℕ → Pp × S → Prop} (hb : HandsBack c.blocksInOrder Rc) {z : Pp} {s : S} (h : Rc 358 (z, s))
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) {V : OwnSeats} {idx : ℕ}
    (hF : ∀ s₁, Rc 356 (z, s₁) → FrontM4 idx s₁) (hB : ∀ s₂, Rc 357 (z, s₂) → BehindM4 V idx s₂) :
    ownSitsB V s = true := by
  obtain ⟨s₂, b₂, f2, R2, c2, m2, r2, hb2, y2⟩ := hb 357 z s h
  obtain ⟨s₁, b₁, f1, R1, c1, m1, r1, hb1, y1⟩ := hb 356 z s₂ r2
  obtain ⟨w, hw, ⟨rs', gs, hd⟩, -, -⟩ := IM.at_356 hS hR O hb1 y1
  obtain rfl : s = s₂ := IM.at_357 hS hR O hb2 y2
  obtain ⟨msg, -, rfl⟩ := (K13.Law.wAt_is _ _ _ w).1 hw
  exact ownSitsB_atM4 hd hsp (hF _ r1) (hB _ r2)

/-- At the wrapped family: what a run makes. -/
theorem ownSitsB_last (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pp : Type} {ft : ℕ}
    {start : Pp → S} {z : Pp} {s : S}
    (h : Reach ft (c.blocksInOrder.map Sound.below) start 358 (z, s))
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) {V : OwnSeats} {idx : ℕ}
    (hF : ∀ s₁, Reach ft (c.blocksInOrder.map Sound.below) start 356 (z, s₁) → FrontM4 idx s₁)
    (hB : ∀ s₂, Reach ft (c.blocksInOrder.map Sound.below) start 357 (z, s₂) → BehindM4 V idx s₂) :
    ownSitsB V s = true :=
  ownSitsB_last_of hS hR O (handsBack_below ft c.blocksInOrder start) h hsp hF hB

end

end ToldDesc

#print axioms ToldDesc.ownSitsB_last
#print axioms ToldDesc.ownSitsB_last_of
#print axioms ToldDesc.handsBack_reach
#print axioms ToldDesc.handsBack_below
#print axioms ToldDesc.step_of_below
#print axioms ToldDesc.atM4_two
#print axioms ToldDesc.group_there
#print axioms ToldDesc.ownSitsB_atM4
#print axioms ToldDesc.reach_two
