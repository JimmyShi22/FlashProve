-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/UnheardAt.lean: IN FRONT OF THE LOOKUP ON THE CALLS THE LINK's OWN
PART OF THE STATE IS FRESH: at the cut 14 l + 3 of every link l < 24: at the proof file's seat, in
the goals' scope, from the fold's return alone. "The state": the verifier's state, the value that
the fold of the IOP as written in Lean carries from sub-protocol to sub-protocol. "The cut k": the
state behind the flat list's first k entries.
WHY IT HOLDS: the link's own part (S.here = .lay a or .att a) is laid by the frames' "opened", which
is joined behind the link's first sub-protocol in one entry of the flat list (number 14 l + 2); it
ends in S.enterLay? or S.enterAtt?, which lay L, F and tl (and, at an attention link, two defaults)
and leave every other field at its default none. The cut 14 l + 3 is that entry's own return: no
sub-protocol stands between.
  FreshLay a, FreshAtt a: every field of the part that has the default none is none.
  enterLay_fresh, enterAtt_fresh; framesOf_fresh: every link's "opened" lays a fresh part, or (the
    head's) hands the state back.
  unheard_at: THE TOP. own_none_at, heard5_none_at: in the letters of the item "callerIn"'s two
    texts: a.own.isNone, a.heard5.isNone.
NOT HERE: which links are layers' and which attention's. The other halves of "callerIn" (the
ledger's next free slot; that the lookup's return is held). The head's link.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: the lookups' files.
Every theorem on states starts from the premise that a fold returns; no proof file is exhibited for
which one does. No soundness.
-/
import Johnson.IMR.FrameEntry
import Johnson.Top.H0.Walk.FrameProps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

/-- Nothing is heard yet in a layers' link's own part. -/
def FreshLay (a : LayOwn) : Prop := a.fo = none ∧ a.own = none ∧ a.lookHeard = none

/-- Nothing is heard yet in an attention link's own part. -/
def FreshAtt (a : AttOwn) : Prop :=
  a.g = none ∧ a.planes = none ∧ a.scores = none ∧ a.t = none ∧ a.lookHeard = none ∧
    a.heard5 = none

theorem enterLay_fresh {s t : S} {L : LinkCtx} {F : Fork} {tl : HTailF2}
    (hB : s.atBetween = true) (h : S.enterLay? s L F tl = .ok t) :
    ∃ a, t.here = .lay a ∧ FreshLay a := by
  have e := ((S.unmarked_ok _ _).1 h).1
  unfold S.enterLay at e
  rw [if_pos hB] at e
  exact ⟨_, by rw [← e], rfl, rfl, rfl⟩

theorem enterAtt_fresh {s t : S} {L : LinkCtx} {F : Fork} {tl : HTailF2}
    (hB : s.atBetween = true) (h : S.enterAtt? s L F tl = .ok t) :
    ∃ a, t.here = .att a ∧ FreshAtt a := by
  have e := ((S.unmarked_ok _ _).1 h).1
  unfold S.enterAtt at e
  rw [if_pos hB] at e
  exact ⟨_, by rw [← e], rfl, rfl, rfl, rfl, rfl, rfl⟩

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- Every link's "opened" lays a fresh part; the head's hands the state back. -/
theorem framesOf_fresh {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs, ∀ s t,
    f.opened s = .ok t →
    (∃ a, t.here = .lay a ∧ FreshLay a) ∨ (∃ a, t.here = .att a ∧ FreshAtt a) ∨ t = s := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      intro s t k
      exact Or.inr (Or.inr (Except.ok.inj k).symm)
  · split at e
    · split at e
      · cases e
      · cases e
        intro s t k
        obtain ⟨hB, -, a, -, k'⟩ := Props.openLayZero_iff.1 k
        exact Or.inl (enterLay_fresh (s := { s with out := a.out }) hB k')
    · split at e
      · cases e
      · cases e
        intro s t k
        obtain ⟨hB, -, a, -, k'⟩ := Props.openAtt_iff.1 k
        exact Or.inr (Or.inl (enterAtt_fresh (s := { s with out := a.out }) hB k'))
      · cases e
        intro s t k
        obtain ⟨hB, -, a, -, k'⟩ := Props.openLay_iff.1 k
        exact Or.inl (enterLay_fresh (s := { s with out := a.out }) hB k')

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN FRONT OF THE LOOKUP ON THE CALLS OF LINK l < 24 THE LINK's OWN PART IS FRESH.** -/
theorem unheard_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    (∃ a, t₁.here = .lay a ∧ FreshLay a) ∨ (∃ a, t₁.here = .att a ∧ FreshAtt a) := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
  obtain ⟨L, hL, -, -⟩ := entry_group hS hR O h24 f₀ f₁
  obtain ⟨hB, -⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have fin : ∀ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
      (fr : Johnson.Desc.First.Walk.Seat.LinkFrame) (m : S) {built : Array Stages.LinkH}
      {first : Params.First} {W : Verify.Public},
      Johnson.Desc.First.Walk.Seat.framesOf built first W = .ok fs → fr ∈ fs →
      fr.opened m = .ok t₁ → m.atBetween = true →
      (∃ a, t₁.here = .lay a ∧ FreshLay a) ∨ (∃ a, t₁.here = .att a ∧ FreshAtt a) := by
    intro fs fr m built first W hfs hf y3 mB
    rcases framesOf_fresh hfs fr hf m t₁ y3 with k | k | k
    · exact Or.inl k
    · exact Or.inr k
    · rw [k, link_between mB] at hL
      cases hL
  by_cases h0 : l = 0
  · subst h0
    have e0s := laid_is_start hS hR O f₀
    obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
    have i0 : c.blocksInOrder[14 * 0 + 2]? = some b := by
      have k := IM.hear_at_flat eLk e0
      rwa [(IM.flatIx_scope hS hR O (by omega : 0 ≤ 24) 0).trans
        (by omega : 14 * 0 + 0 + 2 = 14 * 0 + 2)] at k
    obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
    obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
    revert y1
    generalize rs.take _ = rs'
    generalize gs.take _ = gs'
    intro y1
    have y' : (K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Unit).decide t₀ rs' gs' = .ok m := y1
    have hR0 : t₀.roots = t₀.book.trees.size := by
      rw [e0s, (start_empty O.pub p).1, (start_empty O.pub p).2]
      rfl
    have hK : t₀.check.frame.keptBefore = #[] := by
      rw [e0s]
      exact start_kept O.pub p
    obtain ⟨-, mB⟩ := opening_lists y' hB hR0 hK
    exact fin fs fr m hfs (List.mem_of_getElem? hf) y3 mB
  · obtain ⟨Lk, b, x0, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O l (by omega) h24
    have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
      have k := IM.hear_at_flat eLk e0
      rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
        (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at k
    obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
    obtain ⟨fs, fr, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
    revert y1
    generalize rs.take _ = rs'
    generalize gs.take _ = gs'
    intro y1
    have y1' : x0.decide t₀ rs' gs' = .ok m := y1
    exact fin fs fr m hfs (List.mem_of_getElem? hf) y3 (switch_between hx y1' hB)

/-- In the letters of the item "callerIn" at a layers' link. -/
theorem own_none_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∀ a, t₁.here = .lay a → a.own.isNone = true := by
  intro a ha
  rcases unheard_at hS hR O h24 f₁ with ⟨a', ha', k⟩ | ⟨a', ha', -⟩
  · rw [ha] at ha'
    injection ha' with e
    rw [e, k.2.1]
    rfl
  · rw [ha] at ha'
    cases ha'

/-- In the letters of the item "callerIn" at an attention link. -/
theorem heard5_none_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∀ a, t₁.here = .att a → a.heard5.isNone = true := by
  intro a ha
  rcases unheard_at hS hR O h24 f₁ with ⟨a', ha', -⟩ | ⟨a', ha', k⟩
  · rw [ha] at ha'
    cases ha'
  · rw [ha] at ha'
    injection ha' with e
    rw [e, k.2.2.2.2.2]
    rfl

end

#print axioms framesOf_fresh
#print axioms unheard_at
#print axioms own_none_at
#print axioms heard5_none_at

end Meaning.K2
