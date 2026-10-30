-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/RunStays.lean: code switching (the kind K2): NO CALL OF THE SWITCH's TEXT
BEGINS A GROUP's PROXIMITY TEST: at every number the flag «the test has begun» (Group.inRun) is
behind an accept what it was at the front. NO BLOCK IMPORTS THIS FILE.
  RS S S'          at every number the same flag
  RS.refl | trans · rs_of_groups · join_rs · joins_rs · ledger_rs · rows_rs   call by call
  switch_rs        an accept of the switch itself: RS x.st w.st
  behind_rs        the link's own messages' joins behind it: RS
  yes_rs           an accept of the decision, at each of the three sorts of place: RS x.st s'.st,
                   x the front
For the table of joints' fixed test on the groups' lists of open rows, which asks that the test
has not begun. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.Whole
import Johnson.Top.H0.Tw.K2C.FrontGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut closeLedgerG joinG addRowsG dOf switchE switchBehind sendByL8
  firstBehind)
open VerifiableInference.Desc.Ground (joinP addRowsP)

/-- At every number the same flag «the proximity test has begun». -/
def RS (S S' : Statement) : Prop :=
  ∀ g : Nat, (S'.groups[g]?).map (·.inRun) = (S.groups[g]?).map (·.inRun)

theorem RS.refl (S : Statement) : RS S S := fun _ => rfl

theorem RS.trans {S S₁ S₂ : Statement} (a : RS S S₁) (b : RS S₁ S₂) : RS S S₂ :=
  fun g => (b g).trans (a g)

theorem rs_of_groups {S S' : Statement} (h : S'.groups = S.groups) : RS S S' := by
  intro g
  rw [h]

theorem join_rs {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g o kept = .ok S') :
    RS S S' := by
  intro i
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    unfold joinP at hd
    split at hd
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 hd
      show ((OnBytes.Slice.withMessageInGroup S g o kept G).groups[i]?).map (·.inRun) = _
      unfold OnBytes.Slice.withMessageInGroup
      simp only [Array.getElem?_modify]
      split
      · rw [Option.map_map]
        rfl
      · rfl
    · cases hd
  · cases h

theorem joins_rs {α : Type} (g : Nat) (f : α → Nat) (k : α → Bool) : ∀ (l : List α)
    (S S' : Statement), l.foldlM (fun S p => joinG S g (f p) (k p)) S = .ok S' → RS S S'
  | [], S, S', h => by
    cases h
    exact RS.refl S
  | p :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bindOk h
    exact (join_rs h1).trans (joins_rs g f k l S1 S' h2)

theorem ledger_rs {S S' : Statement} {o : Nat} (h : closeLedgerG S o = .ok S') : RS S S' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at hd
    split at hd
    · cases hd
      exact RS.refl _
    · cases hd
  · cases h

theorem withRows_rs (g : Nat) : ∀ (l : List OnBytes.Row) (S : Statement),
    RS S (OnBytes.Slice.withRows S g l)
  | [], S => RS.refl S
  | r :: l, S => by
    have a : RS S (OnBytes.Slice.withRow S g r) := by
      intro i
      unfold OnBytes.Slice.withRow
      simp only [Array.getElem?_modify]
      split
      · rw [Option.map_map]
        rfl
      · rfl
    exact a.trans (withRows_rs g l _)

theorem rows_rs {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG S g rows = .ok S') : RS S S' := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    unfold addRowsP at hd
    split at hd
    · rw [from_rows g rows _ d hd]
      exact withRows_rs g rows _
    · cases hd
  · cases h

theorem switch_rs {P : _root_.Tw.K2.Par9} {s9 : _root_.Tw.K2.S9} {x : _root_.Tw.K2.Front}
    {r₁ r₂ : Fmt.RoundView} {cols : List _root_.Tw.K2.Col} {w : SwOut} {roots : Nat}
    (hw : switchE switchBehind P sendByL8 s9 x r₁ r₂ cols = .ok (w, roots)) : RS x.st w.st := by
  obtain ⟨y, k⟩ := switchE_inv hw
  obtain ⟨c, Y, S1, S2, S3, rows, hB⟩ := switchBehind_inv k.hBehind
  have g0 : RS x.st y.st := rs_of_groups (sent_ok k.hSend).groups
  have g1 : RS y.st S1 := by
    have h := hB.hLedger
    split at h
    · exact ledger_rs h
    · cases h
      exact RS.refl _
  have g3 : RS S2 S3 := by
    have h := hB.hJoinKept
    rw [← Array.foldlM_toList] at h
    exact joins_rs _ (fun p : Nat × KeptTarget => p.1) (fun p => p.2.keptAgain) _ S2 S3 h
  exact (((g0.trans g1).trans (join_rs hB.hJoinG)).trans g3).trans (rows_rs hB.hAdded)

theorem behind_rs {S S' : Statement} {x : _root_.Tw.K2.Front} {o : Switched} {plain : List E}
    {f : ReqFrame} {mine : Array Nat} (h : firstBehind S x o plain = .ok (S', f, mine)) :
    RS S S' := by
  obtain ⟨mask, bA⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 h
  exact joins_rs x.f.group (fun y : Params.ReqMessage × Nat => y.2)
    (fun y => decide (0 < y.1.life)) _ S S' bA.joins

/-- **An accept of the decision.** -/
theorem yes_rs {p : P2} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ x : _root_.Tw.K2.Front, frontAt p s = some x ∧ RS x.st s'.st := by
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    refine ⟨x, ?_, ?_⟩
    · unfold frontAt
      rw [hp]
      simp only
      rw [k.hFront]
      rfl
    · rw [k.hOut]
      exact (switch_rs k.hSwitch).trans (behind_rs k.hBehind)
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    refine ⟨headFrontOf s a G.target, ?_, ?_⟩
    · unfold frontAt
      rw [hp, k.hHere]
      simp only
      rw [k.hGroup]
      rfl
    · rw [k.hOut]
      exact switch_rs k.hSwitch
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    refine ⟨finFrontOf s a G, ?_, ?_⟩
    · unfold frontAt
      rw [hp, k.hHere]
      simp only
      rw [k.hLaid]
      rfl
    · rw [k.hOut]
      exact switch_rs k.hSwitch

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.switch_rs
#print axioms VerifiableInference.Desc.First.K2.yes_rs
