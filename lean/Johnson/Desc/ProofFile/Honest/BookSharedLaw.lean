-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookSharedLaw.lean: at an owner in the shared chain the whole book's
entries are `sharedAhead`'s (Honest/BookShared.lean). Statements with their proofs. One
abbreviation.

  1  `spendingBook_ahead`   where `spendingBook` returns: of which five lists its entries are made
  2  `bookRaw_ahead`        where `bookRaw` returns: which makers have returned what, and of which
                           lists its entries are made
  3  `bookWhole_ahead_shared`   WHERE `bookWhole` RETURNS B: `sharedAhead` returns a list l, and at
                           every owner that stands at no place of the first or the second chain the
                           entries of B with that owner are those of l, in the same order

  4  `bookWhole_spent_known_shared`   so `ProverCoinCounts.spentBy` and `ProverCoinCounts.knownBy` (Honest/Frame.lean) at
                           such an owner are the same at the book whose entries are l

WHAT THEY ARE FOR. `ProverCoinCounts.spentBy` and `ProverCoinCounts.knownBy` at an owner read the entries of that owner
alone. So a test on the book at an owner in the shared chain that reads these two is a function of
the short list.

Limits.
  * That `bookWhole` returns is a premise.
  * That an owner stands at no place of the first or the second chain is the caller's to show: by
    the description's test on the places, or by evaluating two tests of membership.
  * Nothing is said of the book's tables of counts, nor of the order of places.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookShared
import Johnson.Desc.ProofFile.Honest.BookSharedKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared

variable {Xi : Type}

/-- The messages under a sending's label. -/
abbrev BookShared.under (ms : List SentMsg) (label : String) : List SentMsg :=
  ms.filter fun m => m.label == label

theorem spendingBook_ahead {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) :
    ∃ (ws : List Want) (f0 f1 f2 : List Ahead),
      (∀ w ∈ ws, w.msg.owner.place ∈ F.first.blocksInOrder.map (·.place)) ∧
      foldEntries (planOf F.first.blocksInOrder) (planOf F.second.blocksInOrder) p0 = .ok f0 ∧
      foldEntries (planOf F.shared.blocksInOrder) [] p1 = .ok f1 ∧
      foldEntries (planOf F.second.blocksInOrder) [] p2 = .ok f2 ∧
      B₀.ahead = ws.map (·.entry) ++ f0 ++ f1 ++ f2 ++ (splitEntry F.shared.blocksInOrder p1).toList := by
  unfold spendingBook at h
  obtain ⟨r0, -, h⟩ := ex_bind h
  obtain ⟨r1, -, h⟩ := ex_bind h
  obtain ⟨r2, -, h⟩ := ex_bind h
  rcases hidx : ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
      "link 0, moment 0" isIndexMaskMsg with _ | idx
  · rw [hidx] at h
    obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  rw [hidx] at h
  obtain ⟨idx', hy, h⟩ := ex_bind h
  obtain rfl : idx = idx' := Except.ok.inj hy
  obtain ⟨a, ha, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨f0, hf0, h⟩ := ex_bind h
  obtain ⟨f1, hf1, h⟩ := ex_bind h
  obtain ⟨f2, hf2, h⟩ := ex_bind h
  have e := Except.ok.inj h
  have hix : idx.owner.place ∈ F.first.blocksInOrder.map (·.place) := ownerOf_owner hidx
  refine ⟨a.1 ++ (loneWants idx M.lone
      ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1,
    f0, f1, f2, ?_, hf0, hf1, hf2, by subst e; rfl⟩
  intro w hw
  rcases List.mem_append.1 hw with h1 | h1
  · exact linksWants_owner hix _ _ a ha w h1
  · rw [loneWants_msg _ _ _ _ w h1]
    exact hix

theorem bookRaw_ahead {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {W : ProverCoinCounts}
    (h : bookRaw F p0 p1 p2 M = .ok W) :
    ∃ (B₀ : ProverCoinCounts) (m0 m1 : List SentMsg) (seg cF cO : List Ahead) (iF iO : Nat)
      (pq : Addr × Addr) (tail : Nat),
      spendingBook F p0 p1 p2 M = .ok B₀ ∧
      sentIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok m0 ∧
      sentIn F.shared.blocksInOrder p1 = .ok m1 ∧
      segmentCarries (planOf F.first.blocksInOrder) m0 = .ok seg ∧
      due? "the folded row's sending" ((under m1 "the folded row").head?.map (·.round)) = .ok iF ∧
      groupCarries (planOf F.shared.blocksInOrder) iF
        ((under m1 "the folded row").filter (!·.fresh) ++ (under m1 "Omega").filter (·.masks))
        ((under m1 "the folded row").find? (·.fresh)) = .ok cF ∧
      due? "the folded row's test's last switch"
        ((((seedRounds F.shared.blocksInOrder).zip p1.sends).filter fun x =>
          testOf x.2.label == "the folded row's test").getLast?.map (·.1)) = .ok iO ∧
      groupCarries (planOf F.shared.blocksInOrder) iO (under m1 "Omega") none = .ok cO ∧
      due? "the second chain's first fold, with a sending behind it"
        (behindFold (planOf F.second.blocksInOrder) 0) = .ok pq ∧
      due? "the shared chain's mask code" ((codesUnder p1 "Omega").map (·.2.r)) = .ok tail ∧
      W.ahead = B₀.ahead ++ seg ++ cF ++ cO ++
        carryPair pq.1 pq.2
          (m0.filter (·.masks) ++ (under m0 "W").filter (!·.fresh) ++
            (under m1 "Omega").filter (!·.masks))
          ((under m0 "W").find? (·.fresh)) ++
        (ownFreshIn F.shared.blocksInOrder).map (·.carry tail) := by
  unfold bookRaw at h
  obtain ⟨B₀, hB, h⟩ := ex_bind h
  obtain ⟨m0, hm0, h⟩ := ex_bind h
  obtain ⟨m1, hm1, h⟩ := ex_bind h
  obtain ⟨r0, -, h⟩ := ex_bind h
  obtain ⟨r1, -, h⟩ := ex_bind h
  obtain ⟨r2, -, h⟩ := ex_bind h
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨seg, hseg, h⟩ := ex_bind h
  obtain ⟨iF, hiF, h⟩ := ex_bind h
  obtain ⟨cF, hcF, h⟩ := ex_bind h
  obtain ⟨iO, hiO, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨cO, hcO, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨pq, hpq, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨tail, htail, h⟩ := ex_bind h
  have e := Except.ok.inj h
  exact ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, hm1, hseg, hiF, hcF, hiO, hcO, hpq,
    htail, by subst e; rfl⟩

theorem checked_ok {F : FileDescription Xi} {W B : ProverCoinCounts} (h : ProverCoinCounts.checked F W = .ok B) : W = B := by
  unfold ProverCoinCounts.checked at h
  split at h
  · exact Except.ok.inj h
  · cases h

/-- **AT AN OWNER THAT STANDS AT NO PLACE OF THE FIRST OR THE SECOND CHAIN THE WHOLE BOOK's ENTRIES
ARE `sharedAhead`'s**, in the same order. -/
theorem bookWhole_ahead_shared {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) :
    ∃ l, sharedAhead F p1 = .ok l ∧
      ∀ o : Addr, o.place ∉ F.first.blocksInOrder.map (·.place) → o.place ∉ F.second.blocksInOrder.map (·.place) →
        B.ahead.filter (·.owner == o) = l.filter (·.owner == o) := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, hm1, hseg, hiF, hcF, hiO, hcO, hpq,
    htail, eW⟩ := bookRaw_ahead hW
  obtain ⟨ws, f0, f1, f2, hws, hf0, hf1, hf2, eB⟩ := spendingBook_ahead hB
  refine ⟨f1 ++ (splitEntry F.shared.blocksInOrder p1).toList ++ cF ++ cO ++
    carryPair pq.1 pq.2 ((under m1 "Omega").filter (!·.masks)) none ++
    (ownFreshIn F.shared.blocksInOrder).map (·.carry tail), ?_, ?_⟩
  · unfold sharedAhead
    refine bind_of_ok hf1 ?_
    refine bind_of_ok hm1 ?_
    refine bind_of_ok hiF ?_
    refine bind_of_ok hcF ?_
    refine bind_of_ok hiO ?_
    refine bind_of_ok hcO ?_
    refine bind_of_ok hpq ?_
    refine bind_of_ok htail ?_
    rfl
  · intro o h1 h3
    have ne1 : ∀ a : Addr, a.place ∈ F.first.blocksInOrder.map (·.place) → a ≠ o :=
      fun a ha e => h1 (e ▸ ha)
    have ne3 : ∀ a : Addr, a.place ∈ F.second.blocksInOrder.map (·.place) → a ≠ o :=
      fun a ha e => h3 (e ▸ ha)
    have s0 : ∀ m ∈ m0, m.sender ≠ o := fun m hm => ne1 _ (sentIn_sender hm0 m hm)
    have z1 : (ws.map (·.entry)).filter (·.owner == o) = [] := filter_none (by
      intro e he
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
      exact ne1 _ (hws w hw))
    have z2 : f0.filter (·.owner == o) = [] := filter_none (by
      intro e he
      refine ne1 e.owner ?_
      rw [← planOf_places F.first.blocksInOrder]
      exact foldEntries_owner hf0 e he)
    have z3 : f2.filter (·.owner == o) = [] := filter_none (by
      intro e he
      refine ne3 e.owner ?_
      rw [← planOf_places F.second.blocksInOrder]
      exact foldEntries_owner hf2 e he)
    have z4 : seg.filter (·.owner == o) = [] := filter_none (by
      intro e he
      obtain ⟨m, hm, hom⟩ := segmentCarries_owner hseg e he
      rw [hom]
      exact s0 m hm)
    have z5 := carryPair_filter (p := pq.1) (q := pq.2) (o := o)
      (R₁ := m0.filter (·.masks) ++ (under m0 "W").filter (!·.fresh))
      (R₂ := (under m1 "Omega").filter (!·.masks)) (own := (under m0 "W").find? (·.fresh))
      (by
        intro m hm
        rcases List.mem_append.1 hm with h4 | h4
        · exact s0 m (List.mem_filter.1 h4).1
        · exact s0 m (List.mem_filter.1 (List.mem_filter.1 h4).1).1)
      (by
        intro m hm
        exact s0 m (List.mem_filter.1 (List.mem_of_find?_eq_some hm)).1)
    rw [eW, eB]
    simp only [List.filter_append]
    rw [z5]
    simp only [z1, z2, z3, z4, List.nil_append, List.append_assoc]

/-- **What is spent of such an owner's coins, and what is known there, are read off the short
list**: `ProverCoinCounts.spentBy` and `ProverCoinCounts.knownBy` (Honest/Frame.lean) at the whole book are what they are at
the book whose entries are `sharedAhead`'s list. -/
theorem bookWhole_spent_known_shared {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends}
    {M : Merges} {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) :
    ∃ l, sharedAhead F p1 = .ok l ∧
      ∀ o : Addr, o.place ∉ F.first.blocksInOrder.map (·.place) → o.place ∉ F.second.blocksInOrder.map (·.place) →
        (∀ p, B.spentBy o p = ({ B with ahead := l } : ProverCoinCounts).spentBy o p) ∧
        ∀ ord p, B.knownBy ord o p = ({ B with ahead := l } : ProverCoinCounts).knownBy ord o p := by
  obtain ⟨l, hl, hf⟩ := bookWhole_ahead_shared h
  refine ⟨l, hl, fun o h1 h3 => ⟨fun p => ?_, fun ord p => ?_⟩⟩
  · have k := filter_owner_and (hf o h1 h3) (fun e => e.spender == p && e.once)
    unfold ProverCoinCounts.spentBy
    simpa only [Bool.and_assoc] using k
  · have k := filter_owner_and (hf o h1 h3)
      (fun e => !(e.spender == p && e.once) && (e.spender == p || e.spender.before ord p))
    unfold ProverCoinCounts.knownBy
    simpa only [Bool.and_assoc] using k

end ProofFile.Honest

#print axioms ProofFile.Honest.spendingBook_ahead
#print axioms ProofFile.Honest.bookRaw_ahead
#print axioms ProofFile.Honest.checked_ok
#print axioms ProofFile.Honest.bookWhole_ahead_shared
#print axioms ProofFile.Honest.bookWhole_spent_known_shared
