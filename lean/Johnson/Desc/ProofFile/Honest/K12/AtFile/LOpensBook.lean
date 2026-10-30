-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LOpensBook.lean: the tie of the coins `CoinsTied`
(LOpensRows.lean) from a public test on the book of random values, where the frame has lent the
finish's part and a part that carries the finish's messages their coins. General in the book, the
run's coins, the finish's place and the carrying part.

  `closingBookTest`     the public test, on the book's entries alone
  `own_of_lendPart_at_opens`     what `lendPart` hands a part as its own is the cut of its purse
                                 from 0 on
  `cut_of_cut`          a cut of that cut is the purse's cut
  `carried_is_stretch`  the code switch's reader of a lent list and this folder's are one
  `coinsTied_of_book`   THE LAW

The clauses of `closingBookTest`, entry by entry of what is carried to the part at a, in the book's
order. (1) The first entries, as many as the finish carries, have the owner, start and count of the
entries by which the finish's part carries. (2) The next is the finish's own coins from 0 on, by the
carrying message's count. (3) The next is the finish's own coins from message 1's start on, by the
fresh table's count, within the finish's own count.

Limits.
- No book is shown to pass the test here.
- That the frame has lent both parts their coins is a premise.
- The test reads entries, not the parts' texts.
- Nothing on how a coin is sampled. Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `coinsTied_of_book` bears this label; the rule is at its home, the
head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the two premises on `lendPart` tie the
letters cK and c to a run's coins.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LOpensRows
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light (carriedOf lend_cut carried_of_lendPart cut_at)

/-- **The public test on the book's entries** (its clauses: the head of this file). p: the finish's
place. a: the address of the part that carries the finish's messages. -/
def closingBookTest (Bk : ProverCoinCounts) (p : K2.SwitchPlace) (a : Addr) : Bool :=
  let mine := carriedOf Bk a
  let his := carriedOf Bk ⟨p.place, 0⟩
  let fresh := K2.switchFresh p.sizes p.others p.foldVars
  ((List.range p.front.length).all fun n =>
    match mine[n]?, his[n]? with
    | some x, some y => x.owner == y.owner && x.start == y.start && x.count == y.count
    | _, _ => false) &&
  (match mine[p.front.length]? with
    | some x => x.owner == ⟨p.place, 0⟩ && x.start == ⟨0, 0⟩ &&
        x.count == K2.messageDue p.sizes.codes (shapeL p) none
    | none => false) &&
  (match mine[p.front.length + 1]? with
    | some x => x.owner == ⟨p.place, 0⟩ &&
        x.start == K2.dueBefore p.sizes.codes (sentL p) fresh 1 &&
        x.count == K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars) &&
        decide (x.start.e + x.count.e ≤ (K2.sendingDue p.sizes.codes (sentL p) fresh).e)
    | none => false)

variable {V W X : Type}

/-- What `lendPart` hands a part as its own is the cut of its purse from 0 on. -/
theorem own_of_lendPart_at_opens (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Addr) (p : Part V W X) (c : p.Coins)
    (h : lendPart Bk rows look a p = .ok c) :
    (look a).2.cut ⟨0, 0⟩ p.takes = some c.1 := by
  unfold lendPart at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i own hown
  cases h1 : lend look p.spends ((Bk.ahead.filter fun e => e.spender == a).filter (·.once)) with
  | error _ =>
    rw [h1] at h
    cases h
  | ok sp =>
    rw [h1] at h
    cases h2 : lend look p.carries ((Bk.ahead.filter fun e => e.spender == a).filter (!·.once)) with
    | error _ =>
      change Except.map _ (lend look p.carries _) = _ at h
      rw [h2] at h
      cases h
    | ok ca =>
      change Except.map _ (lend look p.carries _) = _ at h
      rw [h2] at h
      cases h
      exact hown

/-- A cut of the cut from 0 on is the purse's cut. -/
theorem cut_of_cut {d t N b : Due} (c : Cs d) {own : Cs t} (h1 : c.cut ⟨0, 0⟩ t = some own)
    {c' : Cs N} (h2 : own.cut b N = some c') {x : Cs N} (h3 : c.cut b N = some x) : c' = x := by
  unfold Cs.cut at h1 h2 h3
  split at h1
  · split at h2
    · split at h3
      · cases h1
        cases h2
        cases h3
        simp
      · cases h3
    · cases h2
  · cases h1

/-- The code switch's reader of a lent list and this folder's are one, at the list's own count. -/
theorem carried_is_stretch : ∀ (l : List (String × Due)) (c : CsAll l) (n : ℕ) (x : String × Due),
    l[n]? = some x → K2.Stretch.carried l c n = .ok (asK2 x.2 (stretches l c n))
  | [], _, _, _, h => by simp at h
  | d :: l, c, 0, x, h => by
    have e : d = x := by simpa using h
    subst e
    simp only [K2.Stretch.carried, stretches, asK2_stretchOf]
  | d :: l, c, n + 1, x, h => by
    simp only [K2.Stretch.carried, stretches]
    exact carried_is_stretch l _ n x (by simpa using h)

/-- Two cuts of one purse at one start and count are one stretch. -/
theorem stretch_of_same (look : Addr → (d : Due) × Cs d) {e₁ e₂ : Ahead}
    (ho : e₁.owner = e₂.owner) (hs : e₁.start = e₂.start) (hc : e₁.count = e₂.count)
    {x₁ : Cs e₁.count} {x₂ : Cs e₂.count}
    (h₁ : (look e₁.owner).2.cut e₁.start e₁.count = some x₁)
    (h₂ : (look e₂.owner).2.cut e₂.start e₂.count = some x₂) : stretchOf x₁ = stretchOf x₂ := by
  obtain ⟨n₁, o₁, s₁, c₁, p₁, b₁⟩ := e₁
  obtain ⟨n₂, o₂, s₂, c₂, p₂, b₂⟩ := e₂
  obtain rfl : o₁ = o₂ := ho
  obtain rfl : s₁ = s₂ := hs
  obtain rfl : c₁ = c₂ := hc
  have e : x₁ = x₂ := Option.some.inj (h₁.symm.trans h₂)
  rw [e]

/-- **THE LAW: the book's test gives the tie.** q: the part that carries the finish's messages. -/
theorem coinsTied_of_book (Bk : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (p : K2.SwitchPlace) (a : Addr) (q : Part V W X)
    (cK : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries)
    (hK : lendPart Bk rows look ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) = .ok cK)
    (c : q.Coins) (hq : lendPart Bk rows look a q = .ok c)
    (hB : closingBookTest Bk p a = true) : CoinsTied p cK (stretches q.carries c.2.2) := by
  unfold closingBookTest at hB
  dsimp only at hB
  rw [Bool.and_eq_true, Bool.and_eq_true] at hB
  obtain ⟨⟨b1, b2⟩, b3⟩ := hB
  have Lq := carried_of_lendPart Bk rows look a q c hq
  have LK := carried_of_lendPart Bk rows look ⟨p.place, 0⟩
    (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) cK hK
  have hown := own_of_lendPart_at_opens Bk rows look ⟨p.place, 0⟩
    (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) cK hK
  refine ⟨fun n x hx => ?_, fun c' hc' => ?_, fun i hi => ?_⟩
  · have hn : n < p.front.length := by
      have := (List.getElem?_eq_some_iff.1 hx).1
      simpa [K2.SwitchPlace.carries] using this
    have k := List.all_eq_true.1 b1 n (List.mem_range.2 hn)
    split at k
    · rename_i e₂ e₁ h₂ h₁
      simp only [Bool.and_eq_true, beq_iff_eq] at k
      obtain ⟨x₂, c₂, s₂⟩ := lend_cut look _ _ _ Lq n e₂ h₂
      obtain ⟨x₁, c₁, s₁⟩ := lend_cut look _ _ _ LK n e₁ h₁
      rw [carried_is_stretch p.carries cK.2.2 n x hx, s₂]
      have s₁' : stretches p.carries cK.2.2 n = stretchOf x₁ := s₁
      rw [s₁', stretch_of_same look k.1.1 k.1.2 k.2 c₂ c₁]
    · cases k
  · split at b2
    · rename_i e he
      simp only [Bool.and_eq_true, beq_iff_eq] at b2
      obtain ⟨⟨ho, hs⟩, hc⟩ := b2
      obtain ⟨x, hx, hst⟩ := lend_cut look _ _ _ Lq _ e he
      obtain ⟨en, eo, es, ec, ep, eb⟩ := e
      obtain rfl : eo = ⟨p.place, 0⟩ := ho
      obtain rfl : es = ⟨0, 0⟩ := hs
      obtain rfl : ec = K2.messageDue p.sizes.codes (shapeL p) none := hc
      rw [hst, asK2_stretchOf, cut_of_cut _ hown hc' hx]
      rfl
    · cases b2
  · split at b3
    · rename_i e he
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at b3
      obtain ⟨⟨⟨ho, hs⟩, hc⟩, hin⟩ := b3
      obtain ⟨x, hx, hst⟩ := lend_cut look _ _ _ Lq _ e he
      have hi' : i < e.count.e := by
        rw [hc]
        exact hi
      have hj : e.start.e + i < (K2.sendingDue p.sizes.codes (sentL p)
          (K2.switchFresh p.sizes p.others p.foldVars)).e := by omega
      rw [hst, cut_at _ _ _ x hx i hi', ← hs, ho]
      have e2 := cut_at _ _ _ cK.1 hown (e.start.e + i) hj
      have e3 : K1.ce cK.1 (e.start.e + i) = (stretchOf cK.1).e (e.start.e + i) := rfl
      rw [e3, e2]
      show _ = (stretchOf (look ⟨p.place, 0⟩).2).e (0 + (e.start.e + i))
      rw [Nat.zero_add]
    · cases b3

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.closingBookTest
#print axioms ProofFile.Honest.K12.AtProof.own_of_lendPart_at_opens
#print axioms ProofFile.Honest.K12.AtProof.cut_of_cut
#print axioms ProofFile.Honest.K12.AtProof.carried_is_stretch
#print axioms ProofFile.Honest.K12.AtProof.stretch_of_same
#print axioms ProofFile.Honest.K12.AtProof.coinsTied_of_book
