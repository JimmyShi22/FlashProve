-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/BookOwners.lean: whose coins the book of coins spends (ProverCoinCounts,
Honest/Frame.lean). Every entry of the whole book (bookWhole, Honest/BookWhole.lean) that spends
coins has as its owner a part at a sub-protocol that holds a round "SEND seed". So a part at a
sub-protocol with no such round has none of its coins spent, by anybody. That is the premise on the
book that the laws of the next token and of the closing take (Honest/K7/Rows.lean,
Honest/K10/RowsOfClosings.lean).

  `SendsIn`   a sub-protocol of a list stands at a place and holds a round "SEND seed"
  `addrOfRound_held`   the address of a round is that of a sub-protocol that holds the round
  `seed_at`   what `seedRounds` lists is a round "SEND seed"
  `ownerOf_sends`, `linksWants_sends`, `loneWants_sends`, `foldEntries_seedOwner`, `splitEntry_owner`
                   the makers of the spending entries, one by one
  `bookWhole_owner`   the statement at every spending entry of the whole book
  `bookWhole_spent_nil`   no entry spends a coin of a part at a sub-protocol of the first chain
                   that holds no round "SEND seed"

Limits. That `bookWhole` returns is a premise, and so is `F.placesOk = true` in the last statement.
Nothing is evaluated at a public file. The statements are on lists, addresses and names of rounds.
This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookRowStretch
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

variable {Xi S Cl : Type}

/-- **A sub-protocol of the list stands at the place and holds a round "SEND seed".** -/
def SendsIn (bs : List (Block S Cl)) (p : Place) : Prop :=
  ∃ b ∈ bs, b.place = p ∧ ∃ d ∈ b.rounds, d.entry.name = "SEND seed"

/-- The address of round number i is that of a sub-protocol that holds that round. -/
theorem addrOfRound_held : ∀ (bs : List (Block S Cl)) (i : Nat) (a : Addr) (d : Fmt.DeclaredRound),
    addrOfRound bs i = some a → (bs.flatMap (·.rounds))[i]? = some d →
      ∃ b ∈ bs, b.place = a.place ∧ d ∈ b.rounds
  | [], _, _, _, h, _ => by
    unfold addrOfRound at h
    cases h
  | b :: l, i, a, d, h, hd => by
    unfold addrOfRound at h
    rw [List.flatMap_cons] at hd
    split at h
    · rename_i hi
      have e := Option.some.inj h
      rw [List.getElem?_append_left hi] at hd
      exact ⟨b, List.Mem.head _, by rw [← e], List.mem_of_getElem? hd⟩
    · rename_i hi
      rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hd
      obtain ⟨x, hx, h1, h2⟩ := addrOfRound_held l _ a d h hd
      exact ⟨x, List.Mem.tail _ hx, h1, h2⟩

/-- What a list of the numbers of rounds "SEND seed" holds is such a round. The form of the list is
that of `seedRounds` and of `foldEntries`'s own list. -/
theorem seed_at (rs : List Fmt.DeclaredRound) {i : Nat}
    (h : i ∈ (rs.zipIdx.filter fun r => r.1.entry.name == "SEND seed").map (·.2)) :
    ∃ d, rs[i]? = some d ∧ d.entry.name = "SEND seed" := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
  obtain ⟨hm, hn⟩ := List.mem_filter.1 hr
  exact ⟨r.1, List.mem_zipIdx_iff_getElem?.1 hm, by simpa using hn⟩

/-- **The owner that `ownerOf` makes stands at a sending.** -/
theorem ownerOf_sends {name label : String} {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {pick : OnBytes.OracleNotice → Bool} {m : MsgAt}
    (h : ownerOf name bs c later label pick = some m) : SendsIn bs m.owner.place := by
  unfold ownerOf at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  dsimp only at h
  obtain ⟨a, ha, h⟩ := opt_bind h
  obtain ⟨st, -, h⟩ := opt_bind h
  obtain ⟨free, -, h⟩ := opt_map h
  have hz := List.mem_of_find?_eq_some hx
  have h1 : x.1 ∈ seedRounds bs := (List.of_mem_zip (a := x.1) (b := x.2) hz).1
  obtain ⟨d, hd, hn⟩ := seed_at _ h1
  obtain ⟨b, hb, hp, hm⟩ := addrOfRound_held bs _ a d ha hd
  rw [← h]
  exact ⟨b, hb, hp, d, hm, hn⟩

/-- One part's ranges are of the mask row or of the index-mask message. -/
theorem partWants_seedMsg (row idx : MsgAt) (merge : Bool) (p : PartAt) (j t : Nat) :
    ∀ w ∈ (partWants row idx merge p j t).1, w.msg = row ∨ w.msg = idx := by
  intro w hw
  unfold partWants at hw
  dsimp only at hw
  split at hw
  · cases hw
  · split at hw
    · obtain rfl := mem_one hw
      exact Or.inl rfl
    · split at hw
      · obtain rfl := mem_one hw
        exact Or.inl rfl
      · split at hw
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact Or.inl rfl
          · obtain rfl := mem_one hw
            exact Or.inr rfl
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact Or.inl rfl
          · obtain rfl := mem_one hw
            exact Or.inl rfl

theorem partsWants_seedMsg (row idx : MsgAt) (merges : List Addr) :
    ∀ (ps : List PartAt) (j t : Nat), ∀ w ∈ (partsWants row idx merges ps j t).1,
      w.msg = row ∨ w.msg = idx
  | [], _, _ => by
    intro w hw
    cases hw
  | p :: ps, j, t => by
    intro w hw
    unfold partsWants at hw
    dsimp only at hw
    rcases List.mem_append.1 hw with h | h
    · exact partWants_seedMsg row idx _ p j t w h
    · exact partsWants_seedMsg row idx merges ps _ _ w h

/-- The segments' ranges are of messages whose owners stand at sendings. -/
theorem linksWants_sends {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr}
    (hi : SendsIn bs idx.owner.place) :
    ∀ (ls : List Nat) (t : Nat) (a : List Want × Nat),
      linksWants bs c later idx merges ls t = .ok a → ∀ w ∈ a.1, SendsIn bs w.msg.owner.place
  | [], t, a, h => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e]
    intro w hw
    cases hw
  | l :: ls, t, a, h => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      obtain ⟨y, hy, e⟩ := ex_mapE h
      rw [← e]
      intro w hw
      rcases List.mem_append.1 hw with h1 | h1
      · rcases partsWants_seedMsg row idx merges _ _ _ w h1 with e1 | e1
        · rw [e1]
          exact ownerOf_sends hrow
        · rw [e1]
          exact hi
      · exact linksWants_sends hi ls _ y hy w h1

/-- The ranges of the sumchecks outside a segment are of the index-mask message. -/
theorem loneWants_seedMsg (idx : MsgAt) (lone : List Addr) :
    ∀ (ps : List PartAt) (t : Nat), ∀ w ∈ (loneWants idx lone ps t).1, w.msg = idx
  | [], _ => by
    intro w hw
    cases hw
  | p :: ps, t => by
    intro w hw
    unfold loneWants at hw
    dsimp only at hw
    rcases List.mem_append.1 hw with h | h
    · split at h
      · unfold loneSumWants at h
        split at h
        · obtain rfl := mem_one h
          rfl
        · cases h
      · cases h
    · exact loneWants_seedMsg idx lone ps _ w h

/-- **The owner of a fold's spending entry stands at a sending of the chain.** -/
theorem foldEntries_seedOwner {here later : List PlanB} {c : Johnson.G.ChainSends} {l : List Ahead}
    (h : foldEntries here later c = .ok l) :
    ∀ e ∈ l, ∃ x ∈ here, x.place = e.owner.place ∧
      ∃ d ∈ x.rounds, d.entry.name = "SEND seed" := by
  unfold foldEntries at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, ∃ x ∈ here,
      x.place = a.owner.place ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed") ?_ hll
      inner hin a ha
    intro x hxm r hr
    have hz := (List.mem_filter.1 hxm).1
    have h1 := (List.of_mem_zip (a := x.1) (b := x.2) hz).1
    obtain ⟨d, hd, hn⟩ := seed_at _ h1
    refine mapM_all _ r ?_ hr
    intro j _ b hb
    try dsimp only at hb
    split at hb
    · cases hb
    · cases hb
    · split at hb
      · rename_i o p st ho hp hst
        have e2 := Except.ok.inj hb
        obtain ⟨y, hy, hy1, hy2⟩ := addrIn_holds _ _ _ _ ho hd
        rw [← e2]
        exact ⟨y, hy, hy1, d, hy2, hn⟩
      · cases hb

/-- The owner of the shared split's coin stands at a sending of the chain. -/
theorem splitEntry_owner {bs : List (Block S Cl)} {c : Johnson.G.ChainSends} {e : Ahead}
    (h : splitEntry bs c = some e) : SendsIn bs e.owner.place := by
  unfold splitEntry at h
  dsimp only at h
  obtain ⟨p, -, h⟩ := opt_bind h
  obtain ⟨m, hm, h⟩ := opt_map h
  rw [← h]
  exact ownerOf_sends hm

/-- A plan's sending is a sending of the list. -/
theorem sends_of_plan {bs : List (Block S Cl)} {p : Place}
    (h : ∃ x ∈ planOf bs, x.place = p ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed") :
    SendsIn bs p := by
  obtain ⟨x, hx, hp, d, hd, hn⟩ := h
  unfold planOf at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  exact ⟨b, hb, hp, d, hd, hn⟩

/-- **WHOSE COINS THE WHOLE BOOK SPENDS.** Every entry that spends has its owner at a sub-protocol of
one of the three chains that holds a round "SEND seed". -/
theorem bookWhole_owner {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (h : bookWhole F p0 p1 p2 M = .ok B) :
    ∀ e ∈ B.ahead, e.once = true →
      SendsIn F.first.blocksInOrder e.owner.place ∨ SendsIn F.shared.blocksInOrder e.owner.place ∨
        SendsIn F.second.blocksInOrder e.owner.place := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, hm1, hseg, hiF, hcF, hiO, hcO, hpq,
    htail, eW⟩ := bookRaw_ahead hW
  obtain ⟨idx, a, f0, f1, f2, hidx, ha, hfree, hf0, hf1, hf2, eB⟩ := spendingBook_open hB
  have hi := ownerOf_sends hidx
  have both : ∀ {P : Ahead → Prop} {L₁ L₂ : List Ahead}, (∀ e ∈ L₁, P e) → (∀ e ∈ L₂, P e) →
      ∀ e ∈ L₁ ++ L₂, P e := by
    intro P L₁ L₂ h₁ h₂ e he
    rcases List.mem_append.1 he with h | h
    · exact h₁ e h
    · exact h₂ e h
  have carried : ∀ {P : Ahead → Prop} {L : List Ahead}, (∀ e ∈ L, e.once = false) →
      ∀ e ∈ L, e.once = true → P e := by
    intro P L hL e he ho
    rw [hL e he] at ho
    cases ho
  rw [eW, eB]
  refine both (both (both (both (both (both (both (both (both ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · intro e he _
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
    refine Or.inl ?_
    rcases List.mem_append.1 hw with h1 | h1
    · exact linksWants_sends hi _ _ a ha w h1
    · have e1 := loneWants_seedMsg idx M.lone _ _ w h1
      show SendsIn F.first.blocksInOrder w.msg.owner.place
      rw [e1]
      exact hi
  · intro e he _
    obtain ⟨x, hx, hp, d, hd, hn⟩ := foldEntries_seedOwner hf0 e he
    exact Or.inl (sends_of_plan ⟨x, hx, hp, d, hd, hn⟩)
  · intro e he _
    obtain ⟨x, hx, hp, d, hd, hn⟩ := foldEntries_seedOwner hf1 e he
    exact Or.inr (Or.inl (sends_of_plan ⟨x, hx, hp, d, hd, hn⟩))
  · intro e he _
    obtain ⟨x, hx, hp, d, hd, hn⟩ := foldEntries_seedOwner hf2 e he
    exact Or.inr (Or.inr (sends_of_plan ⟨x, hx, hp, d, hd, hn⟩))
  · intro e he _
    have hs : splitEntry F.shared.blocksInOrder p1 = some e := by
      cases hsp : splitEntry F.shared.blocksInOrder p1 with
      | none =>
        rw [hsp] at he
        cases he
      | some e' =>
        rw [hsp] at he
        rw [mem_one he]
    exact Or.inr (Or.inl (splitEntry_owner hs))
  · exact carried (segmentCarries_once hseg)
  · exact carried (groupCarries_once hcF)
  · exact carried (groupCarries_once hcO)
  · exact carried carryPair_once
  · refine carried ?_
    intro e he
    obtain ⟨o, -, rfl⟩ := List.mem_map.1 he
    rfl

/-- **NO ENTRY SPENDS A COIN OF A PART AT A SUB-PROTOCOL THAT SENDS NOTHING**: at a sub-protocol of
the first chain that holds no round "SEND seed", at every part and for every spender. -/
theorem bookWhole_spent_nil {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder)
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed") (j : Nat) (q : Addr) :
    B.spentBy ⟨b.place, j⟩ q = [] := by
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  have c1 : b.place.chain = 1 := chain_first hp _ (List.mem_map.2 ⟨b, hb, rfl⟩)
  refine spentBy_nil B _ _ ?_
  intro e he ho eo _
  rcases bookWhole_owner h e he ho with ⟨x, hx, hpl, d, hd, hn'⟩ | ⟨x, hx, hpl, -⟩ | ⟨x, hx, hpl, -⟩
  · rw [eo] at hpl
    have e' : x = b := List.inj_on_of_nodup_map hn hx hb hpl
    rw [e'] at hd
    exact hF d hd hn'
  · have h2 := chain_shared hp x.place (List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [hpl, eo] at h2
    have h3 : b.place.chain = 2 := h2
    omega
  · have h2 := chain_second hp x.place (List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [hpl, eo] at h2
    have h3 : b.place.chain = 3 := h2
    omega

end ProofFile.Honest

#print axioms ProofFile.Honest.SendsIn
#print axioms ProofFile.Honest.addrOfRound_held
#print axioms ProofFile.Honest.seed_at
#print axioms ProofFile.Honest.ownerOf_sends
#print axioms ProofFile.Honest.partWants_seedMsg
#print axioms ProofFile.Honest.partsWants_seedMsg
#print axioms ProofFile.Honest.linksWants_sends
#print axioms ProofFile.Honest.loneWants_seedMsg
#print axioms ProofFile.Honest.foldEntries_seedOwner
#print axioms ProofFile.Honest.splitEntry_owner
#print axioms ProofFile.Honest.sends_of_plan
#print axioms ProofFile.Honest.bookWhole_owner
#print axioms ProofFile.Honest.bookWhole_spent_nil
