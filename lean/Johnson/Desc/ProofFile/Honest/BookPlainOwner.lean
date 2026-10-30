-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookPlainOwner.lean: conditional: at a sub-protocol of the first chain
none of whose rounds is named "SEND seed", no entry of the whole book of coins has its owner. No kind
is named: the book's maker names owners by the sendings and by the folds of the other chains.

  plain_no_owner      the statement; it stands beside plain_no_carry (Honest/BookPlain.lean)
  stated_has_entry    conditional: a part of a sub-protocol of the first chain in a link, no merge,
                      for which the maker states a stretch, is the spender of an entry of the book

Ten helpers (namespace ProofFile.Honest.BookPlain): a part that holds a sending (HoldsASending); that the
makers' owners hold sendings or stand in another chain (ownerOf_holds, linksWants_holds, sentIn_holds,
foldEntries_holds, spendingBook_holds, splitEntry_owner, groupCarries_owner, ownFresh_fold); that
the first chain's stretches are entries (spendingBook_wants).

Limits. Implications: that the book's maker returns is a hypothesis, proved at no files here; so is
the test on the places. plain_no_owner speaks of the first chain alone, and it is silent on a book
with no entries: a book without any entry meets it. stated_has_entry is what shows, at a given
sub-protocol, that the book has an entry at all. The shared chain has a sister of plain_no_owner
(plain_no_owner_shared, Honest/BookPlainOwnerShared.lean). On public data alone: names of rounds, places,
counts. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookPlain
import Johnson.Desc.ProofFile.Honest.BookSharedLaw
import Johnson.Desc.ProofFile.Honest.Small.WantsStated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.BookPlain
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

variable {Xi S Cl : Type}

/-- **The part at an address holds a round named "SEND seed"** of the list, by its number. -/
abbrev HoldsASending (bs : List (Block S Cl)) (a : Addr) : Prop :=
  ∃ i ∈ seedRounds bs, addrOfRound bs i = some a

/-- An owner that ownerOf names holds a sending. -/
theorem ownerOf_holds {name : String} {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {label : String} {pick : OnBytes.OracleNotice → Bool} {m : MsgAt}
    (h : ownerOf name bs c later label pick = some m) : HoldsASending bs m.owner := by
  unfold ownerOf at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨a, ha, h⟩ := opt_bind h
  obtain ⟨st, -, h⟩ := opt_bind h
  obtain ⟨fr, -, h⟩ := opt_map h
  rw [← h]
  exact ⟨x.1, (List.of_mem_zip (a := x.1) (b := x.2) (List.mem_of_find?_eq_some hx)).1, ha⟩

/-- Every stretch that linksWants returns is of a message whose owner holds a sending. -/
theorem linksWants_holds {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr}
    (hidx : HoldsASending bs idx.owner) :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat),
      linksWants bs c later idx merges ls t = .ok r →
      ∀ w ∈ r.1, HoldsASending bs w.msg.owner
  | [], t, r, h, w, hw => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e] at hw
    cases hw
  | l :: ls, t, r, h, w, hw => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      try dsimp only at h
      obtain ⟨y, hy, e⟩ := ex_mapE h
      rw [← e] at hw
      rcases List.mem_append.1 hw with h1 | h1
      · rcases partsWants_msg row idx merges _ 0 t w h1 with e1 | e1
        · rw [e1]
          exact ownerOf_holds hrow
        · rw [e1]
          exact hidx
      · exact linksWants_holds hidx ls _ y hy w h1

/-- The sender of every message that sentIn returns holds a sending. -/
theorem sentIn_holds {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {ms : List SentMsg} (h : sentIn bs c later = .ok ms) :
    ∀ m ∈ ms, HoldsASending bs m.sender := by
  unfold sentIn at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, HoldsASending bs a.sender) ?_ hll
      inner hin a ha
    intro x hx r hr
    have hx1 : x.1 ∈ seedRounds bs :=
      (List.of_mem_zip (a := x.1) (b := x.2) (List.mem_filter.1 hx).1).1
    try dsimp only at hr
    refine mapM_all _ r ?_ hr
    intro n _ b hb
    try dsimp only at hb
    split at hb
    · have e2 := Except.ok.inj hb
      rw [← e2]
      exact ⟨x.1, hx1, by assumption⟩
    · cases hb

/-- The owner of every entry that foldEntries returns stands at a sub-protocol of the chain that
holds a round named "SEND seed". -/
theorem foldEntries_holds {here later : List PlanB} {c : Johnson.G.ChainSends} {l : List Ahead}
    (h : foldEntries here later c = .ok l) :
    ∀ e ∈ l, ∃ x ∈ here, x.place = e.owner.place ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed" := by
  unfold foldEntries at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, ∃ x ∈ here, x.place = a.owner.place ∧
      ∃ d ∈ x.rounds, d.entry.name = "SEND seed") ?_ hll inner hin a ha
    intro x hx r hr
    have hx1 := (List.of_mem_zip (a := x.1) (b := x.2) (List.mem_filter.1 hx).1).1
    obtain ⟨y, hy, ey⟩ := List.mem_map.1 hx1
    obtain ⟨hg, hn⟩ := named_of_filter hy
    have key : ∀ o, addrIn here x.1 = some o →
        ∃ z ∈ here, z.place = o.place ∧ ∃ d ∈ z.rounds, d.entry.name = "SEND seed" := by
      intro o ho
      obtain ⟨z, hz, ez, hd⟩ := addrIn_holds here x.1 o y.1 ho (ey ▸ hg)
      exact ⟨z, hz, ez, y.1, hd, hn⟩
    refine mapM_all _ r ?_ hr
    intro j _ b hb
    try dsimp only at hb
    split at hb
    · cases hb
    · cases hb
    · split at hb
      · have e2 := Except.ok.inj hb
        rw [← e2]
        exact key _ (by assumption)
      · cases hb

/-- The split's coin is owned in the list that it is made of. -/
theorem splitEntry_owner {bs : List (Block S Cl)} {c : Johnson.G.ChainSends} {e : Ahead}
    (h : splitEntry bs c = some e) : e.owner.place ∈ bs.map (·.place) := by
  unfold splitEntry at h
  dsimp only at h
  obtain ⟨p, -, h⟩ := opt_bind h
  obtain ⟨m, hm, h⟩ := opt_map h
  rw [← h]
  exact ownerOf_owner hm

/-- A run that groupCarries hands on is of a message of the group or of its own table. -/
theorem groupCarries_owner {l : List PlanB} {i : Nat} {g : List SentMsg} {own : Option SentMsg}
    {r : List Ahead} (h : groupCarries l i g own = .ok r) :
    ∀ e ∈ r, ∃ m, (m ∈ g ∨ own = some m) ∧ e.owner = m.sender := by
  unfold groupCarries at h
  split at h
  · have e := Except.ok.inj h
    rw [← e]
    exact carryPair_owner
  · cases h

/-- A fold that sends its own table stands at a sub-protocol of the chain. -/
theorem ownFresh_fold {bs : List (Block S Cl)} {o : OwnFresh} (h : o ∈ ownFreshIn bs) :
    o.fold.place ∈ bs.map (·.place) := by
  have h' : o ∈ (((planOf bs).flatMap (·.rounds)).zipIdx.filter fun r =>
      r.1.entry.name == "FOLD epsilon" && r.1.entry.roots != 0).filterMap fun r =>
      if r.2 == 0 then none else
      (behindFold (planOf bs) (r.2 - 1)).bind fun pq =>
        (foldBehind (planOf bs) (r.2 - 1)).map fun f =>
          (⟨pq.1, pq.2, f.2.2, (maskWordsByRound bs).getD r.2 0 / 3⟩ : OwnFresh) := h
  obtain ⟨r, -, hr⟩ := List.mem_filterMap.1 h'
  by_cases h0 : (r.2 == 0) = true
  · rw [if_pos h0] at hr
    cases hr
  · rw [if_neg h0] at hr
    obtain ⟨pq, hpq, h1⟩ := opt_bind hr
    obtain ⟨f, -, rfl⟩ := opt_map h1
    obtain ⟨p, q⟩ := pq
    obtain ⟨⟨x, hx, ex, -⟩, -⟩ := behindFold_named hpq
    show p.place ∈ bs.map (·.place)
    rw [← ex, ← planOf_places]
    exact List.mem_map_of_mem hx

/-- spendingBook's entries, with the owners of its stretches holding sendings. -/
theorem spendingBook_holds {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) :
    ∃ (ws : List Want) (f0 f1 f2 : List Ahead),
      (∀ w ∈ ws, HoldsASending F.first.blocksInOrder w.msg.owner) ∧
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
  have hix : HoldsASending F.first.blocksInOrder idx.owner := ownerOf_holds hidx
  refine ⟨a.1 ++ (loneWants idx M.lone
      ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1,
    f0, f1, f2, ?_, hf0, hf1, hf2, by subst e; rfl⟩
  intro w hw
  rcases List.mem_append.1 hw with h1 | h1
  · exact linksWants_holds hix _ _ a ha w h1
  · rw [loneWants_msg _ _ _ _ w h1]
    exact hix

/-- spendingBook's stretches of the first chain stand among its entries. -/
theorem spendingBook_wants {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) :
    ∃ (idx : MsgAt) (a : List Want × Nat),
      linksWants F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) idx M.ends
        (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a ∧
      ∀ w ∈ a.1 ++ (loneWants idx M.lone
        ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1,
        w.entry ∈ B₀.ahead := by
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
  refine ⟨idx, a, ha, fun w hw => ?_⟩
  subst e
  show w.entry ∈ (a.1 ++ _).map (·.entry) ++ f0 ++ f1 ++ f2 ++ _
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map_of_mem hw))))

end ProofFile.Honest.BookPlain

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow ProofFile.Honest.BookPlain

variable {Xi : Type}

/-- **AT A SUB-PROTOCOL OF THE FIRST CHAIN NONE OF WHOSE ROUNDS IS NAMED "SEND seed", NO ENTRY OF THE
WHOLE BOOK HAS ITS OWNER.** Conditional: hB: the book's maker returns B; hp: the description's test on
its places accepts; hb; hs. -/
theorem plain_no_owner {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true) {b : Block F.S₁ F.Cl}
    (hb : b ∈ F.first.blocksInOrder) (hs : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed") :
    ∀ e ∈ B.ahead, e.owner.place ≠ b.place := by
  intro e he hpl
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB₀, hm0, hm1, hseg, -, hcF, -, hcO, -, -, eW⟩ :=
    bookRaw_ahead hW
  obtain ⟨ws, f0, f1, f2, hws, hf0, hf1, hf2, eB⟩ := spendingBook_holds hB₀
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  have c1 : b.place.chain = 1 := chain_first hp _ (List.mem_map_of_mem hb)
  have s1 : ∀ a, HoldsASending F.first.blocksInOrder a → a.place ≠ b.place := by
    rintro a ⟨i, hi, ha⟩
    obtain ⟨r, hr, hnm⟩ := seed_named hi
    exact round_not_here hn hb hs ha hr hnm
  have no2 : ∀ a : Place, a ∈ F.shared.blocksInOrder.map (·.place) → a ≠ b.place := by
    intro a h2 ea
    have := chain_shared hp _ h2
    rw [ea, c1] at this
    cases this
  have no3 : ∀ a : Place, a ∈ F.second.blocksInOrder.map (·.place) → a ≠ b.place := by
    intro a h3 ea
    have := chain_second hp _ h3
    rw [ea, c1] at this
    cases this
  have s0 : ∀ m ∈ m0, m.sender.place ≠ b.place := fun m hm => s1 _ (sentIn_holds hm0 m hm)
  have s2 : ∀ m ∈ m1, m.sender.place ≠ b.place := fun m hm => no2 _ (sentIn_sender hm1 m hm)
  rw [eW, eB] at he
  simp only [List.mem_append] at he
  rcases he with ((((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h1
    exact s1 _ (hws w hw) hpl
  · obtain ⟨x, hx, ex, d, hd, hnm⟩ := foldEntries_holds hf0 e h1
    have hx' : x ∈ F.first.blocksInOrder.map fun b => (⟨b.place, partsCut b, b.rounds⟩ : PlanB) := hx
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hx'
    obtain rfl : b' = b := List.inj_on_of_nodup_map hn hb' hb (ex.trans hpl)
    exact hs d hd hnm
  · have h2 := foldEntries_owner hf1 e h1
    rw [planOf_places] at h2
    exact no2 _ h2 hpl
  · have h3 := foldEntries_owner hf2 e h1
    rw [planOf_places] at h3
    exact no3 _ h3 hpl
  · exact no2 _ (splitEntry_owner (Option.mem_toList.1 h1)) hpl
  · obtain ⟨m, hm, hom⟩ := segmentCarries_owner hseg e h1
    rw [hom] at hpl
    exact s0 m hm hpl
  · obtain ⟨m, hm, hom⟩ := groupCarries_owner hcF e h1
    rw [hom] at hpl
    rcases hm with hm | hm
    · rcases List.mem_append.1 hm with h4 | h4
      · exact s2 m (List.mem_filter.1 (List.mem_filter.1 h4).1).1 hpl
      · exact s2 m (List.mem_filter.1 (List.mem_filter.1 h4).1).1 hpl
    · exact s2 m (List.mem_filter.1 (List.mem_of_find?_eq_some hm)).1 hpl
  · obtain ⟨m, hm, hom⟩ := groupCarries_owner hcO e h1
    rw [hom] at hpl
    rcases hm with hm | hm
    · exact s2 m (List.mem_filter.1 hm).1 hpl
    · cases hm
  · obtain ⟨m, hm, hom⟩ := carryPair_owner e h1
    rw [hom] at hpl
    rcases hm with hm | hm
    · rcases List.mem_append.1 hm with h4 | h4
      · rcases List.mem_append.1 h4 with h5 | h5
        · exact s0 m (List.mem_filter.1 h5).1 hpl
        · exact s0 m (List.mem_filter.1 (List.mem_filter.1 h5).1).1 hpl
      · exact s2 m (List.mem_filter.1 (List.mem_filter.1 h4).1).1 hpl
    · exact s0 m (List.mem_filter.1 (List.mem_of_find?_eq_some hm)).1 hpl
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h1
    exact no2 _ (ownFresh_fold ho) hpl

/-- **A PART OF A SUB-PROTOCOL OF THE FIRST CHAIN IN A LINK, NO MERGE, FOR WHICH THE MAKER STATES A
STRETCH, IS THE SPENDER OF AN ENTRY OF THE WHOLE BOOK.** Conditional: hB: the book's maker returns B;
hp: the description's test on its places accepts; hb; hl; hq: q is the part number i; hm; hst. -/
theorem stated_has_entry {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true) {b : Block F.S₁ F.Cl}
    (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l) {i : Nat} {q : PartAt}
    (hq : (planParts b)[i]? = some q) (hm : M.ends.contains ⟨b.place, i⟩ = false)
    (hst : ProofFile.Honest.Small.stated q ≠ []) :
    ∃ e ∈ B.ahead, e.spender = ⟨b.place, i⟩ := by
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB₀, hm0, hm1, hseg, -, hcF, -, hcO, -, -, eW⟩ :=
    bookRaw_ahead hW
  obtain ⟨idx, a, ha, hin⟩ := spendingBook_wants hB₀
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  have hw := ProofFile.Honest.Small.wants_at_plain ha hn hb hl i hm
  rw [hq] at hw
  have hne : ((a.1 ++ (loneWants idx M.lone
      ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
        fun w => w.spender == ⟨b.place, i⟩) ≠ [] := by
    intro h0
    rw [h0] at hw
    apply hst
    simpa using hw.symm
  obtain ⟨w, hmem⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hmem
  refine ⟨w.entry, ?_, beq_iff_eq.1 h2⟩
  have h3 := hin w h1
  rw [eW]
  simp only [List.mem_append, h3, true_or]

end ProofFile.Honest

#print axioms ProofFile.Honest.plain_no_owner
#print axioms ProofFile.Honest.BookPlain.spendingBook_wants
#print axioms ProofFile.Honest.stated_has_entry
