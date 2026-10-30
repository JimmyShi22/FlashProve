-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookPlainHolder.lean: conditional: whose coins a plain sub-protocol of
the first chain spends. No kind is named.

  spendingBook_stretches   the book's entries, with the first chain's stretches by name
  partWants_row, partsWants_row   a part that is no merge spends the segment's mask row alone
  plain_spent_row     at a sub-protocol of the first chain in a link, none of whose rounds is named
                      "SEND seed" or "FOLD epsilon" and none of whose parts is a merge, the owner of
                      every entry handed to it is the owner of the link's mask row
  ownerOf_found       where ownerOf returns, its owner is the address of the sending's round

Limits. Implications: that the book's maker returns is a hypothesis, proved at no files here; so is
the test on the places. On public data alone: names of rounds, places, counts. No property is
claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookPlainOwner
import Johnson.Desc.ProofFile.Honest.BookRowKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow ProofFile.Honest.BookPlain

variable {Xi S Cl : Type}

/-- spendingBook's entries, with its stretches of the first chain by name. -/
theorem spendingBook_stretches {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) :
    ∃ (idx : MsgAt) (a : List Want × Nat) (f0 f1 f2 : List Ahead),
      linksWants F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) idx M.ends
        (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a ∧
      foldEntries (planOf F.first.blocksInOrder) (planOf F.second.blocksInOrder) p0 = .ok f0 ∧
      foldEntries (planOf F.shared.blocksInOrder) [] p1 = .ok f1 ∧
      foldEntries (planOf F.second.blocksInOrder) [] p2 = .ok f2 ∧
      B₀.ahead = (a.1 ++ (loneWants idx M.lone
        ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).map (·.entry) ++
        f0 ++ f1 ++ f2 ++ (splitEntry F.shared.blocksInOrder p1).toList := by
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
  exact ⟨idx, a, f0, f1, f2, ha, hf0, hf1, hf2, by subst e; rfl⟩

/-- A part that is no merge spends the segment's mask row alone. -/
theorem partWants_row (row idx : MsgAt) {merge : Bool} (hm : merge = false) (p : PartAt)
    (j t : Nat) : ∀ w ∈ (partWants row idx merge p j t).1, w.msg = row := by
  subst hm
  intro w hw
  unfold partWants at hw
  dsimp only at hw
  split at hw
  · cases hw
  · split at hw
    · have e := mem_one hw
      subst e
      rfl
    · split at hw
      · have e := mem_one hw
        subst e
        rfl
      · split at hw
        · rename_i hc
          cases hc
        · rcases mem_two hw with e | e <;> subst e <;> rfl

/-- In a list of parts, a stretch whose spender is no merge is of the segment's mask row. -/
theorem partsWants_row (row idx : MsgAt) (merges : List Addr) :
    ∀ (ps : List PartAt) (j t : Nat), ∀ w ∈ (partsWants row idx merges ps j t).1,
      merges.contains w.spender = false → w.msg = row
  | [], _, _, w, hw, _ => by
    unfold partsWants at hw
    try dsimp only at hw
    cases hw
  | p :: ps, j, t, w, hw, hc => by
    unfold partsWants at hw
    try dsimp only at hw
    rcases List.mem_append.1 hw with h | h
    · have e := ProofFile.Honest.BookRow.partWants_spender _ _ _ _ _ _ w h
      exact partWants_row row idx (by rw [← e]; exact hc) p j t w h
    · exact partsWants_row row idx merges ps _ _ w h hc

/-- **AT SUCH A SUB-PROTOCOL IN A LINK, NO PART A MERGE, THE OWNER OF EVERY ENTRY HANDED TO IT IS THE
OWNER OF THE LINK's MASK ROW.** Conditional: hB; hp; hb; hs; hf; hl; hm. -/
theorem plain_spent_row {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true) {b : Block F.S₁ F.Cl}
    (hb : b ∈ F.first.blocksInOrder) (hs : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed")
    (hf : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") {l : Nat} (hl : b.place.link = some l)
    (hm : ∀ a : Addr, a.place = b.place → M.ends.contains a = false) :
    ∀ e ∈ B.ahead, e.spender.place = b.place →
      ∃ row, ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some row ∧ e.owner = row.owner := by
  intro e he hpl
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB₀, -, -, hseg, -, hcF, -, hcO, hpq, -, eW⟩ :=
    bookRaw_ahead hW
  obtain ⟨idx, a, f0, f1, f2, ha, hf0, hf1, hf2, eB⟩ := spendingBook_stretches hB₀
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  have c1 : b.place.chain = 1 := chain_first hp _ (List.mem_map_of_mem hb)
  have no1 : ∀ x ∈ planOf F.first.blocksInOrder, x.place = e.spender.place →
      ∀ d ∈ x.rounds, ¬ (d.entry.name = "FOLD epsilon" ∨ d.entry.name = "SEND seed") := by
    intro x hx ex d hd hnm
    have hx' : x ∈ F.first.blocksInOrder.map fun b => (⟨b.place, partsCut b, b.rounds⟩ : PlanB) := hx
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hx'
    obtain rfl : b' = b := List.inj_on_of_nodup_map hn hb' hb (ex.trans hpl)
    rcases hnm with h1 | h1
    · exact hf d hd h1
    · exact hs d hd h1
  have no2 : e.spender.place ∉ F.shared.blocksInOrder.map (·.place) := fun h2 => by
    have := chain_shared hp _ h2
    rw [hpl, c1] at this
    cases this
  have no3 : e.spender.place ∉ F.second.blocksInOrder.map (·.place) := fun h3 => by
    have := chain_second hp _ h3
    rw [hpl, c1] at this
    cases this
  have in2 : ∀ x ∈ planOf F.shared.blocksInOrder, x.place ≠ e.spender.place := fun x hx ex =>
    no2 (by rw [← ex, ← planOf_places]; exact List.mem_map_of_mem hx)
  have in3 : ∀ x ∈ planOf F.second.blocksInOrder, x.place ≠ e.spender.place := fun x hx ex =>
    no3 (by rw [← ex, ← planOf_places]; exact List.mem_map_of_mem hx)
  rw [eW, eB] at he
  simp only [List.mem_append] at he
  rcases he with ((((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h1
    have hpl' : w.spender.place = b.place := hpl
    rcases List.mem_append.1 hw with h2 | h2
    · have hmem : l ∈ (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups :=
        List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨b, hb, hl⟩)
      obtain ⟨row, t', hrow, hfil⟩ := ProofFile.Honest.BookRow.linksWants_at _ 0 a
        (ProofFile.Honest.BookRow.nodup_eraseDups _ _ (Nat.le_refl _)) hmem ha
      have h3 : w ∈ a.1.filter fun y => y.spender == w.spender :=
        List.mem_filter.2 ⟨h2, by simp⟩
      rw [hfil w.spender (by rw [hpl']; exact hl)] at h3
      have h4 := partsWants_row row idx M.ends _ 0 t' w (List.mem_filter.1 h3).1 (hm _ hpl')
      exact ⟨row, hrow, congrArg MsgAt.owner h4⟩
    · exfalso
      obtain ⟨q, hq, e2⟩ := ProofFile.Honest.BookRow.loneWants_spender idx M.lone _ a.2 w h2
      obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
      have h3 := ProofFile.Honest.BookRow.planParts_place hq2
      have h4 := (List.mem_filter.1 hx).2
      have h5 : x.place = b.place := by
        rw [← h3, ← e2]
        exact hpl'
      rw [h5, hl] at h4
      cases h4
  · obtain ⟨x, hx, ex, d, hd, hnm⟩ := foldEntries_spender hf0 e h1
    rcases List.mem_append.1 hx with hx | hx
    · exact absurd (Or.inl hnm) (no1 x hx ex d hd)
    · exact absurd ex (in3 x hx)
  · obtain ⟨x, hx, ex, -⟩ := foldEntries_spender hf1 e h1
    rw [List.append_nil] at hx
    exact absurd ex (in2 x hx)
  · obtain ⟨x, hx, ex, -⟩ := foldEntries_spender hf2 e h1
    rw [List.append_nil] at hx
    exact absurd ex (in3 x hx)
  · exact absurd (splitEntry_spender (Option.mem_toList.1 h1)) no2
  · obtain ⟨x, hx, ex, d, hd, hnm⟩ := segmentCarries_ends hseg e h1
    exact absurd hnm (no1 x hx ex d hd)
  · obtain ⟨x, hx, ex, -⟩ := groupCarries_ends hcF e h1
    exact absurd ex (in2 x hx)
  · obtain ⟨x, hx, ex, -⟩ := groupCarries_ends hcO e h1
    exact absurd ex (in2 x hx)
  · obtain ⟨x, hx, ex, -⟩ := pair_ends (p := pq.1) (q := pq.2) (due_some hpq) e h1
    exact absurd ex (in3 x hx)
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h1
    exact absurd (ownFresh_behind ho) no2

/-- Where ownerOf returns, its owner is the address of the sending's round. -/
theorem ownerOf_found {name : String} {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {label : String} {pick : OnBytes.OracleNotice → Bool} {m : MsgAt}
    (h : ownerOf name bs c later label pick = some m) :
    ∃ x, ((seedRounds bs).zip c.sends).find? (fun y => y.2.label == label) = some x ∧
      addrOfRound bs x.1 = some m.owner := by
  unfold ownerOf at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨a, ha, h⟩ := opt_bind h
  obtain ⟨st, -, h⟩ := opt_bind h
  obtain ⟨fr, -, h⟩ := opt_map h
  rw [← h]
  exact ⟨x, hx, ha⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.spendingBook_stretches
#print axioms ProofFile.Honest.partWants_row
#print axioms ProofFile.Honest.partsWants_row
#print axioms ProofFile.Honest.plain_spent_row
#print axioms ProofFile.Honest.ownerOf_found
