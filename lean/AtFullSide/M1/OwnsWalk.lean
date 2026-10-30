-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the owners of the written book, by the makers' structure.
/-
AtFullSide/M1/OwnsWalk.lean: the 80 owners of the written entries rawAheadW: owners_written, by the makers' structure (no walk of the 13,116 entries): the kernel evaluates only the written pieces, 26 messages and 189 senders; ownersW_is: they are K1's 52 senders, the 25 code
switches and three on the shared chain, each at part 0. Statements at written values. No property of the protocol is claimed.
-/
import AtFullSide.K14.RawEntriesKit
import Johnson.SendSim.Seat.ReadsAtWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.M1.Own
open ProofFile.Honest ProofFile.Honest.BookShared ProofFile.Honest.K14 AtFullSide.K14
open OnBytes.SendSim.Seat (parsW)
open ProofFile.Honest.K2.Law (placesW)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The 80 owners of the written entries. -/
def ownersW : List Addr := [
  ⟨⟨1, some 0, 1, .K1⟩, 0⟩,
  ⟨⟨1, some 0, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 0, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 1, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 1, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 2, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 2, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 3, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 3, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 4, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 4, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 5, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 5, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 6, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 6, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 7, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 7, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 8, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 8, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 9, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 9, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 10, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 10, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 11, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 11, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 12, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 12, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 13, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 13, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 14, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 14, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 15, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 15, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 16, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 16, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 17, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 17, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 18, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 18, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 19, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 19, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 20, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 20, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 21, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 21, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 22, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 22, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 23, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 23, 6, .K1⟩, 0⟩,
  ⟨⟨1, some 24, 5, .K1⟩, 0⟩,
  ⟨⟨1, some 24, 7, .K1⟩, 0⟩,
  ⟨⟨1, none, 4, .K1⟩, 0⟩,
  ⟨⟨1, some 1, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 2, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 3, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 4, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 5, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 6, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 7, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 8, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 9, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 10, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 11, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 12, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 13, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 14, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 15, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 16, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 17, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 18, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 19, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 20, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 21, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 22, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 23, 1, .K2⟩, 0⟩,
  ⟨⟨1, some 24, 2, .K2⟩, 0⟩,
  ⟨⟨1, none, 1, .K2⟩, 0⟩,
  ⟨⟨2, none, 2, .K1⟩, 0⟩,
  ⟨⟨2, none, 5, .K1⟩, 0⟩,
  ⟨⟨2, none, 10, .K12⟩, 0⟩]

/-- A property of the index-mask message and of every link's mask row holds of the message of every stretch of the links. -/
theorem linksWants_msg_of {S Cl : Type} {bs : List (VerifiableInference.Desc.Block S Cl)}
    {c : Johnson.G.ChainSends} {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr}
    {P : MsgAt → Prop} (hidx : P idx) :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat),
      (∀ l ∈ ls, ∀ row, ownerOf maskRowRun bs c later s!"link {l}, moment 0" isMaskRowMsg = some row →
        P row) →
      linksWants bs c later idx merges ls t = .ok r → ∀ w ∈ r.1, P w.msg
  | [], t, r, _, h, w, hw => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e] at hw
    cases hw
  | l :: ls, t, r, hr, h, w, hw => by
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
          exact hr l List.mem_cons_self row hrow
        · rw [e1]
          exact hidx
      · exact linksWants_msg_of hidx ls _ y (fun l' hl' => hr l' (List.mem_cons_of_mem _ hl')) hy w h1

/-- Each stretch's entry spends, and its owner is the index-mask message's or a link's mask row's. -/
theorem wants_owner_is : ∀ e ∈ rawWantsW.map (·.entry), e.once = true ∧
    (e.owner = rawIdxW.owner ∨ ∃ x ∈ rawRowsW, e.owner = x.2.owner) := by
  intro e he
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
  refine ⟨rfl, ?_⟩
  show w.msg.owner = rawIdxW.owner ∨ ∃ x ∈ rawRowsW, w.msg.owner = x.2.owner
  obtain ⟨a, ha⟩ := rawLinksWants_returns
  have ea : rawLinksW = a := rawLinks_ok ha
  unfold rawWantsW at hw
  rw [ea] at hw
  rcases List.mem_append.1 hw with h | h
  · refine linksWants_msg_of (bs := WP.first.blocksInOrder) (c := proofSendsFull.1) (later := rawLater)
      (idx := rawIdxW) (merges := (mergesByName WP.first.blocksInOrder).ends)
      (P := fun m => m.owner = rawIdxW.owner ∨ ∃ x ∈ rawRowsW, m.owner = x.2.owner)
      (Or.inl rfl) _ 0 a ?_ ha w h
    intro l hl row hrow
    rw [rawLinks_written, ← rawRowsW_numbers] at hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    rw [rawRows_written x hx] at hrow
    obtain rfl := Option.some.inj hrow
    exact Or.inr ⟨x, hx, rfl⟩
  · rw [loneWants_msg _ _ _ _ w h]
    exact Or.inl rfl

set_option maxRecDepth 1000000 in
/-- The written pieces have their owners among the 80. -/
theorem owners_short : (rawShortW.all fun e => ownersW.contains e.owner) = true := by
  decide +kernel

/-- So has the index-mask message. -/
theorem owners_idx : ownersW.contains rawIdxW.owner = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- So have the 25 mask rows. -/
theorem owners_rows : (rawRowsW.all fun x => ownersW.contains x.2.owner) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- So have the senders of the 189 messages. -/
theorem owners_sent : (sentFirstW.all fun m => ownersW.contains m.sender) = true := by
  decide +kernel

/-- **EVERY ENTRY OF THE WRITTEN BOOK HAS ONE OF THE 80 FOR OWNER.** A stretch's owner is the sender of
a message among 26 (wants_owner_is), a carrying entry's is a sender among the 189
(segmentCarries_owner), and only the written pieces and these senders are evaluated. -/
theorem owners_written : (rawAheadW.all fun e => ownersW.contains e.owner) = true := by
  refine rawAll_whole _ ?_ ?_ owners_short
  · refine List.all_eq_true.2 fun e he => ?_
    show ownersW.contains e.owner = true
    rcases (wants_owner_is e he).2 with h | ⟨x, hx, h⟩
    · rw [h]
      exact owners_idx
    · rw [h]
      exact List.all_eq_true.1 owners_rows x hx
  · refine List.all_eq_true.2 fun e he => ?_
    show ownersW.contains e.owner = true
    obtain ⟨m, hm, h⟩ := segmentCarries_owner rawSeg_returns e he
    rw [h]
    exact List.all_eq_true.1 owners_sent m hm

set_option maxRecDepth 1000000 in
/-- They are K1's 52 senders, the 25 code switches, the two sendings and the fold's own table on the shared chain, each at part 0. -/
theorem ownersW_is : ownersW = (parsW.map fun P => (⟨P.place, 0⟩ : Addr)) ++
    (placesW.map fun p => (⟨p.place, 0⟩ : Addr)) ++
    [⟨⟨2, none, 2, .K1⟩, 0⟩, ⟨⟨2, none, 5, .K1⟩, 0⟩, ⟨⟨2, none, 10, .K12⟩, 0⟩] := by
  decide +kernel

end AtFullSide.M1.Own

#print axioms AtFullSide.M1.Own.owners_written
#print axioms AtFullSide.M1.Own.ownersW_is
