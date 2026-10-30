-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the whole book spends no coin of a proximity test's parts.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/BookAtTest.lean: every entry of the whole book (bookWhole,
Honest/BookWhole.lean) that spends coins has its owner at a place that is no proximity test's, under
one public test on each chain's sendings. So noneSpent holds at a part of such a test: the premise of
the frame's sentence fresh at it.

Why not bookWhole_spent_nil (BookOwners.lean): that asks a sub-protocol with no round "SEND seed", and
a proximity test has such rounds, one for each switch. What keeps its sendings off the spending
entries: a fold's entries skip the sendings that the label marks as a switch (foldEntries), and the
other entries look their owners up by label.

  sendsOffTests        the public test on a chain's sendings
  namesSought          the labels that the book looks up in the first chain
  addrIn_planOf, rounds_planOf, off_of_test, owner_off, linksWants_off, fold_off, split_off   the pieces
  bookWhole_owner_off  the statement at every spending entry
  bookWhole_noneSpent  the test on the book at an address of such a test

That bookWhole returns is a premise. Nothing here evaluates the test. No property of the protocol is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookOwners
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Place KindName)
open ProofFile.Honest ProofFile.Honest.BookShared ProofFile.Honest.BookRow
open ProofFile.Honest.Small (noneSpent)

variable {Xi S Cl : Type}

/-- **The public test on a chain's sendings.** Each sending either is a switch and none of the labels
that the book looks up, or stands at a place of no proximity test. -/
def sendsOffTests (bs : List (Block S Cl)) (c : Johnson.G.ChainSends) (names : List String) : Bool :=
  ((seedRounds bs).zip c.sends).all fun x =>
    (isSwitch x.2.label && !names.contains x.2.label) ||
      (addrOfRound bs x.1).all fun a => a.place.kind != .K12

/-- The labels that the book looks up in the first chain. -/
def namesSought (bs : List (Block S Cl)) : List String :=
  "link 0, moment 0" :: ((bs.filterMap (·.place.link)).eraseDups.map fun l => s!"link {l}, moment 0")

/-- A list of plans finds a round's address as the blocks do. -/
theorem addrIn_planOf : ∀ (bs : List (Block S Cl)) (i : Nat), addrIn (planOf bs) i = addrOfRound bs i
  | [], _ => rfl
  | b :: l, i => by
    show addrIn (⟨b.place, partsCut b, b.rounds⟩ :: planOf l) i = _
    unfold addrIn addrOfRound
    dsimp only
    split
    · rfl
    · exact addrIn_planOf l _

theorem rounds_planOf (bs : List (Block S Cl)) :
    (planOf bs).flatMap (·.rounds) = bs.flatMap (·.rounds) := by
  unfold planOf
  rw [List.flatMap_map]

/-- What the test gives at a member of the zip. -/
theorem off_of_test {bs : List (Block S Cl)} {c : Johnson.G.ChainSends} {names : List String}
    (T : sendsOffTests bs c names = true) {x : Nat × Johnson.G.Sending}
    (hx : x ∈ (seedRounds bs).zip c.sends)
    (hl : isSwitch x.2.label = false ∨ x.2.label ∈ names) {a : Addr}
    (ha : addrOfRound bs x.1 = some a) : a.place.kind ≠ .K12 := by
  have h := List.all_eq_true.1 T x hx
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exfalso
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases hl with e | e
    · rw [e] at h1
      cases h1
    · have : names.contains x.2.label = true := by simpa using e
      rw [this] at h2
      cases h2
  · rw [ha] at h
    simpa using h

/-- **A message that is looked up by a label of the list has its owner off the tests.** -/
theorem owner_off {bs : List (Block S Cl)} {c : Johnson.G.ChainSends} {names : List String}
    (T : sendsOffTests bs c names = true) {name : String} {later : List Fmt.DeclaredRound}
    {label : String} {pick : OnBytes.OracleNotice → Bool} {m : MsgAt} (hl : label ∈ names)
    (h : ownerOf name bs c later label pick = some m) : m.owner.place.kind ≠ .K12 := by
  unfold ownerOf at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  dsimp only at h
  obtain ⟨a, ha, h⟩ := opt_bind h
  obtain ⟨st, -, h⟩ := opt_bind h
  obtain ⟨free, -, h⟩ := opt_map h
  have hz := List.mem_of_find?_eq_some hx
  have hlab : x.2.label = label := by simpa using List.find?_some hx
  rw [← h]
  exact off_of_test T hz (Or.inr (hlab ▸ hl)) ha

/-- The segments' ranges are of messages off the tests. -/
theorem linksWants_off {bs : List (Block S Cl)} {c : Johnson.G.ChainSends} {names : List String}
    (T : sendsOffTests bs c names = true) {later : List Fmt.DeclaredRound} {idx : MsgAt}
    {merges : List Addr} (hi : idx.owner.place.kind ≠ .K12) :
    ∀ (ls : List Nat) (_ : ∀ l ∈ ls, s!"link {l}, moment 0" ∈ names) (t : Nat)
      (a : List Want × Nat), linksWants bs c later idx merges ls t = .ok a →
      ∀ w ∈ a.1, w.msg.owner.place.kind ≠ .K12
  | [], _, t, a, h => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e]
    intro w hw
    cases hw
  | l :: ls, hn, t, a, h => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      obtain ⟨y, hy, e⟩ := ex_mapE h
      rw [← e]
      intro w hw
      rcases List.mem_append.1 hw with h1 | h1
      · rcases partsWants_msg row idx merges _ _ _ w h1 with e1 | e1
        · rw [e1]
          exact owner_off T (hn l (List.mem_cons_self ..)) hrow
        · rw [e1]
          exact hi
      · exact linksWants_off T hi ls (fun l' h' => hn l' (List.mem_cons_of_mem _ h')) _ y hy w h1

/-- **The owner of a fold's spending entry is off the tests.** -/
theorem fold_off {bs : List (Block S Cl)} {later : List PlanB} {c : Johnson.G.ChainSends}
    {names : List String} (T : sendsOffTests bs c names = true) {l : List Ahead}
    (h : foldEntries (planOf bs) later c = .ok l) : ∀ e ∈ l, e.owner.place.kind ≠ .K12 := by
  unfold foldEntries at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, a.owner.place.kind ≠ .K12) ?_ hll
      inner hin a ha
    intro x hxm r hr
    have hz := (List.mem_filter.1 hxm).1
    have hns : isSwitch x.2.label = false := by
      have := (List.mem_filter.1 hxm).2
      simpa using this
    have hseeds : ((planOf bs).flatMap (·.rounds)).zipIdx.filter
        (fun r => r.1.entry.name == "SEND seed") =
        (bs.flatMap (·.rounds)).zipIdx.filter (fun r => r.1.entry.name == "SEND seed") := by
      rw [rounds_planOf]
    have hz' : x ∈ (seedRounds bs).zip c.sends := by
      unfold seedRounds
      rw [← hseeds]
      exact hz
    refine mapM_all _ r ?_ hr
    intro j _ b hb
    try dsimp only at hb
    split at hb
    · cases hb
    · cases hb
    · split at hb
      · rename_i o p st ho hp hst
        have e2 := Except.ok.inj hb
        rw [addrIn_planOf] at ho
        rw [← e2]
        exact off_of_test T hz' (Or.inl hns) ho
      · cases hb

/-- The owner of the shared split's coin is off the tests. -/
theorem split_off {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    (T : sendsOffTests bs c ["Omega"] = true) {e : Ahead} (h : splitEntry bs c = some e) :
    e.owner.place.kind ≠ .K12 := by
  unfold splitEntry at h
  dsimp only at h
  obtain ⟨p, -, h⟩ := opt_bind h
  obtain ⟨m, hm, h⟩ := opt_map h
  rw [← h]
  exact owner_off T (List.mem_singleton.2 rfl) hm

/-- **WHOSE COINS THE WHOLE BOOK SPENDS: no proximity test's.** -/
theorem bookWhole_owner_off {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B)
    (T0 : sendsOffTests F.first.blocksInOrder p0 (namesSought F.first.blocksInOrder) = true)
    (T1 : sendsOffTests F.shared.blocksInOrder p1 ["Omega"] = true)
    (T2 : sendsOffTests F.second.blocksInOrder p2 [] = true) :
    ∀ e ∈ B.ahead, e.once = true → e.owner.place.kind ≠ .K12 := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, hm1, hseg, hiF, hcF, hiO, hcO, hpq,
    htail, eW⟩ := bookRaw_ahead hW
  obtain ⟨idx, a, f0, f1, f2, hidx, ha, hfree, hf0, hf1, hf2, eB⟩ := spendingBook_open hB
  have hi : idx.owner.place.kind ≠ .K12 := owner_off T0 (List.mem_cons_self ..) hidx
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
    rcases List.mem_append.1 hw with h1 | h1
    · exact linksWants_off T0 hi _ (fun l hl => List.mem_cons_of_mem _ (List.mem_map.2 ⟨l, hl, rfl⟩))
        _ a ha w h1
    · have e1 := loneWants_msg idx M.lone _ _ w h1
      show w.msg.owner.place.kind ≠ .K12
      rw [e1]
      exact hi
  · intro e he _
    exact fold_off T0 hf0 e he
  · intro e he _
    exact fold_off T1 hf1 e he
  · intro e he _
    exact fold_off T2 hf2 e he
  · intro e he _
    have hs : splitEntry F.shared.blocksInOrder p1 = some e := by
      cases hsp : splitEntry F.shared.blocksInOrder p1 with
      | none =>
        rw [hsp] at he
        cases he
      | some e' =>
        rw [hsp] at he
        rw [mem_one he]
    exact split_off T1 hs
  · exact carried (segmentCarries_once hseg)
  · exact carried (groupCarries_once hcF)
  · exact carried (groupCarries_once hcO)
  · exact carried carryPair_once
  · refine carried ?_
    intro e he
    obtain ⟨o, -, rfl⟩ := List.mem_map.1 he
    rfl

/-- **No entry spends of a part of a proximity test.** -/
theorem bookWhole_noneSpent {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B)
    (T0 : sendsOffTests F.first.blocksInOrder p0 (namesSought F.first.blocksInOrder) = true)
    (T1 : sendsOffTests F.shared.blocksInOrder p1 ["Omega"] = true)
    (T2 : sendsOffTests F.second.blocksInOrder p2 [] = true) (o : Addr) (ho : o.place.kind = .K12) :
    noneSpent B o = true := by
  refine List.all_eq_true.2 fun e he => ?_
  cases hon : e.once with
  | false => rfl
  | true =>
    have hk := bookWhole_owner_off h T0 T1 T2 e he hon
    have hne : (e.owner == o) = false := by
      rw [beq_eq_false_iff_ne]
      intro hc
      rw [hc] at hk
      exact hk ho
    simp [hne]

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.sendsOffTests
#print axioms ProofFile.Honest.K12.Sim2.bookWhole_owner_off
#print axioms ProofFile.Honest.K12.Sim2.bookWhole_noneSpent
