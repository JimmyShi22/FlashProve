-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/BookAtK1.lean: THE BOOK AT A SUB-PROTOCOL OF THE KIND K1, IN THE
FIRST AND THE SHARED CHAIN: where the book's maker returns at a description whose plan passes the two
tests of Written.lean, the book has at each such member the cut [2], no row behind part 0 and no
entry that names the place as its spender (BookAt, OnePart.lean, but for the count). Under the head
the description passes them: clean_at_head.

Limits. Implications. Public data alone. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K1.Pay.Written
import Johnson.Desc.ProofFile.Honest.K1.Pay.OnePart
import Johnson.Desc.ProofFile.Honest.BookRawRows
import Johnson.Desc.ProofFile.Honest.BookAlike
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc (Block FileDescription Place KindName PlanAlike Chain)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow ProofFile.Honest.BookPlain
open P2Law.ProofPlan (WP)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

variable {Xi S Cl : Type}

theorem partsCut_two {b : Block S Cl} (hk : b.place.kind = .K1)
    (hn : b.rounds.map (·.entry.name) = ["SEND seed", "SEND answer"]) : partsCut b = [2] := by
  unfold partsCut
  rw [hk, hn]
  decide +kernel

theorem mem_cutsIn {bs : List (Block S Cl)} {b : Block S Cl} (hb : b ∈ bs)
    (hr : b.rounds ≠ []) : (b.place, partsCut b) ∈ cutsIn bs := by
  unfold cutsIn
  exact List.mem_map.2 ⟨b, List.mem_filter.2 ⟨hb, by simpa using hr⟩, rfl⟩

/-- The book's cut at a place of the maker's cuts. -/
theorem cuts_lookup {F : FileDescription Xi} (hp : F.placesOk = true) {B : ProverCoinCounts} (hc : B.cuts = cutsOf F)
    {a : Place} {c : List Nat} (hm : (a, c) ∈ cutsOf F) : B.cuts.lookup a = some c := by
  rw [hc]
  refine lookup_of_nodup _ ?_ _ _ hm
  unfold cutsOf
  rw [List.map_append, List.map_append]
  exact (orderOf_nodup hp).sublist
    (((cutsIn_places _).append (cutsIn_places _)).append (cutsIn_places _))

/-- The part that holds a round of a chain stands at a sub-protocol of the chain; where that
sub-protocol's cut is [2] it is part 0. -/
theorem addrOfRound_part : ∀ (bs : List (Block S Cl)) (i : Nat) (a : Addr),
    addrOfRound bs i = some a → ∃ b ∈ bs, b.place = a.place ∧ (partsCut b = [2] → a.part = 0)
  | [], _, _, h => by
    unfold addrOfRound at h
    cases h
  | b :: bs, i, a, h => by
    unfold addrOfRound at h
    split at h
    · have e := Option.some.inj h
      refine ⟨b, List.mem_cons_self, by rw [← e], fun hc => ?_⟩
      rw [← e]
      simp [hc]
    · obtain ⟨b', hb', e1, e2⟩ := addrOfRound_part bs _ a h
      exact ⟨b', List.mem_cons_of_mem _ hb', e1, e2⟩

/-- A list of rows whose addresses are the chain's rounds' has none behind part 0 at a member of cut
[2]. -/
theorem rows_zero {bs : List (Block S Cl)} (hn : (bs.map (·.place)).Nodup) {b : Block S Cl}
    (hb : b ∈ bs) (hc : partsCut b = [2]) {l : List (Addr × Due)}
    (hl : ∀ y ∈ l, (∃ i, addrOfRound bs i = some y.1) ∨ y.1.place ≠ b.place) :
    l.any (fun r => r.1.place == b.place && decide (1 ≤ r.1.part)) = false := by
  refine List.any_eq_false.2 fun y hy => ?_
  by_cases e : y.1.place = b.place
  · rcases hl y hy with ⟨i, hi⟩ | hne
    · obtain ⟨b', hb', ep, hz⟩ := addrOfRound_part bs i y.1 hi
      obtain rfl : b' = b := List.inj_on_of_nodup_map hn hb' hb (ep.trans e)
      simp [hz hc]
    · exact absurd e hne
  · simp [e]

/-- **The plan's two tests at the three chains.** -/
structure Clean (F : FileDescription Xi) : Prop where
  n1 : k1Names (planOf F.first.blocksInOrder) = true
  n2 : k1Names (planOf F.shared.blocksInOrder) = true
  n3 : k1Names (planOf F.second.blocksInOrder) = true
  q1 : qTest (planOf F.first.blocksInOrder) = true
  q2 : qTest (planOf F.shared.blocksInOrder) = true
  q3 : qTest (planOf F.second.blocksInOrder) = true
  p1 : placesTest k1PlacesW (planOf F.first.blocksInOrder) = true
  p2 : placesTest k1PlacesS (planOf F.shared.blocksInOrder) = true
  p3 : placesTest [] (planOf F.second.blocksInOrder) = true
  c1 : k1Count (planOf F.first.blocksInOrder) = 52
  c2 : k1Count (planOf F.shared.blocksInOrder) = 2
  c3 : k1Count (planOf F.second.blocksInOrder) = 0

theorem clean_of_alike {F : FileDescription Xi} (h : PlanAlike WP F) : Clean F := by
  have e1 := planOf_alike h.first
  have e2 := planOf_alike h.shared
  have e3 := planOf_alike h.second
  exact ⟨e1 ▸ written_first.1, e2 ▸ written_shared.1, e3 ▸ written_second.1,
    e1 ▸ written_first.2, e2 ▸ written_shared.2, e3 ▸ written_second.2,
    e1 ▸ written_places.1, e2 ▸ written_places.2.1, e3 ▸ written_places.2.2,
    e1 ▸ written_counts.1, e2 ▸ written_counts.2.1, e3 ▸ written_counts.2.2⟩

/-- **No entry of the book has its spender at a place of the kind K1.** -/
theorem no_spender_k1 {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (C : Clean F) :
    ∀ e ∈ B.ahead, e.spender.place.kind ≠ .K1 := fun e he hk =>
  no_spender hB (sendOnly_of_names C.n1 hk) (sendOnly_of_names C.n2 hk)
    (sendOnly_of_names C.n3 hk)
    (fun _ _ _ hb eq => behind_not_k1 C.q1 hb (eq ▸ hk))
    (fun _ _ _ hb eq => behind_not_k1 C.q2 hb (eq ▸ hk))
    (fun _ _ _ hb eq => behind_not_k1 C.q3 hb (eq ▸ hk)) e he rfl

theorem raw_of_whole {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) : bookRaw F p0 p1 p2 M = .ok B := by
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := ex_bindE hB
  obtain rfl := checked_ok hc
  exact hW

/-- **THE BOOK AT A MEMBER OF THE KIND K1 IN THE FIRST CHAIN.** -/
theorem bookAt_first {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (hpl : F.planOk = true) (C : Clean F)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) (hk : b.place.kind = .K1) {d : Due}
    (hd : d = dueAt (B.rowsOf 0) ⟨b.place, 0⟩) : BookAt F B 0 b d := by
  have hp : F.placesOk = true := Johnson.RunOne.Sound.placesOk_of_planOk _ hpl
  have hn : b.rounds.map (·.entry.name) = ["SEND seed", "SEND answer"] :=
    names_of C.n1 (mem_planOf hb) hk
  have hc := partsCut_two hk hn
  have hl2 : b.rounds.length = 2 := by simpa using congrArg List.length hn
  obtain ⟨r0, r1, r2, s0, s1, s2, tail, e0, -, -, w0, -, -, -, ef, -, -, ecut⟩ :=
    bookRaw_rows (raw_of_whole hB)
  have hnod : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  obtain ⟨sh1, -, -⟩ := planOk_all hpl
  refine ⟨List.mem_map_of_mem hb, hl2, ?_, ?_, ?_, ?_, hd⟩
  · rw [(shaped_parts (sh1 b hb).2).1, hl2]
  · rw [← hc]
    refine cuts_lookup hp ecut ?_
    unfold cutsOf
    refine List.mem_append_left _ (List.mem_append_left _ (mem_cutsIn hb ?_))
    intro e
    rw [e] at hl2
    cases hl2
  · show B.first.any _ = false
    rw [ef]
    refine rows_zero hnod hb hc fun y hy => ?_
    rcases List.mem_append.1 hy with h | h
    · obtain ⟨i, -, e⟩ := rowsIn_seed e0 y h
      exact .inl ⟨i, e⟩
    · obtain ⟨i, -, e⟩ := switchRows_seed w0 y h
      exact .inl ⟨i, e⟩
  · intro e he ep
    exact no_spender_k1 hB C e he (by rw [ep]; exact hk)

/-- **THE BOOK AT A MEMBER OF THE KIND K1 IN THE SHARED CHAIN.** -/
theorem bookAt_shared {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (hpl : F.planOk = true) (C : Clean F)
    {b : Block F.S₂ F.Cl} (hb : b ∈ F.shared.blocksInOrder) (hk : b.place.kind = .K1) {d : Due}
    (hd : d = dueAt (B.rowsOf 1) ⟨b.place, 0⟩) : BookAt F B 1 b d := by
  have hp : F.placesOk = true := Johnson.RunOne.Sound.placesOk_of_planOk _ hpl
  have hn : b.rounds.map (·.entry.name) = ["SEND seed", "SEND answer"] :=
    names_of C.n2 (mem_planOf hb) hk
  have hc := partsCut_two hk hn
  have hl2 : b.rounds.length = 2 := by simpa using congrArg List.length hn
  obtain ⟨r0, r1, r2, s0, s1, s2, tail, -, e1, -, -, w1, -, -, -, ef, -, ecut⟩ :=
    bookRaw_rows (raw_of_whole hB)
  have hnod : (F.shared.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).2.1
  obtain ⟨-, sh2, -⟩ := planOk_all hpl
  refine ⟨List.mem_map_of_mem hb, hl2, ?_, ?_, ?_, ?_, hd⟩
  · rw [(shaped_parts (sh2 b hb).2).1, hl2]
  · rw [← hc]
    refine cuts_lookup hp ecut ?_
    unfold cutsOf
    refine List.mem_append_left _ (List.mem_append_right _ (mem_cutsIn hb ?_))
    intro e
    rw [e] at hl2
    cases hl2
  · show B.shared.any _ = false
    rw [ef]
    refine rows_zero hnod hb hc fun y hy => ?_
    rcases List.mem_append.1 hy with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨i, -, e⟩ := rowsIn_seed e1 y h
        exact .inl ⟨i, e⟩
      · obtain ⟨i, -, e⟩ := switchRows_seed w1 y h
        exact .inl ⟨i, e⟩
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h
      obtain ⟨i, hbf⟩ := ownFresh_pq ho
      refine .inr ?_
      exact fold_off (sendOnly_of_names C.n2 hk)
        (fun _ _ _ hb' eq => behind_not_k1 C.q2 hb' (eq ▸ hk)) hbf (Or.inl rfl)
  · intro e he ep
    exact no_spender_k1 hB C e he (by rw [ep]; exact hk)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head, at any return of the maker, at any filling: the description, its plan's tests
and the book's maker.** -/
theorem head_pack (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.F.planOk = true ∧ Clean A.F ∧ ∃ p0 p1 p2 M, bookWhole A.F p0 p1 p2 M = .ok A.B := by
  obtain ⟨-, eF⟩ := atPure_at_laid h.laid hA
  refine ⟨atPure_planOk h.laid hA, ?_, Zp.made.proof.1, Zp.made.proof.2.1, Zp.made.proof.2.2,
    mergesByName cF.blocksInOrder, ?_⟩
  · rw [eF]
    exact clean_of_alike (K14.planAlike_at_head h)
  · rw [eF]
    exact K14.atPure_book_at_head h hA

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.no_spender_k1
#print axioms ProofFile.Honest.K1.Pay.bookAt_first
#print axioms ProofFile.Honest.K1.Pay.bookAt_shared
#print axioms ProofFile.Honest.K1.Pay.head_pack
