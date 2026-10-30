-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/HandedW.lean: WHAT THE LENDING HANDS,
and that the stretch holds the
sender's coins. General in the book and the coins. No run is named.

  `look_last_first`, `look_last_shared`   the last chain sees an owner of the first chain as that
                 chain sees it, and an owner of the shared chain, where the first has no row for it,
                 as the shared chain sees it: one purse
  `carried_is_cut`, `spent_is_cut`   what `lendPart` hands for carried or spent entry number n is
                 `stretchOf` of the cut
  `spent_held`   the join at a spent entry: its coins are the sender's from its start on
  `lent_reads_owner`   a stretch cut out of an owner's coins at `s` reads, number by number, what
                 the owner's own coins read from `s` on: the premises `hf`, `he` of
                 `wMember_mem_rows` and `first_member_rows`, where the member's `startR` is the
                 entry's start
  `member_held_shared`   the like of a stretch from 0 on, cut out of a shared chain's part's coins
  `member_held`   THE JOIN, at a book: at a message's own coins the stretch that the frame carries
                 to a part reads what the sender's own coins read, where the entry's owner has a row
                 of the first chain alone, of the sender's count, and the entry's start and count
                 are the message's

Limits.
- That the owner's own coins are what `lendPart` hands it, and the entry's start and count are those
  of the message, are the caller's: the written starts are AtFullSide/K12/HandedAtHeadW.lean's.
- That `c₀` is what `lendPart` hands the sender is `lendPart`'s text: the own cut at its count. No
  run is named.
- Omega's member is not of K1's form: its rows read `c.e` from 0 through `laid`: HeldAtHeadW.lean
  (AtFullSide/K12/) joins `member_held_shared` to `mem_rows_below` (LaidBelow.lean).
- Nothing on what a half plays.
- What may be said of this pair on hiding stands in the head of HalfW.lean in this folder.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.SendersW
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowLens

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

/-- **The last chain sees an owner of the first chain as that chain sees it.** -/
theorem look_last_first {B : ProverCoinCounts} (k : Coins B) (a : Addr) {y : (d : Due) × Cs d}
    (h : Purse.find? B.first k.first a = some y) : k.look 2 a = k.look 0 a := by
  simp [Coins.look, h]

/-- **And an owner of the shared chain, where the first has no row for it, as the shared chain
sees it.** -/
theorem look_last_shared {B : ProverCoinCounts} (k : Coins B) (a : Addr) {y : (d : Due) × Cs d}
    (h₀ : Purse.find? B.first k.first a = none) (h : Purse.find? B.shared k.shared a = some y) :
    k.look 2 a = k.look 1 a := by
  simp [Coins.look, sharedLook, h₀, h]

/-- **A stretch cut out of an owner's coins reads what the owner's own coins read from its start
on.** c₀: the owner's own, cut from 0; x: the entry's, cut at s. -/
theorem lent_reads_owner {d t n : Due} (c : Cs d) (s : Due) {c₀ : Cs t} {x : Cs n}
    (h₀ : c.cut ⟨0, 0⟩ t = some c₀) (hx : c.cut s n = some x) (hf : s.f + n.f ≤ t.f)
    (he : s.e + n.e ≤ t.e) :
    (∀ i, i < n.f → K1.cf c₀ (s.f + i) = (stretchOf x).f i) ∧
      ∀ i, i < n.e → K1.ce c₀ (s.e + i) = (stretchOf x).e i := by
  unfold Cs.cut at h₀ hx
  split at h₀
  · split at hx
    · obtain rfl := Option.some.inj h₀
      obtain rfl := Option.some.inj hx
      constructor
      · intro i hi
        have h : s.f + i < t.f := by omega
        simp [K1.cf, stretchOf, h, hi]
      · intro i hi
        have h : s.e + i < t.e := by omega
        simp [K1.ce, stretchOf, h, hi]
    · cases hx
  · cases h₀

/-- **What `lendPart` hands for carried entry number n is `stretchOf` of the cut.** -/
theorem carried_is_cut {V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {a : Addr} {p : Part V W X} {y : p.Coins}
    (hl : lendPart B rows look a p = .ok y) {n : Nat} {e : Ahead} (he : (carryE B a)[n]? = some e) :
    ∃ x : Cs e.count, (look e.owner).2.cut e.start e.count = some x ∧
      stretches p.carries y.2.2 n = stretchOf x := by
  unfold lendPart at hl
  simp only at hl
  split at hl
  · cases hl
  · split at hl
    · cases hl
    · rename_i own _
      obtain ⟨sp, -, hl⟩ := ProofFile.Honest.exBind_ok hl
      obtain ⟨ca, hca, rfl⟩ := ProofFile.Honest.exMap_ok hl
      exact (ProofFile.Honest.K12.lend_stretch look p.carries _ ca hca n e he).2

/-- **What `lendPart` hands for spent entry number n is `stretchOf` of the cut.** -/
theorem spent_is_cut {V W X : Type} {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {a : Addr} {p : Part V W X} {y : p.Coins}
    (hl : lendPart B rows look a p = .ok y) {n : Nat} {e : Ahead} (he : (spentE B a)[n]? = some e) :
    ∃ x : Cs e.count, (look e.owner).2.cut e.start e.count = some x ∧
      stretches p.spends y.2.1 n = stretchOf x := by
  unfold lendPart at hl
  simp only at hl
  split at hl
  · cases hl
  · split at hl
    · cases hl
    · rename_i own _
      obtain ⟨sp, hsp, hl⟩ := ProofFile.Honest.exBind_ok hl
      obtain ⟨ca, -, rfl⟩ := ProofFile.Honest.exMap_ok hl
      exact (ProofFile.Honest.K12.lend_stretch look p.spends _ sp hsp n e he).2

/-- **The join at a spent entry**, of an owner of the first chain alone, at a count within its
owner's: its coins read the sender's own from its start on. -/
theorem spent_held {V W X : Type} {B : ProverCoinCounts} (k : Coins B) {a : Addr} {p : Part V W X}
    {y : p.Coins} (hl : lendPart B (B.rowsOf 2) (k.look 2) a p = .ok y) {n : Nat} {e : Ahead}
    (he : (spentE B a)[n]? = some e) {t : Due} (hd : dueAt B.first e.owner = t)
    (h₂ : B.shared.any (fun r => r.1 == e.owner) = false)
    (h₃ : B.second.any (fun r => r.1 == e.owner) = false)
    (hbf : e.start.f + e.count.f ≤ t.f) (hbe : e.start.e + e.count.e ≤ t.e) {c₀ : Cs t}
    (h₀ : (k.look 0 e.owner).2.cut ⟨0, 0⟩ t = some c₀) :
    (∀ i, i < e.count.f → K1.cf c₀ (e.start.f + i) = (stretches p.spends y.2.1 n).f i) ∧
    ∀ i, i < e.count.e → K1.ce c₀ (e.start.e + i) = (stretches p.spends y.2.1 n).e i := by
  obtain ⟨x, hx, hst⟩ := spent_is_cut hl he
  obtain ⟨get, -, -, -, hk⟩ := Coins.lens₀ e.owner _ hd h₂ h₃
  rw [hk 2 (Or.inr rfl) k] at hx
  rw [hk 0 (Or.inl rfl) k] at h₀
  rw [hst]
  exact lent_reads_owner (get k) e.start h₀ hx hbf hbe

/-- **THE JOIN AT A BOOK.** At a message's own coins the stretch that the frame carries to a part of
the last chain reads what the sender's own coins read. -/
theorem member_held {V W X : Type} {B : ProverCoinCounts} (k : Coins B) {a : Addr} {p : Part V W X}
    {y : p.Coins} (hl : lendPart B (B.rowsOf 2) (k.look 2) a p = .ok y) {n : Nat} {e : Ahead}
    (he : (carryE B a)[n]? = some e) (P : VerifiableInference.Desc.K1.Par)
    (ride : Nat → Option K1.Ride) (m : Nat) (hm : m < P.sent.size)
    (hs : e.start = K1.startR P ride m)
    (hc : e.count = K1.dueMsg P.codes (Johnson.Prover.Send.shapeAt P m) (ride m))
    (hd : dueAt B.first e.owner = K1.dueR P ride)
    (h₂ : B.shared.any (fun r => r.1 == e.owner) = false)
    (h₃ : B.second.any (fun r => r.1 == e.owner) = false)
    {c₀ : Cs (K1.dueR P ride)}
    (h₀ : (k.look 0 e.owner).2.cut ⟨0, 0⟩ (K1.dueR P ride) = some c₀) :
    (∀ i, i < (K1.dueMsg P.codes (Johnson.Prover.Send.shapeAt P m) (ride m)).f →
      K1.cf c₀ ((K1.startR P ride m).f + i) = (stretches p.carries y.2.2 n).f i) ∧
    ∀ i, i < (K1.dueMsg P.codes (Johnson.Prover.Send.shapeAt P m) (ride m)).e →
      K1.ce c₀ ((K1.startR P ride m).e + i) = (stretches p.carries y.2.2 n).e i := by
  obtain ⟨x, hx, hst⟩ := carried_is_cut hl he
  obtain ⟨get, -, -, -, hk⟩ := Coins.lens₀ e.owner _ hd h₂ h₃
  rw [hk 2 (Or.inr rfl) k] at hx
  rw [hk 0 (Or.inl rfl) k] at h₀
  have hbf : e.start.f + e.count.f ≤ (K1.dueR P ride).f := by
    rw [hs, hc]
    exact K1.msg_in_f P ride m hm
  have hbe : e.start.e + e.count.e ≤ (K1.dueR P ride).e := by
    rw [hs, hc]
    exact K1.msg_in_e P ride m hm
  obtain ⟨f1, f2⟩ := lent_reads_owner (get k) e.start h₀ hx hbf hbe
  rw [hst, ← hs]
  refine ⟨fun i hi => f1 i ?_, fun i hi => f2 i ?_⟩
  · rw [hc]
    exact hi
  · rw [hc]
    exact hi

/-- **The join at a shared chain's owner, from 0 on.** What the frame carries reads the owner's own
coins below the entry's count. -/
theorem member_held_shared {V W X : Type} {B : ProverCoinCounts} (k : Coins B) {a : Addr} {p : Part V W X}
    {y : p.Coins} (hl : lendPart B (B.rowsOf 2) (k.look 2) a p = .ok y) {n : Nat} {e : Ahead}
    (he : (carryE B a)[n]? = some e) {t : Due} (hd : dueAt B.shared e.owner = t)
    (h₁ : B.first.any (fun r => r.1 == e.owner) = false)
    (h₃ : B.second.any (fun r => r.1 == e.owner) = false) (hs : e.start = ⟨0, 0⟩)
    (hbf : e.count.f ≤ t.f) (hbe : e.count.e ≤ t.e) {c₀ : Cs t}
    (h₀ : (k.look 1 e.owner).2.cut ⟨0, 0⟩ t = some c₀) :
    ∀ i, i < e.count.e → (stretches p.carries y.2.2 n).e i = (stretchOf c₀).e i := by
  obtain ⟨x, hx, hst⟩ := carried_is_cut hl he
  obtain ⟨get, -, -, -, hk⟩ := Coins.lens₁ e.owner _ hd h₁ h₃
  rw [hk 2 (Or.inr rfl) k] at hx
  rw [hk 1 (Or.inl rfl) k] at h₀
  obtain ⟨-, f2⟩ := lent_reads_owner (get k) e.start h₀ hx
    (by rw [hs]; simpa using hbf) (by rw [hs]; simpa using hbe)
  intro i hi
  have q := f2 i hi
  rw [hs, Nat.zero_add] at q
  rw [hst, ← q]
  rfl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.look_last_first
#print axioms ProofFile.Honest.K12.AtProof.look_last_shared
#print axioms ProofFile.Honest.K12.AtProof.lent_reads_owner
#print axioms ProofFile.Honest.K12.AtProof.carried_is_cut
#print axioms ProofFile.Honest.K12.AtProof.spent_is_cut
#print axioms ProofFile.Honest.K12.AtProof.spent_held
#print axioms ProofFile.Honest.K12.AtProof.member_held
#print axioms ProofFile.Honest.K12.AtProof.member_held_shared
