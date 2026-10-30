-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Members.lean: `LookOk` (Honest/Law/Rule/MemberLay.lean) holds
at a chain's lists of parts (`look_ok`), at `preOf` (Honest/Rule.lean) of each sub-protocol's place.
What a session looks up by address (its simulators,
`tellerOf`; which places have a list of parts) and what the honest side looks up (`realIn`,
Honest/Law/Rule/Real.lean) are the lists' own parts and simulators. The hypotheses: every list has
its side at the description's own sub-protocol, and that side fits; no two lists are at one place;
and no two sub-protocols of the description's list are.

  1  `find_none_flat`, `find_flat`   a search through concatenated lists
  2  `members_ge`, `members_find`, `members_sim`, `row_place`   the `Member`s of a list of parts by
     their numbers; each one's simulator by its address
  3  `side_ok`   what the side of such a list is
  4  `look_ok`   the main lemma

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.MemberLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {S Cl V W Y Pb : Type}

/-! ## 1 A search through concatenated lists -/

theorem find_none_flat {α β : Type} (f : α → List β) (p : β → Bool) : ∀ l : List α,
    (∀ y ∈ l, (f y).find? p = none) → (l.flatMap f).find? p = none
  | [], _ => rfl
  | y :: l, h => by
    rw [List.flatMap_cons, List.find?_append, h y (List.mem_cons.2 (Or.inl rfl)),
      find_none_flat f p l fun z hz => h z (List.mem_cons_of_mem _ hz)]
    rfl

/-- Where all lists but x's hold nothing that is sought, what is found is what x's list gives. -/
theorem find_flat {α β : Type} (f : α → List β) (p : β → Bool) (x : α) : ∀ l : List α, x ∈ l →
    (∀ y ∈ l, y ≠ x → (f y).find? p = none) → (l.flatMap f).find? p = (f x).find? p
  | [], h, _ => by cases h
  | y :: l, hx, h => by
    rw [List.flatMap_cons, List.find?_append]
    by_cases hy : y = x
    · subst hy
      cases hf : (f y).find? p with
      | some b => rfl
      | none =>
        have : (l.flatMap f).find? p = none := find_none_flat f p l fun z hz => by
          by_cases hz' : z = y
          · rw [hz']
            exact hf
          · exact h z (List.mem_cons_of_mem _ hz) hz'
        rw [this]
        rfl
    · rw [h y (List.mem_cons.2 (Or.inl rfl)) hy]
      have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with e | e
        · exact absurd e.symm hy
        · exact e
      exact find_flat f p x l hx' fun z hz => h z (List.mem_cons_of_mem _ hz)

/-! ## 2 The `Member`s of a list of parts -/

theorem members_ge : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), ∀ u ∈ membersOf row j rs, j ≤ u.number
  | [], _, _, u, hu => by cases hu
  | q :: row, j, rs, u, hu => by
    rcases List.mem_cons.1 hu with e | e
    · rw [e]
    · have := members_ge row (j + 1) _ u e
      omega

/-- A `Member` is found by its number. -/
theorem members_find : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), ∀ u ∈ membersOf row j rs,
    ((membersOf row j rs).find? fun t => t.number == u.number) = some u
  | [], _, _, u, hu => by cases hu
  | q :: row, j, rs, u, hu => by
    show ((⟨j, rs.take q.1.moves.length, q.1, q.2⟩ :: membersOf row (j + 1)
      (rs.drop q.1.moves.length) : List (Member V W Y Pb)).find? fun t =>
        t.number == u.number) = some u
    rcases List.mem_cons.1 hu with e | e
    · rw [e, List.find?_cons_of_pos (by simp)]
    · have hge := members_ge row (j + 1) _ u e
      rw [List.find?_cons_of_neg (by
        show ¬ ((j == u.number) = true)
        simp only [beq_iff_eq]
        omega)]
      exact members_find row (j + 1) _ u e

/-- A `Member`'s simulator is found by the `Member`'s address, where each simulator of the list
names its part's address. -/
theorem members_sim (pl : Place) : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)),
    (∀ s ∈ row.zipIdx j, s.1.2.addr = ⟨pl, s.2⟩) → ∀ u ∈ membersOf row j rs,
    ((row.map (·.2)).find? fun t => t.addr == ⟨pl, u.number⟩) = some u.sim
  | [], _, _, _, u, hu => by cases hu
  | q :: row, j, rs, h, u, hu => by
    have hq : q.2.addr = ⟨pl, j⟩ :=
      h (q, j) (by rw [List.zipIdx_cons]; exact List.mem_cons.2 (Or.inl rfl))
    have ht : ∀ s ∈ row.zipIdx (j + 1), s.1.2.addr = ⟨pl, s.2⟩ := fun s hs =>
      h s (by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hs)
    rw [List.map_cons]
    rcases List.mem_cons.1 hu with e | e
    · rw [e, List.find?_cons_of_pos (by rw [hq]; simp)]
    · have hge := members_ge row (j + 1) _ u e
      rw [List.find?_cons_of_neg (by
        rw [hq]
        simp only [beq_iff_eq, Addr.mk.injEq, true_and]
        omega)]
      exact members_sim pl row (j + 1) _ ht u e

/-- Every simulator of such a list names the list's place. -/
theorem row_place (pl : Place) : ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat),
    (∀ s ∈ row.zipIdx j, s.1.2.addr = ⟨pl, s.2⟩) → ∀ t ∈ row.map (·.2), t.addr.place = pl
  | [], _, _, t, ht => by cases ht
  | q :: row, j, h, t, ht => by
    rcases List.mem_cons.1 ht with e | e
    · rw [e, h (q, j) (by rw [List.zipIdx_cons]; exact List.mem_cons.2 (Or.inl rfl))]
    · exact row_place pl row (j + 1) (fun s hs =>
        h s (by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hs)) t e

/-! ## 3 The side of a list of parts -/

theorem side_ok {Bk : ProverCoinCounts} {L : Lettered Bk S Cl V W Y Pb} {bs : List (Block S Cl)}
    {fs : List (Fall S)} {σ : Side S Cl V W Y Pb} (h : L.side bs fs = some σ) :
    σ.block ∈ bs ∧ σ.block.place = L.place ∧ σ.row = L.row := by
  unfold Lettered.side Side.seated at h
  cases hb : bs.find? fun b => b.place == L.place with
  | none =>
    rw [hb] at h
    cases h
  | some b =>
    rw [hb] at h
    cases h
    have hq₀ := List.find?_some hb
    have hq : (b.place == L.place) = true := hq₀
    exact ⟨List.mem_of_find?_eq_some hb, beq_iff_eq.1 hq, rfl⟩

/-! ## 4 The main lemma -/

section
variable {Bk : ProverCoinCounts} (R : RealAt Bk) (ch : Nat) (φ : Face V W Pb) (pb : Pb)
  (bs : List (Block S Cl)) (Ls : List (Lettered Bk S Cl V W Y Pb))
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)

/-- **A session's look-ups are the lists' own.** `ft`, `earlier`: as `realIn` takes them. -/
theorem look_ok {ft : Nat} {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (hR : R ch = realIn φ bs Ls ch ft earlier (dryAt keys dsAll m₀))
    (hseat : ∀ L ∈ Ls, ∃ σ, L.side bs = some σ ∧ σ.fits = true)
    (hLs : (Ls.map (·.place)).Nodup) (hbs : (bs.map (·.place)).Nodup) :
    ∀ b ∈ bs, LookOk R ch (tellerOf (Ls.flatMap fun L => L.row.map (·.2)) pb)
      (fun a => (Ls.flatMap fun L => L.row.map (·.2)).any (·.addr.place == a)) φ pb
      (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)) keys dsAll m₀
      (preOf ch ft earlier bs b.place) b := by
  intro b hb
  have hfind : ((Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)).find? fun g =>
      g.place == b.place) = (Ls.find? fun L => L.place == b.place).map fun L =>
        (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y) := by
    rw [List.find?_map]
    rfl
  have haddr : ∀ L ∈ Ls, ∀ t ∈ L.row.map (·.2), t.addr.place = L.place := by
    intro L hL t ht
    obtain ⟨σ, hσ, hf⟩ := hseat L hL
    obtain ⟨-, h2, h3⟩ := side_ok hσ
    unfold Side.fits at hf
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hf
    rw [h3, h2] at hf
    exact row_place L.place L.row 0 hf.1.1 t ht
  unfold LookOk
  refine ⟨fun hnone => ?_, fun g hg => ?_⟩
  · rw [hfind] at hnone
    have hn : (Ls.find? fun L => L.place == b.place) = none := by
      cases hh : Ls.find? fun L => L.place == b.place with
      | none => rfl
      | some L =>
        rw [hh] at hnone
        cases hnone
    show ((Ls.flatMap fun L => L.row.map (·.2)).any fun t => t.addr.place == b.place) = false
    rw [List.any_eq_false]
    intro t ht hp
    obtain ⟨L, hL, htL⟩ := List.mem_flatMap.1 ht
    have h1 := haddr L hL t htL
    have h2 := List.find?_eq_none.1 hn L hL
    exact h2 (by rw [← h1]; exact hp)
  · rw [hfind] at hg
    cases hh : Ls.find? fun L => L.place == b.place with
    | none =>
      rw [hh] at hg
      cases hg
    | some L =>
      rw [hh] at hg
      cases hg
      have hL : L ∈ Ls := List.mem_of_find?_eq_some hh
      have hq₀ := List.find?_some hh
      have hq : (L.place == b.place) = true := hq₀
      have hpl : L.place = b.place := beq_iff_eq.1 hq
      obtain ⟨σ, hσ, hf⟩ := hseat L hL
      obtain ⟨h1, h2, h3⟩ := side_ok hσ
      have hblock : σ.block = b :=
        List.inj_on_of_nodup_map hbs h1 hb (h2.trans hpl)
      have hother : ∀ L' ∈ Ls, L' ≠ L → L'.place ≠ b.place := fun L' hL' hne e =>
        hne (List.inj_on_of_nodup_map hLs hL' hL (e.trans hpl.symm))
      unfold Side.fits at hf
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hf
      have hfa : ∀ s ∈ L.row.zipIdx 0, s.1.2.addr = ⟨b.place, s.2⟩ := by
        have := hf.1.1
        rw [h3, hblock] at this
        exact this
      refine ⟨σ, hblock, by rw [h3], ?_, ?_, ?_⟩
      · -- which places have a list of parts
        rw [h3]
        cases hrow : L.row with
        | nil =>
          show ((Ls.flatMap fun L => L.row.map (·.2)).any fun t => t.addr.place == b.place) = false
          rw [List.any_eq_false]
          intro t ht hp
          obtain ⟨L', hL', htL'⟩ := List.mem_flatMap.1 ht
          by_cases e : L' = L
          · rw [e, hrow] at htL'
            cases htL'
          · exact hother L' hL' e ((haddr L' hL' t htL').symm.trans (beq_iff_eq.1 hp))
        | cons q row =>
          show ((Ls.flatMap fun L => L.row.map (·.2)).any fun t => t.addr.place == b.place) = true
          rw [List.any_eq_true]
          refine ⟨q.2, List.mem_flatMap.2 ⟨L, hL, by rw [hrow]; exact List.mem_cons.2 (Or.inl rfl)⟩,
            ?_⟩
          rw [haddr L hL q.2 (by rw [hrow]; exact List.mem_cons.2 (Or.inl rfl)), hpl]
          simp
      · -- the honest side
        intro u hu
        rw [hR]
        funext k f ds asks
        unfold realIn
        show ((Ls.find? fun L => L.place == b.place).bind fun L => (L.side bs).bind fun σ =>
          (σ.members.find? fun t => t.number == u.number).bind fun u' =>
            partShows φ σ u' Bk ch (preOf ch ft earlier bs L.place)
              (dryAt keys dsAll m₀ ⟨b.place, u.number⟩) k f ds asks) = _
        rw [hh]
        show ((L.side bs).bind fun σ => (σ.members.find? fun t => t.number == u.number).bind
          fun u' => partShows φ σ u' Bk ch (preOf ch ft earlier bs L.place)
            (dryAt keys dsAll m₀ ⟨b.place, u.number⟩) k f ds asks) = _
        rw [hσ]
        show ((σ.members.find? fun t => t.number == u.number).bind fun u' =>
          partShows φ σ u' Bk ch (preOf ch ft earlier bs L.place)
            (dryAt keys dsAll m₀ ⟨b.place, u.number⟩) k f ds asks) = _
        rw [hpl, show (σ.members.find? fun t => t.number == u.number) = some u from
          members_find σ.row 0 _ u hu]
        rfl
      · -- the simulator
        intro u hu
        unfold tellerOf
        have hu' : u ∈ membersOf L.row 0 (σ.block.rounds.zip σ.block.oracles) := by
          rw [← h3]
          exact hu
        have hoth : ∀ L' ∈ Ls, L' ≠ L → ((fun L : Lettered Bk S Cl V W Y Pb => L.row.map (·.2))
            L').find? (fun t => t.addr == ⟨b.place, u.number⟩) = none := by
          intro L' hL' hne
          rw [List.find?_eq_none]
          intro t ht hp
          have e1 := haddr L' hL' t ht
          rw [beq_iff_eq.1 hp] at e1
          exact hother L' hL' hne e1.symm
        rw [find_flat (fun L : Lettered Bk S Cl V W Y Pb => L.row.map (·.2)) _ L Ls hL hoth]
        show (((L.row.map (·.2)).find? fun t => t.addr == ⟨b.place, u.number⟩).map fun S =>
          (⟨S.takes, S.tell pb⟩ : Teller)) = _
        rw [members_sim b.place L.row 0 _ hfa u hu']
        rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.find_none_flat
#print axioms ProofFile.Honest.find_flat
#print axioms ProofFile.Honest.members_ge
#print axioms ProofFile.Honest.members_find
#print axioms ProofFile.Honest.members_sim
#print axioms ProofFile.Honest.row_place
#print axioms ProofFile.Honest.side_ok
#print axioms ProofFile.Honest.look_ok
