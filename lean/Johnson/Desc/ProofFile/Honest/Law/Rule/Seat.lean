-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Seat.lean: which side, with which parameter `On`, is at a
sub-protocol of a chain (`seatOf`); that it satisfies `SeatOk` (Honest/Law/Rule/ChainHere.lean), at
`preOf` (Honest/Rule.lean) of the chain's whole list: the proof is that of `look_ok`
(Honest/Law/Rule/Members.lean), stated of the list's own side (`seat_ok`); and what a chain's
`Step`s that are prepared at one run's coins say of each sub-protocol (`chain_facts`). It is the
ninth piece of the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Members
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainHere

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

/-- **What a chain's `Step`s say of each sub-protocol.** -/
theorem chain_facts {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} : ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)),
    chainSteps B rows look v bs hs = .ok ss → ∀ b ∈ bs,
    b.oracles.length = b.rounds.length ∧ (chainKeys [b] hs).length = b.rounds.length ∧
      ∀ g, (hs.find? fun g => g.place == b.place) = some g →
        B.cuts.lookup b.place = some (g.parts.map (·.moves.length))
  | [], _, _, b, hb => by cases hb
  | b₀ :: bs, ss, h, b, hb => by
    obtain ⟨ho, l, hl, hcase⟩ := chainSteps_cons_ok h
    rcases List.mem_cons.1 hb with e | e
    · subst e
      have hzl : (b.rounds.zip b.oracles).length = b.rounds.length := by
        rw [List.length_zip, ho, Nat.min_self]
      have e1 := chainSteps_keys _ _ _ h
      have e2 := chainSteps_keys _ _ _ hl
      rcases hcase with ⟨h1, h2⟩ | ⟨g, c, h1, h2, h3, -, h5⟩
      · refine ⟨ho, ?_, fun g hg => by rw [h1] at hg; cases hg⟩
        rw [h2, List.map_append, e2, chainKeys_cons b bs hs] at e1
        rw [← List.append_cancel_right e1, List.length_map]
        have e := congrArg List.length (bare_states (W := W) (Y := Y) b)
        rw [List.length_map, hzl] at e
        exact e
      · refine ⟨ho, ?_, fun g' hg => by
          rw [h1] at hg
          rw [← Option.some.inj hg]
          exact h3⟩
        rw [h5, List.map_append, e2, chainKeys_cons b bs hs] at e1
        rw [← List.append_cancel_right e1, List.length_map]
        have e := congrArg List.length (row_states g b v c h2 ho)
        rw [List.length_map, hzl] at e
        exact e
    · exact chain_facts bs l hl b e

section
variable {Bk : ProverCoinCounts} (R : RealAt Bk) (ch : Nat) (φ : Face V W Pb) (pb : Pb)
  (bs : List (Block S Cl)) (Ls : List (Lettered Bk S Cl V W Y Pb))
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)

/-- **The side at a sub-protocol, with the parameter `On` of its list of parts.** -/
def seatOf (b : Block S Cl) : Option (Side S Cl V W Y Pb × OnT V W Y Pb) :=
  (Ls.find? fun L => L.place == b.place).bind fun L => (L.side bs).map fun σ => (σ, L.On)

/-- **`seatOf` satisfies `SeatOk`**: it agrees with the session's look-ups and with the prover's
sides. `ft`, `earlier`: as `realIn` takes them. -/
theorem seat_ok {ft : Nat} {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (hR : R ch = realIn φ bs Ls ch ft earlier (dryAt keys dsAll m₀))
    (hseat : ∀ L ∈ Ls, ∃ σ, L.side bs = some σ ∧ σ.fits = true)
    (hLs : (Ls.map (·.place)).Nodup) (hbs : (bs.map (·.place)).Nodup)
    (hcut : ∀ b ∈ bs, ∀ g, ((Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)).find?
      fun g => g.place == b.place) = some g →
      Bk.cuts.lookup b.place = some (g.parts.map (·.moves.length))) :
    ∀ b ∈ bs, SeatOk R ch ft (tellerOf (Ls.flatMap fun L => L.row.map (·.2)) pb)
      (fun a => (Ls.flatMap fun L => L.row.map (·.2)).any (·.addr.place == a)) φ pb
      (Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)) keys dsAll m₀
      (seatOf bs Ls) earlier bs b := by
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
  refine ⟨fun hnone => ?_, fun p hp => ?_⟩
  · have hn : (Ls.find? fun L => L.place == b.place) = none := by
      cases hh : Ls.find? fun L => L.place == b.place with
      | none => rfl
      | some L =>
        obtain ⟨σ, hσ, -⟩ := hseat L (List.mem_of_find?_eq_some hh)
        unfold seatOf at hnone
        rw [hh] at hnone
        have hnone' : ((L.side bs).map fun σ => (σ, L.On)) = none := hnone
        rw [hσ] at hnone'
        cases hnone'
    show ((Ls.flatMap fun L => L.row.map (·.2)).any fun t => t.addr.place == b.place) = false
    rw [List.any_eq_false]
    intro t ht hp
    obtain ⟨L, hL, htL⟩ := List.mem_flatMap.1 ht
    have h1 := haddr L hL t htL
    have h2 := List.find?_eq_none.1 hn L hL
    exact h2 (by rw [← h1]; exact hp)
  · unfold seatOf at hp
    cases hh : Ls.find? fun L => L.place == b.place with
    | none =>
      rw [hh] at hp
      cases hp
    | some L =>
      rw [hh] at hp
      have hp : ((L.side bs).map fun σ => (σ, L.On)) = some p := hp
      have hL : L ∈ Ls := List.mem_of_find?_eq_some hh
      have hq₀ := List.find?_some hh
      have hq : (L.place == b.place) = true := hq₀
      have hpl : L.place = b.place := beq_iff_eq.1 hq
      obtain ⟨σ, hσ, hf⟩ := hseat L hL
      rw [hσ] at hp
      have ep : (σ, L.On) = p := Option.some.inj hp
      subst ep
      have hfind' : ((Ls.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed V W Y)).find? fun g =>
          g.place == b.place) = some ⟨L.place, L.row.map (·.1)⟩ := by
        rw [hfind, hh]
        rfl
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
      refine ⟨hblock, ⟨_, hfind', by rw [h3]⟩, ?_, ?_, ?_, ?_⟩
      · -- which places have a list of parts
        show _ = !σ.row.isEmpty
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
      · -- the book's cut
        rw [hcut b hb _ hfind', List.map_map]
        show _ = some (σ.row.map (·.1.moves.length))
        rw [h3]
        rfl
      · -- the honest side
        intro u hu
        show R ch ⟨σ.block.place, u.number⟩ =
          partShows φ σ u Bk ch (preOf ch ft earlier bs σ.block.place)
            (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩)
        rw [hblock, hR]
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
        show tellerOf (Ls.flatMap fun L => L.row.map (·.2)) pb ⟨σ.block.place, u.number⟩ = _
        rw [hblock]
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

#print axioms ProofFile.Honest.chain_facts
#print axioms ProofFile.Honest.seat_ok
#print axioms ProofFile.Honest.seatOf
