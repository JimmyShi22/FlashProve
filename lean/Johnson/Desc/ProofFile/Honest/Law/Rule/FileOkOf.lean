-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/FileOkOf.lean: `FileOk` (Honest/Law/Rule/Model.lean) from
`Owed` (Honest/Owed.lean): this is `fileOk_of`. `FileOk` holds the thirteen facts on a description,
a book and its lists of parts that the model uses. They follow from the tests on the plan, the
places and the book (`B.word F = none`), from `Good.fits`, and from the tests that a run which goes
through has passed (no two prover's sides at one place).

  1  `count_place`, `nodup_of_twice`, `tests_twice`   no two prover's sides at one place
  2  `shape_of`, `mem_of_lookup`, `cuts_of`, `seat_fits`   shapes; cuts; the side of a list of parts
     fits
  3  `fileOk_of`   the main lemma

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.RunLaws
import Johnson.Desc.ProofFile.Honest.Owed
import Johnson.Desc.ProofFile.Honest.Law.Rule.Model
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 No two prover's sides at one place -/

theorem count_place : ∀ (hs : List (Placed V W Y)) (a : Place),
    (hs.map (·.place)).count a = (hs.filter fun h => h.place == a).length
  | [], _ => rfl
  | h :: hs, a => by
    rw [List.map_cons, List.count_cons, count_place hs a]
    by_cases e : (h.place == a) = true
    · rw [List.filter_cons_of_pos (p := fun h : Placed V W Y => h.place == a) e, if_pos e]
      rfl
    · rw [List.filter_cons_of_neg (p := fun h : Placed V W Y => h.place == a) e, if_neg e]
      rfl

theorem nodup_of_twice {hs : List (Placed V W Y)} (h : twice hs = []) :
    (hs.map (·.place)).Nodup := by
  refine nodup_of_count _ fun a ha => ?_
  have hf : ((hs.map (·.place)).filter fun a =>
      decide (1 < (hs.filter fun h => h.place == a).length)) = [] := by
    unfold twice at h
    cases hl : (hs.map (·.place)).filter fun a =>
        decide (1 < (hs.filter fun h => h.place == a).length) with
    | nil => rfl
    | cons b l =>
      rw [hl] at h
      simp [List.eraseDups_cons] at h
  have h1 := List.filter_eq_nil_iff.1 hf a ha
  have h2 : ¬ (1 < (hs.filter fun h => h.place == a).length) := by simpa using h1
  have h3 : 0 < (hs.map (·.place)).count a := List.count_pos_iff.2 ha
  rw [count_place] at h3 ⊢
  omega

theorem tests_twice {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    (h : readyTests F B H w₀ = .ok ()) :
    twice H.first = [] ∧ twice H.shared = [] ∧ twice H.second = [] := by
  unfold readyTests at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h2
  have e : twice H.first ++ twice H.shared ++ twice H.second = [] := by
    simpa using h2
  obtain ⟨e12, e3⟩ := List.append_eq_nil_iff.1 e
  obtain ⟨e1, e2⟩ := List.append_eq_nil_iff.1 e12
  exact ⟨e1, e2, e3⟩

/-! ## 2 Shapes, cuts, sides -/

theorem shape_of {b : Block S Cl} (h : b.shaped = true) :
    ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots := by
  unfold Block.shaped at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact fun z hz => (h.2 z hz).1

theorem mem_of_lookup {β : Type} : ∀ (l : List (Place × β)) (a : Place) (b : β),
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by cases h
  | (a', b') :: l, a, b, h => by
    rw [List.lookup_cons] at h
    cases e : a == a' with
    | true =>
      rw [e] at h
      have hb : b' = b := Option.some.inj h
      rw [← hb, beq_iff_eq.1 e]
      exact List.mem_cons.2 (Or.inl rfl)
    | false =>
      rw [e] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup l a b h)

/- Where the book passes its tests: no part of a cut has 0 rounds. -/
theorem cuts_of {F : FileDescription Xi} {B : ProverCoinCounts} (h : B.word F = none) :
    ∀ a cs, B.cuts.lookup a = some cs → ∀ n ∈ cs, n ≠ 0 := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, -, -, -, -, -, -, t10, -⟩ := t
  intro a cs hl n hn
  have hm : (a, cs) ∈ B.cuts := mem_of_lookup _ _ _ hl
  have := List.all_eq_true.1 t10 (a, cs) hm
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  simpa using this.1.2 n hn

/-- A list of parts that has a side, and whose side, with its chain's falls, meets `Good`: its side
fits. -/
theorem seat_fits {Bk : ProverCoinCounts} {φ : Face V W Pb} {bs : List (Block S Cl)} {ord : List Place}
    {ch ft : Nat} {fs : List (Fall S)} {L : Lettered Bk S Cl V W Y Pb}
    {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (hgood : L.goodAt earlier φ bs ord ch ft fs) (hs : (L.side bs).isSome = true) :
    ∃ σ, L.side bs = some σ ∧ σ.fits = true := by
  obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hs
  refine ⟨σ, hσ, ?_⟩
  unfold Lettered.side Side.seated at hσ
  cases hfind : bs.find? fun b => b.place == L.place with
  | none =>
    rw [hfind] at hσ
    cases hσ
  | some b =>
    rw [hfind] at hσ
    have eσ : (⟨b, L.row, fallOf [] L.place⟩ : Side S Cl V W Y Pb) = σ := Option.some.inj hσ
    subst eσ
    exact (hgood ⟨b, L.row, fallOf fs L.place⟩ (by
      unfold Lettered.side Side.seated
      rw [hfind]
      rfl)).fits

/-! ## 3 The main lemma -/

/-- **`FileOk` from `Owed`**, where one run goes through. -/
theorem fileOk_of {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (hO : Owed F Bk H G Rel)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {r : RunC F}
    (hrun : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r) : FileOk F Bk G := by
  obtain ⟨R, a₁, w₁, a₂, w₂, a₃, w₃, hR, -, -, -, -, -, -, -, -⟩ := runC_parts hrun
  obtain ⟨ht, -⟩ := ready_ok hR
  obtain ⟨t1, t2, t3⟩ := tests_twice ht
  have P := (F.planOk_ok).1 hO.plan
  have hn := orderOf_nodup hO.places
  unfold orderOf at hn
  obtain ⟨n12, n3, -⟩ := List.nodup_append.1 hn
  obtain ⟨n1, n2, -⟩ := List.nodup_append.1 n12
  have hs := hO.seats
  unfold Sides.seated at hs
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have r1 := nodup_of_twice t1
  have r2 := nodup_of_twice t2
  have r3 := nodup_of_twice t3
  exact
    { nd₁ := n1
      nd₂ := n2
      nd₃ := n3
      sh₁ := fun b hb => shape_of (P.blocks₁ b hb).2
      sh₂ := fun b hb => shape_of (P.blocks₂ b hb).2
      sh₃ := fun b hb => shape_of (P.blocks₃ b hb).2
      seat₁ := fun L hL =>
        seat_fits (L := L.withField 0 0 F.first.blocksInOrder [] 0) (hO.good.1 L hL) (hs.1.1 L hL)
      seat₂ := fun L hL =>
        seat_fits (L := L.withField 1 0 F.shared.blocksInOrder [] 0) (hO.good.2.1 L hL) (hs.1.2 L hL)
      seat₃ := fun L hL =>
        seat_fits (L := L.withField 2 F.lastChainFirstTreeNumber F.second.blocksInOrder [] 0) (hO.good.2.2 L hL [] 0)
          (hs.2 L hL)
      rows₁ := by
        have e : ((G.prover H).first.map (·.place)) = G.first.map (·.place) := by
          show (G.first.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)).map (·.place) = _
          rw [List.map_map]
          rfl
        rw [← e]
        exact r1
      rows₂ := by
        have e : ((G.prover H).shared.map (·.place)) = G.shared.map (·.place) := by
          show (G.shared.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)).map (·.place) = _
          rw [List.map_map]
          rfl
        rw [← e]
        exact r2
      rows₃ := by
        have e : ((G.prover H).second.map (·.place)) = G.second.map (·.place) := by
          show (G.second.map fun L => (⟨L.place, L.row.map (·.1)⟩ : Placed _ _ _)).map (·.place) = _
          rw [List.map_map]
          rfl
        rw [← e]
        exact r3
      cuts := cuts_of hO.book }

end ProofFile.Honest

#print axioms ProofFile.Honest.count_place
#print axioms ProofFile.Honest.nodup_of_twice
#print axioms ProofFile.Honest.tests_twice
#print axioms ProofFile.Honest.shape_of
#print axioms ProofFile.Honest.mem_of_lookup
#print axioms ProofFile.Honest.cuts_of
#print axioms ProofFile.Honest.seat_fits
#print axioms ProofFile.Honest.fileOk_of
