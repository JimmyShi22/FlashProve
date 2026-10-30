-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowStretch.lean (three general lemmas stand here, last_of_seal · cutDs_held · pairs_of_as: none spends the kind K13: so whoever wants a stretch need not stand over row 1.16's law): at every description, at every block of chains 2 and 3, and at every block of chain 1 but its last (the sealing block, whose sealing round's data are not in the chain's data): the maker's stretch at block n bears the rounds that block n declares: entry, kind, items, trees' count, stored parts, round by round, and just as many. No test, no evaluation.
By roundsOfData (Johnson/Desc/Sound/DataRounds.lean) and cutDs (RowCut.lean). General in the description.
  flat_ne_nil     a row of blocks whose last block has a round declares a round
  stretch_as      Forall₂ RoundAsG ds ‹the blocks' rounds in a row, without the last› → the last block has a round → n is not the last block → Forall₂ RoundAsG (cutDs ds b l n) ‹block n's rounds›
  stretch_of_data₁  the same at chain 1 of a description F with F.data file = .ok D and the head F.first.blocksInOrder = c₁ :: k₁
  stretch_whole · stretch_of_data₂ | ₃   the like at chains 2 and 3, whose data are as many as all their declared rounds
  At chain 1 the last block is barred (n < k₁.length): its sealing round's data are put back by the maker, not held in D.ds₁; at chains 2 and 3 no block is barred
  forall₂_replicate a list that stands in a relation to n copies of a: it has n members, each in that relation to a
  last_of_seal    from the description's test sealLast: the first chain's last block declares a round
  cutDs_held      the maker's cut at the held blocks is the cut at the blocks
  pairs_of_as     Forall₂ RoundAsG st rs → st's (entry, some kind) are rs's (entry, the kind that the name says)
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowCut
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.Sound.TilesDataProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {S Cl : Type}

theorem flat_ne_nil : ∀ (l : List (Block S Cl)) (b : Block S Cl), 1 ≤ lastRounds b l → (b :: l).flatMap (·.rounds) ≠ []
  | [], b, h => by
    have h' : 1 ≤ b.rounds.length := h
    intro e
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
    rw [e] at h'
    exact absurd h' (by decide)
  | b' :: l, b, h => by
    have ih := flat_ne_nil l b' h
    intro e
    rw [List.flatMap_cons] at e
    exact ih (List.append_eq_nil_iff.1 e).2

theorem stretch_as : ∀ (l : List (Block S Cl)) (b : Block S Cl) (n : ℕ) (ds : List RDT) (bn : Block S Cl),
    List.Forall₂ RoundAsG ds ((b :: l).flatMap (·.rounds)).dropLast → 1 ≤ lastRounds b l → n < l.length → (b :: l)[n]? = some bn →
    List.Forall₂ RoundAsG (cutDs ds b l n) bn.rounds
  | [], _, _, _, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | b' :: l, b, 0, ds, bn, h, hl, _, hb => by
    obtain rfl : b = bn := Option.some.inj hb
    have hne := flat_ne_nil l b' hl
    rw [List.flatMap_cons, List.dropLast_append_of_ne_nil hne] at h
    have h2 := List.forall₂_take b.rounds.length h
    rw [List.take_left'] at h2
    · exact h2
    · rfl
  | b' :: l, b, n + 1, ds, bn, h, hl, hn, hb => by
    have hne := flat_ne_nil l b' hl
    rw [List.flatMap_cons, List.dropLast_append_of_ne_nil hne] at h
    have h2 := List.forall₂_drop b.rounds.length h
    rw [List.drop_left'] at h2
    · exact stretch_as l b' n (ds.drop b.rounds.length) bn h2 hl (Nat.lt_of_succ_lt_succ hn) (List.getElem?_cons_succ.symm.trans hb)
    · rfl

end

theorem stretch_of_data₁ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD) (h : F.data file = .ok D)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (q₁ : F.first.blocksInOrder = c₁ :: k₁) (hs : 1 ≤ lastRounds c₁ k₁)
    (n : ℕ) (hn : n < k₁.length) (bn : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some bn) :
    List.Forall₂ RoundAsG (cutDs D.ds₁ c₁ k₁ n) bn.rounds := by
  have h1 : List.Forall₂ RoundAsG D.ds₁ (F.first.blocksInOrder.flatMap (·.rounds)).dropLast := (roundsOfData F file D h).1
  rw [q₁] at h1
  exact stretch_as k₁ c₁ n D.ds₁ bn h1 hs hn hb

section
variable {S Cl : Type}

/-- The like where the data are as many as ALL the declared rounds (chains 2 and 3: nothing is put back): AT EVERY BLOCK, THE LAST TOO: there cutDs hands all that is left, which is that block's. -/
theorem stretch_whole : ∀ (l : List (Block S Cl)) (b : Block S Cl) (n : ℕ) (ds : List RDT) (bn : Block S Cl),
    List.Forall₂ RoundAsG ds ((b :: l).flatMap (·.rounds)) → (b :: l)[n]? = some bn →
    List.Forall₂ RoundAsG (cutDs ds b l n) bn.rounds
  | [], b, 0, ds, bn, h, hb => by
    obtain rfl : b = bn := Option.some.inj hb
    simpa [cutDs] using h
  | [], _, n + 1, _, _, _, hb => by simp at hb
  | b' :: l, b, 0, ds, bn, h, hb => by
    obtain rfl : b = bn := Option.some.inj hb
    rw [List.flatMap_cons] at h
    have h2 := List.forall₂_take b.rounds.length h
    rw [List.take_left'] at h2
    · exact h2
    · rfl
  | b' :: l, b, n + 1, ds, bn, h, hb => by
    rw [List.flatMap_cons] at h
    have h2 := List.forall₂_drop b.rounds.length h
    rw [List.drop_left'] at h2
    · exact stretch_whole l b' n (ds.drop b.rounds.length) bn h2 (List.getElem?_cons_succ.symm.trans hb)
    · rfl

end

theorem stretch_of_data₂ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD) (h : F.data file = .ok D)
    (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl)) (q₂ : F.shared.blocksInOrder = c₂ :: k₂)
    (n : ℕ) (bn : Block F.S₂ F.Cl) (hb : (c₂ :: k₂)[n]? = some bn) :
    List.Forall₂ RoundAsG (cutDs D.ds₂ c₂ k₂ n) bn.rounds := by
  have h1 : List.Forall₂ RoundAsG D.ds₂ (F.shared.blocksInOrder.flatMap (·.rounds)) := (roundsOfData F file D h).2.1
  rw [q₂] at h1
  exact stretch_whole k₂ c₂ n D.ds₂ bn h1 hb

theorem stretch_of_data₃ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD) (h : F.data file = .ok D)
    (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    (n : ℕ) (bn : Block F.S₃ F.Cl) (hb : (c₃ :: k₃)[n]? = some bn) :
    List.Forall₂ RoundAsG (cutDs D.ds₃ c₃ k₃ n) bn.rounds := by
  have h1 : List.Forall₂ RoundAsG D.ds₃ (F.second.blocksInOrder.flatMap (·.rounds)) := (roundsOfData F file D h).2.2
  rw [q₃] at h1
  exact stretch_whole k₃ c₃ n D.ds₃ bn h1 hb

theorem forall₂_replicate {α β : Type} {R : α → β → Prop} (a : β) : ∀ (n : ℕ) (l : List α), List.Forall₂ R l (List.replicate n a) → l.length = n ∧ ∀ d ∈ l, R d a
  | 0, l, h => by
    rw [List.replicate_zero] at h
    cases h
    exact ⟨rfl, fun _ hd => absurd hd (List.not_mem_nil)⟩
  | n + 1, l, h => by
    rw [List.replicate_succ] at h
    cases h with
    | cons hd tl =>
      obtain ⟨e, ha⟩ := forall₂_replicate a n _ tl
      refine ⟨by rw [List.length_cons, e], fun d hd' => ?_⟩
      rcases List.mem_cons.1 hd' with rfl | h'
      · exact hd
      · exact ha d h'

theorem last_of_seal {XI : Type} (F : FileDescription XI) (hs : F.sealLast = true) (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (q₁ : F.first.blocksInOrder = c₁ :: k₁) : 1 ≤ lastRounds c₁ k₁ := by
  have h1 := sealLast_any F hs
  rw [q₁] at h1
  rw [lastRounds_eq, List.getLast?_map]
  cases hg : (c₁ :: k₁).getLast? with
  | none => rw [hg] at h1; cases h1
  | some b =>
    rw [hg] at h1
    have h2 : (!b.rounds.isEmpty) = true := h1
    show 1 ≤ b.rounds.length
    cases hr : b.rounds with
    | nil => rw [hr] at h2; cases h2
    | cons _ _ => simp

section
variable {Pb S Cl : Type}

theorem cutDs_held : ∀ (l : List (Block S Cl)) (n : ℕ) (ds : List RDT) (b : Block S Cl),
    cutDs ds (held b : Block (Pb × S) Cl) (l.map held) n = cutDs ds b l n
  | [], 0, _, _ => rfl
  | [], _ + 1, _, _ => rfl
  | _ :: _, 0, _, _ => rfl
  | c :: l, n + 1, ds, b => cutDs_held l n (ds.drop b.rounds.length) c

end

theorem pairs_of_as : ∀ (st : List RDT) (rs : List Fmt.DeclaredRound), List.Forall₂ RoundAsG st rs →
    st.map (fun d => (d.entry, some d.kind)) = rs.map (fun r => (r.entry, Fmt.kindOf r.entry.name))
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    rw [List.map_cons, List.map_cons, pairs_of_as _ _ t, h.1, h.2.1]

end LPFD

#print axioms LPFD.flat_ne_nil
#print axioms LPFD.stretch_whole
#print axioms LPFD.last_of_seal
#print axioms LPFD.cutDs_held
#print axioms LPFD.pairs_of_as
#print axioms LPFD.stretch_as
#print axioms LPFD.stretch_of_data₁
#print axioms LPFD.stretch_of_data₂
#print axioms LPFD.stretch_of_data₃
#print axioms LPFD.forall₂_replicate
