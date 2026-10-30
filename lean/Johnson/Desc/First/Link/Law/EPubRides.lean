-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/EPubRides.lean: THE PROMISE's PUBLIC TEST AT A BORDER (`ePubAt`,
Johnson/Desc/First/EPubAt.lean) IS HANDED ON BY AN ACCEPTING STEP OF EACH OF A LINK's FOUR
SUB-PROTOCOLS OF THE BATCHING KIND AND THE FRAME (our files call a sub-protocol a block), AT THE
COMPOSED PUBLIC TESTS AND THE COMPOSED FILLING. It is the sixth of the six things that a
sub-protocol owes to «the half of the table's promise that reads the verifier's state is handed on».
Theorems on the sub-protocols' steps: no oracle, no witness.

What is said.
  `e_step9`, `e_stepE`: `ePubAt pub moreAll links pl k (z, s) = true` gives the same at k + 1 and
    s', under the Bool on the tables (`pubFit9`, `pubFitE`), at pub := `pubAll D base`, from what
    the state keeps. `e_batch`, `e_behind`, `e_eq`, `e_shut`: **the sentence at an accepting step of
    the batching, of the frame's sub-protocol behind it, of the one equation, of the shutting.**

Limits. PREMISES THAT STAY: the base's tests answer alike at any two states (so it is at the base
that says no to every public test); `LinkShare` at the batching and behind it (the runs' share);
behind the frame's sub-protocol «the one sum can be taken» (by nobody); at the one equation «no
message of the link's own is the index masks' message» (by nobody). Nothing on soundness.

-/
import Johnson.Desc.First.EPubAt
import Johnson.Desc.First.BordersSucc
import Johnson.Desc.First.Link.Law.RidesAtMg
import Johnson.Desc.First.Link.Law.EqMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where shut messageNow)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.First (S ModelPart Pub PubData SameOn pubAll ePubAt start openSets_succ
  pubSets_succ pubAll_same pubAll_ledger pubAll_indexThere footOf)

variable {P : Type} (D : PubData) (base : Pub → P × S → Bool) (links : List ModelPart) (pl : List Place)
  (z : P) (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s)) (k m : ℕ) (p : Place)

include hb

/-- The public test is handed on, at one of the three quiet sub-protocols. -/
theorem e_step9 (i : ℕ) (hfit : pubFit9 true moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + i) (hi : i = 1 ∨ i = 2 ∨ i = 5)
    (s s' : S) (hs : SameOn D keeps9 s s') (hled : ledgerOk s = true → ledgerOk s' = true)
    (htot : i = 2 → pubAll D base (.totalIn m) (z, s') = true)
    (h : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true := by
  obtain ⟨hB, _⟩ := fit9_at moreAll links pl hfit k m i p hp hl hpc hi
  unfold ePubAt at h ⊢
  rw [pubSets_succ moreAll links pl k p hp, openSets_succ links pl (start links) k p hp]
  rw [List.all_eq_true] at h ⊢
  intro q hq
  have h1 := List.all_eq_true.1 hB q hq
  rcases Bool.or_eq_true_iff.1 h1 with hmade | h2
  · by_cases h2 : i = 2
    · rw [if_pos h2] at hmade
      obtain rfl : q = .totalIn m := by simpa using hmade
      exact htot h2
    · rw [if_neg h2] at hmade
      simp at hmade
  · obtain ⟨hin, h3⟩ := Bool.and_eq_true_iff.1 h2
    have hfront := h q (by simpa using hin)
    rcases Bool.or_eq_true_iff.1 h3 with hl' | hfoot
    · cases q with
      | ledger m' =>
        rw [pubAll_ledger] at hfront ⊢
        exact hled hfront
      | _ => simp [isLedger] at hl'
    · have e0 := foot_at D keeps9 (by decide) q hfoot
      cases hf : foot0 q with
      | none => simp [hf] at hfoot
      | some R =>
        rw [hf] at hfoot e0
        have h4 : R.all keeps9.contains = true := hfoot
        rw [pubAll_same D base q R e0 z s s' (fun r hr => hs r (by
          have := List.all_eq_true.1 h4 r hr
          simpa using this)) (hb q s s')]
        exact hfront

/-- The public test is handed on, at the one equation's sub-protocol. -/
theorem e_stepE (hfit : pubFitE moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3) (s s' : S)
    (hs : SameOn D keepsE s s')
    (ht : ∀ j : ℕ, (s'.st.oracles[j]?).isSome = (s.st.oracles[j]?).isSome)
    (h : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true := by
  obtain ⟨hB, _⟩ := fitE_at moreAll links pl hfit k m p hp hl hpc
  unfold ePubAt at h ⊢
  rw [pubSets_succ moreAll links pl k p hp, openSets_succ links pl (start links) k p hp]
  rw [List.all_eq_true] at h ⊢
  intro q hq
  obtain ⟨hin, h3⟩ := Bool.and_eq_true_iff.1 (List.all_eq_true.1 hB q hq)
  have hfront := h q (by simpa using hin)
  rcases Bool.or_eq_true_iff.1 h3 with hth | hfoot
  · cases q with
    | indexThere =>
      rw [pubAll_indexThere] at hfront ⊢
      have ho : s'.out = s.out := hs .out (by simp [keepsE])
      show (s'.st.oracles[s'.out.indexMasks]?).isSome = true
      rw [ho, ht]
      exact hfront
    | _ => simp [isThere] at hth
  · have e0 := foot_at D keepsE (by decide) q hfoot
    cases hf : foot0 q with
    | none => simp [hf] at hfoot
    | some R =>
      rw [hf] at hfoot e0
      have h4 : R.all keepsE.contains = true := hfoot
      rw [pubAll_same D base q R e0 z s s' (fun r hr => hs r (by
        have := List.all_eq_true.1 h4 r hr
        simpa using this)) (hb q s s')]
      exact hfront

/-- **AT THE BATCHING.** -/
theorem e_batch (hfit : pubFit9 true moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 1) (L : Link S Claim) (pp : Where)
    (h : LinkShare L pp) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (j : ℕ)
    (hstep : L.batchB.step ft s rs cols = .ok (s', j))
    (he : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true :=
  e_step9 D base links pl z hb k m p 1 hfit hp hl hpc (Or.inl rfl) s s'
    (sameOn_of D { check := s.check } {} {} s s' (h.two.1 _ _ _ _ _ j hstep).1
      ((rest_blocks _ _ _ L pp h.hb₁ h.stand).1 _ _ _ _ _ j hstep))
    (ledger_batch L pp h.hb₁ h.sizedLS _ _ _ _ _ j hstep) (fun e => absurd e (by decide)) he

/-- **AT THE FRAME's SUB-PROTOCOL BEHIND THE BATCHING.** -/
theorem e_behind (hfit : pubFit9 true moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 2) (L : Link S Claim) (pp : Where)
    (h : LinkShare L pp) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (j : ℕ)
    (hstep : L.behindB.step ft s rs cols = .ok (s', j))
    (htot : pubAll D base (.totalIn m) (z, s') = true)
    (he : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true :=
  e_step9 D base links pl z hb k m p 2 hfit hp hl hpc (Or.inr (Or.inl rfl)) s s'
    (sameOn_of D { check := s.check } {} {} s s' (h.two.2 _ _ _ _ _ j hstep).1
      ((rest_blocks _ _ _ L pp h.hb₁ h.stand).2 _ _ _ _ _ j hstep))
    (ledger_behind L h.sized _ _ _ _ _ j hstep) (fun _ => htot) he

/-- **AT THE ONE EQUATION.** -/
theorem e_eq {Cl : Type} (hfit : pubFitE moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 3) (pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (j : ℕ)
    (hstep : b₃.step ft s rs cols = .ok (s', j))
    (hne : ∀ a, atS.get? s = some a → ∀ m' o,
      messageNow a.L.check.frame a.L.check.frame.link m' = some o → o ≠ s.out.indexMasks)
    (he : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true := by
  obtain ⟨a0, out, _, _, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ j (hb₃ _ _ _ _ _ hstep)
  refine e_stepE D base links pl z hb k m p hfit hp hl hpc s s' ?_
    (eq_there pw b₃ hb₃ _ _ _ _ _ j hstep) he
  intro r hr
  simp only [keepsE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · show s'.out = s.out
    rw [hs']
    exact out_set s _
  · show s'.check.frame = s.check.frame
    rw [hs']
    exact congrArg (·.frame) (check_set s _)
  · exact fun lay n lin => eq_hasRow pw b₃ hb₃ _ _ _ _ _ j hstep hne lay n lin

/-- **AT THE SHUTTING.** -/
theorem e_shut {Cl : Type} (hfit : pubFit9 true moreAll links pl = true) (hp : pl[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + 5) (pw : Where) (piece : ℕ)
    (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (j : ℕ)
    (hstep : b₅.step ft s rs cols = .ok (s', j))
    (he : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true :=
  e_step9 D base links pl z hb k m p 5 hfit hp hl hpc (Or.inr (Or.inr rfl)) s s'
    (sameOn_of D { check := s.check } {} {} s s' (rb_shutB pw piece b₅ hb₅ _ _ _ _ _ j hstep).1
      (rest_shut _ _ _ pw piece b₅ hb₅ _ _ _ _ _ j hstep))
    (ledger_shut pw piece b₅ hb₅ _ _ _ _ _ j hstep) (fun e => absurd e (by decide)) he

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.e_batch
#print axioms VerifiableInference.Desc.LinkJoin.e_behind
#print axioms VerifiableInference.Desc.LinkJoin.e_eq
#print axioms VerifiableInference.Desc.LinkJoin.e_shut
