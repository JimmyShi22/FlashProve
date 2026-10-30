-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/Support.lean: the code switch: A GENERATOR ROW OF THE TEXT HAS NO
COEFFICIENT OUTSIDE THE ENTRIES OF THE NEW SENDING, AT EVERY INDEX INSIDE ITS TABLE.

GenJoin.lean's ReadsAs compares a row of the text with a typed vector at the entries of the new
sending alone. The typed row is 0 at every other entry of the open messages. If a row of the text
had a coefficient elsewhere (on another message; at an index of a table that names no entry), "the
text's row holds" and "the typed row holds" could part. Here: it has none, at every index inside its
table.
  Named     three numbers (the statement's number of a message, a table, an index) are those of an
            entry of the new sending
  InBits    the index lies inside the table: below 2 ^ (the table's index bits), asked for g's two
            tables and for the kept members' new main tables; of any other table nothing is asked
  OnlyAt    a row has the coefficient 0 at all three numbers inside the tables that are not Named
  main_only, mask_only, kept_only  the generator rows (All of them at the rows of DrawJoin.lean's
            gen_join: gen_join2, in HandsOn.lean.)
  stretchAt_ne, add_ne, ite_ne, padNoOf_at, named_g, beq2  tools
WHY InBits. A tensor does not look at the bits of an index above its variables
(Johnson/Top/H0/H2K/GenRowsAt.lean says so of genMask_at and formAt_keptForm): at an index from 2 ^
bits on, coefAt repeats the coefficient of the index's low bits. A table has no such index, so
nothing is lost; but it cannot be left out of the statement.
LIMITS. FrameOK, Names and NamesK are premises. The carried claim and the old sample rows are not
here (SupportClaim.lean has them, as far as it can be said): their forms are the record's, and at an
index whose row number is not below the member's rows nothing makes them 0. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hands.DrawJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

theorem stretchAt_ne {places : SwitchPlaces} {first count : ℕ} {c : ℕ → GE} {J : ℕ}
    (h : stretchAt places first count c J ≠ 0) :
    ∃ i, i < count ∧ places.get (first + i) = J ∧ c i ≠ 0 := by
  unfold stretchAt at h
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases e : places.get (first + i) = J
  · rw [if_pos e] at hne
    exact ⟨i, Finset.mem_range.1 hi, e, hne⟩
  · rw [if_neg e] at hne
    exact absurd rfl hne

theorem add_ne {a b : GE} (h : a + b ≠ 0) : a ≠ 0 ∨ b ≠ 0 := by
  by_cases ha : a = 0
  · exact Or.inr fun hb => h (by rw [ha, hb, add_zero])
  · exact Or.inl ha

theorem ite_ne {p : Prop} [Decidable p] {a : GE} (h : (if p then a else 0) ≠ 0) : p ∧ a ≠ 0 := by
  by_cases k : p
  · rw [if_pos k] at h
    exact ⟨k, h⟩
  · rw [if_neg k] at h
    exact absurd rfl h

theorem padNoOf_at : ∀ (pad : List PadPlace), (pad.map (·.index)).Nodup → ∀ q, q < pad.length →
    padNoOf pad (pad.getD q default).index = q
  | [], _, q, h => by simp at h
  | a :: l, hn, 0, _ => by simp [padNoOf]
  | a :: l, hn, q + 1, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    have hq : q < l.length := Nat.lt_of_succ_lt_succ h
    have hm : (l.getD q default).index ∈ l.map (·.index) := by
      rw [List.getD_eq_getElem _ _ hq]
      exact List.mem_map_of_mem (List.getElem_mem hq)
    have hne : ¬ a.index = (l.getD q default).index := fun e => hn.1 (e ▸ hm)
    rw [List.getD_cons_succ, padNoOf, if_neg hne, padNoOf_at l hn.2 q hq]

section Join
variable (cs : Codes) (l : List (OracleShape × ℕ))

/-- Three numbers are those of an entry of the new sending. -/
def Named (ids : ℕ → ℕ) (o : ℕ) (part : Part) (J : ℕ) : Prop :=
  ∃ n : (sigOf cs l).Ent, ids (entAt cs l n).1 = o ∧ (entAt cs l n).2.1 = part ∧
    (entAt cs l n).2.2 = J

/-- A row has no coefficient at three numbers inside the tables that name no entry. -/
def OnlyAt (ids : ℕ → ℕ) (inside : ℕ → Part → ℕ → Prop) (r : OnBytes.Row) : Prop :=
  ∀ o part J, inside o part J → coefAt r o part J ≠ 0 → Named cs l ids o part J

end Join

/-- The index lies inside the table. -/
def InBits {K : Type} (W : SwitchFrame) (pl : K → KeptPlace) (o : ℕ) (part : Part) (J : ℕ) : Prop :=
  (o = W.g → part = Part.main → J < 2 ^ W.tableBits) ∧
    (o = W.g → part = W.restPart → J < 2 ^ W.restBits) ∧
    ∀ κ, o = (pl κ).anew → part = Part.main → J < 2 ^ ((pl κ).rowBits + W.code.logEll)

section Join
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : Codes} {l : List (OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : K → ℕ}
  {pl : K → KeptPlace} {aKept : K → ℕ}

/-- An entry whose numbers in the sending are (0, part, J) is Named at g. -/
theorem named_g (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1) (n : (sigOf cs l).Ent)
    {part : Part} {J : ℕ} (h : entAt cs l n = (0, part, J)) : Named cs l ids W.g part J :=
  ⟨n, (D.gIs n).2 (by rw [h]), by rw [h], by rw [h]⟩

theorem beq2 {g o : ℕ} {p q : Part} (h : (g == o && p == q) = true) : o = g ∧ p = q := by
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact ⟨h.1.symm, h.2⟩

/-- **The main row.** -/
theorem main_only (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1) (x : ℕ) (hx : x < 2 ^ W.code.logN)
    (t : OnBytes.E) : OnlyAt cs l ids (InBits W pl) (genMain W x t) := by
  intro o part J hin hne
  have hl : s.C.l = 2 ^ W.code.logEll := by rw [D.codeC]; exact F.pow
  have hr : s.C.r = W.code.r := by rw [D.codeC]; rfl
  rw [genMain_at W aMain F.mainPieces F.mainInc F.logC x hx t] at hne
  rcases add_ne hne with h1 | h2
  · obtain ⟨c, k1⟩ := ite_ne h1
    clear h1 hne
    obtain ⟨rfl, rfl⟩ := beq2 c
    by_contra no
    refine k1 (lift_message_off W F.pow F.cutBits F.cutRow F.cutTab F.cutAl F.cutFirst x J
      (hin.1 rfl rfl) fun j hj e => no ?_)
    rw [← e]
    exact named_g D _ (D.mainMsg ⟨j, by rw [hl]; exact hj⟩)
  · obtain ⟨c, k2⟩ := ite_ne h2
    clear h2 hne
    obtain ⟨rfl, rfl⟩ := beq2 c
    obtain ⟨i, hi, e, -⟩ := stretchAt_ne k2
    rw [← e]
    exact named_g D _ (D.mainTail ⟨i, by rw [hr]; exact hi⟩)

/-- A mask row, at any two maps of names that lie on its two stretches. -/
theorem mask_only (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1) (j aM aT : ℕ)
    (hM : MaskAt W j aM aT) (pM : Fin s.Z.l → (sigOf cs l).Ent) (pT : Fin s.Z.r → (sigOf cs l).Ent)
    (hpM : ∀ i, entAt cs l (pM i) = (0, W.restPart, W.places.get (aM + i.val)))
    (hpT : ∀ i, entAt cs l (pT i) = (0, W.restPart, W.places.get (aT + i.val))) (x : ℕ)
    (t : OnBytes.E) : OnlyAt cs l ids (InBits W pl) (genMask W x j t) := by
  intro o part J hin hne
  have hl : s.Z.l = W.zk.ell := by rw [D.codeZ]; rfl
  have hr : s.Z.r = W.zk.r := by rw [D.codeZ]; rfl
  by_cases c : (W.g == o && W.restPart == part) = true
  · obtain ⟨rfl, rfl⟩ := beq2 c
    rw [genMask_at W j aM aT hM x t _ _ _ (hin.2.1 rfl rfl), if_pos c] at hne
    rcases add_ne hne with h | h
    · obtain ⟨i, hi, e, -⟩ := stretchAt_ne h
      exact e ▸ named_g D _ (hpM ⟨i, hl ▸ hi⟩)
    · obtain ⟨i, hi, e, -⟩ := stretchAt_ne h
      exact e ▸ named_g D _ (hpT ⟨i, hr ▸ hi⟩)
  · exact absurd (genMask_off W j aM aT hM x t o part J (by simpa using c)) hne

/-- **A kept row.** -/
theorem kept_only (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept) (κ : K) (x : ℕ)
    (hx : x < 2 ^ W.code.logN) (t : OnBytes.E) :
    OnlyAt cs l ids (InBits W pl)
      (genKept W (pl κ) (row κ) (rowsBefore W.kept (mem κ) + row κ) x t) := by
  intro o part J hin hne
  have hr : s.C.r = W.code.r := by rw [D.codeC]; rfl
  have wl : ∀ j, wM (codeOf W.code) x j ≠ 0 → j < s.C.l := fun j h => by
    by_contra k
    rw [D.codeC] at k
    exact h (wM_of_le (Nat.le_of_not_lt k) x)
  have form : ∀ X, X < 2 ^ ((pl κ).rowBits + W.code.logEll) →
      formAt (keptForm W (pl κ) (row κ) x) X ≠ 0 →
      ∃ j : Fin s.C.l, row κ + 2 ^ (pl κ).rowBits * j.val = X := by
    intro X hX h
    rw [formAt_keptForm W (pl κ) (row κ) x X F.pow F.logC hx (DK.rowLt κ) hX] at h
    obtain ⟨e, h⟩ := ite_ne h
    exact ⟨⟨_, wl _ h⟩, by rw [← e]; exact Nat.mod_add_div X _⟩
  by_cases cA : o = (pl κ).anew ∧ part = Part.main
  · obtain ⟨rfl, rfl⟩ := cA
    rw [genKept_new W (pl κ) (row κ) _ (aKept κ) (DK.tailPieces κ) (DK.tailInc κ) F.logC x hx t
      (DK.notG κ) (DK.padNodup κ)] at hne
    by_cases hp : J ∈ (pl κ).pad.map (·.index)
    · rw [if_pos hp] at hne
      exact absurd rfl hne
    · rw [if_neg hp] at hne
      obtain ⟨j, rfl⟩ := form J (hin.2.2 κ rfl rfl) hne
      have e : entAt cs l (iJ (.inl (some κ, j))) =
          (1 + mem κ, Part.main, row κ + 2 ^ (pl κ).rowBits * j.val) := by
        rw [DK.keptMsg κ j]
        unfold keptAt keptNm
        rw [if_neg hp]
      exact ⟨_, (DK.anewIs κ _).2 (by rw [e]), by rw [e], by rw [e]⟩
  · by_cases cB : o = W.g ∧ part = W.restPart
    · obtain ⟨rfl, rfl⟩ := cB
      rw [genKept_g W (pl κ) (row κ) _ (aKept κ) (DK.tailPieces κ) (DK.tailInc κ) F.logC x hx t
        (DK.notG κ)] at hne
      rcases add_ne hne with h | h
      · obtain ⟨q, hq, e, h⟩ := stretchAt_ne h
        obtain ⟨j, hj⟩ := form _ (DK.padIn κ q hq) h
        have hm : row κ + 2 ^ (pl κ).rowBits * j.val ∈ (pl κ).pad.map (·.index) := by
          rw [hj, List.getD_eq_getElem _ _ hq]
          exact List.mem_map_of_mem (List.getElem_mem hq)
        refine e ▸ named_g D (iJ (.inl (some κ, j))) ?_
        rw [DK.keptMsg κ j]
        unfold keptAt keptNm restAt
        rw [if_pos hm, hj, padNoOf_at _ (DK.padNodup κ) q hq]
      · obtain ⟨i, hi, e, -⟩ := stretchAt_ne h
        exact e ▸ named_g D _ (DK.keptTail κ ⟨i, hr ▸ hi⟩)
    · exact absurd (genKept_other W (pl κ) (row κ) _ (aKept κ) (DK.tailPieces κ) (DK.tailInc κ)
        F.logC x hx t o part cA cB J) hne

end Join

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.main_only
#print axioms VerifiableInference.Desc.First.K2Hands.mask_only
#print axioms VerifiableInference.Desc.First.K2Hands.kept_only
