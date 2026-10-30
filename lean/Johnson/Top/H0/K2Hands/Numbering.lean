-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/Numbering.lean: the code switch: THE NUMBERING OF THE ROWS: at which
place of the program's list each typed row stands, as ONE FUNCTION with a name, one to one, and onto
the numbers below 1 + (all sample rows) + t * (1 + kept rows + 2).

The typed rows behind a switch are a family over names (LdLocD.RowN, Cb/Req1/LdSegAfterRows.lean):
one for the claim; one for each answer of each held message's sample; one for each coordinate of
each long symbol read. The program lays a list. The batching that follows weighs row number i of
that list by the i-th coefficient of its seed, so whoever ties the two needs the numbering by name.
  rowNo     THE NUMBERING, in the text's own order:
              the claim:  0
              answer s of the held message k:  1 + (the sample rows of the members in front) + iOf k
                s
              coordinate α of the long symbol of draw i:  1 + (all sample rows) + i * (1 + kept rows
                + 2) + rowPlace α
  before_succ, before_step, before_le, before_cons, before_zero, block_lt, block_inj, block_onto
            a list made of blocks
  SlotsAll  what is asked of the kept slots: each holds a row of a member; two slots hold two rows;
            every row of every kept member has a slot
  rowPlace_lt, rowPlace_inj, rowPlace_onto  the rows of one draw
  rowsBefore_eq, keptRows_eq, slot_lt, smpOf, smp_lt  steps
  Held      what is asked of the held messages' names: aOf k is a kept member's number, iOf k s the
            number of one of its stored sample rows; both one to one; every stored sample row of
            every kept member is met
  rowNo_inj, rowNo_onto, rows_length  two typed rows stand at two places; every number below 1 +
            (all sample rows) + t * (1 + kept rows + 2) is a typed row's; the list has 1 + (all
            sample rows) + (draws) * (1 + kept rows + old.masks) rows
The names' types are letters here (Kh, Sk, t), so that the file needs none of the typed caller's
files; at LdLocD.RowN they are hd.K, fun k => (hd.o k).Z.S and the number of positions.
LIMITS. SlotsAll and Held are PREMISES. That these numbers are just the list's places holds where
old.masks = 2 and there are as many draws as the typed number t of positions: no statement of this
file takes these two; the meeting is HandsOn.lean's hands_on_count, where both are premises. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.DrawJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

/-! ## A list made of blocks -/

section Blocks
variable {α β : Type} (f : α → List β)

theorem before_cons (y : α) (l : List α) (a : ℕ) :
    before f (y :: l) (a + 1) = (f y).length + before f l a := by
  simp [before]

theorem before_zero (l : List α) : before f l 0 = 0 := by simp [before]

theorem before_succ : ∀ (l : List α) (a : ℕ) (x : α), l[a]? = some x →
    before f l (a + 1) = before f l a + (f x).length
  | [], _, _, h => by simp at h
  | y :: l, 0, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [before_cons, before_zero, before_zero]
    omega
  | y :: l, a + 1, x, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [before_cons, before_cons, before_succ l a x h]
    omega

theorem before_step : ∀ (l : List α) (a : ℕ), before f l a ≤ before f l (a + 1)
  | [], a => by simp [before]
  | y :: l, 0 => by rw [before_zero]; exact Nat.zero_le _
  | y :: l, a + 1 => by
    rw [before_cons, before_cons]
    exact Nat.add_le_add_left (before_step l a) _

theorem before_le (l : List α) (a : ℕ) : ∀ d, before f l a ≤ before f l (a + d)
  | 0 => Nat.le_refl _
  | d + 1 => Nat.le_trans (before_le l a d) (before_step f l (a + d))

theorem block_lt {l : List α} {a a' s : ℕ} {x : α} (hx : l[a]? = some x) (hs : s < (f x).length)
    (h : a < a') (s' : ℕ) : before f l a + s < before f l a' + s' := by
  have h1 := before_succ f l a x hx
  have h2 := before_le f l (a + 1) (a' - (a + 1))
  rw [show a + 1 + (a' - (a + 1)) = a' by omega] at h2
  omega

/-- Two places in two blocks, or two places in one block, are two places of the list. -/
theorem block_inj {l : List α} {a a' s s' : ℕ} {x x' : α} (hx : l[a]? = some x)
    (hs : s < (f x).length) (hx' : l[a']? = some x') (hs' : s' < (f x').length)
    (h : before f l a + s = before f l a' + s') : a = a' ∧ s = s' := by
  rcases Nat.lt_trichotomy a a' with k | k | k
  · exact absurd h (Nat.ne_of_lt (block_lt f hx hs k s'))
  · subst k
    exact ⟨rfl, by omega⟩
  · exact absurd h.symm (Nat.ne_of_lt (block_lt f hx' hs' k s))

/-- Every place of the list lies in a block. -/
theorem block_onto : ∀ (l : List α) (m : ℕ), m < before f l l.length →
    ∃ a x s, l[a]? = some x ∧ s < (f x).length ∧ m = before f l a + s
  | [], m, h => by simp [before] at h
  | y :: l, m, h => by
    rw [List.length_cons, before_cons] at h
    by_cases k : m < (f y).length
    · exact ⟨0, y, m, rfl, k, by rw [before_zero, Nat.zero_add]⟩
    · obtain ⟨a, x, s, hx, hs, e⟩ := block_onto l (m - (f y).length) (by omega)
      exact ⟨a + 1, x, s, by simpa using hx, hs, by rw [before_cons]; omega⟩

end Blocks

/-! ## The rows of one draw -/

theorem rowsBefore_eq (ks : List KeptPlace) (a : ℕ) :
    rowsBefore ks a = before (fun k : KeptPlace => List.range k.rows) ks a := by
  simp [rowsBefore, before]

theorem keptRows_eq (W : SwitchFrame) :
    keptRows W = before (fun k : KeptPlace => List.range k.rows) W.kept W.kept.length := by
  simp [keptRows, before]

section Draw
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K]

/-- What is asked of the kept slots. -/
structure SlotsAll (W : SwitchFrame) (mem row : K → ℕ) (pl : K → KeptPlace) : Prop where
  member : ∀ κ, W.kept[mem κ]? = some (pl κ)
  rowIn : ∀ κ, row κ < (pl κ).rows
  two : ∀ κ κ', mem κ = mem κ' → row κ = row κ' → κ = κ'
  all : ∀ a k b, W.kept[a]? = some k → b < k.rows → ∃ κ, mem κ = a ∧ row κ = b

variable {s K} {W : SwitchFrame} {mem row : K → ℕ} {pl : K → KeptPlace}

omit [Fintype K] [DecidableEq K] in
theorem slot_lt (A : SlotsAll K W mem row pl) (κ : K) :
    rowsBefore W.kept (mem κ) + row κ < keptRows W := by
  rw [rowsBefore_eq, keptRows_eq]
  have hlt : mem κ < W.kept.length := (List.getElem?_eq_some_iff.1 (A.member κ)).1
  have h1 := before_succ (fun k : KeptPlace => List.range k.rows) W.kept (mem κ) (pl κ) (A.member κ)
  have h2 := before_le (fun k : KeptPlace => List.range k.rows) W.kept (mem κ + 1)
    (W.kept.length - (mem κ + 1))
  rw [show mem κ + 1 + (W.kept.length - (mem κ + 1)) = W.kept.length by omega] at h2
  rw [List.length_range] at h1
  have := A.rowIn κ
  omega

theorem rowPlace_lt (A : SlotsAll K W mem row pl) (α : (s.cKept K).Aa) :
    rowPlace s K W mem row α < 1 + keptRows W + 2 := by
  rcases α with ⟨_ | κ, ⟨⟩⟩ | ⟨⟩ | ⟨⟩
  · show 0 < _
    omega
  · show 1 + (rowsBefore W.kept (mem κ) + row κ) < _
    have := slot_lt A κ
    omega
  · show 1 + (keptRows W + 0) < _
    omega
  · show 1 + (keptRows W + 1) < _
    omega

theorem rowPlace_inj (A : SlotsAll K W mem row pl) {α α' : (s.cKept K).Aa}
    (h : rowPlace s K W mem row α = rowPlace s K W mem row α') : α = α' := by
  have sl := slot_lt A
  rcases α with ⟨_ | κ, ⟨⟩⟩ | ⟨⟩ | ⟨⟩ <;> rcases α' with ⟨_ | κ', ⟨⟩⟩ | ⟨⟩ | ⟨⟩ <;>
    simp only [rowPlace] at h <;> first
      | rfl
      | (exfalso; have a1 := sl κ; omega)
      | (exfalso; have a2 := sl κ'; omega)
      | (exfalso; omega)
      | skip
  have e : rowsBefore W.kept (mem κ) + row κ = rowsBefore W.kept (mem κ') + row κ' := by omega
  rw [rowsBefore_eq, rowsBefore_eq] at e
  obtain ⟨e1, e2⟩ := block_inj (fun k : KeptPlace => List.range k.rows) (A.member κ)
    (by rw [List.length_range]; exact A.rowIn κ) (A.member κ')
    (by rw [List.length_range]; exact A.rowIn κ') e
  rw [A.two κ κ' e1 e2]

theorem rowPlace_onto (A : SlotsAll K W mem row pl) (c : ℕ) (hc : c < 1 + keptRows W + 2) :
    ∃ α : (s.cKept K).Aa, rowPlace s K W mem row α = c := by
  by_cases h0 : c = 0
  · exact ⟨.inl (none, ()), h0.symm⟩
  by_cases h1 : c - 1 < keptRows W
  · rw [keptRows_eq] at h1
    obtain ⟨a, k, b, hk, hb, e⟩ := block_onto (fun k : KeptPlace => List.range k.rows) W.kept _ h1
    rw [List.length_range] at hb
    obtain ⟨κ, rfl, rfl⟩ := A.all a k b hk hb
    refine ⟨.inl (some κ, ()), ?_⟩
    show 1 + (rowsBefore W.kept (mem κ) + row κ) = c
    rw [rowsBefore_eq]
    omega
  by_cases h2 : c = 1 + (keptRows W + 0)
  · exact ⟨.inr (.inl ()), h2.symm⟩
  · refine ⟨.inr (.inr ()), ?_⟩
    show 1 + (keptRows W + 1) = c
    omega

end Draw

/-! ## All rows -/

section All
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K] {Kh : Type} {Sk : Kh → Type} {t : ℕ}

/-- The sample rows of a kept member, as the switch lays them. -/
abbrev smpOf (St : Statement) (W : SwitchFrame) : KeptPlace → List OnBytes.Row :=
  fun k => (samplesOf St k).map (sampleRow W k)

/-- **The numbering.** -/
def rowNo (St : Statement) (W : SwitchFrame) (mem row : K → ℕ) (aOf : Kh → ℕ)
    (iOf : ∀ k, Sk k → ℕ) : Unit ⊕ (Σ k, Sk k) ⊕ (Fin t × (s.cKept K).Aa) → ℕ
  | .inl _ => 0
  | .inr (.inl ks) => 1 + (before (smpOf St W) W.kept (aOf ks.1) + iOf ks.1 ks.2)
  | .inr (.inr iα) =>
    1 + (allSamples St W + (iα.1.val * (1 + keptRows W + 2) + rowPlace s K W mem row iα.2))

/-- What is asked of the held messages' names. -/
structure Held (St : Statement) (W : SwitchFrame) (aOf : Kh → ℕ) (iOf : ∀ k, Sk k → ℕ) : Prop where
  member : ∀ k, ∃ p, W.kept[aOf k]? = some p ∧ ∀ σ, iOf k σ < (samplesOf St p).length
  twoK : ∀ k k', aOf k = aOf k' → k = k'
  twoS : ∀ k σ σ', iOf k σ = iOf k σ' → σ = σ'
  all : ∀ a p i, W.kept[a]? = some p → i < (samplesOf St p).length →
    ∃ k σ, aOf k = a ∧ iOf k σ = i

variable {s K} {St : Statement} {W : SwitchFrame} {mem row : K → ℕ} {pl : K → KeptPlace}
  {aOf : Kh → ℕ} {iOf : ∀ k, Sk k → ℕ}

theorem smp_lt (H : Held St W aOf iOf) (ks : Σ k, Sk k) :
    before (smpOf St W) W.kept (aOf ks.1) + iOf ks.1 ks.2 < allSamples St W := by
  obtain ⟨p, hp, hi⟩ := H.member ks.1
  have hlt : aOf ks.1 < W.kept.length := (List.getElem?_eq_some_iff.1 hp).1
  have h1 := before_succ (smpOf St W) W.kept (aOf ks.1) p hp
  have h2 := before_le (smpOf St W) W.kept (aOf ks.1 + 1) (W.kept.length - (aOf ks.1 + 1))
  rw [show aOf ks.1 + 1 + (W.kept.length - (aOf ks.1 + 1)) = W.kept.length by omega] at h2
  rw [List.length_map] at h1
  have := hi ks.2
  show _ < before (smpOf St W) W.kept W.kept.length
  omega

/-- **Two typed rows stand at two places.** -/
theorem rowNo_inj (A : SlotsAll K W mem row pl) (H : Held St W aOf iOf)
    {b b' : Unit ⊕ (Σ k, Sk k) ⊕ (Fin t × (s.cKept K).Aa)}
    (h : rowNo s K St W mem row aOf iOf b = rowNo s K St W mem row aOf iOf b') : b = b' := by
  rcases b with ⟨⟩ | ks | ⟨i, α⟩ <;> rcases b' with ⟨⟩ | ks' | ⟨i', α'⟩ <;>
    simp only [rowNo] at h
  · rfl
  · omega
  · omega
  · omega
  · obtain ⟨k, σ⟩ := ks
    obtain ⟨k', σ'⟩ := ks'
    dsimp only at h
    obtain ⟨p, hp, hi⟩ := H.member k
    obtain ⟨p', hp', hi'⟩ := H.member k'
    obtain ⟨e1, e2⟩ := block_inj (smpOf St W) hp (by rw [List.length_map]; exact hi σ) hp'
      (by rw [List.length_map]; exact hi' σ') (by omega)
    obtain rfl := H.twoK k k' e1
    rw [H.twoS k σ σ' e2]
  · have := smp_lt H ks
    omega
  · omega
  · have := smp_lt H ks'
    omega
  · have c1 := rowPlace_lt (s := s) A α
    have c2 := rowPlace_lt (s := s) A α'
    have e : i.val * (1 + keptRows W + 2) + rowPlace s K W mem row α =
        i'.val * (1 + keptRows W + 2) + rowPlace s K W mem row α' := by omega
    have ei : i.val = i'.val := by
      have d1 : (i.val * (1 + keptRows W + 2) + rowPlace s K W mem row α) / (1 + keptRows W + 2) =
          i.val := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt c1, Nat.add_zero]
      have d2 : (i'.val * (1 + keptRows W + 2) + rowPlace s K W mem row α') /
          (1 + keptRows W + 2) = i'.val := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt c2, Nat.add_zero]
      rw [← d1, ← d2, e]
    have eα : rowPlace s K W mem row α = rowPlace s K W mem row α' := by
      rw [ei] at e
      omega
    rw [Fin.ext ei, rowPlace_inj A eα]

/-- **Every place below 1 + (all sample rows) + t * (the rows of a draw) is a typed row's.** -/
theorem rowNo_onto (A : SlotsAll K W mem row pl) (H : Held St W aOf iOf) (m : ℕ)
    (hm : m < 1 + allSamples St W + t * (1 + keptRows W + 2)) :
    ∃ b : Unit ⊕ (Σ k, Sk k) ⊕ (Fin t × (s.cKept K).Aa),
      rowNo s K St W mem row aOf iOf b = m := by
  by_cases h0 : m = 0
  · exact ⟨.inl (), h0.symm⟩
  by_cases h1 : m - 1 < allSamples St W
  · obtain ⟨a, p, i, hp, hi, e⟩ := block_onto (smpOf St W) W.kept (m - 1) h1
    rw [List.length_map] at hi
    obtain ⟨k, σ, rfl, rfl⟩ := H.all a p i hp hi
    refine ⟨.inr (.inl ⟨k, σ⟩), ?_⟩
    show 1 + (before (smpOf St W) W.kept (aOf k) + iOf k σ) = m
    omega
  · have hR : 0 < 1 + keptRows W + 2 := by omega
    have hq : (m - 1 - allSamples St W) / (1 + keptRows W + 2) < t :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    obtain ⟨α, hα⟩ := rowPlace_onto (s := s) A ((m - 1 - allSamples St W) % (1 + keptRows W + 2))
      (Nat.mod_lt _ hR)
    refine ⟨.inr (.inr (⟨_, hq⟩, α)), ?_⟩
    show 1 + (allSamples St W + ((m - 1 - allSamples St W) / (1 + keptRows W + 2) *
      (1 + keptRows W + 2) + rowPlace s K W mem row α)) = m
    rw [hα, Nat.div_add_mod']
    omega

end All

/-- The number of rows that a switch lays. -/
theorem rows_length {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : ℕ} {anew : Array ℕ}
    {pos : Positions} {y : Array OnBytes.E} {rows : List OnBytes.Row} {W : SwitchFrame}
    {carried : OnBytes.Row} (L : Laid S old T g anew pos y rows W carried) :
    rows.length = 1 + allSamples S W + pos.draws.toList.length * (1 + keptRows W + old.masks) := by
  have hR : ∀ x ∈ pos.draws.toList, (switchGenerators W old x (symAtB old pos y x)).length =
      1 + keptRows W + old.masks := fun x _ => gens_length W old x _
  rw [L.rows, List.length_append, List.length_cons, length_flatMap_before, length_flatMap_before,
    before_const _ _ _ _ hR (Nat.le_refl _)]
  show before _ W.kept W.kept.length + 1 + _ = 1 + before _ W.kept W.kept.length + _
  omega

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.rowNo_inj
#print axioms VerifiableInference.Desc.First.K2Hands.rowNo_onto
#print axioms VerifiableInference.Desc.First.K2Hands.rows_length
