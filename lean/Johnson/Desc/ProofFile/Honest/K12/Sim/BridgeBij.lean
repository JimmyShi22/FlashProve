-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BridgeBij.lean: the map from a proximity test's numbered coins
from the first switch on to the finite type of its random values (`toBody`, Sim/Bridge.lean) is one
to one and onto. Combinatorics of numbers. General: at every stage s and every list rest of the
stages after it, under one hypothesis on the stages' numbers. One structure, one definition,
theorems. Sim/CoreOwn.lean, which imports this file, calls `toBody_bij` and `takes_body`.

In the list: numbered coins are a function c : ℕ → `GE`: an element of the extension field at every
number. A reading rd takes a number off and numbered coins, and returns a value. The window is the
numbers i with off ≤ i < off + n. A stage (`Fmt.M1.Stage`, Fmt/M1Types.lean) has two codes C and Z,
each with numbers a, l and r, and numbers k, h and t. A switch goes from a stage cur to the stage
next after it. The finite type is `BodyK GE s rest` (Johnson/Prover/Link/LinkCoin.lean): for each
switch along s :: rest a `SwK` and, with it, a `RideK` where a further switch follows, or a `WordK`
at the last switch; `Unit` where rest is empty. `SwK`, `RideK` and `WordK` are structures whose
fields are functions on `Fin`. Typed coins are `Cs ⟨0, n⟩` (the frame,
Johnson/Desc/ProofFile/Honest/Frame.lean): n elements of the extension field and none of the base
field, the count stated by the type. `stretchOf` (Johnson/Desc/ProofFile/Honest/K12/Coins.lean)
reads them by number and returns 0 from the count on. The counts `dueFresh`, `dueWord`, `freeRoom`,
`dueSwitch` and `dueFrom` are defined in Coins.lean.

  `toBody_bij`: typed coins to the finite type: one to one and onto. The map takes c in
    `Cs ⟨0, dueFrom s rest⟩` to `toBody s rest 0 (stretchOf c).e` in `BodyK GE s rest`. Hypothesis:
    h ≤ k at every stage in rest
  `takes_body`: along the stages: `toBody` uses just `dueFrom` coins. In Lean:
    `Takes (toBody cur rest) (dueFrom cur rest)`. Under the same hypothesis
  `Takes rd n`: a reading rd of a value off numbered coins, from a number off on, uses just the n
    coins from off on: it reads no other (`congr`); it determines each of them (`inj`); every value
    is read off some coins, whatever stands outside the window (`patch`). A structure in `Prop` with
    these three fields, each at every off
  `takes_unit`, `takes_vec`, `takes_mat`: `Takes rd n` for three readings rd: the one that returns
    `()`, at n = 0; a row of n entries, entry i at the number `off + i`, at n; m rows of r entries,
    entry q of row b at the number `off + b * r + q`, at `m * r`
  `Takes.pair`: from `Takes rd₁ n₁` and `Takes rd₂ n₂`: `Takes` at `n₁ + n₂` for the pair of rd₁
    from off on and rd₂ from `off + n₁` on
  `Takes.map`: from `Takes rd n`: `Takes` at n for rd followed by a map that is one to one and onto
  `Takes.of_eq`: `Takes rd' n'` goes over to rd and n, where rd and rd' return the same value at
    every off and c, and n = n'
  `takes_sw`, `takes_ride`, `takes_word`: `Takes` for three readings of Sim/Bridge.lean:
    `swOf cur next` at `dueSw cur next`; `rideOf next` at `dueFresh next`; `wordOf next` at
    `dueWord next`. The first two under h ≤ k at next, the third without a hypothesis
  `dueSw cur next`: a definition: the count in `takes_sw`: the first three summands of `dueSwitch`
    at cur and next, that is `2 ^ k * C.r + freeRoom cur next + 2 ^ h * Z.r` at the k, h, C, Z of
    next
  `rideAt_eq`: `rideAt cur next off` (Sim/Bridge.lean) is `off + dueSw cur next`
  `sw_bij`, `ride_bij`, `word_bij`: the map from the tuple of its fields to a `SwK`, to a `RideK`,
    to a `WordK` is one to one and onto
  `sg_k`: where h ≤ k at a stage, h + g of its `sgOf` (Johnson/Desc/K12/Law/ChainOf.lean, where g is
    k - h) is its k

By what. `toBody_bij` takes `takes_body` at off = 0: `inj` gives one to one; `patch` and `congr`
give onto. Below the count `stretchOf` returns the coin of that number, by unfolding. `takes_body`
goes by recursion along the three cases of the definition of `toBody`: `takes_unit`; `takes_sw`
paired with `takes_word`; `takes_sw` paired with `takes_ride` and with the statement at the shorter
list. The counts add up by unfolding `dueSwitch`, `dueFrom` and `dueSw`. `takes_sw` and `takes_ride`
join `takes_vec` and `takes_mat`, and `takes_word` joins `takes_vec` only, by `Takes.pair`; then
comes `Takes.map` at `sw_bij`, `ride_bij` or `word_bij`, then `Takes.of_eq`. `sg_k` turns h + g into
k. `takes_mat` follows from `takes_vec` at `m * r` by `Takes.map`, along a map that is shown one to
one and onto by division with remainder. The proofs name no lemma of another file of this library:
those that they name are of Lean's core or of Mathlib.

Limits. The two main theorems have the hypothesis h ≤ k at every stage after the first; where it
fails, nothing is stated. At `sgOf` of a stage the types in LinkCoin.lean have h + (k - h) where the
counts in Coins.lean have k. No property is claimed; nothing here speaks of a law or of a simulator.
The statements are on the map `toBody` only: nothing on which of these values a definition of a
prover reads, or how often. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-! ## 1 Readings off a window of numbered coins -/

/-- A reading uses just the n coins from off on. `congr`: if c and c' agree at every number i with
off ≤ i < off + n, then rd off c = rd off c'. `inj`: if rd off c = rd off c', then c and c'
agree at every such i. `patch`: for every value a and every c₀ there is a c with rd off c = a
that agrees with c₀ at every i with i < off or off + n ≤ i. -/
structure Takes {α : Type} (rd : ℕ → (ℕ → GE) → α) (n : ℕ) : Prop where
  congr : ∀ off c c', (∀ i, off ≤ i → i < off + n → c i = c' i) → rd off c = rd off c'
  inj : ∀ off c c', rd off c = rd off c' → ∀ i, off ≤ i → i < off + n → c i = c' i
  patch : ∀ off a (c₀ : ℕ → GE), ∃ c, rd off c = a ∧ ∀ i, (i < off ∨ off + n ≤ i) → c i = c₀ i

theorem takes_unit : Takes (fun _ _ => ()) 0 :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ i h1 h2 => by omega, fun _ _ c₀ => ⟨c₀, rfl, fun _ _ => rfl⟩⟩

theorem takes_vec (n : ℕ) : Takes (fun off c (i : Fin n) => c (off + i.val)) n where
  congr := fun off c c' h => funext fun i => h _ (by omega) (by have := i.isLt; omega)
  inj := fun off c c' h i h1 h2 => by
    have e := congrFun h ⟨i - off, by omega⟩
    simp only at e
    rwa [show off + (i - off) = i by omega] at e
  patch := fun off a c₀ =>
    ⟨fun i => if h : off ≤ i ∧ i - off < n then a ⟨i - off, h.2⟩ else c₀ i, funext fun i => by
      have h : off ≤ off + i.val ∧ off + i.val - off < n :=
        ⟨by omega, by have := i.isLt; omega⟩
      show (if h : off ≤ off + i.val ∧ off + i.val - off < n then a ⟨off + i.val - off, h.2⟩
        else c₀ (off + i.val)) = a i
      rw [dif_pos h]
      exact congrArg a (Fin.ext (by show off + i.val - off = i.val; omega)),
      fun i hi => dif_neg (by omega)⟩

theorem Takes.of_eq {α : Type} {rd rd' : ℕ → (ℕ → GE) → α} {n n' : ℕ} (h : Takes rd' n')
    (e : ∀ off c, rd off c = rd' off c) (en : n = n') : Takes rd n := by
  subst en
  have : rd = rd' := funext fun off => funext fun c => e off c
  rw [this]
  exact h

theorem Takes.map {α β : Type} {rd : ℕ → (ℕ → GE) → α} {n : ℕ} (h : Takes rd n) (e : α → β)
    (he : Function.Bijective e) : Takes (fun off c => e (rd off c)) n where
  congr := fun off c c' hc => congrArg e (h.congr off c c' hc)
  inj := fun off c c' hc => h.inj off c c' (he.1 hc)
  patch := fun off b c₀ => by
    obtain ⟨a, rfl⟩ := he.2 b
    obtain ⟨c, h1, h2⟩ := h.patch off a c₀
    exact ⟨c, congrArg e h1, h2⟩

theorem Takes.pair {α β : Type} {rd₁ : ℕ → (ℕ → GE) → α} {rd₂ : ℕ → (ℕ → GE) → β} {n₁ n₂ : ℕ}
    (h₁ : Takes rd₁ n₁) (h₂ : Takes rd₂ n₂) :
    Takes (fun off c => (rd₁ off c, rd₂ (off + n₁) c)) (n₁ + n₂) where
  congr := fun off c c' hc => Prod.ext
    (h₁.congr off c c' fun i a b => hc i a (by omega))
    (h₂.congr (off + n₁) c c' fun i a b => hc i (by omega) (by omega))
  inj := fun off c c' hc i a b => by
    by_cases hi : i < off + n₁
    · exact h₁.inj off c c' (congrArg Prod.fst hc) i a hi
    · exact h₂.inj (off + n₁) c c' (congrArg Prod.snd hc) i (by omega) (by omega)
  patch := fun off x c₀ => by
    obtain ⟨c₁, e1, o1⟩ := h₂.patch (off + n₁) x.2 c₀
    obtain ⟨c₂, e2, o2⟩ := h₁.patch off x.1 c₁
    refine ⟨c₂, Prod.ext e2 ?_, fun i hi => ?_⟩
    · show rd₂ (off + n₁) c₂ = x.2
      rw [← e1]
      exact h₂.congr (off + n₁) c₂ c₁ fun i a _ => o2 i (Or.inr a)
    · rw [o2 i (by omega), o1 i (by omega)]

theorem takes_mat (m r : ℕ) :
    Takes (fun off c (b : Fin m) (q : Fin r) => c (off + b.val * r + q.val)) (m * r) := by
  have lt : ∀ (b : Fin m) (q : Fin r), b.val * r + q.val < m * r := fun b q =>
    calc b.val * r + q.val < b.val * r + r := by have := q.isLt; omega
      _ = (b.val + 1) * r := by ring
      _ ≤ m * r := Nat.mul_le_mul_right r b.isLt
  have pos : ∀ n : ℕ, n < m * r → 0 < r := fun n hn =>
    Nat.pos_of_ne_zero fun h0 => by
      rw [h0, Nat.mul_zero] at hn
      exact Nat.not_lt_zero _ hn
  let e : (Fin (m * r) → GE) → Fin m → Fin r → GE := fun v b q => v ⟨b.val * r + q.val, lt b q⟩
  have he : Function.Bijective e := by
    constructor
    · intro v v' h
      funext i
      have hr := pos i.val i.isLt
      have hb : i.val / r < m :=
        Nat.div_lt_of_lt_mul (lt_of_lt_of_eq i.isLt (Nat.mul_comm m r))
      have e1 := congrFun (congrFun h ⟨i.val / r, hb⟩) ⟨i.val % r, Nat.mod_lt _ hr⟩
      have e2 : i.val / r * r + i.val % r = i.val := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod _ _
      have e3 : (⟨i.val / r * r + i.val % r, lt ⟨i.val / r, hb⟩ ⟨i.val % r, Nat.mod_lt _ hr⟩⟩ :
          Fin (m * r)) = i := Fin.ext e2
      show v i = v' i
      rw [← e3]
      exact e1
    · intro M
      refine ⟨fun i => M
        ⟨i.val / r, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq i.isLt (Nat.mul_comm m r))⟩
        ⟨i.val % r, Nat.mod_lt _ (pos i.val i.isLt)⟩, funext fun b => funext fun q => ?_⟩
      have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) q.isLt
      have d1 : (b.val * r + q.val) / r = b.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt q.isLt, Nat.zero_add]
      have d2 : (b.val * r + q.val) % r = q.val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt q.isLt]
      show M ⟨(b.val * r + q.val) / r, _⟩ ⟨(b.val * r + q.val) % r, _⟩ = M b q
      congr 1
      · exact Fin.ext d1
      · exact Fin.ext d2
  exact ((takes_vec (m * r)).map e he).of_eq
    (fun off c => funext fun b => funext fun q => congrArg c (Nat.add_assoc _ _ _)) rfl

/-! ## 2 The structures `SwK`, `RideK` and `WordK` -/

section Fields
variable (cur next : Fmt.M1.Stage)

theorem sw_bij : Function.Bijective fun x : (Fin (2 ^ ((sgOf next).h + (sgOf next).g)) →
      Fin (sgOf next).C.r → GE) × (Fin (Fmt.M1.fillOf (sgOf cur).st (sgOf next).st) → GE) ×
      (Fin (2 ^ (sgOf next).h) → Fin (sgOf next).Z.r → GE) =>
    (⟨x.1, x.2.1, x.2.2⟩ : SwK GE (sgOf cur) (sgOf next)) :=
  ⟨fun a b h => by
    injection h with h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3), fun k => ⟨(k.mainTail, k.free, k.maskTail), rfl⟩⟩

theorem ride_bij : Function.Bijective fun x : (Fin (2 * ((sgOf next).h + (sgOf next).g) + 1) → GE) ×
      (Fin (2 ^ (sgOf next).h) → Fin (sgOf next).Z.r → GE) =>
    (⟨x.1, x.2⟩ : RideK GE (sgOf next)) :=
  ⟨fun a b h => by
    injection h with h1 h2
    exact Prod.ext h1 h2, fun k => ⟨(k.W, k.tail), rfl⟩⟩

theorem word_bij : Function.Bijective fun x : (Fin (sgOf next).C.r → GE) ×
      (Fin (sgOf next).C.l → GE) × (Fin (sgOf next).Z.l → GE) × (Fin (sgOf next).Z.r → GE) =>
    (⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩ : WordK GE (sgOf next)) :=
  ⟨fun a b h => by
    injection h with h1 h2 h3 h4
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)),
    fun k => ⟨(k.mainTail, k.main, k.mask, k.maskTail), rfl⟩⟩

theorem sg_k (h : next.h ≤ next.k) : (sgOf next).h + (sgOf next).g = next.k :=
  Nat.add_sub_cancel' h

/-- The coins of a switch's own message. A count: the first three summands of `dueSwitch`
(Johnson/Desc/ProofFile/Honest/K12/Coins.lean). -/
def dueSw : ℕ := 2 ^ next.k * next.C.r + freeRoom cur next + 2 ^ next.h * next.Z.r

theorem rideAt_eq (off : ℕ) : rideAt cur next off = off + dueSw cur next := by
  unfold rideAt dueSw
  omega

theorem takes_sw (h : next.h ≤ next.k) : Takes (swOf cur next) (dueSw cur next) := by
  have hk := sg_k next h
  refine (((takes_mat (2 ^ ((sgOf next).h + (sgOf next).g)) (sgOf next).C.r).pair
    ((takes_vec (Fmt.M1.fillOf (sgOf cur).st (sgOf next).st)).pair
      (takes_mat (2 ^ (sgOf next).h) (sgOf next).Z.r))).map _ (sw_bij cur next)).of_eq
    (fun off c => ?_) ?_
  · unfold swOf
    simp only [hk]
    rfl
  · unfold dueSw
    rw [hk]
    show _ = 2 ^ next.k * next.C.r + (freeRoom cur next + 2 ^ next.h * next.Z.r)
    omega

theorem takes_ride (h : next.h ≤ next.k) : Takes (rideOf next) (dueFresh next) := by
  have hk := sg_k next h
  refine (((takes_vec (2 * ((sgOf next).h + (sgOf next).g) + 1)).pair
    (takes_mat (2 ^ (sgOf next).h) (sgOf next).Z.r)).map _ (ride_bij next)).of_eq
    (fun off c => ?_) ?_
  · unfold rideOf
    simp only [hk]
    rfl
  · unfold dueFresh
    rw [hk]
    rfl

theorem takes_word : Takes (wordOf next) (dueWord next) := by
  refine (((takes_vec (sgOf next).C.r).pair ((takes_vec (sgOf next).C.l).pair
    ((takes_vec (sgOf next).Z.l).pair (takes_vec (sgOf next).Z.r)))).map _ (word_bij next)).of_eq
    (fun off c => rfl) ?_
  unfold dueWord
  show _ = next.C.r + (next.C.l + (next.Z.l + next.Z.r))
  omega

end Fields

/-! ## 3 Along the stages -/

/-- **`toBody` uses just `dueFrom` coins.** Hypothesis: h ≤ k at every stage in rest. -/
theorem takes_body : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage), (∀ st ∈ rest, st.h ≤ st.k) →
    Takes (toBody cur rest) (dueFrom cur rest)
  | _, [], _ => takes_unit
  | cur, [next], h => by
    refine ((takes_sw cur next (h next (by simp))).pair (takes_word next)).of_eq
      (fun off c => ?_) ?_
    · show (swOf cur next off c, wordOf next (rideAt cur next off) c) = _
      rw [rideAt_eq]
    · show dueSwitch cur next true + 0 = _
      unfold dueSwitch dueSw
      simp
  | cur, next :: n₂ :: rest, h => by
    have ih := takes_body next (n₂ :: rest) fun st hst => h st (List.mem_cons_of_mem _ hst)
    have hn := h next (by simp)
    refine ((takes_sw cur next hn).pair ((takes_ride next hn).pair ih)).of_eq (fun off c => ?_) ?_
    · show (swOf cur next off c, rideOf next (rideAt cur next off) c,
        toBody next (n₂ :: rest) (off + dueSwitch cur next false) c) = _
      have e : off + dueSwitch cur next false = off + dueSw cur next + dueFresh next := by
        unfold dueSwitch dueSw
        simp only [Bool.false_eq_true, if_false]
        omega
      rw [e, rideAt_eq]
    · show dueSwitch cur next false + dueFrom next (n₂ :: rest) = _
      unfold dueSwitch dueSw
      simp only [Bool.false_eq_true, if_false]
      omega

/-- **Typed coins to the finite type: one to one and onto.** The map takes c to
`toBody s rest 0 (stretchOf c).e`. Hypothesis h: h ≤ k at every stage in rest. -/
theorem toBody_bij (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (h : ∀ st ∈ rest, st.h ≤ st.k) :
    Function.Bijective fun c : Cs ⟨0, dueFrom s rest⟩ => toBody s rest 0 (stretchOf c).e := by
  have hg := takes_body s rest h
  have rd : ∀ (c : Cs ⟨0, dueFrom s rest⟩) (i : Fin (dueFrom s rest)),
      (stretchOf c).e i.val = c.e i := fun c i => dif_pos i.isLt
  constructor
  · intro c c' hc
    have e := hg.inj 0 _ _ hc
    cases c with
    | mk f e₁ =>
      cases c' with
      | mk f' e₂ =>
        have h1 : f = f' := funext fun i => i.elim0
        have h2 : e₁ = e₂ := funext fun i => by
          have hi : i.val < dueFrom s rest := i.isLt
          have := e i.val (Nat.zero_le _) (by omega)
          rwa [rd, rd] at this
        rw [h1, h2]
  · intro k
    obtain ⟨c, hc, -⟩ := hg.patch 0 k fun _ => 0
    refine ⟨⟨fun i => i.elim0, fun i => c i.val⟩, ?_⟩
    show toBody s rest 0 _ = k
    rw [← hc]
    exact hg.congr 0 _ _ fun i _ hi => dif_pos (show i < dueFrom s rest by omega)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.takes_unit
#print axioms ProofFile.Honest.K12.takes_vec
#print axioms ProofFile.Honest.K12.Takes.of_eq
#print axioms ProofFile.Honest.K12.Takes.map
#print axioms ProofFile.Honest.K12.Takes.pair
#print axioms ProofFile.Honest.K12.takes_mat
#print axioms ProofFile.Honest.K12.sw_bij
#print axioms ProofFile.Honest.K12.ride_bij
#print axioms ProofFile.Honest.K12.word_bij
#print axioms ProofFile.Honest.K12.sg_k
#print axioms ProofFile.Honest.K12.rideAt_eq
#print axioms ProofFile.Honest.K12.takes_sw
#print axioms ProofFile.Honest.K12.takes_ride
#print axioms ProofFile.Honest.K12.takes_word
#print axioms ProofFile.Honest.K12.takes_body
#print axioms ProofFile.Honest.K12.toBody_bij
#print axioms ProofFile.Honest.K12.Takes
#print axioms ProofFile.Honest.K12.dueSw
