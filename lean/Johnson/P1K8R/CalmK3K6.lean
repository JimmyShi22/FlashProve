-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/CalmK3K6.lean: four lots of the first chain are quiet (Johnson/P1K8R/CalmLots.lean):
no part of theirs has a first stop that fires, and each states the share 0 for it.

  k3_calm, k4_calm, k5_calm, k6_calm   the lots of the kinds K3, K4, K5 and K6, as widerPairs
      writes them, at every type of own state, with no premise
  namespace K3K6   what these need: a lifted part and two parts as one are quiet if their sources
      are, the lots made by HLot.byPub and HLot.byRows are quiet if what they wrap is, and each
      kind's row is quiet

Limits. Nothing is said of the first stop, of a run, or of any other lot.
-/
import Johnson.P1K8R.CalmLots
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open OnBytes.Desc.First.K4.Honest (K4Pub)

namespace K3K6

variable {V W X V' W' Y : Type}

/-! ## Lists -/

theorem all_nil {A : Type} {P : A → Prop} : ∀ x ∈ ([] : List A), P x :=
  fun _ h => by cases h

theorem all_cons {A : Type} {P : A → Prop} {a : A} {l : List A} (ha : P a)
    (hl : ∀ x ∈ l, P x) : ∀ x ∈ a :: l, P x := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | h
  · exact ha
  · exact hl x h

theorem all_append {A : Type} {P : A → Prop} {a b : List A} (ha : ∀ x ∈ a, P x)
    (hb : ∀ x ∈ b, P x) : ∀ x ∈ a ++ b, P x :=
  fun x hx => (List.mem_append.1 hx).elim (ha x) (hb x)

theorem ite_of {A : Type} {P : A → Prop} {c : Prop} [Decidable c] {a b : A} (ha : P a)
    (hb : P b) : P (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    exact hb

theorem all_ite {A : Type} {P : A → Prop} {c : Prop} [Decidable c] {a b : List A}
    (ha : ∀ x ∈ a, P x) (hb : ∀ x ∈ b, P x) : ∀ x ∈ (if c then a else b), P x := by
  by_cases h : c
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    exact hb

/-- What a value of an option's map is made of. -/
theorem map_some {A B : Type} {f : A → B} {o : Option A} {b : B} (h : o.map f = some b) :
    ∃ a, f a = b := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, Option.some.inj h⟩

/-! ## Parts -/

/-- A part is quiet if its first stop is none everywhere and its share's numerator is 0. -/
theorem calm_of_zero (p : Part V W X) (h : ∀ l o, p.bad l o = none)
    (s : p.badShare.num = 0) : Calm p :=
  ⟨h, by simp [Odds.val, s]⟩

/-- A share of the value 0 has the numerator 0. -/
theorem num_zero {o : Odds} (h : o.val = 0) : o.num = 0 := by
  have h' : (o.num : ENNReal) / (o.den : ENNReal) = 0 := h
  rcases ENNReal.div_eq_zero_iff.1 h' with e | e
  · exact_mod_cast e
  · exact absurd e (ENNReal.natCast_ne_top _)

/-- A lifted part is quiet if its source is. -/
theorem calm_lift {see : V → V'} {wit : W → W'} {get : X → Y} {set : X → Y → X}
    {p : Part V' W' Y} (h : Calm p) : Calm (Part.lift see wit get set p) :=
  ⟨fun l o => h.1 l o, h.2⟩

/-- Every part of a lifted list is quiet if every part of the list is. -/
theorem calm_lifted {see : V → V'} {wit : W → W'} {get : X → Y} {set : X → Y → X}
    {ps : List (Part V' W' Y)} (h : ∀ p ∈ ps, Calm p) {q : Part V W X}
    (hq : q ∈ ps.map (Part.lift see wit get set)) : Calm q := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  exact calm_lift (h p hp)

/-- Two stops that never fire, as one, never fire. -/
theorem stopBoth_none (n m : ℕ) {f g : List Fmt.Drawn → List Fmt.Drawn → Option String}
    (hf : ∀ a b, f a b = none) (hg : ∀ a b, g a b = none) (a b : List Fmt.Drawn) :
    stopBoth n m f g a b = none := by
  simp [stopBoth, hf, hg]

/-- Two parts as one are quiet if both are. -/
theorem calm_andThen {p q : Part V W X} (hp : Calm p) (hq : Calm q) :
    Calm (p.andThen q) :=
  calm_of_zero _ (fun l o => stopBoth_none _ _ hp.1 hq.1 l o) (by
    show p.badShare.num * q.badShare.den + q.badShare.num * p.badShare.den = 0
    rw [num_zero hp.2, num_zero hq.2, Nat.zero_mul, Nat.zero_mul])

/-! ## Lots -/

/-- A lot that reads the index at the public part is quiet if it is at every reader. -/
theorem lotCalm_byPub {W₀ : Type} (weights : ProofFile.Pub → W₀ → Weights)
    (L : (W₀ → Weights) → HLot V W X) (h : ∀ wt, LotCalm (L wt)) :
    LotCalm (HLot.byPub weights L) :=
  fun Z G => h (weights Z) Z G

/-- A lot that reads the rows' data is quiet if it is at all data. -/
theorem lotCalm_byRows {Xi : Type} (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi)
    (L : RowDataOf Xi → HLot V W X) (h : ∀ d, LotCalm (L d)) :
    LotCalm (HLot.byRows D L) :=
  fun Z G => h (D Z G) Z G

/-! ## K3 -/

theorem partOf_calm (R : K3.Reads) (J : K3.LookJobs W) (a : K3.At) (s : K3.Stage) (i : ℕ) :
    Calm (K3.partOf (V := V) R J a s i) := by
  unfold K3.partOf
  split
  · exact calm_of_zero _ (fun _ _ => rfl) rfl
  · exact calm_of_zero _ (fun _ _ => rfl) rfl

theorem lookRow_calm (R : K3.Reads) (J : K3.LookJobs W) (a : K3.At) :
    ∀ p ∈ K3.lookRow (V := V) R J a, Calm p := by
  intro p hp
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hp
  exact partOf_calm R J a y.1 y.2

theorem lookSeat_calm {W₁ : Type} (R : K3.Reads) (J : K3.LookJobs W) (wit : W₁ → W)
    (a : K3.At) : HalfCalm (K3.proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) R J wit a) := by
  intro q hq
  exact calm_lifted (lookRow_calm R J a) hq

theorem lotBy_calm (row : K3.Site → List (Part V W X)) (h : ∀ s, ∀ p ∈ row s, Calm p) :
    LotCalm (K3.lotBy row) := by
  intro Z G x hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 hx
  exact h s

theorem rowLot_calm (A : K3.Fill W) : LotCalm (K3.rowLot (V := V) (X := X) A) :=
  lotBy_calm _ fun s => lookSeat_calm _ _ _ _

theorem rowLotAt_calm (A : ProofFile.Pub → K3.Fill W) :
    LotCalm (K3.rowLotAt (V := V) (X := X) A) :=
  fun Z G => rowLot_calm (A Z) Z G

/-! ## K4 -/

theorem k4Sorts_calm {Pb : Type} (Q : K4Pub) :
    ∀ s ∈ K4.k4Sorts (Pb := Pb) Q, ∀ i, Calm (s.part i) := by
  unfold K4.k4Sorts
  try dsimp only
  refine all_append (all_append ?_ (all_ite ?_ ?_)) ?_
  all_goals
    repeat' first
      | exact all_nil
      | exact fun _ => calm_of_zero _ (fun _ _ => rfl) rfl
      | exact ite_of (P := fun s : K4.K4Sort Pb => ∀ i, Calm (s.part i))
          (fun _ => calm_of_zero _ (fun _ _ => rfl) rfl)
          (fun _ => calm_of_zero _ (fun _ _ => rfl) rfl)
      | refine all_cons ?_ ?_

theorem k4RowIn_calm (Q : K4Pub) : ∀ p ∈ K4.k4RowIn Q, Calm p := by
  intro p hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp
  exact k4Sorts_calm Q y.1 (List.fst_mem_of_mem_zipIdx hy) y.2

theorem k4Half_calm {W₀ Rc Xi Tr : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (Q : K4Pub) : HalfCalm (K4.k4Half (Rc := Rc) (X := X) cells weights tokens look Q) := by
  intro q hq
  exact calm_lifted (k4RowIn_calm Q) hq

theorem k4HLot_calm {W₀ Rc Tr : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    LotCalm (K4.k4HLot (Rc := Rc) (X := X) cells weights look) := by
  intro Z G x hx
  obtain ⟨y, _, hy⟩ := List.mem_filterMap.1 hx
  obtain ⟨Q, rfl⟩ := map_some hy
  exact k4Half_calm _ _ _ _ Q

/-! ## K5 -/

theorem rowOf_calm (a : Place) (x : OnBytes.Params.AttentionRounds)
    (c : List Fmt.Drawn → H2K5.Honest.Chal) (J : K5.Jobs W) :
    ∀ p ∈ K5.rowOf a x c J, Calm p := by
  intro p hp
  obtain ⟨s, _, rfl⟩ := List.mem_map.1 hp
  rcases s with ⟨sh, i⟩
  cases sh with
  | sum k => exact calm_of_zero _ (fun _ _ => rfl) rfl
  | one n =>
    cases n with
    | zero => exact calm_of_zero _ (fun _ _ => rfl) rfl
    | succ n => exact calm_of_zero _ (fun _ _ => rfl) rfl

theorem k5Half_calm {W₀ Rc Xi Tr : Type} (cells : Tr → Cells) (Z : K5.Seat5) :
    HalfCalm (K5.k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z) := by
  intro q hq
  exact calm_lifted (ps := K5.k5Row Z) (rowOf_calm _ _ _ _) hq

theorem k5LotK_calm {W₀ Rc Xi Tr : Type} (cells : Tr → Cells)
    (keyOf : ProofFile.Pub → ProofFile.Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) :
    LotCalm (K5.k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf) := by
  intro Z G x hx
  obtain ⟨y, _, hy⟩ := List.mem_filterMap.1 hx
  obtain ⟨Q, rfl⟩ := map_some hy
  exact k5Half_calm _ Q

/-! ## K6 -/

theorem headParts_calm (p : VerifiableInference.Desc.Kinds.Head.Par) (at_ : Place) :
    ∀ q ∈ K6.headParts p at_, Calm q := by
  unfold K6.headParts
  try dsimp only
  repeat' first
    | exact all_nil
    | exact calm_of_zero _ (fun _ _ => rfl) rfl
    | refine all_cons ?_ ?_

theorem headLot_calm {W₀ Rc Tr : Type} (fits : ProofFile.Pub → ProofFile.Ground → Bool)
    (wit : ProofFile.Pub → ProofFile.Ground → Local W₀ Rc ProofFile.Inst Tr → K6.HeadAsk) :
    LotCalm (K6.headLot (X := X) fits wit) := by
  intro Z G x hx
  change x ∈ (if fits Z G = true then _ else _) at hx
  by_cases hf : fits Z G = true
  · rw [if_pos hf] at hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
    intro q hq
    exact calm_lifted (headParts_calm _ _) hq
  · rw [if_neg hf] at hx
    cases hx

end K3K6

open K3K6

variable {W₀ X : Type}

/-- **K3's lot is quiet.** -/
theorem k3_calm (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : LotCalm (HLot.byPub I.weights (LongLots.plain (X := X) o S O).k3) :=
  lotCalm_byPub _ _ fun _ => rowLotAt_calm _

/-- **K4's lot is quiet.** -/
theorem k4_calm (I : WiderIn W₀) :
    LotCalm (HLot.byPub I.weights fun wt =>
      K4.k4HLot (Rc := IndexCommitterCoins) (X := X) id wt fun _ _ => K4.k4LookAt) :=
  lotCalm_byPub _ _ fun _ => k4HLot_calm _ _ _

/-- **K5's lot is quiet.** -/
theorem k5_calm (O : OnlineProverArguments) :
    LotCalm (K5.k5LotK (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := X) id O.keyOf) :=
  k5LotK_calm _ _

/-- **K6's lot is quiet.** -/
theorem k6_calm (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : LotCalm (HLot.byPub I.weights (LongLots.plain (X := X) o S O).k6) :=
  lotCalm_byPub _ _ fun _ => headLot_calm _ _

-- The four theorems state the lots that stand at places 5 to 8 of the filling's list, from 0.
example (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ L ∈ ((widerFillAt I o S O).lots.drop 5).take 4, LotCalm L :=
  all_cons (k3_calm I o S O) (all_cons (k4_calm I) (all_cons (k5_calm O)
    (all_cons (k6_calm I o S O) all_nil)))

end P1K8

#print axioms P1K8.K3K6.calm_lift
#print axioms P1K8.K3K6.calm_andThen
#print axioms P1K8.K3K6.lotCalm_byPub
#print axioms P1K8.K3K6.lotCalm_byRows
#print axioms P1K8.k3_calm
#print axioms P1K8.k4_calm
#print axioms P1K8.k5_calm
#print axioms P1K8.k6_calm
