-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQXLawsProofs.lean: the proofs of Run/PlanQXLaws.lean. Many statements of this library are
written twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same
name outside that namespace proves it (lean/GLOSSARY.md).

Main theorems (statements and hypotheses: Run/PlanQXLaws.lean):
  `psofX_local`: a local verifier for the protocol with two stored tables.
  `wqX_okg`: the library's laws for its wiring `wqX`.
What is not claimed: the head of Run/PlanQXLaws.lean.

That the verifier is local is proved as in Run/PlanQSLaws.lean (`rhoS_eq`, `rvS_congr`,
`colAtS_congr`), with the view's entries treated case by case on their key. The count of external
reads is by induction over the rounds, with the openings' counts split by the number of the round.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQXLaws
import Iop.WireOK

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch
open Run.Twin (RS PS)

theorem key_ge (b : Bool) : 2 ^ 16 ≤ storedKey b := Nat.le_add_right _ _

theorem okX_own : Spec.okX_own := by
  intro ds a xs h d hd n hn
  unfold okX at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2 d hd n hn

theorem weX_ok : Spec.weX_ok := fun a =>
  ⟨(WireE.two_ok (2 ^ a) SgX (0, [])).nodup,
    (WireE.two_ok (2 ^ a) SgX (0, [])).complete,
    (WireE.two_ok (2 ^ a) SgX (0, [])).build_rd⟩

/-! ## The count -/

/-- what xWanted keeps of a pair (key, position) -/
def keepX (kx : Nat × Nat) : Option (Bool × Nat) :=
  if kx.1 = storedKey false then some (false, kx.2)
  else if kx.1 = storedKey true then some (true, kx.2)
  else none

theorem keepX_own (kx : Nat × Nat) (h : kx.1 < 2 ^ 16) : keepX kx = none := by
  unfold keepX
  rw [if_neg (fun e => absurd (key_ge false) (by omega)),
    if_neg (fun e => absurd (key_ge true) (by omega))]

theorem list_len (a : Nat) (o : XO) (D : _root_.Fmt.Drawn) : (o.list a D).length ≤ o.count := by
  unfold XO.list XO.raw
  refine le_trans (_root_.Fmt.listOf_len _) ?_
  rw [List.length_map]
  exact List.length_take_le _ _

theorem partA_len (a : Nat) (D : _root_.Fmt.Drawn) :
    ∀ L : List XO, (L.flatMap fun o => (o.list a D).map fun x => (storedKey o.which, x)).length ≤
      (L.map (·.count)).sum
  | [] => Nat.le_refl 0
  | o :: L => by
      rw [List.flatMap_cons, List.length_append, List.length_map, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (list_len a o D) (partA_len a D L)

theorem sum_split (i : Nat) :
    ∀ xs : List XO, ((xs.filter fun o => decide (i ≤ o.round)).map (·.count)).sum =
      ((xsAt xs i).map (·.count)).sum +
        ((xs.filter fun o => decide (i + 1 ≤ o.round)).map (·.count)).sum
  | [] => rfl
  | o :: xs => by
      have ih := sum_split i xs
      unfold xsAt at ih ⊢
      by_cases h1 : o.round = i
      · have a1 : decide (i ≤ o.round) = true := decide_eq_true (by omega)
        have a2 : (o.round == i) = true := by simpa using h1
        have a3 : decide (i + 1 ≤ o.round) = false := decide_eq_false (by omega)
        simp only [List.filter_cons, a1, a2, a3, if_true, Bool.false_eq_true, if_false,
          List.map_cons, List.sum_cons]
        omega
      · have a2 : (o.round == i) = false := by simpa using h1
        by_cases h2 : i ≤ o.round
        · have a1 : decide (i ≤ o.round) = true := decide_eq_true h2
          have a3 : decide (i + 1 ≤ o.round) = true := decide_eq_true (by omega)
          simp only [List.filter_cons, a1, a2, a3, if_true, Bool.false_eq_true, if_false,
            List.map_cons, List.sum_cons]
          omega
        · have a1 : decide (i ≤ o.round) = false := decide_eq_false h2
          have a3 : decide (i + 1 ≤ o.round) = false := decide_eq_false (by omega)
          simp only [List.filter_cons, a1, a2, a3, Bool.false_eq_true, if_false]
          exact ih

theorem small_nil (L : List (Nat × Nat)) (h : ∀ kx ∈ L, kx.1 < 2 ^ 16) : L.filterMap keepX = [] :=
  List.filterMap_eq_nil_iff.2 fun kx hkx => keepX_own kx (h kx hkx)

theorem wantedXL_len (a : Nat) (all : List RD) (xs : List XO) :
    ∀ (i : Nat) (ds : List RD) (Ds : List _root_.Fmt.Drawn), (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
      ((wantedXL a all xs i ds Ds).filterMap keepX).length ≤
        ((xs.filter fun o => decide (i ≤ o.round)).map (·.count)).sum
  | _, [], _, _ => by simp [wantedXL]
  | _, _ :: _, [], _ => by simp [wantedXL]
  | i, d :: ds, D :: Ds, h => by
      have ih := wantedXL_len a all xs (i + 1) ds Ds fun e he => h e (List.mem_cons_of_mem _ he)
      rw [wantedXL, List.filterMap_append, List.filterMap_append, List.length_append,
        List.length_append, sum_split i xs]
      refine le_trans
        (Nat.add_le_add
          (Nat.add_le_add (le_trans (List.length_filterMap_le _ _) (partA_len a D _))
            (Nat.le_of_eq (congrArg List.length (small_nil _ ?_)))) ih) (by simp)
      intro kx hkx
      obtain ⟨n, hn, hm⟩ := List.mem_flatMap.1 hkx
      split at hm
      · cases hm
      · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
        exact h d List.mem_cons_self n hn

theorem xWanted_len : Spec.xWanted_len := by
  intro a ds xs Ds h
  have := wantedXL_len a ds xs 0 ds Ds h
  rw [List.filter_eq_self.2 (fun o _ => decide_eq_true (Nat.zero_le _))] at this
  exact this

/-! ## Locality -/

theorem all_congr_mem {α : Type} (f g : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | x :: l, h => by
      rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
        all_congr_mem f g l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- an entry of `wantedXL` whose key is no stored tree's is an entry of `wantedL`
(Run/PlanQTypes.lean) -/
theorem own_of_wantedXL (a : Nat) (all : List RD) (xs : List XO) (kx : Nat × Nat)
    (h0 : kx.1 ≠ storedKey false) (h1 : kx.1 ≠ storedKey true) :
    ∀ (i : Nat) (ds : List RD) (Ds : List _root_.Fmt.Drawn),
      kx ∈ wantedXL a all xs i ds Ds → kx ∈ wantedL all ds Ds
  | _, [], _, h => by simp [wantedXL] at h
  | _, _ :: _, [], h => by simp [wantedXL] at h
  | i, d :: ds, D :: Ds, h => by
      rw [wantedXL] at h
      rw [wantedL]
      have h' := h
      rcases List.mem_append.1 h' with hab | hr
      · rcases List.mem_append.1 hab with ha | hb
        · obtain ⟨o, _, hm⟩ := List.mem_flatMap.1 ha
          obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
          cases hw : o.which with
          | false => exact absurd (by show storedKey o.which = storedKey false; rw [hw]) h0
          | true => exact absurd (by show storedKey o.which = storedKey true; rw [hw]) h1
        · exact List.mem_append_left _ hb
      · exact List.mem_append_right _ (own_of_wantedXL a all xs kx h0 h1 (i + 1) ds Ds hr)

theorem psofX_local : Spec.psofX_local := by
  rintro C ds a xs dec x y y' ⟨m0, c0, τ⟩ ⟨m0', c0', τ'⟩ hρ hp he hr
  have e1 : τ.rho = τ'.rho := congrArg Prod.snd hρ
  have e2 : τ.plains = τ'.plains := congrArg Prod.snd hp
  have he' : ∀ wx ∈ xWanted a ds xs (drawnSL C ds τ.rho),
      ∀ p, xPos (2 ^ a) wx = some p → (twoExternalStrings (2 ^ a) SgX).rd y p = (twoExternalStrings (2 ^ a) SgX).rd y' p := by
    intro wx hwx p hpos
    refine he p ?_
    show p ∈ ((xWanted a ds xs (drawnSL C ds τ.rho)).filterMap (xPos (2 ^ a))).toFinset
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨wx, hwx, hpos⟩
  have hc : symbolsCarryTheirPositions a ds xs (drawnSL C ds τ.rho) y = symbolsCarryTheirPositions a ds xs (drawnSL C ds τ.rho) y' := by
    unfold symbolsCarryTheirPositions
    refine all_congr_mem _ _ _ fun wx hwx => ?_
    cases hpos : xPos (2 ^ a) wx with
    | none => rfl
    | some p =>
        show (((twoExternalStrings (2 ^ a) SgX).rd y p).1 == wx.2) = (((twoExternalStrings (2 ^ a) SgX).rd y' p).1 == wx.2)
        rw [he' wx hwx p hpos]
  have hv : viewX C ds a xs y τ = viewX C ds a xs y' τ' := by
    unfold viewX
    rw [rvS_congr C ds τ τ' e1 e2, rhoS_eq, rhoS_eq, ← e1]
    congr 1
    refine filterMap_congr_mem _ _ _ fun kx hkx => ?_
    by_cases h0 : kx.1 = storedKey false
    · rw [if_pos h0, if_pos h0]
      have hw : (false, kx.2) ∈ xWanted a ds xs (drawnSL C ds τ.rho) :=
        List.mem_filterMap.2 ⟨kx, hkx, if_pos h0⟩
      cases hpos : xPos (2 ^ a) (false, kx.2) with
      | none => rfl
      | some p =>
          show some (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2) =
            some (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y' p).2)
          rw [he' _ hw p hpos]
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : kx.1 = storedKey true
      · rw [if_pos h1, if_pos h1]
        have hw : (true, kx.2) ∈ xWanted a ds xs (drawnSL C ds τ.rho) :=
          List.mem_filterMap.2 ⟨kx, hkx, by rw [if_neg h0, if_pos h1]⟩
        cases hpos : xPos (2 ^ a) (true, kx.2) with
        | none => rfl
        | some p =>
            show some (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2) =
              some (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y' p).2)
            rw [he' _ hw p hpos]
      · rw [if_neg h1, if_neg h1]
        rw [colAtS_congr C ds τ τ' kx.1 kx.2 fun p hpos => ?_]
        refine hr (Sum.inr p) ?_
        show (Sum.inr p : OPos (Twin.up (SOf C ds))) ∈
          (((wanted ds (drawnSL C ds τ.rho)).filterMap fun nx =>
            (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
        rw [List.mem_toFinset, List.mem_filterMap]
        exact ⟨kx, own_of_wantedXL a ds xs kx h0 h1 0 ds _ hkx, by rw [hpos]; rfl⟩
  show (passSL C ds (rhoSL C ds τ) && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ)) &&
      symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ)) y && dec (viewX C ds a xs y τ)) =
    (passSL C ds (rhoSL C ds τ') && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ')) &&
      symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ')) y' && dec (viewX C ds a xs y' τ'))
  rw [rhoS_eq, rhoS_eq, ← e1, hc, hv]

/-! ## The wiring -/

theorem wqX_okg : Spec.wqX_okg := fun C K chal ds a xs dec dec₀ hown h =>
  { sh := h.sh
    ext := weX_ok a
    opens := fun x ρ pl => by
      have h1 := h.opens x ρ pl
      have h1' : ((((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
            (posAtS C ds nx.1 nx.2).map fun p =>
              (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset).card ≤ nOpen ds :=
        le_trans (Nat.le_add_right _ _) h1
      show (List.toFinset _).card + (List.toFinset _).card ≤ nOpen ds + (xs.map (·.count)).sum
      exact Nat.add_le_add h1'
        (le_trans (List.toFinset_card_le _)
          (le_trans (List.length_filterMap_le _ _) (xWanted_len a ds xs _ hown)))
    depth := ⟨⟨Nat.zero_le _, Nat.zero_le _⟩,
      depthSL C K chal _ ds fun d hd =>
        le_trans ((foldl_max_le (fun d => depthOf d.tree) ds 0).2 d hd) (le_max_left _ _)⟩ }

end Run.PQ
