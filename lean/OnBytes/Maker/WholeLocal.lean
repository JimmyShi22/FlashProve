-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/WholeLocal.lean: the reduction of a whole file with three joined chains (`reductionOfWholeFile`,
OnBytes/Maker/Whole.lean) is local (`IOR.IsLocal`, Ior/Ior.lean): its verdict hangs on the stored
table and on the prover's oracles only at the positions that it declares as read.

  `colOf_congr`       the column at a want is the same at two tables and two transcripts that agree
                      at the want's one position
  `carriesOf_congr`   the test that every symbol read of the stored table carries its position
  `viewOf_congr`      a chain's view
  `wholeIOR_out_congr`, `wholeIOR_isLocal`
                      the reduction is local; `wholeIOR_local`: so is its protocol
  `wholeIOR_point`    every round's oracle is a string (`Shape.IsPoint`, Iop/Shape.lean)

No hypothesis is made on the data, on the test of the three silent rounds, or on the run.
Not claimed. Nothing on soundness, and nothing on an honest prover.


-/
import OnBytes.Maker.Whole
import OnBytes.Maker.TreesLaws
import OnBytes.Maker.ChainsLaws

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ Compile.Joined

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- The column at a want hangs on the table and on the transcript only at the want's position. -/
theorem colOf_congr (y y' : (oneExternalString (2 ^ D.a) SgX).Str) (τ τ' : Tr (chainsOf C D tF tJ t3).sh)
    (w : Want) (hE : ∀ p, extPosOf D w = some p → y p = y' p)
    (hO : ∀ p, ownPosOf C D tF tJ t3 w = some p → τ.read p = τ'.read p) :
    colOf C D y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
        ((chainsOf C D tF tJ t3).tr₃ τ) w =
      colOf C D y' ((chainsOf C D tF tJ t3).tr₁ τ') ((chainsOf C D tF tJ t3).tr₂ τ')
        ((chainsOf C D tF tJ t3).tr₃ τ') w := by
  cases w with
  | table item x =>
    simp only [colOf]
    by_cases h : x < 2 ^ D.a
    · rw [dif_pos h, dif_pos h, hE ⟨x, h⟩ (dif_pos h)]
    · rw [dif_neg h, dif_neg h]
  | tree j x =>
    simp only [colOf]
    simp only [ownPosOf] at hO
    by_cases h1 : j < D.t₁
    · rw [if_pos h1, if_pos h1]
      rw [if_pos h1] at hO
      exact colAtST_congr C D.ds₁ _ _ j x fun p hp =>
        (read_i₁ (chainsOf C D tF tJ t3) τ τ' p).1 (hO _ (by rw [hp]; rfl))
    · rw [if_neg h1, if_neg h1]
      rw [if_neg h1] at hO
      by_cases h2 : j - D.t₁ < D.t₂
      · rw [if_pos h2, if_pos h2]
        rw [if_pos h2] at hO
        exact colAtST_congr C D.ds₂ _ _ (j - D.t₁) x fun p hp =>
          (read_i₂ (chainsOf C D tF tJ t3) τ τ' p).1 (hO _ (by rw [hp]; rfl))
      · rw [if_neg h2, if_neg h2]
        rw [if_neg h2] at hO
        exact colAtST_congr C D.ds₃ _ _ (j - D.t₁ - D.t₂) x fun p hp =>
          (read_i₃ (chainsOf C D tF tJ t3) τ τ' p).1 (hO _ (by rw [hp]; rfl))

/-- The test on the symbols read of the stored table hangs on the table only at these. -/
theorem carriesOf_congr (y y' : (oneExternalString (2 ^ D.a) SgX).Str) :
    ∀ ws : List Want, (∀ w ∈ ws, ∀ p, extPosOf D w = some p → y p = y' p) →
      carriesOf D y ws = carriesOf D y' ws
  | [], _ => rfl
  | w :: ws, h => by
    have ih := carriesOf_congr y y' ws fun w hw => h w (List.mem_cons_of_mem _ hw)
    unfold carriesOf at ih ⊢
    rw [List.all_cons, List.all_cons, ih]
    congr 1
    cases w with
    | table item x =>
      by_cases hx : x < 2 ^ D.a
      · simp only [dif_pos hx]
        rw [h _ List.mem_cons_self ⟨x, hx⟩ (dif_pos hx)]
      · simp only [dif_neg hx]
    | tree j x => rfl

/-- A chain's view hangs on the table and on the transcript only at its wants' positions. -/
theorem viewOf_congr (y y' : (oneExternalString (2 ^ D.a) SgX).Str) (τ τ' : Tr (chainsOf C D tF tJ t3).sh)
    (rs : List RV) (key : ℕ → ℕ) (ws : List Want)
    (hE : ∀ w ∈ ws, ∀ p, extPosOf D w = some p → y p = y' p)
    (hO : ∀ w ∈ ws, ∀ p, ownPosOf C D tF tJ t3 w = some p → τ.read p = τ'.read p) :
    viewOf C D y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
        ((chainsOf C D tF tJ t3).tr₃ τ) rs key ws =
      viewOf C D y' ((chainsOf C D tF tJ t3).tr₁ τ') ((chainsOf C D tF tJ t3).tr₂ τ')
        ((chainsOf C D tF tJ t3).tr₃ τ') rs key ws := by
  unfold viewOf
  congr 1
  refine List.filterMap_congr fun w hw => ?_
  rw [colOf_congr C D tF tJ t3 y y' τ τ' w (hE w hw) (hO w hw)]

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- The verdict is the same at two tables and two transcripts that agree where the verifier
reads. -/
theorem wholeIOR_out_congr (x : Xi) (y y' : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ τ' : Tr (chainsOf C D tF tJ t3).sh) (hρ : τ.rho = τ'.rho) (hp : τ.plains = τ'.plains)
    (hE : ∀ p ∈ ((wants₁ C D tF tJ t3 τ.rho ++
      (wants₂ C D tF tJ t3 τ.rho ++ wants₃ C D tF tJ t3 τ.rho)).filterMap (extPosOf D)).toFinset,
      y p = y' p)
    (hO : ∀ p ∈ ((wants₁ C D tF tJ t3 τ.rho ++
      (wants₂ C D tF tJ t3 τ.rho ++ wants₃ C D tF tJ t3 τ.rho)).filterMap
        (ownPosOf C D tF tJ t3)).toFinset, τ.read p = τ'.read p) :
    (reductionOfWholeFile C D tF tJ t3 silent run).out x y τ =
      (reductionOfWholeFile C D tF tJ t3 silent run).out x y' τ' := by
    obtain ⟨⟨r1, p1⟩, ⟨r2, p2⟩, ⟨r3, p3⟩, sF, sJ, s3⟩ :=
      parts_congr (chainsOf C D tF tJ t3) τ τ' hρ hp
    have q1 : rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ) = (chainsOf C D tF tJ t3).rho₁ τ.rho :=
      (rhoT_eq C D.ds₁ _).trans ((chainsOf C D tF tJ t3).rho_tr₁ τ)
    have q2 : rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ) = (chainsOf C D tF tJ t3).rho₂ τ.rho :=
      (rhoT_eq C D.ds₂ _).trans ((chainsOf C D tF tJ t3).rho_tr₂ τ)
    have q3 : rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ) = (chainsOf C D tF tJ t3).rho₃ τ.rho :=
      (rhoT_eq C D.ds₃ _).trans ((chainsOf C D tF tJ t3).rho_tr₃ τ)
    have q1' : rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ') =
        (chainsOf C D tF tJ t3).rho₁ τ.rho :=
      (rhoT_eq C D.ds₁ _).trans (r1.symm.trans ((chainsOf C D tF tJ t3).rho_tr₁ τ))
    have q2' : rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ') =
        (chainsOf C D tF tJ t3).rho₂ τ.rho :=
      (rhoT_eq C D.ds₂ _).trans (r2.symm.trans ((chainsOf C D tF tJ t3).rho_tr₂ τ))
    have q3' : rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ') =
        (chainsOf C D tF tJ t3).rho₃ τ.rho :=
      (rhoT_eq C D.ds₃ _).trans (r3.symm.trans ((chainsOf C D tF tJ t3).rho_tr₃ τ))
    have hE' : ∀ w ∈ wants₁ C D tF tJ t3 τ.rho ++
        (wants₂ C D tF tJ t3 τ.rho ++ wants₃ C D tF tJ t3 τ.rho),
        ∀ p, extPosOf D w = some p → y p = y' p := fun w hw p hpw =>
      hE p (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨w, hw, hpw⟩))
    have hO' : ∀ w ∈ wants₁ C D tF tJ t3 τ.rho ++
        (wants₂ C D tF tJ t3 τ.rho ++ wants₃ C D tF tJ t3 τ.rho),
        ∀ p, ownPosOf C D tF tJ t3 w = some p → τ.read p = τ'.read p := fun w hw p hpw =>
      hO p (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨w, hw, hpw⟩))
    have m1 : ∀ w ∈ wants₁ C D tF tJ t3 τ.rho, w ∈ wants₁ C D tF tJ t3 τ.rho ++
        (wants₂ C D tF tJ t3 τ.rho ++ wants₃ C D tF tJ t3 τ.rho) := fun w hw =>
      List.mem_append_left _ hw
    have m2 : ∀ w ∈ wants₂ C D tF tJ t3 τ.rho, w ∈ wants₁ C D tF tJ t3 τ.rho ++
        (wants₂ C D tF tJ t3 τ.rho ++ wants₃ C D tF tJ t3 τ.rho) := fun w hw =>
      List.mem_append_right _ (List.mem_append_left _ hw)
    have m3 : ∀ w ∈ wants₃ C D tF tJ t3 τ.rho, w ∈ wants₁ C D tF tJ t3 τ.rho ++
        (wants₂ C D tF tJ t3 τ.rho ++ wants₃ C D tF tJ t3 τ.rho) := fun w hw =>
      List.mem_append_right _ (List.mem_append_right _ hw)
    have hc := carriesOf_congr D y y' _ hE'
    have v1 := viewOf_congr C D tF tJ t3 y y' τ τ'
      (rvT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ)) D.key₁ (wants₁ C D tF tJ t3 τ.rho)
      (fun w hw => hE' w (m1 w hw)) (fun w hw => hO' w (m1 w hw))
    have v2 := viewOf_congr C D tF tJ t3 y y' τ τ'
      (rvT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ)) D.key₂ (wants₂ C D tF tJ t3 τ.rho)
      (fun w hw => hE' w (m2 w hw)) (fun w hw => hO' w (m2 w hw))
    have v3 := viewOf_congr C D tF tJ t3 y y' τ τ'
      (rvT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ)) D.key₃ (wants₃ C D tF tJ t3 τ.rho)
      (fun w hw => hE' w (m3 w hw)) (fun w hw => hO' w (m3 w hw))
    rw [rvT_congr C D.ds₁ _ _ r1 p1] at v1
    rw [rvT_congr C D.ds₂ _ _ r2 p2] at v2
    rw [rvT_congr C D.ds₃ _ _ r3 p3] at v3
    unfold wants₁ at v1 hc
    unfold wants₂ at v2 hc
    unfold wants₃ at v3 hc
    simp only [q1, q2, q3, q1', q2', q3']
    rw [rvT_congr C D.ds₁ _ _ r1 p1, rvT_congr C D.ds₂ _ _ r2 p2, rvT_congr C D.ds₃ _ _ r3 p3,
      hc, v1, v2, v3, sF, sJ, s3]

/-- **The reduction of a whole file is local.** -/
theorem wholeIOR_isLocal : (reductionOfWholeFile C D tF tJ t3 silent run).IsLocal where
  out := fun x y y' τ τ' hρ hp hE hO =>
    wholeIOR_out_congr C D tF tJ t3 silent run x y y' τ τ' hρ hp hE hO
  imp := fun _ _ _ _ q => q.elim

/-- Its protocol is local. -/
theorem wholeIOR_local : (reductionOfWholeFile C D tF tJ t3 silent run).toInteractiveOracleProof.IsLocal :=
  fun x y y' τ τ' hρ hp hE hO =>
    congrArg Option.isSome ((wholeIOR_isLocal C D tF tJ t3 silent run).out x y y' τ τ' hρ hp hE hO)

end

/-- The oracle of a round that sends a plain part alone is a string without a position. -/
def pointPlain (T : Type) (t : T) : (plainRound T t).IsPoint :=
  ⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩

/-- Two shapes of strings laid behind each other. -/
def pointApp : {s t : Shape} → s.IsPoint → t.IsPoint → (s ++ t).IsPoint
  | [], _, _, b => b
  | _ :: _, _, (a, as), b => (a, pointApp as b)

/-- **Every round's oracle is a string.** -/
theorem wholeIOR_point (C : CK) (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool) :
    Nonempty (reductionOfWholeFile C D tF tJ t3 silent run).shape.IsPoint :=
  ⟨(pointPlain TF tF, pointApp (pointsT C D.ds₁)
    (pointPlain TJ tJ, pointApp (pointsT C D.ds₂) (pointPlain T3 t3, pointsT C D.ds₃)))⟩

end OnBytes.Maker
