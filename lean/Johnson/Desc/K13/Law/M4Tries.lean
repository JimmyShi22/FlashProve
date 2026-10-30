-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/M4Tries.lean: the tries of the form of the law of
Johnson/Desc/K13/Law/M4Law.lean, proved.
Main names:
  `quiet_ok`: where a piece without a round says yes, its block's own decision has said yes.
  `not_back_lazy`: the block that says yes to all and lays no row does not meet the form.
  `back_no`: a block that refuses all meets it.
  `some_matrix_fails`: whatever the words, a row with a weight that is not 0 is false of some
    matrix: so without `WIs` nothing goes back from words to the matrix.
Used of `verify-on-bytes`: nothing beside what Johnson/Desc/K13/Law/M4.lean names.

What is not claimed. What rules out the block that refuses all is the run on an honest file.
`not_back_lazy` asks that W's vector fits its table under the blank record's codes.

-/
import Johnson.Desc.K13.Law.M4Law
import Johnson.Desc.K13.Law.Silly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Maker
open OnBytes.Means (Words Says)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)
open Johnson.L5.Layers (rd)

variable {Cl W : Type} {nR : ℕ}

/-- **Where a piece without a round says yes**, its block's own decision has said yes, on no round.
-/
theorem quiet_ok {F : Frame} {B : Block S Cl} {base : ℕ} {a b : S × F.E.Str}
    {τ : Tr (uLT (ckP .two) (pieceQuiet (W := W) F B base).ds)}
    (h : (pieceQuiet (W := W) F B base).ior.red.out a τ = some b) :
    ∃ gs, B.decide a.1 [] gs = .ok b.1 := by
  have hb' : (if sTests (ckP .two) (pieceQuiet (W := W) F B base).stage a.2 τ
      then (pieceQuiet (W := W) F B base).run a.1
        (sView (ckP .two) (pieceQuiet (W := W) F B base).stage a.2 τ)
      else none).map (fun xo => (xo, (pieceQuiet (W := W) F B base).ior.imp a.2 τ)) = some b := h
  split at hb'
  · cases hrun : (pieceQuiet (W := W) F B base).run a.1
        (sView (ckP .two) (pieceQuiet (W := W) F B base).stage a.2 τ) with
    | none =>
      rw [hrun] at hb'
      cases hb'
    | some s' =>
      rw [hrun] at hb'
      obtain rfl := Option.some.inj hb'
      obtain ⟨gs, _, hdec⟩ := single_ok hrun
      exact ⟨gs, hdec⟩
  · cases hb'

/-- The block that lays no row does not meet the form. -/
theorem not_back_lazy : Spec.not_back_lazy := by
  intro Cl nR F P base y hP h
  have hon : FrontOk P ((falseClaim, y) : S × F.E.Str) := by
    intro l hl
    obtain rfl := Option.some.inj hl
    exact ⟨⟨_, rfl⟩, hP⟩
  have h1 : ∀ b, (pieceQuiet (Cl := Cl) (W := Unit) F lazyB base).ior.red.out (falseClaim, y) () =
      some b → True ∧ ∀ w, Behind (nR := nR) P (fun _ _ _ => 0) (fun _ _ _ _ => 0)
        (fun _ _ => True) b w →
        RowsHold (fun w => witOf ((fun _ _ _ => 0 : Unit → Fin nR → (Fin P.lin.kCol → Bool) → GE) w)
          ((fun _ _ _ _ => 0 : Unit → Words GE) w)) (fun _ _ => True) (falseClaim, y) w :=
    h (falseClaim, y) hon
  have h2 := (h1 _ rfl).2 () ⟨trivial,
    ⟨fun g G hG => by simp [falseClaim, S.blank, S.start] at hG,
      fun o x hx => by simp [falseClaim, S.blank, S.start] at hx⟩,
    fun l hl e _ => by simp⟩
  have h3 := h2.2 (rowOfClaim (memberClaim ⟨[], [], [], oneE⟩)) (List.mem_singleton.2 rfl)
  rw [rowOfClaim_member] at h3
  have h4 : lhs ρg _ (⟨[], [], [], oneE⟩ : TensorRow) = ρg.val oneE := h3
  rw [lhs_nil, ρg.one] at h4
  exact zero_ne_one h4

/-- A block that refuses all meets the form. -/
theorem back_no : Spec.back_no := by
  intro Cl W nR F P base rwM rwW Pin a _
  show ∀ b, _ = some b → _
  intro b hb
  obtain ⟨_, hdec⟩ := quiet_ok hb
  have hdec' : (Except.error "no" : Except String S) = .ok b.1 := hdec
  cases hdec'

/-- Whatever the words, a row with a weight that is not 0 is false of some matrix. -/
theorem some_matrix_fails : Spec.some_matrix_fails := by
  intro nR k row m ⟨i₀, hi⟩
  by_contra hall
  push Not at hall
  have h0 : Alg.mle (colOf (witOf (fun _ _ => 0) m) (weights ρg nR row.g)) (rd ρg k row.psi) +
      formVal ρg (maskOf m) row.masks = ρg.val row.target := hall fun _ _ => 0
  have h1 : Alg.mle (colOf (witOf (fun i _ => if i = i₀ then 1 else 0) m) (weights ρg nR row.g))
      (rd ρg k row.psi) + formVal ρg (maskOf m) row.masks = ρg.val row.target :=
    hall fun i _ => if i = i₀ then 1 else 0
  have e0 : Alg.mle (colOf (witOf (fun _ _ => 0) m) (weights ρg nR row.g)) (rd ρg k row.psi) =
      0 := by
    simp [Alg.mle, colOf, witOf]
  have e1 : Alg.mle (colOf (witOf (fun i _ => if i = i₀ then 1 else 0) m) (weights ρg nR row.g))
      (rd ρg k row.psi) = weights ρg nR row.g i₀ := by
    have : colOf (witOf (fun i _ => if i = i₀ then (1 : GE) else 0) m) (weights ρg nR row.g) =
        fun _ : Fin k → Bool => weights ρg nR row.g i₀ := by
      funext c
      simp [colOf, witOf]
    rw [this]
    unfold Alg.mle
    rw [← Finset.sum_mul, Alg.sum_eqk, one_mul]
  rw [e0] at h0
  rw [e1, ← h0] at h1
  exact hi (by simpa using h1)

end VerifiableInference.Desc.K13.Law
