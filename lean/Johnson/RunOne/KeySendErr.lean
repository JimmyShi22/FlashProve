-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendErr.lean: THEOREMS. **The number of bad seeds of a sending (errPort), which has no code, is held below a share of all seeds by a Boolean that has code.**
  qE          the extension field's number of elements, as a number with code
  badOwn      of a message's own seeds (a point of b coordinates and a factor other than 0): at most so many are bad: (the list's bound choose 2) times the sample map's number
  shareB      THE TEST: for every sampled message of the place: (the number of the place's messages) · badOwn · 2 ^ K is at most the number of its own seeds. The first factor pays for the sum over the messages
  portZ_err   the sample map's number, written out
  own_card    the number of a message's own seeds
  errPort_share   **shareB K P rad = true ⇒ errPort P rad · 2 ^ K ≤ the number of the place's joint seeds**
What is not claimed. That shareB says yes anywhere: that is a matter of evaluation. Nothing on how a count of typed seeds reads as a count of written challenges. Nothing on soundness.

-/
import Johnson.RunOne.KeySendGood
import OnBytes.Slice.RatesToy
import Cb.Ent.CdNums

set_option autoImplicit false

namespace Johnson.RunOne.KeySendErr

open OnBytes OnBytes.Params OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc.K1 (Par Seeds errPort shapeAt shapesOf sampledAt Rest card_part one_le_seeds bits_le_coordinates)

def qE : Nat := Fmt.Fld.two.p ^ 3

def badOwn (cs : Codes) (s : OracleShape) (e : Nat) : Nat :=
  (lOf cs s e).choose 2 * max (bitsZ cs s * qE ^ (bitsZ cs s - 1) * (qE - 1)) (qE ^ bitsZ cs s)

def shareB (K : Nat) (P : Par) (rad : Nat → Nat) : Bool :=
  decide (∀ k : Fin (shapesOf P).length, sampledAt P k →
    (shapesOf P).length * badOwn P.codes (shapeAt P k) (rad k.val) * 2 ^ K ≤ qE ^ bitsZ P.codes (shapeAt P k) * (qE - 1))

theorem portZ_err (cs : Codes) (s : OracleShape) :
    (portZ cs s).err = max (bitsZ cs s * qE ^ (bitsZ cs s - 1) * (qE - 1)) (qE ^ bitsZ cs s) := by
  have gen : ∀ {E M J0 P B J : Type} [Field E] [Fintype E] [Fintype M] [DecidableEq M] [Fintype B] [Nonempty B]
      (pl : J0 → M → Bool) (w : P → E) (v : B → E) (r : J → J0 ⊕ P) (m q u : Nat),
      Fintype.card M = m → Fintype.card E = q → Fintype.card B = u →
      ((Sample.pad E M J0 P B pl w v).comap r).err = max (m * q ^ (m - 1) * u) (q ^ m) := by
    intro E M J0 P B J _ _ _ _ _ _ pl w v r m q u hm hq hu
    subst hm hq hu
    rfl
  have units : ∀ {K : Type} [Field K] [Fintype K] (i : Fintype Kˣ) (q : Nat), Fintype.card K = q → @Fintype.card Kˣ i = q - 1 := by
    intro K _ _ i q hq
    classical
    subst hq
    exact (congrArg (@Fintype.card Kˣ) (Subsingleton.elim i _)).trans (Fintype.card_units K)
  have hF : Fintype.card GE = qE := OnBytes.Slice.card_GE
  exact gen _ _ _ _ (bitsZ cs s) qE (qE - 1) (Fintype.card_fin _) hF (units (K := GE) _ qE hF)

theorem own_card (b : Nat) : Fintype.card (Fin 1 → (Fin b → GE) × GEˣ) = qE ^ b * (qE - 1) := by
  have gen : ∀ {G U : Type} [Fintype G] [Fintype U] (q : Nat), Fintype.card G = q → Fintype.card U = q - 1 →
      Fintype.card (Fin 1 → (Fin b → G) × U) = q ^ b * (q - 1) := by
    intro G U _ _ q hG hU
    rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hG, hU, pow_one]
  have units : ∀ {K : Type} [Field K] [Fintype K] (i : Fintype Kˣ) (q : Nat), Fintype.card K = q → @Fintype.card Kˣ i = q - 1 := by
    intro K _ _ i q hq
    classical
    subst hq
    exact (congrArg (@Fintype.card Kˣ) (Subsingleton.elim i _)).trans (Fintype.card_units K)
  have hF : Fintype.card GE = qE := OnBytes.Slice.card_GE
  exact gen qE hF (units (K := GE) _ qE hF)

/-- **The test's yes holds the number of bad seeds below the share.** -/
theorem errPort_share (K : Nat) (P : Par) (rad : Nat → Nat) (h : shareB K P rad = true) : errPort P rad * 2 ^ K ≤ Fintype.card (Seeds P) := by
  unfold shareB at h
  have h' := of_decide_eq_true h
  set n := (shapesOf P).length with hn
  set T := Fintype.card (Seeds P) with hT
  have term : ∀ k : Fin n, n * ((if sampledAt P k then (lOf P.codes (shapeAt P k) (rad k.val)).choose 2 * (portZ P.codes (shapeAt P k)).err *
      Fintype.card (Rest GE GEˣ P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k))) else 0) * 2 ^ K) ≤ T := by
    intro k
    by_cases hk : sampledAt P k
    · rw [if_pos hk, portZ_err]
      have c : T = qE ^ bitsZ P.codes (shapeAt P k) * (qE - 1) * Fintype.card (Rest GE GEˣ P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k))) := by
        rw [hT, ← own_card]
        exact card_part P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k)) (one_le_seeds P k hk) (bits_le_coordinates P k hk)
      rw [c]
      have q := Nat.mul_le_mul_right (Fintype.card (Rest GE GEˣ P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k)))) (h' k hk)
      unfold badOwn at q
      calc _ = n * ((lOf P.codes (shapeAt P k) (rad k.val)).choose 2 * max (bitsZ P.codes (shapeAt P k) * qE ^ (bitsZ P.codes (shapeAt P k) - 1) * (qE - 1)) (qE ^ bitsZ P.codes (shapeAt P k))) * 2 ^ K *
              Fintype.card (Rest GE GEˣ P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k))) := by ring
        _ ≤ _ := q
    · rw [if_neg hk]
      simp
  by_cases h0 : n = 0
  · have : errPort P rad = 0 := by
      unfold errPort
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk := k.isLt
      omega
    rw [this]
    simp
  · have hs : n * (errPort P rad * 2 ^ K) ≤ n * T := by
      unfold errPort
      rw [Finset.sum_mul, Finset.mul_sum]
      refine le_trans (Finset.sum_le_card_nsmul _ _ T fun k _ => ?_) ?_
      · exact term k
      · simp [hn]
    exact Nat.le_of_mul_le_mul_left hs (Nat.pos_of_ne_zero h0)

end Johnson.RunOne.KeySendErr

#print axioms Johnson.RunOne.KeySendErr.portZ_err
#print axioms Johnson.RunOne.KeySendErr.own_card
#print axioms Johnson.RunOne.KeySendErr.errPort_share
