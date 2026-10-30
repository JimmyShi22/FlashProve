--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Tie.lean: kind K13, the members' batching: THE SCALARS OF THE BIJECTION ARE
THE SCALARS OF THE PROVER's ROUNDS. Definitions; statements with their proofs.

Why. Johnson/Desc/K13/Honest/Bij.lean and BijLaw.lean speak of `sumU` and `sent` at coefficients
that are a function on 2 n + 1 numbers. The prover's rounds (`movesAtM3`,
Johnson/Desc/K13/Honest/MovesAtM3.lean) call the same two functions at the mask entries of a witness
that were taken for the hiding polynomial. Four things stand between the two; the first is shown
here, the other three in Johnson/Desc/K13/Honest/WithTaken.lean:
  1 `sumU`, `sentL` and `sent` read the coefficients below the number 2 n + 1 alone;
  2 where the taken entries differ from each other, a witness can be given any values at them;
  3 a row that names none of them keeps its truth;
  4 the rows' tables read no mask entry.
That the taken entries differ, and when no row on the pile names one:
Johnson/Desc/K13/Honest/Fresh.lean.
Main names:
  `tailU_congr`, `sentL_congr`, `sent_congr`, `viewT_of_fun`: the first.
  `withTaken_self`: the witness itself is the member of the family at its own values.
  `scalars_withTaken`: the prover's scalars at that witness are `viewT` at v.
  `roundsOfView σ x eps gs V`: a scalar and pairs as rounds.
  `moves_are_view`: **the prover's rounds at that witness are the rounds of `viewT` at v.**
  `moves_law`: **over uniform values at the taken entries, the prover's rounds have the distribution
    of the rounds of 2 k + 1 uniform scalars.**

WHICH PROVER. `movesAtM3` is handed the list fresh of its mask entries from outside: so
`moves_are_view` and `moves_law` serve THE PROVER THAT IS HANDED THE LIST OF ITS ENTRIES: no state
of a verifier and no test on a state stands in them; that the list's entries differ and are 2 k + 1
is a premise on the list. The prover that reads the list off the verifier's state: TieAtM3.lean.

What is not claimed. What Johnson/Desc/K13/Honest/BijLaw.lean does not claim; its paragraph WHOSE
HALF THIS IS holds of `moves_law` too: it is the half of the sub-protocol that spends the entries,
AND IS NOT TO BE QUOTED WITHOUT THE SENDER's SENTENCE BESIDE IT. The matrix, the other mask entries,
the pile and the sampled elements are fixed before the values are sampled, and none of them is made
of these values: a pile whose weights or points were made of a taken entry is outside these
statements. THE MAP IS ONE TO ONE: with all that is held fixed, the scalars sent fix every one of
these entries, and so every other value that is computed from them. Nothing on soundness, on zero
knowledge or on hiding.

-/
import Johnson.Desc.K13.Honest.BijLaw
import Johnson.Desc.K13.Honest.WithTaken

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K13.Law

/-! ## 1 Which coefficients are read -/

section Reads
variable {K : Type} [CommRing K]

/-- The sum reads the 2 n + 1 coefficients from the number i on, and no other. -/
theorem tailU_congr {u v : ℕ → K} : ∀ n i : ℕ,
    (∀ j, i ≤ j → j < i + (2 * n + 1) → u j = v j) → tailU u n i = tailU v n i
  | 0, _, _ => rfl
  | 1, i, h => by
    show 2 * u i + u (i + 1) + u (i + 2) = 2 * v i + v (i + 1) + v (i + 2)
    rw [h i (by omega) (by omega), h (i + 1) (by omega) (by omega),
      h (i + 2) (by omega) (by omega)]
  | n + 2, i, h => by
    show u i + u (i + 1) + 2 * tailU u (n + 1) (i + 2) =
      v i + v (i + 1) + 2 * tailU v (n + 1) (i + 2)
    rw [h i (by omega) (by omega), h (i + 1) (by omega) (by omega),
      tailU_congr (n + 1) (i + 2) fun j h1 h2 => h j (by omega) (by omega)]

/-- So does what is sent, the summand a parameter. -/
theorem sentL_congr {u v : ℕ → K} (eps : K) (q : List K → K × K × K) : ∀ (n i : ℕ)
    (seen gs : List K), (∀ j, i ≤ j → j < i + (2 * n + 1) → u j = v j) →
    sentL u eps q n i seen gs = sentL v eps q n i seen gs
  | 0, _, _, _, _ => rfl
  | 1, i, seen, _, h => by
    show [(u i + eps * (q seen).1, u (i + 2) + eps * (q seen).2.2)] =
      [(v i + eps * (q seen).1, v (i + 2) + eps * (q seen).2.2)]
    rw [h i (by omega) (by omega), h (i + 2) (by omega) (by omega)]
  | n + 2, i, seen, gs, h => by
    show (tailU u (n + 1) (i + 2) + eps * (q seen).1, u (i + 1) + eps * (q seen).2.2) ::
        sentL u eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail =
      (tailU v (n + 1) (i + 2) + eps * (q seen).1, v (i + 1) + eps * (q seen).2.2) ::
        sentL v eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail
    rw [h (i + 1) (by omega) (by omega),
      tailU_congr (n + 1) (i + 2) fun j h1 h2 => h j (by omega) (by omega),
      sentL_congr eps q (n + 1) (i + 2) _ _ fun j h1 h2 => h j (by omega) (by omega)]

/-- So does what is sent, the summand given by tables. -/
theorem sent_congr {u v : ℕ → K} (eps : K) (S : List (List K × List K)) (n : ℕ) (gs : List K)
    (h : ∀ j, j < 2 * n + 1 → u j = v j) : sent u eps n 0 S gs = sent v eps n 0 S gs := by
  have e1 := sent_eq u eps S n 0 [] gs
  have e2 := sent_eq v eps S n 0 [] gs
  have e3 : sent u eps n 0 S gs =
      sentL u eps (fun seen => quadAll (foldsAll seen S)) n 0 [] gs := e1
  have e4 : sent v eps n 0 S gs =
      sentL v eps (fun seen => quadAll (foldsAll seen S)) n 0 [] gs := e2
  rw [e3, e4]
  exact sentL_congr eps _ n 0 [] gs fun j _ hj => h j (by omega)

/-- **What is sent at a function u of all numbers is `viewT` at u's first 2 n + 1 values.** -/
theorem viewT_of_fun {n : ℕ} (u : ℕ → K) (v : Fin (2 * n + 1) → K) (eps : K)
    (S : List (List K × List K)) (gs : List K)
    (h : ∀ j (hj : j < 2 * n + 1), u j = v ⟨j, hj⟩) :
    (sumU u n, sent u eps n 0 S gs) = viewT eps S n gs v := by
  have h' : ∀ j, j < 2 * n + 1 → u j = onNat v j := fun j hj => by
    rw [onNat_of_lt v j hj]
    exact h j hj
  exact Prod.ext (tailU_congr n 0 fun j _ hj => h' j (by omega)) (sent_congr eps S n gs h')

end Reads

/-! ## 2, 3, 4 A witness with other values at the taken entries: WithTaken.lean -/

variable {K : Type} [Field K] (ρ : Reading K) {nR k : ℕ}

/-- **The family holds the witness itself**: at its own values at the taken entries. -/
theorem withTaken_self (w : Wit K nR k) (fresh : List Slot) (N : ℕ) (hl : fresh.length = N) :
    withTaken w fresh (onNat fun j : Fin N => maskAt w fresh j) = w := by
  exact withTaken_own w fresh _ fun j hj =>
    onNat_of_lt (fun j : Fin N => maskAt w fresh j) j (by omega)

/-! ## The tie -/

/-- **The prover's scalars at that witness are `viewT` at v.** -/
theorem scalars_withTaken (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot)
    (hn : fresh.Nodup) (hl : fresh.length = 2 * k + 1) (v : Fin (2 * k + 1) → K) (a eps : K)
    (gs : List K) :
    (sumU (maskAt (withTaken w fresh (onNat v)) fresh) k,
      sent (maskAt (withTaken w fresh (onNat v)) fresh) eps k 0
        (tabsOf ρ (withTaken w fresh (onNat v)) pile a) gs) =
      viewT eps (tabsOf ρ w pile a) k gs v :=
  viewT_of_fun _ v eps _ gs fun j hj => by
    rw [maskAt_withTaken w fresh (onNat v) hn j (by omega), onNat_of_lt v j hj]

variable (σ : K → E)

/-- A scalar and pairs as the rounds of the batching, beside the sampled elements. -/
def roundsOfView (x eps : E) (gs : List E) (V : K × List (K × K)) : List Fmt.RoundView :=
  roundsOf x ⟨σ V.1, eps, codeRounds σ V.2 gs, []⟩

/-- **The prover's rounds at that witness are the rounds of `viewT` at v.** THE SPENDER's HALF: see
the head. -/
theorem moves_are_view (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot)
    (hn : fresh.Nodup) (hl : fresh.length = 2 * k + 1) (v : Fin (2 * k + 1) → K) (x eps : E)
    (gs : List E) :
    movesAtM3 ρ σ (withTaken w fresh (onNat v)) pile fresh x eps gs =
      roundsOfView σ x eps gs
        (viewT (ρ.val eps) (tabsOf ρ w pile (ρ.val x)) k (gs.map ρ.val) v) := by
  have e := scalars_withTaken ρ w pile fresh hn hl v (ρ.val x) (ρ.val eps) (gs.map ρ.val)
  have e1 : sumU (maskAt (withTaken w fresh (onNat v)) fresh) k =
      (viewT (ρ.val eps) (tabsOf ρ w pile (ρ.val x)) k (gs.map ρ.val) v).1 := congrArg Prod.fst e
  have e2 : sent (maskAt (withTaken w fresh (onNat v)) fresh) (ρ.val eps) k 0
      (tabsOf ρ (withTaken w fresh (onNat v)) pile (ρ.val x)) (gs.map ρ.val) =
      (viewT (ρ.val eps) (tabsOf ρ w pile (ρ.val x)) k (gs.map ρ.val) v).2 := congrArg Prod.snd e
  show roundsOf x ⟨σ (sumU (maskAt (withTaken w fresh (onNat v)) fresh) k), eps,
    codeRounds σ (sent (maskAt (withTaken w fresh (onNat v)) fresh) (ρ.val eps) k 0
      (tabsOf ρ (withTaken w fresh (onNat v)) pile (ρ.val x)) (gs.map ρ.val)) gs, []⟩ = _
  rw [e1, e2]
  rfl

/-- **Over uniform values at the taken entries, the prover's rounds have the distribution of the
rounds of 2 k + 1 uniform scalars.** All else is fixed before these values are sampled. THE
SPENDER's HALF: see the head; not to be quoted without the sender's sentence. -/
theorem moves_law [Fintype K] (w : Wit K nR k) (pile : List TensorRow) (fresh : List Slot)
    (hk : 1 ≤ k) (hn : fresh.Nodup) (hl : fresh.length = 2 * k + 1) (x eps : E) (gs : List E) :
    (Prob.unif (Fin (2 * k + 1) → K)).map
        (fun v => movesAtM3 ρ σ (withTaken w fresh (onNat v)) pile fresh x eps gs) =
      (Prob.unif (Fin (2 * k + 1) → K)).map fun c =>
        roundsOfView σ x eps gs (tellL (onNat c) k) := by
  have e : (fun v : Fin (2 * k + 1) → K =>
      movesAtM3 ρ σ (withTaken w fresh (onNat v)) pile fresh x eps gs) = fun v =>
      roundsOfView σ x eps gs
        (viewT (ρ.val eps) (tabsOf ρ w pile (ρ.val x)) k (gs.map ρ.val) v) :=
    funext fun v => moves_are_view ρ σ w pile fresh hn hl v x eps gs
  rw [e]
  exact viewT_law (ρ.val eps) _ k hk (gs.map ρ.val) (roundsOfView σ x eps gs)

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.tailU_congr
#print axioms VerifiableInference.Desc.K13.Honest.sentL_congr
#print axioms VerifiableInference.Desc.K13.Honest.sent_congr
#print axioms VerifiableInference.Desc.K13.Honest.viewT_of_fun
#print axioms VerifiableInference.Desc.K13.Honest.withTaken_self
#print axioms VerifiableInference.Desc.K13.Honest.scalars_withTaken
#print axioms VerifiableInference.Desc.K13.Honest.moves_are_view
#print axioms VerifiableInference.Desc.K13.Honest.moves_law
