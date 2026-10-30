--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/SumLaw.lean: THE LAW OF THE HONEST SCALARS OF A MASKED SUMCHECK OF ONE
SHAPE: every variable summed plainly (at 0 and 1), round polynomials of degree 2, no scalar sent
ahead of the sum, no value shown at the end (Johnson/Desc/K13/Honest/Moves.lean: `sumU`, `sentL`,
`sent`). THE SUMMAND IS A PARAMETER; the shape is not: a search of the library found no caller of
that shape but the members' batching, in a proof file and in a key file. Over any commutative ring.
Statements with their proofs.

The parameter. q: from the challenges heard so far to the three coefficients (of 1, X, X^2) of the
summand's polynomial of the next round. v: from the challenges heard so far to the summand's sum
over the variables that are left. What is asked of them (`Fits`), for fewer challenges than there
are variables: v is the round's polynomial at 0 plus at 1; and with one more challenge g heard, v is
the round's polynomial at g. Nothing else is asked: the summand may be any function of a witness.

The polynomial of the sumcheck is U + eps (s X_1 .. X_n + the summand), with U the hiding polynomial
of Johnson/Desc/K13/Honest/Moves.lean (`tailU`; its value at a point: `uAt`, Code.lean) and s the
value of the claim's incoming mask form. The term s X_1 .. X_n lies wholly in the linear
coefficients, which are not sent: it comes in through the argument pre of the law, at pre := eps s.
Main names:
  `Fits N q v`: what is asked of the parameter.
  `after_sentL`: **the running claim (`after`, Code.lean), begun at pre + the sum of U + eps v, ends
    at the value of pre X_1 .. X_n + U at the challenges, plus eps v at all challenges.**
  `foldsAll_snoc`, `sized_foldsAll`, `fits_tables`, `sent_eq`: tables meet what is asked, and
    `sent` is `sentL` at them.
  `after_sent`: **the law at tables.**
  `sentL_take`, `sent_take`: **a round's scalars read the earlier challenges alone**: two lists of
    challenges that agree on the first t give the same first t + 1 pairs.

What is not claimed. Other ways of summing, other degrees, a further variable with shown values, a
caller's scalars sent ahead of the sum: not treated. `after` and `uAt` are tied to a verifier's text
in Johnson/Desc/K13/Honest/CodeRow.lean alone, and there to the members' batching's. Nothing on
soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.Code

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest

variable {K : Type} [CommRing K]

/-- What is asked of the summand's two functions, at N variables. -/
structure Fits (N : ℕ) (q : List K → K × K × K) (v : List K → K) : Prop where
  /-- the sum that is left is the round's polynomial at 0 plus at 1 -/
  sum : ∀ seen : List K, seen.length < N → v seen = 2 * (q seen).1 + (q seen).2.1 + (q seen).2.2
  /-- with one more challenge heard it is the round's polynomial there -/
  step : ∀ (seen : List K) (g : K), seen.length < N →
    v (seen ++ [g]) = (q seen).1 + (q seen).2.1 * g + (q seen).2.2 * g ^ 2

/-- **The law**: the running claim, begun at pre + the sum of U + eps v, ends at the value of
pre X_1 .. X_n + U at the challenges, plus eps v at all challenges. -/
theorem after_sentL (u : ℕ → K) (eps : K) {N : ℕ} {q : List K → K × K × K} {v : List K → K}
    (hq : Fits N q v) : ∀ (n i : ℕ) (seen gs : List K) (pre : K), seen.length + n = N →
    gs.length = n →
    after (sentL u eps q n i seen gs) gs (pre + tailU u n i + eps * v seen) =
      uAt u n i pre gs + eps * v (seen ++ gs)
  | 0, i, seen, [], pre, _, _ => by
    show pre + 0 + eps * v seen = pre + eps * v (seen ++ [])
    rw [List.append_nil]
    ring
  | 1, i, seen, [g], pre, hN, _ => by
    have h1 := hq.sum seen (by omega)
    have h2 := hq.step seen g (by omega)
    show (u i + eps * (q seen).1) +
        ((pre + (2 * u i + u (i + 1) + u (i + 2)) + eps * v seen) -
          2 * (u i + eps * (q seen).1) - (u (i + 2) + eps * (q seen).2.2)) * g +
        (u (i + 2) + eps * (q seen).2.2) * g ^ 2 =
      (pre * g + u i + u (i + 1) * g + u (i + 2) * g ^ 2) + eps * v (seen ++ [g])
    rw [h1, h2]
    ring
  | n + 2, i, seen, g :: gs, pre, hN, hg => by
    have h1 := hq.sum seen (by omega)
    have h2 := hq.step seen g (by omega)
    have ih := after_sentL u eps hq (n + 1) (i + 2) (seen ++ [g]) gs
      (pre * g + u i * g + u (i + 1) * g ^ 2)
      (by rw [List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_cons] at hg; omega)
    have e : seen ++ g :: gs = seen ++ [g] ++ gs := by simp
    show after (sentL u eps q (n + 1) (i + 2) (seen ++ [g]) gs) gs
        ((tailU u (n + 1) (i + 2) + eps * (q seen).1) +
          ((pre + (u i + u (i + 1) + 2 * tailU u (n + 1) (i + 2)) + eps * v seen) -
            2 * (tailU u (n + 1) (i + 2) + eps * (q seen).1) -
            (u (i + 1) + eps * (q seen).2.2)) * g +
          (u (i + 1) + eps * (q seen).2.2) * g ^ 2) =
      uAt u (n + 1) (i + 2) (pre * g + u i * g + u (i + 1) * g ^ 2) gs + eps * v (seen ++ g :: gs)
    rw [e, ← ih, h2, h1]
    congr 1
    ring
  | 0, _, _, _ :: _, _, _, hg => by simp only [List.length_cons] at hg; omega
  | 1, _, _, [], _, _, hg => by simp only [List.length_nil] at hg; omega
  | 1, _, _, _ :: _ :: _, _, _, hg => by simp only [List.length_cons] at hg; omega
  | _ + 2, _, _, [], _, _, hg => by simp only [List.length_nil] at hg; omega

/-! ## Tables as the parameter -/

/-- One more variable set, behind the others. -/
theorem foldsAll_snoc (g : K) : ∀ (seen : List K) (S : List (List K × List K)),
    foldsAll (seen ++ [g]) S = foldAll g (foldsAll seen S)
  | [], _ => rfl
  | a :: seen, S => foldsAll_snoc g seen (foldAll a S)

/-- Tables with some variables set have the size of the variables that are left. -/
theorem sized_foldsAll : ∀ (seen : List K) (n : ℕ) (S : List (List K × List K)),
    Sized S (seen.length + n) → Sized (foldsAll seen S) n
  | [], n, S, h => by
    have e : ([] : List K).length + n = n := by simp
    rw [e] at h
    exact h
  | a :: seen, n, S, h => by
    have e : (a :: seen).length + n = (seen.length + n) + 1 := by
      simp only [List.length_cons]
      omega
    rw [e] at h
    exact sized_foldsAll seen n (foldAll a S) (h.fold a)

/-- **Tables meet what is asked.** -/
theorem fits_tables {N : ℕ} {S : List (List K × List K)} (hS : Sized S N) :
    Fits N (fun seen => quadAll (foldsAll seen S)) (fun seen => dotAll (foldsAll seen S)) where
  sum := fun seen h => by
    obtain ⟨m, rfl⟩ : ∃ m, N = seen.length + (m + 1) := ⟨N - seen.length - 1, by omega⟩
    exact dotAll_quad (2 ^ m) _ (sized_foldsAll seen (m + 1) S hS).even
  step := fun seen g _ => by
    show dotAll (foldsAll (seen ++ [g]) S) = _
    rw [foldsAll_snoc]
    exact dotAll_fold g _

/-- What is sent at tables is what is sent at the functions that they make. -/
theorem sent_eq (u : ℕ → K) (eps : K) (S₀ : List (List K × List K)) : ∀ (n i : ℕ)
    (seen gs : List K),
    sent u eps n i (foldsAll seen S₀) gs =
      sentL u eps (fun seen => quadAll (foldsAll seen S₀)) n i seen gs
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | n + 2, i, seen, gs => by
    show _ :: sent u eps (n + 1) (i + 2) (foldAll (gs.headD 0) (foldsAll seen S₀)) gs.tail =
      _ :: sentL u eps _ (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail
    rw [← foldsAll_snoc, sent_eq u eps S₀ (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail]

/-- **The law at tables**: the running claim ends at the polynomial's value at the challenges. It
begins at "pre, plus the sum of U, plus eps times the sum of the products". -/
theorem after_sent (u : ℕ → K) (eps : K) (n : ℕ) (S : List (List K × List K)) (gs : List K)
    (pre : K) (hS : Sized S n) (hg : gs.length = n) :
    after (sent u eps n 0 S gs) gs (pre + tailU u n 0 + eps * dotAll S) =
      uAt u n 0 pre gs + eps * dotAll (foldsAll gs S) := by
  have h := after_sentL u eps (fits_tables hS) n 0 [] gs pre (by simp) hg
  have e := sent_eq u eps S n 0 [] gs
  rw [← e] at h
  exact h

/-! ## No later challenge is read -/

/-- Two lists that agree on their first t + 1 members agree in their heads and in the first t
members of their tails. -/
theorem take_succ_parts : ∀ (gs gs' : List K) (t : ℕ), gs.take (t + 1) = gs'.take (t + 1) →
    gs.headD 0 = gs'.headD 0 ∧ gs.tail.take t = gs'.tail.take t
  | [], [], _, _ => ⟨rfl, rfl⟩
  | a :: l, b :: l', t, h => by
    rw [List.take_succ_cons, List.take_succ_cons] at h
    exact ⟨(List.cons.inj h).1, (List.cons.inj h).2⟩
  | [], _ :: _, _, h => by
    rw [List.take_succ_cons] at h
    cases h
  | _ :: _, [], _, h => by
    rw [List.take_succ_cons] at h
    cases h

/-- **A round's scalars read the earlier challenges alone.** -/
theorem sentL_take (u : ℕ → K) (eps : K) (q : List K → K × K × K) : ∀ (n i : ℕ)
    (seen gs gs' : List K) (t : ℕ), gs.take t = gs'.take t →
    (sentL u eps q n i seen gs).take (t + 1) = (sentL u eps q n i seen gs').take (t + 1)
  | 0, _, _, _, _, _, _ => rfl
  | 1, _, _, _, _, _, _ => rfl
  | n + 2, i, seen, gs, gs', 0, _ => rfl
  | n + 2, i, seen, gs, gs', t + 1, h => by
    obtain ⟨h1, h2⟩ := take_succ_parts gs gs' t h
    show _ :: (sentL u eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail).take (t + 1) =
      _ :: (sentL u eps q (n + 1) (i + 2) (seen ++ [gs'.headD 0]) gs'.tail).take (t + 1)
    rw [h1, sentL_take u eps q (n + 1) (i + 2) _ gs.tail gs'.tail t h2]

/-- The same at tables. -/
theorem sent_take (u : ℕ → K) (eps : K) (n : ℕ) (S : List (List K × List K)) (gs gs' : List K)
    (t : ℕ) (h : gs.take t = gs'.take t) :
    (sent u eps n 0 S gs).take (t + 1) = (sent u eps n 0 S gs').take (t + 1) := by
  have e := sent_eq u eps S n 0 [] gs
  have e' := sent_eq u eps S n 0 [] gs'
  have e0 : foldsAll ([] : List K) S = S := rfl
  rw [e0] at e e'
  rw [e, e']
  exact sentL_take u eps _ n 0 [] gs gs' t h

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.after_sentL
#print axioms VerifiableInference.Desc.K13.Honest.foldsAll_snoc
#print axioms VerifiableInference.Desc.K13.Honest.sized_foldsAll
#print axioms VerifiableInference.Desc.K13.Honest.fits_tables
#print axioms VerifiableInference.Desc.K13.Honest.sent_eq
#print axioms VerifiableInference.Desc.K13.Honest.after_sent
#print axioms VerifiableInference.Desc.K13.Honest.take_succ_parts
#print axioms VerifiableInference.Desc.K13.Honest.sentL_take
#print axioms VerifiableInference.Desc.K13.Honest.sent_take
