-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Count.lean
(kind K9's soundness lemma): THEOREMS: (T3), the count, and the top theorem.
  count_terms   a polynomial in chi, given as terms (exponent, coefficient) with exponents that
                differ from each other and are at most d, and with a coefficient other than 0, is 0
                at no more than d elements of the field. CARRIED from the library's zero-evader of
                powers (Cb/Gen/BatEvader.lean) through powersAt_ok (Johnson/Desc/LinkLaw.lean).
  passes_root   a challenge that passes is a root of that polynomial: (T1) and (T2) put together.
  batch_sound   **IF THE POLYNOMIAL IN chi THAT THE CLAIMS ADD UP TO ON THE DATA D IS NOT THE ZERO
                POLYNOMIAL, AT MOST d ELEMENTS OF THE FIELD ARE READINGS OF A CHALLENGE AT WHICH
                K9's TEXT ADDS ALL CLAIMS AND MAKES AN EQUATION THAT HOLDS ON D.**
  t3, k9Law     (T3), and the lemma as one proposition (Law/Statements.lean: K9Law), hold of
                addClaim and K9.equation.
  batch_sound_words   the same count on machine words: in any finite set of challenges on which the
                reading is one-to-one, at most d pass.
  gl_injOn      the library's reading Reading.gl is one-to-one on words below the prime (okE).
THE PREMISES are the structure Premises (Law/Statements.lean), each under its name. THE DATA D ARE
QUANTIFIED OUTSIDE chi. What is not claimed: that the premises hold of a segment of the protocol;
THAT THE COEFFICIENTS OF t ARE THE VALUES ON D OF THE EQUATIONS BEHIND THE CLAIMS, or that d is the
plan's n + Q - 1: whoever pays fixedBefore builds t; anything on the row that K9.asRow makes of the
equation; anything on how chi is drawn.

-/
import Johnson.Desc.LinkLaw
import Johnson.Desc.First.Batch.Law.Equation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (equation)

theorem sum_map_fin {K α : Type} [AddCommMonoid K] (f : α → K) :
    ∀ l : List α, (l.map f).sum = ∑ j : Fin l.length, f (l.get j)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_fin f l]
    show _ = ∑ j : Fin (l.length + 1), f ((a :: l).get j)
    rw [Fin.sum_univ_succ]
    rfl

/-- **The count of roots**, from the library's zero-evader of powers. -/
theorem count_terms (K : Type) [Field K] [Fintype K] (t : List (ℕ × K)) (d : ℕ)
    (ht : TermsOk t d) (hne : ∃ y ∈ t, y.2 ≠ 0) :
    Prob.cnt (fun x : K => termsSum t x = 0) ≤ d := by
  let e : Fin t.length → Fin (d + 1) :=
    fun j => ⟨(t.get j).1, Nat.lt_succ_of_le (ht.2 _ (List.get_mem t j))⟩
  have he : Function.Injective e := by
    intro a b hab
    have h1 : (t.get a).1 = (t.get b).1 := congrArg Fin.val hab
    have h2 : t.get a = t.get b :=
      List.inj_on_of_nodup_map ht.1 (List.get_mem t a) (List.get_mem t b) h1
    exact (List.nodup_iff_injective_get.mp (List.Nodup.of_map _ ht.1)) h2
  let v : Fin t.length → K := fun j => (t.get j).2
  have hv : v ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := hne
    obtain ⟨j, hj⟩ := List.get_of_mem hy
    intro h0
    apply hy0
    have h1 : v j = 0 := by rw [h0]; rfl
    rw [← hj]
    exact h1
  have ok : Prob.cnt (fun x : K => ∑ j : Fin t.length, x ^ (t.get j).1 * (t.get j).2 = 0) ≤ d :=
    powersAt_ok K d e he v hv
  refine le_trans (Prob.cnt_mono fun x hx => ?_) ok
  rw [← sum_map_fin (fun y : ℕ × K => x ^ y.1 * y.2) t]
  exact hx

variable {K : Type} [Field K] (ρ : Reading K)

/-- **A challenge that passes is a root.** -/
theorem passes_root (D : Bound K) (L : E → LinkCtx) (F : E → Fork) (cls : E → List Claim)
    (after : E → Fork → Option Fork) (t : List (ℕ × K)) (d : ℕ)
    (P : Premises addClaim ρ D L F cls after t d) (chi : E)
    (h : Passes addClaim equation ρ D L F cls after chi) : termsSum t (ρ.val chi) = 0 := by
  obtain ⟨G, H, q, G', ha, hh, he, hv⟩ := h
  have hk := P.keepsSums chi G H hh
  have hs : (F chi).LS.size = (F chi).ns := by
    obtain ⟨s1, s2⟩ := addAll_sizes (cls chi) (F chi) G ha
    have k := hk
    simp only [sums, Prod.mk.injEq] at k
    rw [← s1, ← s2, ← k.2.1, ← k.2.2.2]
    exact equation_sized (L chi) H G' q he
  have a1 := (addAll_total ρ (worldAt ρ (L chi) H D) (cls chi) (F chi) G hs ha).1
  have b := equation_total ρ D (L chi) H G' q he
  rw [total_of_sums ρ _ G H hk, a1, total_of_empty ρ _ (F chi) (P.startsEmpty chi), zero_add,
    P.holdsChi chi, P.fixedBefore chi G H ha hh] at b
  rw [← b, hv]

/-- **THE COUNT.** -/
theorem batch_sound [Fintype K] (D : Bound K) (L : E → LinkCtx) (F : E → Fork)
    (cls : E → List Claim) (after : E → Fork → Option Fork) (t : List (ℕ × K)) (d : ℕ)
    (P : Premises addClaim ρ D L F cls after t d) (hne : ∃ y ∈ t, y.2 ≠ 0) :
    Prob.cnt (fun x : K =>
      ∃ chi, ρ.val chi = x ∧ Passes addClaim equation ρ D L F cls after chi) ≤ d :=
  le_trans
    (Prob.cnt_mono fun x hx => by
      obtain ⟨chi, hc, hp⟩ := hx
      rw [← hc]
      exact passes_root ρ D L F cls after t d P chi hp)
    (count_terms K t d P.termsOk hne)

/-- (T3) holds of addClaim and K9.equation. -/
theorem t3 : T3 addClaim equation :=
  fun _ _ _ ρ D L F cls after t d P hne => batch_sound ρ D L F cls after t d P hne

/-- **THE LEMMA: K9's own functions meet it.** -/
theorem k9Law : K9Law addClaim equation := ⟨t1, t2, t3⟩

/-- **The count on machine words.** -/
theorem batch_sound_words [Fintype K] (D : Bound K) (L : E → LinkCtx) (F : E → Fork)
    (cls : E → List Claim) (after : E → Fork → Option Fork) (t : List (ℕ × K)) (d : ℕ)
    (P : Premises addClaim ρ D L F cls after t d) (hne : ∃ y ∈ t, y.2 ≠ 0) (S : Finset E)
    (hS : Set.InjOn ρ.val (S : Set E)) :
    Nat.card {chi : E // chi ∈ S ∧ Passes addClaim equation ρ D L F cls after chi} ≤ d := by
  refine le_trans ?_ (batch_sound ρ D L F cls after t d P hne)
  apply Nat.card_le_card_of_injective
    (fun c : {chi : E // chi ∈ S ∧ Passes addClaim equation ρ D L F cls after chi} =>
      (⟨ρ.val c.1, c.1, rfl, c.2.2⟩ :
        {x : K // ∃ chi, ρ.val chi = x ∧ Passes addClaim equation ρ D L F cls after chi}))
  intro a b hab
  have h1 : ρ.val a.1 = ρ.val b.1 := congrArg Subtype.val hab
  exact Subtype.ext (hS a.2.1 b.2.1 h1)

/-- The library's reading is one-to-one on words below the prime. -/
theorem gl_injOn : Set.InjOn Reading.gl.val {x : E | okE x = true} := by
  intro a ha b hb h
  have h1 : a.triple = b.triple :=
    Slice.toE_inj a.triple b.triple (by rw [← okE_triple]; exact ha)
      (by rw [← okE_triple]; exact hb) h
  rw [← E.ofTriple_triple a, ← E.ofTriple_triple b, h1]

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.powersAt_ok
#print axioms VerifiableInference.Desc.clean_powersAt
#print axioms VerifiableInference.Desc.K9L.count_terms
#print axioms VerifiableInference.Desc.K9L.passes_root
#print axioms VerifiableInference.Desc.K9L.batch_sound
#print axioms VerifiableInference.Desc.K9L.t3
#print axioms VerifiableInference.Desc.K9L.k9Law
#print axioms VerifiableInference.Desc.K9L.batch_sound_words
#print axioms VerifiableInference.Desc.K9L.gl_injOn
