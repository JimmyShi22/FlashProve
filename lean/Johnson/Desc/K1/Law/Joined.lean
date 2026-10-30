-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Joined.lean: the condition of the kind's law, the bad seeds of a place, and
their number.

Main names: Seeds, msgAt, sampledAt, msgAt_answers_le, msgAt_v_le, ownSeeds, ownSeeds_eq; listV,
conditionB, Condition; Bad, errOf, clash_count, bad_count.
The count over a list is the library's ood_cnt_clash_on (Cb/Gen/OodDecPadProofs.lean).

What is not claimed. The lists are letters: which tables count as near a word that was sent, that
they are few, and that two of them differ on a pad of three entries by elements of the base field,
are premises (Condition). That errOf is small is not said here (Tries2.lean: term_frac). Nothing on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Fair
import Johnson.Desc.K1.Law.When

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Cb Cb.Ood Prob

/-! ## A place's messages and seeds -/

/-- The joint seeds of a place, in the field: factors other than 0. -/
abbrev Seeds (P : Par) : Type := Fin P.seeds → (Fin P.coordinates → GE) × GEˣ

/-- The numbers of the place's message number k. -/
def msgAt (P : Par) (k : Fin (shapesOf P).length) : Msg := Msg.of P.codes (shapesOf P)[k.val]

/-- It is sampled. -/
def sampledAt (P : Par) (k : Fin (shapesOf P).length) : Prop := (msgAt P k).answers ≠ 0

instance (P : Par) (k : Fin (shapesOf P).length) : Decidable (sampledAt P k) :=
  inferInstanceAs (Decidable (_ ≠ _))

theorem msgAt_answers_le (P : Par) (k : Fin (shapesOf P).length) :
    (msgAt P k).answers ≤ P.seeds := le_seeds P _ (List.getElem_mem k.isLt)

theorem fold_max_v (codes : Codes) (l : List OracleShape) : ∀ acc : Nat,
    acc ≤ l.foldl (fun b s => max b (Msg.of codes s).v) acc ∧
      ∀ s ∈ l, (Msg.of codes s).v ≤ l.foldl (fun b s => max b (Msg.of codes s).v) acc := by
  induction l with
  | nil => intro acc; simp
  | cons t l ih =>
    intro acc
    have h := ih (max acc (Msg.of codes t).v)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h.1, fun s hs => ?_⟩
    rcases List.mem_cons.1 hs with rfl | hs
    · exact Nat.le_trans (Nat.le_max_right _ _) h.1
    · exact h.2 s hs

theorem msgAt_v_le (P : Par) (k : Fin (shapesOf P).length) (h : sampledAt P k) :
    (msgAt P k).v ≤ P.coordinates := by
  refine (fold_max_v P.codes P.tuple 0).2 _ ?_
  simp only [Par.tuple, List.mem_filter]
  exact ⟨List.getElem_mem k.isLt, by simpa using h⟩

/-- What a message reads of joint seeds: the first seeds, and of each point the first coordinates.
-/
def ownSeeds {n v : Nat} (a v' : Nat) (ρ : Fin n → (Fin v → GE) × GEˣ) :
    Fin a → (Fin v' → GE) × GEˣ := fun i =>
  if h : i.val < n then (fun t => pointOf (ρ ⟨i.val, h⟩).1 t.val, (ρ ⟨i.val, h⟩).2)
  else (fun _ => 0, 1)

theorem ownSeeds_eq {n v : Nat} (a v' : Nat) (ha : a ≤ n) (hv : v' ≤ v)
    (ρ : Fin n → (Fin v → GE) × GEˣ) : ownSeeds a v' ρ = (partSeeds n a v v' ha hv ρ).1 := by
  funext i
  have h : i.val < n := Nat.lt_of_lt_of_le i.isLt ha
  unfold ownSeeds
  rw [dif_pos h]
  refine Prod.ext (funext fun t => ?_) rfl
  have h' : t.val < v := Nat.lt_of_lt_of_le t.isLt hv
  show pointOf _ t.val = _
  unfold pointOf
  rw [dif_pos h']
  rfl

/-! ## The condition -/

/-- A list of tables as a list of vectors of the sample map. -/
def listV (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (k : Fin (shapesOf P).length) :
    ((msgAt P k).J₀ ⊕ Fin (msgAt P k).answers × Fin (msgAt P k).e → GE) → Prop :=
  fun x => ∃ u, Lst k.val u ∧ (msgAt P k).vec u = x

/-- The two tests on public data, as one Boolean: the first is the condition's, the second is asked
beside it by WhenLaw alone: no clause on bad seeds or on lists needs it. -/
def conditionB (P : Par) : Bool := planOkOwn P && P.codes.lengthsOk

/-- **The condition under which the law holds.** Lst k: the tables that count as near the word sent
as message number k: a letter here. Lb k: a bound on their number. -/
structure Condition (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (Lb : Nat → Nat) : Prop where
  /-- the tests on the plan -/
  onPlan : planOkOwn P = true
  /-- every list is bounded -/
  list : ∀ k, sampledAt P k → ListLE (listV P Lst k) (Lb k.val)
  /-- where a pad has three entries, two members of a list differ on it by elements of the base
  field -/
  padsInF : ∀ k, sampledAt P k → (msgAt P k).e = 3 → ∀ u u', Lst k.val u → Lst k.val u' →
    ∀ x ∈ (msgAt P k).pads, u (msgAt P k).padPart x.2.1 - u' (msgAt P k).padPart x.2.1 ∈
      Set.range (algebraMap GF GE)

/-! ## The bad seeds -/

/-- **The bad seeds**: some sampled message's list has two members, different as vectors, with the
same answers. No answer of the prover occurs here. -/
def Bad (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (ρ : Seeds P) : Prop :=
  ∃ k, sampledAt P k ∧
    Clash (listV P Lst k) (msgAt P k).Z.val (ownSeeds (msgAt P k).answers (msgAt P k).v ρ)

/-- Their number is at most this. -/
noncomputable def errOf (P : Par) (Lb : Nat → Nat) : Nat :=
  ∑ k : Fin (shapesOf P).length, if sampledAt P k then
    (Lb k.val).choose 2 * (msgAt P k).Z.err *
      Fintype.card (Rest GE GEˣ P.seeds (msgAt P k).answers P.coordinates (msgAt P k).v)
  else 0

theorem clash_count (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (Lb : Nat → Nat)
    (hC : Condition P Lst Lb) (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    cnt (Clash (listV P Lst k) (msgAt P k).Z.val) ≤ (Lb k.val).choose 2 * (msgAt P k).Z.err := by
  rcases (msgAt P k).e_cases with he | he
  · exact ood_cnt_clash_on GE _ (msgAt P k).Z (PadInF GE) _ _ (hC.list k hk)
      ((msgAt P k).Z_okOn_E he) fun _ _ _ _ n => ⟨_, rfl⟩
  · refine ood_cnt_clash_on GE _ (msgAt P k).Z (PadInF GF) _ _ (hC.list k hk)
      ((msgAt P k).Z_okOn_F he) ?_
    rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩ n
    exact hC.padsInF k hk he u u' hu hu' (n.1.val, (msgAt P k).padIdx n.1.val n.2.val, n.2.val)
      (((msgAt P k).mem_pads _).2 ⟨_, _, n.1.isLt, n.2.isLt, rfl⟩)

/-- **The bad seeds are few.** -/
theorem bad_count (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (Lb : Nat → Nat)
    (hC : Condition P Lst Lb) : cnt (Bad P Lst) ≤ errOf P Lb := by
  unfold Bad errOf
  refine Nat.le_trans (cnt_exists_le _) (Finset.sum_le_sum fun k _ => ?_)
  by_cases hk : sampledAt P k
  · rw [if_pos hk]
    have e : (fun ρ : Seeds P => sampledAt P k ∧ Clash (listV P Lst k) (msgAt P k).Z.val
        (ownSeeds (msgAt P k).answers (msgAt P k).v ρ)) =
        fun ρ : Seeds P => Clash (listV P Lst k) (msgAt P k).Z.val
          (partSeeds P.seeds (msgAt P k).answers P.coordinates (msgAt P k).v
            (msgAt_answers_le P k) (msgAt_v_le P k hk) ρ).1 := by
      funext ρ
      rw [ownSeeds_eq _ _ (msgAt_answers_le P k) (msgAt_v_le P k hk)]
      exact propext ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
    rw [e, cnt_part]
    exact Nat.mul_le_mul_right _ (clash_count P Lst Lb hC k hk)
  · rw [if_neg hk]
    exact Nat.le_of_eq (cnt_false fun ρ h => hk h.1)

end VerifiableInference.Desc.K1
