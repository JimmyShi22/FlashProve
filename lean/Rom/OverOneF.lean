-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Rom/OverOneF.lean: the step to one hash function in which the first hash block of an answer is
queried, and the others only if a test on the first block says so (a third exit, beside
`OComp.overOne`, Rom/Family.lean, and `OComp.overOneN`, Rom/OverOneN.lean).

Why. A search tries queries until the answer passes a test. Where the test reads the answer's first
hash block alone, a try that fails needs no other block. `overOne` asks all blocks of every answer;
`overOneN` marks blocks by the oracle, the query and the block's number, before any answer is seen:
it cannot tell a try that fails from one that passes.

What is proved. Where the program reads an answer only up to `AgreeF m more` (the condition
`FactorsBy`), the third exit has, AT EVERY HASH FUNCTION, the law of the output that the program has
at the family read out of it: so the first exit's law, probabilities and completeness error. Its
queries to f are bounded by a sum of weights that hang on the answers.

Main names.
  `More S lam`        the test: of the oracle, the query and the answer's first hash block.
  `askFirst`          query f at the first of n strings; at the others if the test says yes; else
                      the all-zero block `dig0` stands for them.
  `OComp.overOneF`    the same algorithm over the hash function, by `askFirst`. An answer is joined
                      by `(m.rng o).symm`, as in `overOne`.
  `valFirst`          the blocks that `askFirst` returns under a fixed hash function.
  `AgreeF m more`     two answers have the same first block, and all blocks the same where the test
                      says yes at it: the relation for `OComp.FactorsBy` (Rom/OverOneN.lean).
  `costF m more`      what an answer costs: all its blocks, or one.
  `OComp.CostBoundR`  `OComp.CostBoundAt` (Rom/OverOneN.lean) with a weight that may hang on the
                      answer.
  `overOneArgF`       an argument system over f whose prover goes by `overOneF`; committer and
                      verifier by `overOne`, as in `schemeOverOneHashFunction`.
  `runEager_askFirst`, `agreeF_first`, `runEager_overOneF`, `runEager_overOneF_eq`, `Pr_overOneF`
                      the same law at every hash function.
  `runEager_mixed`, `Pr_mixed`   first exit, then third, then first: the typed bind's law.
  `completeness_overOneF`   `completeness_overOne` (Rom/ExitBind.lean) at `overOneArgF`.
  `noCoin_overOneF`, `overOneF_bind`, `overOneF_all`   as programs.
  `queryBound_overOneF`   the count. `OComp.CostBoundR.mono`, `.bind`, `.of_costBound`,
                      `.of_queryBound`: how the weighted bound is had.

Limits. The all-zero block can appear in the output: a program that returns a block that was not
asked returns `dig0` whatever f is: what shuts that out is the condition `FactorsBy (AgreeF m
more)`, which is a premise of every
statement on values.

-/
import Rom.OverOneN
import Rom.ExitBind
import Rom.NoCoinExits
import Rom.SigmaExits

set_option autoImplicit false

namespace Rom
open ZKCP

open scoped ENNReal

variable {S : OSpec} {lam : ℕ} {α β γ : Type}

/-- The test on an answer's first hash block: yes: the other blocks are asked too. -/
abbrev More (S : OSpec) (lam : ℕ) : Type := (o : S.ι) → S.Dom o → (Fin lam → Bool) → Bool

/-- Query f at the first of n strings; at the others, in the order of `askAll`, if the test says yes
at the first answer; else the all-zero block stands for them. -/
def askFirst (lam : ℕ) :
    (n : ℕ) → ((Fin lam → Bool) → Bool) → (Fin n → List Bool) →
      OComp (rom lam) (Fin n → Fin lam → Bool)
  | 0, _, _ => .pure fun i => i.elim0
  | n + 1, mr, g => .query (S := rom lam) () (g 0) fun r =>
      match mr r with
      | true => (askAll lam n fun i => g i.succ).bind fun rest =>
          .pure (Fin.cons (α := fun _ => Fin lam → Bool) r rest)
      | false => .pure (Fin.cons (α := fun _ => Fin lam → Bool) r fun _ => dig0 lam)

/-- The same algorithm over the hash function: of each answer the first block, and the others if the
test says yes. -/
def OComp.overOneF (m : OracleCoding S lam) (more : More S lam) : OComp S α → OComp (rom lam) α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => (k r).overOneF m more
  | .query o q k =>
    (askFirst lam (m.blocks o) (more o q) (m.code o q)).bind fun bs =>
      (k ((m.rng o).symm bs)).overOneF m more

/-- The blocks that `askFirst` returns under the hash function g. -/
def valFirst (g : Fam (rom lam)) {n : ℕ} (mr : (Fin lam → Bool) → Bool) (pts : Fin n → List Bool) :
    Fin n → Fin lam → Bool := fun j =>
  if j.val = 0 ∨ mr (g () (pts ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩)) = true then
    g () (pts j)
  else dig0 lam

/-- Two answers to (o, q) have the same first hash block; and all blocks the same, if the test says
yes at the first block. -/
def AgreeF (m : OracleCoding S lam) (more : More S lam) (o : S.ι) (q : S.Dom o) (r r' : S.Rng o) : Prop :=
  ∀ j : Fin (m.blocks o),
    (j.val = 0 ∨ more o q (m.rng o r ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩) = true) →
      m.rng o r j = m.rng o r' j

/-- What the answer r to (o, q) costs in queries to f. -/
def costF (m : OracleCoding S lam) (more : More S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o) : ℕ :=
  if h : 0 < m.blocks o then (if more o q (m.rng o r ⟨0, h⟩) = true then m.blocks o else 1) else 0

/-- On every path, whatever the answers and the coins, the weights w o q r of the queries with their
answers add up to at most t. -/
def OComp.CostBoundR (w : (o : S.ι) → S.Dom o → S.Rng o → ℕ) : OComp S α → ℕ → Prop
  | .pure _, _ => True
  | .sample _ k, t => ∀ r, (k r).CostBoundR w t
  | .query o q k, t => ∀ r, ∃ t', t = w o q r + t' ∧ (k r).CostBoundR w t'

/-- The argument system over f whose prover asks first blocks first. -/
def overOneArgF {I X W IVK ISK Pf : Type} (m : OracleCoding S lam) (more : More S lam)
    (A : Gen.Arg S I X W IVK ISK Pf) : Gen.Arg (rom lam) I X W IVK ISK Pf where
  C := fun i => (A.C i).overOne m
  P := fun k b => (A.P k b).overOneF m more
  V := fun v x π => (A.V v x π).overOne m

/-! ## The run under a fixed hash function -/

/-- Under a fixed hash function g the run of `askFirst` returns `valFirst g mr pts`. -/
theorem runEager_askFirst (g : Fam (rom lam)) :
    ∀ (n : ℕ) (mr : (Fin lam → Bool) → Bool) (pts : Fin n → List Bool),
      (askFirst lam n mr pts).runEager g = PMF.pure (valFirst g mr pts)
  | 0, _, _ => by
    simp only [askFirst, OComp.runEager]
    congr 1; funext j; exact j.elim0
  | n + 1, mr, pts => by
    unfold askFirst
    simp only [OComp.runEager]
    cases h : mr (g () (pts 0))
    · simp only [OComp.runEager]
      congr 1; funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [valFirst]
      · simp [valFirst, h]
    · simp only [OComp.runEager_bind, runEager_askAll]
      refine (PMF.pure_bind _ _).trans ?_
      simp only [OComp.runEager]
      congr 1; funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [valFirst]
      · simp [valFirst, h]

/-- What `overOneF` joins at the query (o, q) agrees with the true answer. -/
theorem agreeF_first (m : OracleCoding S lam) (more : More S lam) (g : Fam (rom lam)) (o : S.ι)
    (q : S.Dom o) :
    AgreeF m more o q ((m.rng o).symm (valFirst g (more o q) (m.code o q)))
      (readBlocks m g o q) := by
  intro j hj
  unfold readBlocks
  rw [Equiv.apply_symm_apply] at hj ⊢
  rw [Equiv.apply_symm_apply]
  have h0 : valFirst g (more o q) (m.code o q)
      ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩ =
      g () (m.code o q ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩) := if_pos (Or.inl rfl)
  rw [h0] at hj
  exact if_pos hj

/-- **The same law of the output at every hash function**: the third exit behaves, for every fixed
function, as the algorithm over the family that is read out of it. -/
theorem runEager_overOneF (m : OracleCoding S lam) (more : More S lam) (g : Fam (rom lam)) :
    ∀ c : OComp S α, c.FactorsBy (AgreeF m more) →
      (c.overOneF m more).runEager g = c.runEager (readBlocks m g) := by
  intro c
  induction c with
  | pure a => intro _; rfl
  | sample n k ih =>
    intro h
    simp only [OComp.overOneF, OComp.runEager]
    congr 1; funext r
    exact ih r (h r)
  | query o q k ih =>
    intro h
    simp only [OComp.overOneF, OComp.runEager, OComp.runEager_bind, runEager_askFirst]
    refine (PMF.pure_bind _ _).trans ?_
    rw [ih _ (h.2 _), h.1 _ _ (agreeF_first m more g o q)]

/-- The third exit and the first have one law at every hash function. -/
theorem runEager_overOneF_eq (m : OracleCoding S lam) (more : More S lam) (g : Fam (rom lam))
    (c : OComp S α) (h : c.FactorsBy (AgreeF m more)) :
    (c.overOneF m more).runEager g = (c.overOne m).runEager g := by
  rw [runEager_overOneF m more g c h, runEager_overOne]

/-- Two programs with one law at every family have the same probabilities. -/
theorem Pr_congr_runEager {S' : OSpec} {c c' : OComp S' α}
    (h : ∀ g, c.runEager g = c'.runEager g) (E : Fam S' → Set α) : Pr c E = Pr c' E := by
  unfold Pr PrCoins
  simp only [h]

/-- The probabilities agree. -/
theorem Pr_overOneF (m : OracleCoding S lam) (more : More S lam) (c : OComp S α) (E : Set α)
    (h : c.FactorsBy (AgreeF m more)) :
    Pr (c.overOneF m more) (fun _ => E) = Pr c (fun _ => E) :=
  (Pr_congr_runEager (fun g => runEager_overOneF_eq m more g c h) _).trans (Pr_overOne m c E)

/-- **First exit, third exit, first exit**: at every hash function the law of the typed bind. -/
theorem runEager_mixed (m : OracleCoding S lam) (more : More S lam) (g : Fam (rom lam)) (c₁ : OComp S α)
    (c₂ : α → OComp S β) (c₃ : α → β → OComp S γ)
    (h : ∀ a, (c₂ a).FactorsBy (AgreeF m more)) :
    ((c₁.overOne m).bind fun a => ((c₂ a).overOneF m more).bind fun b =>
      (c₃ a b).overOne m).runEager g =
      (c₁.bind fun a => (c₂ a).bind fun b => c₃ a b).runEager (readBlocks m g) := by
  simp only [OComp.runEager_bind, runEager_overOne]
  congr 1; funext a
  rw [runEager_overOneF m more g (c₂ a) (h a)]

/-- The same for probabilities. -/
theorem Pr_mixed (m : OracleCoding S lam) (more : More S lam) (c₁ : OComp S α) (c₂ : α → OComp S β)
    (c₃ : α → β → OComp S γ) (h : ∀ a, (c₂ a).FactorsBy (AgreeF m more)) (E : Set γ) :
    Pr ((c₁.overOne m).bind fun a => ((c₂ a).overOneF m more).bind fun b => (c₃ a b).overOne m)
      (fun _ => E) = Pr (c₁.bind fun a => (c₂ a).bind fun b => c₃ a b) (fun _ => E) :=
  (Pr_congr_runEager (fun g => by
    rw [runEager_mixed m more g c₁ c₂ c₃ h, runEager_overOne]) _).trans (Pr_overOne m _ E)

/-! ## Programs -/

theorem noCoin_askFirst : ∀ (n : ℕ) (mr : (Fin lam → Bool) → Bool) (pts : Fin n → List Bool),
    (askFirst lam n mr pts).NoCoin
  | 0, _, _ => trivial
  | n + 1, mr, pts => fun r => by
    cases h : mr r
    · simp only [h]
      trivial
    · simp only [h]
      exact OComp.NoCoin.bind (noCoin_askAll n fun i => pts i.succ) fun _ => trivial

theorem noCoin_overOneF (m : OracleCoding S lam) (more : More S lam) :
    ∀ c : OComp S α, c.NoCoin → (c.overOneF m more).NoCoin
  | .pure _, _ => trivial
  | .query _ _ k, h =>
    OComp.NoCoin.bind (noCoin_askFirst _ _ _) fun _ => noCoin_overOneF m more (k _) (h _)
  | .sample _ _, h => h.elim

theorem overOneF_bind (m : OracleCoding S lam) (more : More S lam) (c : OComp S α) (g : α → OComp S β) :
    (c.bind g).overOneF m more = (c.overOneF m more).bind fun a => (g a).overOneF m more := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, OComp.overOneF, ih]
  | query o q k ih => simp only [OComp.bind, OComp.overOneF, ih, OComp.bind_assoc]

theorem askFirst_all : ∀ (n : ℕ) (pts : Fin n → List Bool),
    askFirst lam n (fun _ => true) pts = askAll lam n pts
  | 0, _ => rfl
  | _ + 1, _ => rfl

/-- With the test "always yes" the third exit is the first, as a program. -/
theorem overOneF_all (m : OracleCoding S lam) (c : OComp S α) :
    c.overOneF m (fun _ _ _ => true) = c.overOne m := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.overOneF, OComp.overOne, ih]
  | query o q k ih => simp only [OComp.overOneF, OComp.overOne, ih, askFirst_all]

/-! ## The weighted bound -/

namespace OComp.CostBoundR

variable {w : (o : S.ι) → S.Dom o → S.Rng o → ℕ}

theorem mono {c : OComp S α} : ∀ {s t : ℕ}, c.CostBoundR w s → s ≤ t → c.CostBoundR w t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun h hst r => ih r (h r) hst
  | query o q k ih =>
    intro s t h hst r
    obtain ⟨s', rfl, h'⟩ := h r
    exact ⟨t - w o q r, by omega, ih r h' (by omega)⟩

theorem bind {c : OComp S α} {g : α → OComp S β} {t : ℕ} (hg : ∀ a, (g a).CostBoundR w t) :
    ∀ {s : ℕ}, c.CostBoundR w s → (c.bind g).CostBoundR w (s + t) := by
  induction c with
  | pure a => exact fun _ => (hg a).mono (by omega)
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    intro s h r
    obtain ⟨s', rfl, h'⟩ := h r
    exact ⟨s' + t, by omega, ih r h'⟩

theorem pure (a : α) (t : ℕ) : (OComp.pure a : OComp S α).CostBoundR w t := trivial

/-- A bound by a weight of the oracle alone that is nowhere below w. -/
theorem of_costBound {v : S.ι → ℕ} (hv : ∀ o q r, w o q r ≤ v o) {c : OComp S α} :
    ∀ {t : ℕ}, c.CostBound v t → c.CostBoundR w t := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro t ⟨t', rfl, h⟩ r
    have := hv o q r
    exact ⟨v o + t' - w o q r, by omega, (ih r (h r)).mono (by omega)⟩

/-- A bound on the number of queries, where no query that is asked weighs more than 1. -/
theorem of_queryBound {c : OComp S α} :
    ∀ {t : ℕ}, c.QueryBound t → c.AsksIn (fun o q => ∀ r, w o q r ≤ 1) → c.CostBoundR w t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun h ha r => ih r (h r) (ha r)
  | query o q k ih =>
    intro t h ha r
    cases t with
    | zero => exact h.elim
    | succ t =>
      have := ha.1 r
      exact ⟨t + 1 - w o q r, by omega, (ih r (h r) (ha.2 r)).mono (by omega)⟩

end OComp.CostBoundR

theorem costF_le (m : OracleCoding S lam) (more : More S lam) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    costF m more o q r ≤ m.blocks o := by
  unfold costF
  split
  · split <;> omega
  · omega

/-! ## Queries to f -/

/-- `askFirst`, then a program: the queries of both. -/
theorem queryBound_askFirst_bind (n : ℕ) (mr : (Fin lam → Bool) → Bool) (pts : Fin n → List Bool)
    (k : (Fin n → Fin lam → Bool) → OComp (rom lam) β) (t : ℕ)
    (h : ∀ bs : Fin n → Fin lam → Bool, ∃ t',
      t = (if h0 : 0 < n then (if mr (bs ⟨0, h0⟩) = true then n else 1) else 0) + t' ∧
        (k bs).QueryBound t') :
    ((askFirst lam n mr pts).bind k).QueryBound t := by
  cases n with
  | zero =>
    obtain ⟨t', rfl, h'⟩ := h fun i => i.elim0
    exact OComp.QueryBound.mono (c := k fun i => i.elim0) h' (by omega)
  | succ n =>
    have key : ∀ r : Fin lam → Bool, ∀ s, t = s + 1 →
        ((match mr r with
          | true => (askAll lam n fun i => pts i.succ).bind fun rest =>
              OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) r rest)
          | false => OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) r fun _ => dig0 lam) :
            OComp (rom lam) (Fin (n + 1) → Fin lam → Bool)).bind k).QueryBound s := by
      intro r s hs
      cases hr : mr r
      · obtain ⟨t', e, h'⟩ := h (Fin.cons (α := fun _ => Fin lam → Bool) r fun _ => dig0 lam)
        have hr' : mr ((Fin.cons (α := fun _ => Fin lam → Bool) r fun _ => dig0 lam :
            Fin (n + 1) → Fin lam → Bool) ⟨0, Nat.succ_pos n⟩) = false := hr
        rw [dif_pos (Nat.succ_pos n), hr'] at e
        simp only [Bool.false_eq_true, if_false] at e
        exact OComp.QueryBound.mono
          (c := k (Fin.cons (α := fun _ => Fin lam → Bool) r fun _ => dig0 lam)) h' (by omega)
      · simp only [OComp.bind_assoc]
        have hb := (queryBound_askAll (lam := lam) n fun i => pts i.succ).bind (t := s - n)
          (g := fun rest => (OComp.pure (Fin.cons (α := fun _ => Fin lam → Bool) r rest) :
            OComp (rom lam) (Fin (n + 1) → Fin lam → Bool)).bind k) fun rest => by
            obtain ⟨t', e, h'⟩ := h (Fin.cons (α := fun _ => Fin lam → Bool) r rest)
            have hr' : mr ((Fin.cons (α := fun _ => Fin lam → Bool) r rest :
                Fin (n + 1) → Fin lam → Bool) ⟨0, Nat.succ_pos n⟩) = true := hr
            rw [dif_pos (Nat.succ_pos n), hr', if_pos rfl] at e
            exact OComp.QueryBound.mono
              (c := k (Fin.cons (α := fun _ => Fin lam → Bool) r rest)) h' (by omega)
        obtain ⟨t', e, -⟩ := h (Fin.cons (α := fun _ => Fin lam → Bool) r fun _ => dig0 lam)
        have hr' : mr ((Fin.cons (α := fun _ => Fin lam → Bool) r fun _ => dig0 lam :
            Fin (n + 1) → Fin lam → Bool) ⟨0, Nat.succ_pos n⟩) = true := hr
        rw [dif_pos (Nat.succ_pos n), hr', if_pos rfl] at e
        exact hb.mono (by omega)
    obtain ⟨t', e, -⟩ := h fun _ => dig0 lam
    have hpos : 1 ≤ t := by
      rw [dif_pos (Nat.succ_pos n)] at e
      split at e <;> omega
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact fun r => key r s rfl

/-- **The queries to the hash function**: if on every path of c the weights `costF m more` of its
queries with their answers add up to at most t, the third exit makes at most t queries. -/
theorem queryBound_overOneF (m : OracleCoding S lam) (more : More S lam) (c : OComp S α) (t : ℕ)
    (h : c.CostBoundR (costF m more) t) : (c.overOneF m more).QueryBound t := by
  induction c generalizing t with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r t (h r)
  | query o q k ih =>
    refine queryBound_askFirst_bind (m.blocks o) (more o q) (m.code o q)
      (fun bs => (k ((m.rng o).symm bs)).overOneF m more) t fun bs => ?_
    obtain ⟨t', e, h'⟩ := h ((m.rng o).symm bs)
    refine ⟨t', ?_, ih _ t' h'⟩
    rw [e]
    unfold costF
    simp only [Equiv.apply_symm_apply]

/-! ## Completeness -/

section
variable {I X W PP IVK ISK Pf : Type}

theorem verifyAll_overOneF (m : OracleCoding S lam) (more : More S lam) (A : Gen.Arg S I X W IVK ISK Pf)
    (ivk : IVK) (l : List (X × Pf)) :
    Gen.verifyAll (overOneArgF m more A) ivk l = (Gen.verifyAll A ivk l).overOne m := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have e1 : Gen.verifyAll (overOneArgF m more A) ivk (s :: rest) =
        ((A.V ivk s.1 s.2).overOne m).bind fun c =>
          (Gen.verifyAll (overOneArgF m more A) ivk rest).bind fun cs => .pure (c && cs) := rfl
    have e2 : Gen.verifyAll A ivk (s :: rest) = (A.V ivk s.1 s.2).bind fun c =>
        (Gen.verifyAll A ivk rest).bind fun cs => .pure (c && cs) := rfl
    rw [e1, e2, ih]
    simp only [overOne_bind]
    rfl

/-- **The library's road upward from `Gen.HasCompletenessError` takes the third exit at the
prover.** -/
theorem completeness_overOneF (m : OracleCoding S lam) (more : More S lam) (R : Gen.RelPair I X W PP)
    (A : Gen.Arg S I X W IVK ISK Pf) (B : ℕ) (a : ℝ≥0∞)
    (hP : ∀ k b, (A.P k b).FactorsBy (AgreeF m more)) (h : Gen.HasCompletenessError R A B a) :
    Gen.HasCompletenessError R (overOneArgF m more A) B a := by
  intro i b hb
  have e1 : Gen.completenessExp (overOneArgF m more A) i b = ((A.C i).overOne m).bind fun key =>
      ((A.P key.2 b).overOneF m more).bind fun πs =>
        Gen.verifyAll (overOneArgF m more A) key.1 ((b.map Prod.fst).zip πs.val) := rfl
  have e2 : Gen.completenessExp A i b = (A.C i).bind fun key =>
      (A.P key.2 b).bind fun πs => Gen.verifyAll A key.1 ((b.map Prod.fst).zip πs.val) := rfl
  rw [e1]
  simp only [verifyAll_overOneF]
  rw [Pr_mixed m more (A.C i) (fun key => A.P key.2 b)
    (fun key πs => Gen.verifyAll A key.1 ((b.map Prod.fst).zip πs.val)) (fun key => hP key.2 b),
    ← e2]
  exact h i b hb

end

end Rom

#print axioms Rom.runEager_askFirst
#print axioms Rom.agreeF_first
#print axioms Rom.runEager_overOneF
#print axioms Rom.runEager_overOneF_eq
#print axioms Rom.Pr_congr_runEager
#print axioms Rom.Pr_overOneF
#print axioms Rom.runEager_mixed
#print axioms Rom.Pr_mixed
#print axioms Rom.noCoin_askFirst
#print axioms Rom.noCoin_overOneF
#print axioms Rom.overOneF_bind
#print axioms Rom.askFirst_all
#print axioms Rom.overOneF_all
#print axioms Rom.OComp.CostBoundR.mono
#print axioms Rom.OComp.CostBoundR.bind
#print axioms Rom.OComp.CostBoundR.pure
#print axioms Rom.OComp.CostBoundR.of_costBound
#print axioms Rom.OComp.CostBoundR.of_queryBound
#print axioms Rom.costF_le
#print axioms Rom.queryBound_askFirst_bind
#print axioms Rom.queryBound_overOneF
#print axioms Rom.verifyAll_overOneF
#print axioms Rom.completeness_overOneF
