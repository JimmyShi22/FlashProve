-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/PlainRuns.lean
(kind K9's soundness lemma): THEOREMS: A RUN OF PLAIN CLAIMS PAYS RunOk
(Law/Gather.lean) AND THE DISCIPLINE ON THE EXPONENTS (Law/ExpsOk.lean) FROM ONE VALUE A CLAIM.
A claim is PLAIN if it takes its own number's power of chi (eqFirst = none). (By the docstring of
Johnson/Desc/Claim.lean the other sort is the smallness test's ties and reads: not held here.)
  numbered n l   the terms (n, l[0]), (n + 1, l[1]), ..
  plainTm vals   the terms of a run whose claim number k is worth vals q y [k].
  PlainOk        THE PREMISE ON A RUN OF PLAIN CLAIMS: as RunOk, but in place of the sum: every
                 claim of the list is plain, and the list of the claims' VALUES, read in the world
                 of any full later state at the data y, is vals q y: a function of the fixed part
                 and the data alone. NO POWER OF chi, NO NUMBER, NO SUM stands in it.
  runOk_of_plain **PlainOk gives RunOk at the terms plainTm vals.**
  numbered_exps, numbered_inWin   the exponents of numbered n l are n, .., n + l.length - 1: they
                 differ from each other and lie in the window of numbers: the discipline's two
                 clauses at tie = 0. THE DISCIPLINE's WINDOW IS [n, n + len q): so it wants
                 (vals q y).length = len q AT ALL q AND y: PlainOk gives that only where some run
                 says yes: plain_inWin takes it as a premise of its own.
hpart (a later state has a part) is a premise on the letter "more": at the real record it is paid by
Law/FitsAtS.lean: part_of_more.
Not claimed: PlainOk of any real run.

-/
import Johnson.Desc.First.Batch.Law.Gather
import Johnson.Desc.First.Batch.Law.ExpsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens)

variable {T P K : Type}

/-- The terms (n, l[0]), (n + 1, l[1]), .. -/
def numbered : ℕ → List K → List (ℕ × K)
  | _, [] => []
  | n, v :: l => (n, v) :: numbered (n + 1) l

/-- The terms of a run of plain claims. -/
def plainTm (vals : P → Bound K → List K) : ℕ → P → Bound K → List (ℕ × K) :=
  fun n q y => numbered n (vals q y)

theorem numbered_mem : ∀ (l : List K) (n : ℕ) (x : ℕ × K), x ∈ numbered n l →
    n ≤ x.1 ∧ x.1 < n + l.length
  | [], _, _, h => nomatch h
  | v :: l, n, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨Nat.le_refl _, by simp⟩
    · have := numbered_mem l (n + 1) x h
      simp only [List.length_cons]
      omega

/-- The exponents differ from each other. -/
theorem numbered_exps : ∀ (l : List K) (n : ℕ), ((numbered n l).map (·.1)).Nodup
  | [], _ => List.nodup_nil
  | v :: l, n => by
    simp only [numbered, List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, numbered_exps l (n + 1)⟩
    obtain ⟨x, hx, e⟩ := List.mem_map.1 h
    have := (numbered_mem l (n + 1) x hx).1
    omega

/-- They lie in the window of numbers. -/
theorem numbered_inWin (l : List K) (n plan t : ℕ) (x : ℕ × K) (h : x ∈ numbered n l) :
    InWin n l.length plan t 0 x.1 := Or.inl (numbered_mem l n x h)

/-- The discipline's second clause for a run of plain claims, at the window of its own number. -/
theorem plain_inWin (vals : P → Bound K → List K) (len : P → ℕ)
    (hlen : ∀ q y, (vals q y).length = len q) (n plan t : ℕ) (q : P) (y : Bound K) (x : ℕ × K)
    (h : x ∈ plainTm vals n q y) : InWin n (len q) plan t 0 x.1 := by
  rw [← hlen q y]
  exact numbered_inWin _ n plan t x h

variable [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)

/-- The premise on a run of plain claims. -/
def PlainOk (r : Nat → T → Except String (List Claim × T)) (vals : P → Bound K → List K)
    (len : P → ℕ) : Prop :=
  ∀ q front e a c e₁, Fx q e → O.good e → X.get? e = some a → a.F.LS.size = a.F.ns →
    r front e = .ok (c, e₁) →
    ∃ a₁, X.get? e₁ = some a₁ ∧ core a₁.F = core a.F ∧
      treesFrame a₁.F.trees = treesFrame a.F.trees ∧ O.good e₁ ∧ O.more e e₁ ∧
      Fx q e₁ ∧ c.length = len q ∧ (∀ cl ∈ c, cl.eqFirst = none) ∧
      ∀ t b y, laterK X O e₁ t → O.full t → X.get? t = some b →
        c.map (claimValue ρ (worldAt ρ b.L b.F y)) = vals q y

theorem wsumK_plain (t : T) (b : K9.Part) (hb : X.get? t = some b) (y : Bound K) (x : K) :
    ∀ (c : List Claim) (n : ℕ), (∀ cl ∈ c, cl.eqFirst = none) →
      wsumK X ρ t y x n c =
        termsAt K (numbered n (c.map (claimValue ρ (worldAt ρ b.L b.F y)))) x
  | [], _, _ => by simp [wsumK, numbered, termsAt]
  | cl :: l, n, h => by
    have h0 : cl.eqFirst = none := h cl List.mem_cons_self
    rw [wsumK, wsumK_plain t b hb y x l (n + 1) fun c hc => h c (List.mem_cons_of_mem _ hc)]
    simp [wvK, hb, expo, h0, numbered, termsAt]

/-- **A run of plain claims pays RunOk.** hpart: a later state has a part (the letter "more" is to
give it). -/
theorem runOk_of_plain (r : Nat → T → Except String (List Claim × T))
    (vals : P → Bound K → List K) (len : P → ℕ)
    (hpart : ∀ e t a, X.get? e = some a → O.more e t → ∃ b, X.get? t = some b)
    (h : PlainOk ρ X O Fx r vals len) : RunOk ρ X O Fx r (plainTm vals) len := by
  intro q front e a c e₁ hf hg ha hs hr
  obtain ⟨a₁, ha₁, k, w, g1, m1, f1, l1, hp, hv⟩ := h q front e a c e₁ hf hg ha hs hr
  refine ⟨a₁, ha₁, k, w, g1, m1, f1, l1, fun _ _ _ _ _ _ _ t y ht hfu => ?_⟩
  obtain ⟨b, hb⟩ := hpart e₁ t a₁ ha₁ ht.2.1
  rw [wsumK_plain ρ X t b hb y _ c _ hp, hv t b y ht hfu hb]
  rfl

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.numbered_exps
#print axioms VerifiableInference.Desc.K9L.wsumK_plain
#print axioms VerifiableInference.Desc.K9L.runOk_of_plain
