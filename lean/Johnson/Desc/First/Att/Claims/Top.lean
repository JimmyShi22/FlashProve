-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Top.lean: kind K5, the claims are the written lists: the three named
runs of Johnson/Desc/First/Att/RunsP.lean (firstRun, keysRun, secondRun) at `inOld h`. Each
statement is a definition of type Prop in the namespace Spec; each theorem has that name as its
type.

Main names:
  `Spec.FirstIs`: where "first" returns, its forms are the written lists of claims 3, 4 and 5, and
    its key forms the written ones, begun at as many empty key forms as the shape has calls.
  `Spec.FirstIsAt`: the same with Fo.attJoinsT A h, under the premise A.NC = h.S.calls.size. The
    planner sets NC so (OnBytes/Model/AttentionPlan.lean); no theorem on the planner is used.
  `Spec.SecondIs`: where "second" returns: the written lists of claims 6, 7 and 8.
  `Spec.KeysIff`: "keys" returns kf if and only if kf is the joins' key forms and its four tests on
    public numbers pass: every key form is set just once; a call that is no softmax-table call has
    the padding key 0; the count of the padding's places returns; it is the lookup's.
  `Spec.WholeIs`: the three together fill the middle of Fo.attT (same premise on NC).
Limits: a run that returns another list meets none of FirstIs, SecondIs, KeysIff. A run that never
returns meets FirstIs, SecondIs and WholeIs idly: they are one half of the law; the other half,
where the runs return, is Johnson/Desc/First/Att/Claims/Returns.lean. KeysIff is met by neither.
Used of OnBytes: plain records and definitions alone; no routine in a context and no theorem on a
run: the records Attention.Heard, Plan, Joins; the written lists and values Fo.claim3T … claim8T,
claim3V, claim4V, claim5V, attJoinsT, attT, joinForm, planeFormsT, u3Form.
Not claimed: that a claim holds; what a form is worth; that `inOld h` is what a seat reads
(Johnson/Desc/First/Att/Claims/Premises.lean [not in this library]).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Claim58

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf)

variable {K : ℕ}

/-- From the rule to the gathered run. -/
theorem gather_is {α : Type} {r : P.Runs.W α} {v : α} {l : List Aff} (h : GV K r v l) {a : α}
    {l' : List Aff} (hg : P.Runs.gather K r = some (a, l')) : a = v ∧ l' = l := by
  unfold P.Runs.gather at hg
  cases hr : r K #[] with
  | none =>
    have e : (r.run K).run #[] = none := hr
    rw [e] at hg
    cases hg
  | some x =>
    have e : (r.run K).run #[] = some x := hr
    rw [e] at hg
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨h1, h2⟩ := h #[] x.1 x.2 hr
    refine ⟨hg.1 ▸ h1, ?_⟩
    rw [← hg.2, h2]
    simp

/-- The key forms behind claim 5, begun at as many empty key forms as the shape has calls. -/
def joinsT (h : Attention.Heard) : Joins :=
  Fo.claim5V h (Fo.claim4V h (Fo.claim3V h (Joins.empty h.S.calls.size)))

theorem joinsT_att (A : Plan) (h : Attention.Heard) (hN : A.NC = h.S.calls.size) :
    joinsT h = Fo.attJoinsT A h := by
  unfold joinsT Fo.attJoinsT
  rw [hN]

namespace Spec

def FirstIs : Prop :=
  ∀ (h : Attention.Heard) (K : ℕ) (l : List Aff) (j : P.Runs.JoinsP),
    P.Runs.firstRun (inOld h) K = some (l, j) →
      l = Fo.claim3T h K ++ (Fo.claim4T h K ++ Fo.claim5T h K) ∧ j = jP (joinsT h)

def FirstIsAt : Prop :=
  ∀ (A : Plan) (h : Attention.Heard) (K : ℕ) (l : List Aff) (j : P.Runs.JoinsP),
    A.NC = h.S.calls.size → P.Runs.firstRun (inOld h) K = some (l, j) →
      l = Fo.claim3T h K ++ (Fo.claim4T h K ++ Fo.claim5T h K) ∧ j = jP (Fo.attJoinsT A h)

def SecondIs : Prop :=
  ∀ (h : Attention.Heard) (K : ℕ) (l : List Aff),
    P.Runs.secondRun (inOld h) K = some l →
      l = Fo.claim6T h K ++ (Fo.claim7T h K ++ Fo.claim8T h K)

def KeysIff : Prop :=
  ∀ (i : P.Runs.In) (k3 : P.Runs.PadIn) (j : P.Runs.JoinsP) (kf : Array Aff),
    P.Runs.keysRun i k3 j = some kf ↔
      (kf = j.kf ∧ j.joined.all (· == 1) = true ∧
        (i.g.calls.all fun c => c.tab == .kfd || c.padKey == 0) = true ∧
        ∃ laid, P.Runs.laidPadding i.g k3 = some laid ∧ (laid == k3.pub) = true)

def WholeIs : Prop :=
  ∀ (A : Plan) (h : Attention.Heard) (K : ℕ) (k3 : P.Runs.PadIn) (l₁ l₂ : List Aff)
    (j : P.Runs.JoinsP) (kf : Array Aff),
    A.NC = h.S.calls.size → P.Runs.firstRun (inOld h) K = some (l₁, j) →
    P.Runs.keysRun (inOld h) k3 j = some kf → P.Runs.secondRun (inOld h) K = some l₂ →
      Fo.attT A h K = h.g.rows.toList ++ (l₁ ++ ([Fo.joinForm h.g kf] ++ (l₂ ++
        (Fo.planeFormsT h.g h.S.cf.lmb
          (fun e col => Fo.u3Form h.iU3 K ((if e == 0 then h.t.tBit0 else h.t.tBit1) + col))
          (fun col => Fo.u3Form h.iU3 K (h.t.tPin + col))).toList)))

end Spec

theorem gv_first (h : Attention.Heard) :
    GV K (do
      let j ← P.Runs.claim3 (inOld h) (P.Runs.JoinsP.empty (inOld h).g.calls.size)
      let j ← P.Runs.claim4 (inOld h) j
      P.Runs.claim5 (inOld h) j) (jP (joinsT h))
      (Fo.claim3T h K ++ (Fo.claim4T h K ++ Fo.claim5T h K)) := by
  have e : (inOld h).g.calls.size = h.S.calls.size := by
    show (h.S.calls.map _).size = _
    rw [Array.size_map]
  rw [e, jP_empty]
  exact GV.bind (gv_claim3 h _) (GV.bind (gv_claim4 h _) (gv_claim5 h _))

theorem first_is : Spec.FirstIs := by
  intro h K l j hr
  unfold P.Runs.firstRun at hr
  rw [Option.map_eq_some_iff] at hr
  obtain ⟨⟨a, l'⟩, hg, he⟩ := hr
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := gather_is (gv_first h) hg
  exact ⟨he.1 ▸ h2, he.2 ▸ h1⟩

theorem first_is_at : Spec.FirstIsAt := by
  intro A h K l j hN hr
  rw [← joinsT_att A h hN]
  exact first_is h K l j hr

theorem second_is : Spec.SecondIs := by
  intro h K l hr
  unfold P.Runs.secondRun at hr
  rw [Option.map_eq_some_iff] at hr
  obtain ⟨⟨a, l'⟩, hg, he⟩ := hr
  have := gather_is (GV.bind (gv_claim6 h) (GV.bind (gv_claim7 h) (gv_claim8 h))) hg
  exact he ▸ this.2

theorem keys_iff : Spec.KeysIff := by
  intro i k3 j kf
  unfold P.Runs.keysRun P.Runs.gather P.Runs.allJoined P.Runs.paddingLaid P.Runs.mustAs P.Runs.refuse
  cases h1 : j.joined.all (· == 1) with
  | false => simp
  | true =>
    cases h2 : (i.g.calls.all fun c => c.tab == .kfd || c.padKey == 0) with
    | false => simp
    | true =>
      cases h3 : P.Runs.laidPadding i.g k3 with
      | none => simp
      | some laid =>
        cases h4 : laid == k3.pub with
        | false =>
          have h4' : laid ≠ k3.pub := by simpa using h4
          simp [h4']
        | true =>
          have h4' : laid = k3.pub := by simpa using h4
          simp [h4']
          exact eq_comm

theorem keys_is (i : P.Runs.In) (k3 : P.Runs.PadIn) (j : P.Runs.JoinsP) (kf : Array Aff)
    (h : P.Runs.keysRun i k3 j = some kf) : kf = j.kf := ((keys_iff i k3 j kf).1 h).1

theorem whole_is : Spec.WholeIs := by
  intro A h K k3 l₁ l₂ j kf hN h1 hk h2
  obtain ⟨e1, ej⟩ := first_is_at A h K l₁ j hN h1
  have ek := keys_is _ _ _ _ hk
  have e2 := second_is h K l₂ h2
  subst e1 e2 ej ek
  unfold Fo.attT
  simp only [List.append_assoc]
  rfl

end K5Law
