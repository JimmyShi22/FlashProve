-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeftRet.lean: left and leftKey (Att/LeftP.lean) return wherever something
lies under the end values' slots that they read, in a
ledger that is Sized.

Main names:
  `foldlM_some`: a fold returns where each of its steps does.
  `shown_of_put`: what lies under a slot is shown.
  `left_ret`, `leftKey_ret`: the two returns.
  `ends_of_sumAt`: under a sumcheck's end slots something lies, in the ledger from which it is seen
    (SumAt, Att/K5SaidAll.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5LeftAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers
open OnBytes.Tie.Pv.Att (PscH)
open VerifiableInference.Desc.Part

/-- A fold returns where each of its steps does. -/
theorem foldlM_some {α β : Type} (f : β → α → Option β) : ∀ (l : List α), (∀ a ∈ l, ∀ b, ∃ b', f b a = some b') →
    ∀ b, ∃ b', l.foldlM f b = some b'
  | [], _, b => ⟨b, rfl⟩
  | a :: l, h, b => by
    obtain ⟨b1, h1⟩ := h a List.mem_cons_self b
    obtain ⟨b2, h2⟩ := foldlM_some f l (fun x hx => h x (List.mem_cons_of_mem _ hx)) b1
    exact ⟨b2, by rw [List.foldlM_cons, h1]; exact h2⟩

/-- What lies under a slot is shown. -/
theorem shown_of_put {G : Fork} (hz : Sized G) {j : ℕ} {y f : E} (h : Put G j y f) : G.shown j = some y := by
  have hj : j < G.ns := by
    rw [← hz.got]
    rcases Nat.lt_or_ge j G.gotF.size with h' | h'
    · exact h'
    · have e : G.gotF.getD j false = false := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h']
        rfl
      have h1 := h.1
      rw [e] at h1
      cases h1
  unfold Fork.shown
  rw [h.1, h.2.1]
  simp [hj]

/-- left returns. -/
theorem left_ret {G : Fork} (hz : Sized G) (hh : MaskedSum.Heard) (W : Array E) {n : ℕ} (hn : 2 * W.size ≤ n)
    (he : ∀ i, i < n → ∃ y f, Put G (hh.sEnd + i) y f) : ∃ f, left G hh W = some f := by
  unfold left
  obtain ⟨s0, h0⟩ := foldlM_some (fun a b => do
      pure (addE a (mulE (mulE (W.getD b zeroE) (← G.shown (hh.sEnd + 2 * b))) (← G.shown (hh.sEnd + (2 * b + 1))))))
    (List.range W.size) (fun b hb a => by
      have hb' := List.mem_range.1 hb
      obtain ⟨y1, _, p1⟩ := he (2 * b) (by omega)
      obtain ⟨y2, _, p2⟩ := he (2 * b + 1) (by omega)
      exact ⟨_, by beta_reduce; rw [shown_of_put hz p1, shown_of_put hz p2]; rfl⟩) zeroE
  exact ⟨_, by rw [h0]; rfl⟩

/-- leftKey returns. -/
theorem leftKey_ret {G : Fork} (hz : Sized G) (g : Geo) (hh : MaskedSum.Heard) (rho om' : Array E) {n : ℕ}
    (hLam : g.NP ≤ g.Lam * g.HA) (hn : g.Lam + g.NP * g.lt ≤ n)
    (he : ∀ i, i < n → ∃ y f, Put G (hh.sEnd + i) y f) : ∃ f, leftKey g G hh rho om' = some f := by
  unfold leftKey
  obtain ⟨s0, h0⟩ := foldlM_some (fun a b => do
      let kc ← G.shown (hh.sEnd + b / g.HA)
      let t ← (List.range g.lt).foldlM (fun t k => do
        let y := ((chal hh).extract 0 g.lt).getD (g.lt - 1 - k) zeroE
        let v ← G.shown (hh.sEnd + (g.Lam + b * g.lt + k))
        pure (mulE t (addE (mulE v (subE (addE y y) oneE)) (subE oneE y)))) (mulE (om'.getD b zeroE) kc)
      pure (addE a t))
    (List.range g.NP) (fun b hb a => by
      have hb' := List.mem_range.1 hb
      have hq : b / g.HA < g.Lam := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have hbl : (b + 1) * g.lt ≤ g.NP * g.lt := Nat.mul_le_mul_right _ hb'
      rw [Nat.add_mul, Nat.one_mul] at hbl
      obtain ⟨y1, _, p1⟩ := he (b / g.HA) (by omega)
      obtain ⟨t, ht⟩ := foldlM_some (fun t k => do
          let y := ((chal hh).extract 0 g.lt).getD (g.lt - 1 - k) zeroE
          let v ← G.shown (hh.sEnd + (g.Lam + b * g.lt + k))
          pure (mulE t (addE (mulE v (subE (addE y y) oneE)) (subE oneE y))))
        (List.range g.lt) (fun k hk t => by
          have hk' := List.mem_range.1 hk
          obtain ⟨y2, _, p2⟩ := he (g.Lam + b * g.lt + k) (by omega)
          exact ⟨_, by beta_reduce; rw [shown_of_put hz p2]; rfl⟩) (mulE (om'.getD b zeroE) y1)
      exact ⟨_, by beta_reduce; rw [shown_of_put hz p1]; simp only [Option.bind_eq_bind, Option.bind_some] at ht ⊢; rw [ht]; rfl⟩) zeroE
  exact ⟨_, by simp only [Option.bind_eq_bind] at h0 ⊢; rw [h0]; rfl⟩

/-- Under a sumcheck's end slots something lies, in the ledger from which it is seen. -/
theorem ends_of_sumAt {C : Aff} {vs : List MaskedSum.Var} {e : MaskedSum.Ends} {pre : List E} {H : PscH}
    {hh : MaskedSum.Heard} {G : Fork} (h : SumAt C (.sum vs e) pre H hh G) :
    ∀ i, i < e.n → ∃ y f, Put G (hh.sEnd + i) y f := by
  obtain ⟨vs', e', _, G0, _, e1, sd, st⟩ := h
  obtain ⟨rfl, rfl⟩ : vs = vs' ∧ e = e' := by
    cases e1
    exact ⟨rfl, rfl⟩
  exact fun i hi => ⟨_, _, st _ _ _ (sd.ends i hi)⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.left_ret
#print axioms VerifiableInference.Desc.First.Att.P.leftKey_ret
