-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Owner.lean: two lemmas on a list of stages
(Honest/Law/Rule/Stages.lean) whose coins are looked up by address and cut by the book's entries
(Honest/Frame.lean: `Ahead`, `cutAll`; Honest/Law/Rule/Weave.lean: `runs`). The coins K, what has
been produced Φ and what is shown V are type parameters; no part, no description and no run of a
protocol occurs here.

  1  `owner_step`   one owner. The owner's coins are what a lens shows of k, and setting them leaves
     what is looked up at every other address as it is. Suppose that, at each fixed value of the
     other coins, the triple (the blocks that `es` cuts from the owner's coins, what the owner's
     stage shows, the blocks that `known` cuts from the owner's coins) has the distribution in which
     the first is drawn afresh. Suppose also that the stages before the owner's do not read its
     coins, and that those after it, and a U, read them through the blocks of `known` alone. Then
     the blocks of `es` are as drawn afresh beside the triple (the blocks of any other owners'
     entries, what the whole list produces, U). This is the hypothesis `hstep` of `runs_afresh`
  2  `lent_afresh_abs`   a spender. Its own coins, which a second lens shows, and the blocks of all
     its entries together are as drawn afresh beside a T that does not read its own coins, given
     `hstep` for every owner, `hE` and `hruns`

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Stages
import Johnson.Desc.ProofFile.Honest.Law.Rule.Weave

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob

section
variable {K Φ V Ω : Type} [Fintype K] [Nonempty K]

/-- **One owner.** -/
theorem owner_step {d : Due} {get : K → Cs d} {put : Cs d → K → K} (hL : Lens.OK get put)
    (look : K → Addr → (d : Due) × Cs d) (o : Addr) (hlook : ∀ k, look k o = ⟨d, get k⟩)
    (hother : ∀ x k b, b ≠ o → look (put x k) b = look k b)
    (pre mid : List (Kit.Stage K Φ V)) (so : Kit.Stage K Φ V) (Z₀ : Φ) (es known : List Ahead)
    (hpre : ∀ s ∈ pre, ∀ c k L, s.shows (put c k) L = s.shows k L)
    (hmid : ∀ s ∈ mid, ∀ k c c' L, cutAll c known = cutAll c' known →
      s.shows (put c k) L = s.shows (put c' k) L)
    (U : K → Ω) (hU : ∀ k c c', cutAll c known = cutAll c' known → U (put c k) = U (put c' k))
    (hfresh : ∀ k, (unif (Cs d)).map (fun c =>
        (cutAll c es, so.shows (put c k) (Kit.real pre k Z₀), cutAll c known)) =
      (unif (CsAll (es.map Ahead.named) × Cs d)).map fun z =>
        (some z.1, so.shows (put z.2 k) (Kit.real pre k Z₀), cutAll z.2 known))
    (rest : List Ahead) (hrest : ∀ e ∈ rest, e.owner ≠ o) :
    (unif K).map (fun k => (cutAll (look k o).2 es,
        (runs (look k) rest, (Kit.real (pre ++ so :: mid) k Z₀, U k)))) =
      (unif (CsAll (es.map Ahead.named) × K)).map fun z =>
        (some z.1, (runs (look z.2) rest, (Kit.real (pre ++ so :: mid) z.2 Z₀, U z.2))) := by
  have e0 : ∀ c k, Kit.real pre (put c k) Z₀ = Kit.real pre k Z₀ := fun c k =>
    Kit.real_congr (put c k) k pre (fun s hs L => hpre s hs c k L) Z₀
  have hf : ∀ k, (unif (Cs d)).map (fun c => (cutAll c es,
        (fun k => so.shows k (Kit.real pre k Z₀)) (put c k), cutAll c known)) =
      (unif (CsAll (es.map Ahead.named) × Cs d)).map fun z => (some z.1,
        (fun k => so.shows k (Kit.real pre k Z₀)) (put z.2 k), cutAll z.2 known) := by
    intro k
    simp only [e0]
    exact hfresh k
  have hfac : ∀ k c c',
      (fun k => so.shows k (Kit.real pre k Z₀)) (put c k) =
        (fun k => so.shows k (Kit.real pre k Z₀)) (put c' k) →
      cutAll c known = cutAll c' known →
      (fun k => (runs (look k) rest, (Kit.real (pre ++ so :: mid) k Z₀, U k))) (put c k) =
        (fun k => (runs (look k) rest, (Kit.real (pre ++ so :: mid) k Z₀, U k))) (put c' k) := by
    intro k c c' hv hη
    have hv' : so.shows (put c k) (Kit.real pre k Z₀) =
        so.shows (put c' k) (Kit.real pre k Z₀) := by
      have h := hv
      simp only [e0] at h
      exact h
    have h1 : runs (look (put c k)) rest = runs (look (put c' k)) rest :=
      runs_congr _ _ rest fun e he => by
        rw [hother c k _ (hrest e he), hother c' k _ (hrest e he)]
    have h2 : Kit.real (pre ++ so :: mid) (put c k) Z₀ =
        Kit.real (pre ++ so :: mid) (put c' k) Z₀ :=
      Kit.real_factor pre mid so (fun c => cutAll c known) Z₀ hpre hmid k c c' hv' hη
    have h3 : U (put c k) = U (put c' k) := hU k c c' hη
    show (runs (look (put c k)) rest, (Kit.real (pre ++ so :: mid) (put c k) Z₀, U (put c k))) =
      (runs (look (put c' k)) rest, (Kit.real (pre ++ so :: mid) (put c' k) Z₀, U (put c' k)))
    rw [h1, h2, h3]
  have h := Kit.afresh_step hL (fun c => cutAll c es) some (fun c => cutAll c known)
    (fun k => so.shows k (Kit.real pre k Z₀))
    (fun k => (runs (look k) rest, (Kit.real (pre ++ so :: mid) k Z₀, U k))) hf hfac
  have e1 : ∀ k, cutAll (look k o).2 es = cutAll (get k) es := fun k => by rw [hlook k]
  simp only [e1]
  exact h

/-- **A spender.** `getA`, `putA`: the lens on its own coins. `E`: the entries by which it spends.
`spent`: for each owner a list of entries. `hE`: of each owner, E holds either no entry or just the
entries `spent o`. `hruns`: the blocks of E are the same, whatever is set in its own coins. -/
theorem lent_afresh_abs {d : Due} {getA : K → Cs d} {putA : Cs d → K → K}
    (hA : Lens.OK getA putA) (look : K → Addr → (d : Due) × Cs d) (E : List Ahead)
    (spent : Addr → List Ahead)
    (hE : ∀ o, (E.filter fun t => t.owner == o) = [] ∨ (E.filter fun t => t.owner == o) = spent o)
    (T : K → Ω) (hT : ∀ c k, T (putA c k) = T k)
    (hruns : ∀ c k, runs (look (putA c k)) E = runs (look k) E)
    (hstep : ∀ (o : Addr) (rest : List Ahead), (∀ e ∈ rest, e.owner ≠ o) →
      (unif K).map (fun k => (cutAll (look k o).2 (spent o), (runs (look k) rest, T k))) =
        (unif (CsAll ((spent o).map Ahead.named) × K)).map fun z =>
          (some z.1, (runs (look z.2) rest, T z.2))) :
    (unif K).map (fun k => ((some (getA k), runs (look k) E), T k)) =
      (unif ((Cs d × CsAll (E.map Ahead.named)) × K)).map fun z =>
        ((some z.1.1, some z.1.2), T z.2) := by
  have h0 := Kit.afresh_lens hA (fun k => (runs (look k) E, T k)) fun c k => by
    show (runs (look (putA c k)) E, T (putA c k)) = (runs (look k) E, T k)
    rw [hruns, hT]
  have h1 : (unif K).map (fun k => (some (getA k), (runs (look k) E, T k))) =
      (unif (Cs d × K)).map fun z => (some z.1, (runs (look z.2) E, T z.2)) :=
    Kit.afresh_map (X := getA) (ι := id) (W := fun k => (runs (look k) E, T k)) h0
      fun t => (some t.1, t.2)
  have h2 := runs_afresh look T spent hstep E.length E (Nat.le_refl _) hE
  exact Kit.afresh_pair (X := fun k => some (getA k)) (Y := fun k => runs (look k) E) (W := T)
    (ι := some) (κ := some) h1 h2

end

end ProofFile.Honest

#print axioms ProofFile.Honest.owner_step
#print axioms ProofFile.Honest.lent_afresh_abs
