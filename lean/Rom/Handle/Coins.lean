-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Handle/Coins.lean: "ALL COINS FIRST" IS "EACH COIN WHEN IT IS NEEDED", under any rule for
answering queries (Rom/Handle/Defs.lean). Two definitions and their calculus. General in the family
of oracles.

General lemmas. This file states no goal of the release.

An honest prover is often written as a program that is handed all its coins at the start: salts for
all leaves, a first salt, and so on. In a proof it is compared with a program that draws each of
them at the place where it is used. The two have the same run, whatever answers the queries. This
file gives a way to show that, node by node, without a third text of the program.

  CoinsFirst μ prog t   Draw u from μ, then run prog u: under every rule and from every state that
                        is the run of t.
  Resamples μ ν upd     ONE COORDINATE OF μ IS DISTRIBUTED AS ν AND INDEPENDENT OF THE REST: draw u
                        from μ and x from ν, and lay x into u (upd x u): the result is distributed
                        as μ again.

The calculus.
  CoinsFirst.const      a program that does not read its coins.
  CoinsFirst.query, .sample, .bind_left   a query at a point that does not hang on the coins, a draw
                        of the program's own, a first part that does not read the coins: go on with
                        what follows.
  CoinsFirst.draw       THE STEP: t draws x from ν. It is enough to go on with the program in which
                        x is laid into the coins. Nothing is asked on how often, or where, the
                        program reads that coordinate: it reads x at each of these places, a salt
                        that is hashed first and shown later too.
  CoinsFirst.bind_prod  two parts with coins of their own.
  CoinsFirst.of_window  coins of which the program reads a part alone, and the law is known of that
                        part alone.
  CoinsFirst.of_enum    the coins drawn by one draw from a list.

  Resamples.self        the whole of ν.
  Resamples.fst, .snd   a coordinate of a component of an independent pair.
  Resamples.pi          a coordinate of one entry of a uniform tuple.
  Resamples.map_equiv, .congr   another way of writing the coins.
  Resamples.inst, CoinsFirst.inst   the uniform law on a finite type is one law, however the type's
                        members are listed.

At the file's end a small example: two salts, both handed over at the start, against two draws; the
first salt is read twice.

-/
import Rom.Handle.Laws

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {U U' V Y α β : Type}

/-- **One coordinate of μ is distributed as ν and independent of the rest**: to lay a fresh x from ν
into u from μ gives μ again. -/
def Resamples (μ : PMF U) (ν : PMF Y) (upd : Y → U → U) : Prop :=
  (ν.bind fun x => μ.map (upd x)) = μ

/-- **All coins first**: to draw u from μ and then run prog u is to run t, under every rule for
answering queries and from every state. -/
def CoinsFirst (μ : PMF U) (prog : U → OComp S α) (t : OComp S α) : Prop :=
  ∀ (σ : Type) (h : Handler S σ) (s : σ), (μ.bind fun u => (prog u).interp h s) = t.interp h s

/-! ## One coordinate -/

namespace Resamples
variable {μ : PMF U} {ν : PMF Y} {upd : Y → U → U}

/-- How it is used: in front of any continuation. -/
theorem bind_eq (h : Resamples μ ν upd) {γ : Type} (F : U → PMF γ) :
    μ.bind F = ν.bind fun x => μ.bind fun u => F (upd x u) :=
  calc μ.bind F = (ν.bind fun x => μ.map (upd x)).bind F := by
        rw [show (ν.bind fun x => μ.map (upd x)) = μ from h]
    _ = ν.bind fun x => μ.bind fun u => F (upd x u) := by
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

theorem congr {upd' : Y → U → U} (h : Resamples μ ν upd) (e : ∀ x u, upd x u = upd' x u) :
    Resamples μ ν upd' := by
  have : upd = upd' := funext fun x => funext fun u => e x u
  rwa [← this]

/-- The whole of ν. -/
theorem self (ν : PMF Y) : Resamples ν ν (fun x _ => x) := by
  have e : ∀ x : Y, (ν.map fun _ => x) = PMF.pure x := fun x => PMF.map_const ν x
  show (ν.bind fun x => ν.map fun _ => x) = ν
  simp only [e, PMF.bind_pure]

/-- A coordinate of the first component of an independent pair. -/
theorem fst (h : Resamples μ ν upd) (μ₂ : PMF V) :
    Resamples (prod μ μ₂) ν (fun x u => (upd x u.1, u.2)) := by
  refine Eq.trans ?_ (h.bind_eq fun a => μ₂.map fun b => (a, b)).symm
  simp only [prod, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- A coordinate of the second component of an independent pair. -/
theorem snd (h : Resamples μ ν upd) (μ₁ : PMF V) :
    Resamples (prod μ₁ μ) ν (fun x u => (u.1, upd x u.2)) := by
  show (ν.bind fun x => (prod μ₁ μ).map fun u => (u.1, upd x u.2)) = prod μ₁ μ
  simp only [prod, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun a => ?_)
  have e := congrArg (PMF.map fun b => (a, b)) (show (ν.bind fun x => μ.map (upd x)) = μ from h)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at e
  exact e

/-- The coins written in another way. -/
theorem map_equiv (h : Resamples μ ν upd) (e : U ≃ U') :
    Resamples (μ.map e) ν (fun x u' => e (upd x (e.symm u'))) := by
  have e' := congrArg (PMF.map e) (show (ν.bind fun x => μ.map (upd x)) = μ from h)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at e'
  show (ν.bind fun x => (μ.map e).map fun u' => e (upd x (e.symm u'))) = μ.map e
  simp only [PMF.map_comp, Function.comp_def, Equiv.symm_apply_apply]
  exact e'

/-- A coordinate of one entry of a uniform tuple. -/
theorem pi {K : Type} [Fintype K] [DecidableEq K] {C : K → Type} [∀ k, Fintype (C k)]
    [∀ k, Nonempty (C k)] (k₀ : K) {upd : Y → C k₀ → C k₀} (h : Resamples (unif (C k₀)) ν upd) :
    Resamples (unif (∀ k, C k)) ν (fun x u => Function.update u k₀ (upd x (u k₀))) := by
  have h1 := h.fst (unif (∀ j : {j // j ≠ k₀}, C j))
  rw [← unif_prod] at h1
  have h2 := h1.map_equiv (Equiv.piSplitAt k₀ C).symm
  rw [map_unif_equiv] at h2
  refine h2.congr fun x u => funext fun j => ?_
  show (Equiv.piSplitAt k₀ C).symm (upd x (u k₀), fun j => u j) j = _
  rw [Equiv.piSplitAt_symm_apply]
  by_cases hj : j = k₀
  · subst hj
    rw [dif_pos rfl, Function.update_self]
  · rw [dif_neg hj, Function.update_of_ne hj]

/-- The uniform law does not hang on how the type's members are listed. (Lean may find two lists of
the members of one concrete type, which are equal but costly to compare.) -/
theorem inst {i₁ i₂ : Fintype U} [Nonempty U] {upd : Y → U → U}
    (h : Resamples (@unif U i₁ _) ν upd) : Resamples (@unif U i₂ _) ν upd :=
  Subsingleton.elim i₁ i₂ ▸ h

end Resamples

/-! ## All coins first -/

namespace CoinsFirst
variable {μ : PMF U}

/-- A program that does not read its coins. -/
theorem const (μ : PMF U) (t : OComp S α) : CoinsFirst μ (fun _ => t) t :=
  fun _ _ _ => PMF.bind_const _ _

/-- A query at a point that does not hang on the coins. -/
theorem query {o : S.ι} {q : S.Dom o} {k : U → S.Rng o → OComp S α} {k' : S.Rng o → OComp S α}
    (hk : ∀ r, CoinsFirst μ (fun u => k u r) (k' r)) :
    CoinsFirst μ (fun u => .query o q (k u)) (.query o q k') := by
  intro σ h s
  simp only [OComp.interp_query]
  rw [PMF.bind_comm]
  exact congrArg _ (funext fun p => hk p.1 σ h p.2)

/-- A draw of the program's own. -/
theorem sample {n : ℕ} {k : U → Fin (n + 1) → OComp S α} {k' : Fin (n + 1) → OComp S α}
    (hk : ∀ r, CoinsFirst μ (fun u => k u r) (k' r)) :
    CoinsFirst μ (fun u => .sample n (k u)) (.sample n k') := by
  intro σ h s
  simp only [OComp.interp_sample]
  rw [PMF.bind_comm]
  exact congrArg _ (funext fun r => hk r σ h s)

/-- A first part that does not read the coins. -/
theorem bind_left (c : OComp S β) {g : U → β → OComp S α} {g' : β → OComp S α}
    (hg : ∀ b, CoinsFirst μ (fun u => g u b) (g' b)) :
    CoinsFirst μ (fun u => c.bind (g u)) (c.bind g') := by
  intro σ h s
  simp only [OComp.interp_bind]
  rw [PMF.bind_comm]
  exact congrArg _ (funext fun p => hg p.1 σ h p.2)

/-- **The step.** t draws x, distributed as ν, by one draw from a list e. If one coordinate of the
coins is distributed as ν and independent of the rest, it is enough to go on with the program in
which x is laid into the coins. -/
theorem draw {ν : PMF Y} {upd : Y → U → U} {prog : U → OComp S α} {n : ℕ} (e : Fin (n + 1) → Y)
    (hν : (unif (Fin (n + 1))).map e = ν) (hμ : Resamples μ ν upd) {k' : Y → OComp S α}
    (hk : ∀ x, CoinsFirst μ (fun u => prog (upd x u)) (k' x)) :
    CoinsFirst μ prog (.sample n fun r => k' (e r)) := by
  intro σ h s
  rw [hμ.bind_eq, ← hν, PMF.bind_map, OComp.interp_sample]
  exact congrArg _ (funext fun r => hk (e r) σ h s)

/-- Two parts, each with coins of its own. -/
theorem bind_prod {μ₂ : PMF V} {c : U → OComp S β} {c' : OComp S β} {g : V → β → OComp S α}
    {g' : β → OComp S α} (hc : CoinsFirst μ c c')
    (hg : ∀ b, CoinsFirst μ₂ (fun v => g v b) (g' b)) :
    CoinsFirst (prod μ μ₂) (fun u => (c u.1).bind (g u.2)) (c'.bind g') := by
  intro σ h s
  rw [← bind_bind_eq_prod_bind μ μ₂ fun a b => ((c a).bind (g b)).interp h s]
  simp only [OComp.interp_bind]
  rw [← hc σ h s, PMF.bind_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.bind_comm]
  exact congrArg _ (funext fun p => hg p.1 σ h p.2)

/-- The coins written in another way. -/
theorem map {f : U' → U} {μ' : PMF U'} {prog : U → OComp S α} {t : OComp S α}
    (h : CoinsFirst μ' (fun u => prog (f u)) t) : CoinsFirst (μ'.map f) prog t := by
  intro σ hd s
  rw [PMF.bind_map]
  exact h σ hd s

/-- The program reads a part w u of its coins alone, and that part is distributed as the part w' u'
of other coins. -/
theorem of_window {μ' : PMF U'} (w : U → V) (w' : U' → V) (hw : μ.map w = μ'.map w')
    {prog : V → OComp S α} {t : OComp S α} (h : CoinsFirst μ' (fun u => prog (w' u)) t) :
    CoinsFirst μ (fun u => prog (w u)) t := by
  intro σ hd s
  have e := (map h : CoinsFirst (μ'.map w') prog t) σ hd s
  rw [← hw, PMF.bind_map] at e
  exact e

/-- The uniform law does not hang on how the type's members are listed. -/
theorem inst {i₁ i₂ : Fintype U} [Nonempty U] {prog : U → OComp S α} {t : OComp S α}
    (h : CoinsFirst (@unif U i₁ _) prog t) : CoinsFirst (@unif U i₂ _) prog t :=
  Subsingleton.elim i₁ i₂ ▸ h

/-- The coins drawn by one draw from a list, as a program. -/
theorem of_enum {n : ℕ} {e : Fin (n + 1) → U} {prog : U → OComp S α} {t : OComp S α}
    (h : CoinsFirst ((unif (Fin (n + 1))).map e) prog t) (σ : Type) (hd : Handler S σ) (s : σ) :
    (OComp.sample n fun a => prog (e a)).interp hd s = t.interp hd s := by
  rw [← h σ hd s, PMF.bind_map]
  rfl

end CoinsFirst

/-! ## A small example -/

/-- Two salts of type Y, handed over at the start: each is hashed, and the first is the output. -/
def toyFirst (S : OSpec) (o : S.ι) (pt : Y → S.Dom o) (u : Fin 2 → Y) : OComp S Y :=
  .query o (pt (u 0)) fun _ => .query o (pt (u 1)) fun _ => .pure (u 0)

/-- The same with each salt drawn where it is first used, from a list e. -/
def toyLate (S : OSpec) (o : S.ι) (pt : Y → S.Dom o) {n : ℕ} (e : Fin (n + 1) → Y) : OComp S Y :=
  .sample n fun a => .query o (pt (e a)) fun _ =>
    .sample n fun b => .query o (pt (e b)) fun _ => .pure (e a)

theorem toy_coinsFirst [Fintype Y] [Nonempty Y] (S : OSpec) (o : S.ι) (pt : Y → S.Dom o) {n : ℕ}
    (e : Fin (n + 1) → Y) (he : (unif (Fin (n + 1))).map e = unif Y) :
    CoinsFirst (unif (Fin 2 → Y)) (toyFirst S o pt) (toyLate S o pt e) := by
  refine CoinsFirst.draw e he ((Resamples.self (unif Y)).pi (C := fun _ : Fin 2 => Y) 0)
    (k' := fun x => .query o (pt x) fun _ =>
      .sample n fun b => .query o (pt (e b)) fun _ => .pure x) fun x => ?_
  simp only [toyFirst, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  refine CoinsFirst.query fun _ => ?_
  refine CoinsFirst.draw e he ((Resamples.self (unif Y)).pi (C := fun _ : Fin 2 => Y) 1)
    (k' := fun y => .query o (pt y) fun _ => .pure x) fun y => ?_
  simp only [Function.update_self]
  exact CoinsFirst.const _ _

end Rom

#print axioms Rom.Resamples.pi
#print axioms Rom.CoinsFirst.draw
#print axioms Rom.CoinsFirst.of_window
#print axioms Rom.toy_coinsFirst
