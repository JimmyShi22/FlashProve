-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPeelLeaf.lean.
The byte-level lookup routine at any context on a view: which rounds it takes, what it leaves of
the view, and what it has heard.

Main name:
  `look_leaf`: let Forest.pad calls pub lid Fk c = .ok ((g, F'), c'), from a state whose arrays have
    their sizes and a context on a view with no message open. Let the view's rounds that are left at
    c be rv ++ rest, with as many rounds in rv as the lookup's plan Fo.planF g.shape has. Then the
    run has taken exactly rv (Took c rv c') and leaves rest; the record's shape is made of the calls
    (ShapeOf); the state is left as PadLeft says; and the record holds Fo.endsOf at rv read as plain
    data (HeardIs). This holds for every reading ρ and every lm: lm is no argument of the routine.
    endsOf is taken at the record's shape and at the first free slot before the run.
It is Fo.hcOut2V with the rounds taken named from outside: that theorem says that some rounds of the
plan's sizes are taken, and two splittings of one list at one length are one.
Does not say: that the routine returns; anything on a dry run.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadAll

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

theorem look_leaf {K : Type} [CommRing K] (ρ : Reading K) {calls : Array Call} {pub : Array Nat}
    {lid : ℕ} (lm : ℕ) {Fk F' : Fork} {c c' : Ctx} {g : Forest.Heard} {rv rest : List Fmt.RoundView}
    (h : Forest.pad calls pub lid Fk c = .ok ((g, F'), c')) (hF : Sized Fk) (hc : Clean c)
    (hl : c.ch.left = rv ++ rest) (hn : rv.length = (planF g.shape).length) :
    Took c rv c' ∧ c'.ch.left = rest ∧ ShapeOf calls pub lid g.shape ∧
      PadLeft g.shape Fk F' g ∧ HeardIs ρ g F' (endsOf g.shape lm Fk.next (rv.map (rdRV ρ))) := by
  obtain ⟨h1, h2, rv0, ht, hs, hH⟩ := hcOut2V K ρ calls pub lid lm Fk F' c c' g h hF hc
  have e0 : rv0.length = (planF g.shape).length := by rw [← hs, List.length_map]
  obtain ⟨rfl, e2⟩ := List.append_inj (hl.symm.trans ht.2.2) (hn.trans e0.symm)
  exact ⟨ht, e2.symm, h1, h2, hH⟩

end Fo
