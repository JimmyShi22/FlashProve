-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/HearSkel.lean: A PART OF THE LAW "behind K4's hearing its two runs of claims
return" (Johnson/Road/K4/Total/Returns.lean): HearSkel, to the letter: two returns of the hearing at
one plan (the tokens may differ), from lookups of one shape, have one skeleton. Statements and
proofs.

Why it holds: each of the skeleton's clauses is, at a return of the hearing, a function of the plan
(P, hp, g) and of the lookup's shape.
  the environment's layout is P.y; its tables' places are what layTables returns on the plan's
    matrices and tableAsks P.y P.rd g; its number of columns is that of the plan's tree number
    hp.tl.ix.U[2] (hear_public);
  the second token sumcheck's record is there (hearGated_tape);
  the three layers' points have P.rd.muV, P.rd.muH, P.rd.muH2 elements: a layer's point begins as an
    array of mu zeros, and each round sets one place (levelIn_heard, levelR_size);
  the lookup's record is kept as it came (hearNorms_calls, hearTerms_keeps).

  `level_size`: a layer's point has as many elements as the layer has variables.
  `hear_sizes`: at one return: the five clauses beside the environment, in the plan's numbers.
  `hear_env`: at two returns: the environments have one skeleton.
  `hear_skel_two`: the skeleton is one at two public records that share the layout, the record of
    reads and the list of matrices: THE TOKENS MAY DIFFER.
  `hear_skel : HearSkel`: the part: the same, in the sentence's binders.
No new argument: hear_public, hear_calls, hearNorms_calls, hearTerms_keeps
(OnBytes/Desc/First/K4), hearGated_tape, levelR_size (Johnson/Road/K4), levelIn_heard
(OnBytes/Desc/First/P1/Heard.lean).
**Limits.** hear_skel has six premises, as the sentence has them: the two returns, AT ONE hp AND g;
three equations on the two public records (layout, record of reads, list of matrices), which hold by
rfl where the records differ in the tokens alone (K4's block lays the tokens in off the state, so
two requests have two records); and that the two lookups have one shape: the payer of this last is
whoever holds the lookup's promise at both transcripts: nobody here. It does not say that the
hearing returns, nor that a listing does. Nothing on soundness. K04_law, the law of K4's block
itself, IS NOT PROVED. Met through Lean at no member; by a run at one honest proof of each of two
sizes both runs of claims return at all 2 and 12 layers' places: that run is the member of the law
that this serves.


-/
import Johnson.Road.K4.Total.Returns
import Johnson.Road.K4.GatedTape
import Johnson.Road.K4.LevelPoint
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.HearPublic
import OnBytes.Desc.First.K4.NormsCalls
import OnBytes.Desc.First.P1.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard Env)
open OnBytes.Desc.First.P1 (levelIn_heard)
open OnBytes.Road.K4 (levelR_size)

/-- A layer's point has as many elements as the layer has variables. -/
theorem level_size {mu : ℕ} {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork} {t u : Tape}
    {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) : L.r.size = mu := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hr, _⟩ := levelIn_heard h
  rw [hr, levelR_size, Array.size_replicate]

section Hear

variable {P P₀ : Pub} {hp : HPlan2} {g : ℕ}

/-- At one return of the hearing: the five clauses beside the environment. -/
theorem hear_sizes {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
    (h : hear engFl P hp g fo F t = some (o, G, u)) :
    o.H.tT.isSome = true ∧ o.H.wpl.r.size = P.rd.muV ∧ o.hd.r.size = P.rd.muH ∧
      o.hd2.map (·.r.size) = some P.rd.muH2 ∧ o.H.fo = fo := by
  obtain ⟨_, H1, G1, u1, G2, u2, n1, n2, G3, u3, _, hd2, G4, u4, n4, e2⟩ := hear_calls h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rhoI, _, hw, _, _,
    _, hfo⟩ := hearNorms_calls n1
  obtain ⟨kfo, _, _, _, _, _, _, kw, _⟩ := hearTerms_keeps n2
  obtain ⟨tT, G', hT, l1, _, l2⟩ := hearGated_tape n4
  refine ⟨by rw [hT]; rfl, by rw [kw]; exact level_size hw, level_size l1, ?_, by rw [kfo, hfo]⟩
  rw [e2]
  show some hd2.r.size = some P.rd.muH2
  rw [level_size l2]

/-- At two returns of the hearing, at two public records of one layout, one record of reads and one
list of matrices: the environments have one skeleton. -/
theorem hear_env {fo fo₀ : Forest.Heard} {F G F₀ G₀ : Fork} {t u t₀ u₀ : Tape} {o o₀ : Own}
    (hy : P.y = P₀.y) (hrd : P.rd = P₀.rd) (htl : P.tails = P₀.tails)
    (h : hear engFl P hp g fo F t = some (o, G, u))
    (h₀ : hear engFl P₀ hp g fo₀ F₀ t₀ = some (o₀, G₀, u₀)) : EnvSkel o.v o₀.v := by
  obtain ⟨_, _, i, tab, laid, nU3, _, _, _, _, e1, _, e3, _, ev, _⟩ := hear_public h
  obtain ⟨_, _, i', tab', laid', nU3', _, _, _, _, e1', _, e3', _, ev', _⟩ := hear_public h₀
  rw [hy, hrd, htl] at e3
  have hi : i = i' := Option.some.inj (e1.symm.trans e1')
  have ht : tab = tab' := congrArg Prod.fst (Option.some.inj (e3.symm.trans e3'))
  subst hi
  subst ht
  exact ⟨by rw [ev, ev']; exact hy, by rw [ev, ev'], by rw [ev, ev']⟩

/-- **Two returns of the hearing have one skeleton**, at two public records of one layout, one
record of reads and one list of matrices (the tokens may differ), from lookups of one shape. -/
theorem hear_skel_two {fo fo₀ : Forest.Heard} {F G F₀ G₀ : Fork} {t u t₀ u₀ : Tape} {o o₀ : Own}
    (hy : P.y = P₀.y) (hrd : P.rd = P₀.rd) (htl : P.tails = P₀.tails)
    (hs : fo.shape = fo₀.shape) (h : hear engFl P hp g fo F t = some (o, G, u))
    (h₀ : hear engFl P₀ hp g fo₀ F₀ t₀ = some (o₀, G₀, u₀)) : Skel o o₀ := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hear_sizes h
  obtain ⟨b1, b2, b3, b4, b5⟩ := hear_sizes h₀
  rw [hrd] at a2 a3 a4
  exact ⟨hear_env hy hrd htl h h₀, a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm,
    a4.trans b4.symm, by rw [a5, b5]; exact hs⟩

end Hear

/-- **The part HearSkel.** -/
theorem hear_skel : HearSkel :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hy hrd htl hs h h₀ => hear_skel_two hy hrd htl hs h h₀

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.level_size
#print axioms OnBytes.Desc.First.K4.Total.hear_sizes
#print axioms OnBytes.Desc.First.K4.Total.hear_env
#print axioms OnBytes.Desc.First.K4.Total.hear_skel_two
#print axioms OnBytes.Desc.First.K4.Total.hear_skel
