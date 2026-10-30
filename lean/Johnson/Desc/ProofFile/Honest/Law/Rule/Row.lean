-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Row.lean: the rule that joins lists of parts, on this
folder's own functions. One description, one book, one prover whose sides are the lists' own, which
meet `Owed` (Honest/Owed.lean). At every input of the relation and at every list of challenges that
the rounds can draw and that is outside the one silent set (`silentAt`, Honest/Rule.lean): over
uniform coins of a run, what the prover of Honest/Walk.lean produces, and its three views, have the
distribution of the session (Honest/Law/Rule/Session.lean: `simActs`, `session`). This is an
equality of two distributions: no coin occurs on both sides; on the right each stretch before which
the verifier has not rejected and which has a simulator draws that simulator's own coins, apart from
all others. It is a rule of composition, and conditional: it adds up lists of parts that meet
`Owed`.

  1  `row_law`   what the honest side's fold produces has the distribution of the kernels' fold
  2  `rule_laid`   at what is produced
  3  `rule_views`   at the three views
  4  `rule_same`   a corollary: two inputs with one x and the same opened stored columns

One hypothesis beside `Owed`: `Sides.owns` (Honest/Law/Rule/Session.lean: an executable test).
`row_law` takes `FileOk` (Honest/Law/Rule/Model.lean) too, which Honest/Law/Rule/FileOkOf.lean
proves from `Owed` where one run goes through. Of `Good` the proof uses `fits`, `exact` and `fresh`;
never `plays` or `acc`. `exact` is asked at fixed carried blocks, which the simulator is not given:
that is what lets simulators with coins of their own stand for parts that carry one block. Of the
book's eleven tests (`Owed.book` asks all) the proof uses five: the first, fourth, fifth, sixth and
tenth. The other six are used by no line, among them the seventh and the eighth (a coin in two
entries that spend it; a spent coin passed on before its spender) and the ninth, which is a lemma
that no file of this folder uses (Honest/Law/Rule/Lent.lean: `ProverCoinCounts.keptIn`). What bars a second
spending in the proof is the clause of `fresh` on what the parts before the spender know.

Limits.
  (1) Two ways to (w₀, rc). The right side is given x whole and st, the stored tables' columns at
      every position that the declared rounds read at these challenges; st is computed from (w₀,
      rc), and every simulator gets all of it; x is a variable, and by the docstring of `Owed`
      (Honest/Owed.lean) it may hold a sample that is computed from the index and rc. The equation
      reads "given x and st". What may be said of x and of st is not proved here. rc is fixed: no
      distribution over the stored tables' pads and encoding randomness occurs in these files.
  (2) It holds also where nothing is masked: with no part at all and one round that opens a stored
      table, `Owed` and `Sides.owns` are met and the view is what the right side is given.
  (3) It can be met trivially: at an empty relation; where no list is such as the rounds can draw;
      where every list is in the silent set; with no lists of parts; after a sub-protocol that
      rejects early, where any simulators pass: both sides are then fixed substitutes and no
      prover's side has said anything. How large the share of lists and coins is at which some
      sub-protocol rejects is not said. Nothing here excludes that: that the description accepts at
      the same (F, Bk, G, H) is for another theorem.
  (4) G, so the simulators, and Rel are bound before "for all w₀ rc x": a relation that fixes the
      index lets simulators be written for it. That F, Bk, G.sims and H.key are computed from a
      public shape alone, and that Rel ranges over all indices of that shape, has to be proved by
      whoever supplies them.
  (5) No running time: `Sim.tell` may be any function, computable or not. At a relation x = h w₀
      with h one-to-one and public, a part that says w₀ has the simulator that says the inverse of h
      at x.
  (6) The set of lists outside the silent set depends on the input, also on what is not public, and
      is not counted here: it is this rule's one error term, and no distribution of the challenges
      occurs in these files. At a list inside the silent set the two sides differ by their
      definitions: no form "at every list" follows. Under the hypotheses `none` has probability 0 on
      both sides: the option has no effect here, and nothing is said of any case in which the prover
      stops or returns an error.
  (7) No form with an error: `Owed.runs` and `Owed.owed` are asked at all coins: one coin at which a
      part is at fault makes `Owed` false outright.
  (8) It does not add up `Good`s: its hypothesis is `Owed`: `Good`, and that the run goes through,
      and `On` at every part that is called and `bud` at every part, of the run's own values, at all
      coins. Nothing here or in the files that this one imports concludes `Owed.owed` at parameters.
      And `On` is the list's own parameter: with `On` the equation of `exact` itself, `Good.exact`
      holds trivially and all content lies in `Owed.owed`: so `Good` without the definition of `On`,
      or without `On` proved of the run, says nothing.
  (9) It ends at the three views of `runC`: not at what a verifier of the one-slot protocol is
      shown.
  (10) One request: the shared chain's coins are drawn afresh with the slot's. Copies of this
      equation are not the distribution of a batch. Every further request opens further stored
      columns under one rc: of several requests together nothing is said.
  (11) What meets it: seven toy examples (Honest/Law/Rule/ToyRule.lean,
      Honest/Law/Rule/ToyMore.lean, Honest/Law/Rule/ToyOne.lean, Honest/Law/Rule/ToyEightAt.lean,
      Honest/Law/Rule/ToyFullAt.lean; none of these is in the sealed library, and its build does not
      check them); more: Honest/Owed.lean. Three toys have a second stop (a part's own stop that
      reads what it is given in private: `Part.hid` returns `none` in the other four; a verifier's
      rejection at a state that depends on a coin is another thing), a stored column that is
      computed from the index, and an x that holds a sample. In the first of the three
      (Honest/Law/Rule/ToyOne.lean) no coin is spent or carried and no condition at an entry asks
      anything. The second (Honest/Law/Rule/ToyEightAt.lean) has these too, with parts and coins in
      the shared chain. The third (Honest/Law/Rule/ToyFullAt.lean) has beside all these a
      sub-protocol that rejects at a state which depends on a coin, and a first stop: that a run
      falls there is checked by evaluation in its author's files, not proved. The equation is false
      at two wrong simulators (Honest/Law/Rule/ToyTurned.lean, Honest/Law/Rule/ToySkew.lean; none of
      these is in the sealed library, and its build does not check them) and, whatever the
      simulators, at three wrong parts (Honest/Law/Rule/ToyBare.lean, Honest/Law/Rule/ToyCarry.lean,
      Honest/Law/Rule/ToyEcho.lean; none of these is in the sealed library, and its build does not
      check them); so these five toy examples do not meet `Owed` (Honest/Law/Rule/ToyNotOwed.lean,
      Honest/Law/Rule/ToyNotOwedAt.lean, Honest/Law/Rule/ToyEcho.lean; none of these is in the
      sealed library, and its build does not check them): by the rule read backwards: which field
      fails is not said. All five differ in support: that the equation tells apart two distributions
      with one support is proved at no toy example.
  (12) Where the session and `runC` differ by their definitions: a column that has not been produced
      (the session's verifier rejects; `runC` returns an error); the test of `runC` on the sealing
      round, which has no counterpart in the session; a simulator that outputs another number of
      rounds (`none`). Under the hypotheses each has probability 0 on both sides, by the equation.
  (13) One list of challenges, fixed, and given to the right side whole and in advance: also to the
      simulators of early rounds.
  (14) The prover is `G.prover H`: H with the lists' own prover's sides put in: not H; and it is the
      model's prover: how the programs' prover relates to it is not said in these files.
  (15) Hypotheses that the prose above does not name: `Prover.trace … = some` (the request has a
      trace): `row_law`.
  (16) The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Bridge
import Johnson.Desc.ProofFile.Honest.Law.Rule.FileOkOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (FileDescription)

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
  {Rel : W₀ → Rc → Xi → Prop}

/-- **What the honest side's fold produces has the distribution of the kernels' fold.** -/
theorem row_law (hO : Owed F Bk H G Rel) (hF : FileOk F Bk G) (hE : G.owns = true) {w₀ : W₀}
    {rc : Rc} {x : Xi} {tr : Tr} {ρ : Draws} (hrel : Rel w₀ rc x) (hρ : ρ.due F = true)
    (hsil : silentAt F (G.prover H) w₀ rc x ρ = none) (htr : H.trace w₀ x = some tr) :
    (unif (Coins Bk)).map (fun k => some (Kit.real ((theActs F Bk G.sims H.key x ρ).map
        (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ))) k (Stand.start F x))) =
      simActs x (stF F H w₀ rc ρ) (theActs F Bk G.sims H.key x ρ) (Stand.start F x) := by
  obtain ⟨r₀, hrun₀⟩ := hO.runs w₀ rc x hrel (Classical.arbitrary (Coins Bk)) ρ hρ hsil
  obtain ⟨R₀, hR₀, -⟩ := run_setup hO hF htr hrun₀
  have h := row_law_abs (rowOk_of hO hF hrel hρ hsil htr hE)
  rw [file_stage hF hR₀, sim_is] at h
  exact h

/-- **The rule, at what is produced.** -/
theorem rule_laid (hO : Owed F Bk H G Rel) (hE : G.owns = true) :
    ∀ w₀ rc x, Rel w₀ rc x → ∀ ρ : Draws, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      (unif (Coins Bk)).map
          (fun k => (runC F Bk (G.prover H) w₀ rc x k ρ).toOption.map (·.run.laid)) =
        (simActs x (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))
          (theActs F Bk G.sims H.key x ρ) (Stand.start F x)).map fun o => o.map (·.laid) := by
  intro w₀ rc x hrel ρ hρ hsil
  obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.1 (hO.input w₀ rc x hrel).2
  obtain ⟨r₀, hrun₀⟩ := hO.runs w₀ rc x hrel (Classical.arbitrary (Coins Bk)) ρ hρ hsil
  have hF := fileOk_of hO hrun₀
  rw [← row_law hO hF hE hrel hρ hsil htr, PMF.map_comp]
  refine congrArg (fun f => PMF.map f (unif (Coins Bk))) (funext fun k => ?_)
  obtain ⟨r, hr⟩ := hO.runs w₀ rc x hrel k ρ hρ hsil
  show (runC F Bk (G.prover H) w₀ rc x k ρ).toOption.map (·.run.laid) =
    some (Kit.real ((theActs F Bk G.sims H.key x ρ).map
      (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ))) k (Stand.start F x)).laid
  rw [hr, model hF htr hr]
  show some r.run.laid = some (laidOf F ρ r.run.played.1 r.run.played.2.1 r.run.played.2.2)
  rw [laid_is r.run (runOk_of hr).1]

/-- **The rule, at the three views.** -/
theorem rule_views (hO : Owed F Bk H G Rel) (hE : G.owns = true) :
    ∀ w₀ rc x, Rel w₀ rc x → ∀ ρ : Draws, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      (unif (Coins Bk)).map (fun k => outcomeC F Bk (G.prover H) w₀ rc x k ρ) =
        session F Bk G.sims H.key x ρ (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) := by
  intro w₀ rc x hrel ρ hρ hsil
  obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.1 (hO.input w₀ rc x hrel).2
  obtain ⟨r₀, hrun₀⟩ := hO.runs w₀ rc x hrel (Classical.arbitrary (Coins Bk)) ρ hρ hsil
  have hF := fileOk_of hO hrun₀
  unfold session
  rw [← row_law hO hF hE hrel hρ hsil htr, PMF.map_comp]
  refine congrArg (fun f => PMF.map f (unif (Coins Bk))) (funext fun k => ?_)
  obtain ⟨r, hr⟩ := hO.runs w₀ rc x hrel k ρ hρ hsil
  show outcomeC F Bk (G.prover H) w₀ rc x k ρ =
    viewsOff F ρ (stF F H w₀ rc ρ) (Kit.real ((theActs F Bk G.sims H.key x ρ).map
      (Act.stage x (stF F H w₀ rc ρ) (realF F H G w₀ rc x tr ρ))) k (Stand.start F x)).laid
  rw [model hF htr hr]
  obtain ⟨hRO, c₁, c₂, c₃⟩ := runOk_of hr
  show _ = viewsOff F ρ (stF F H w₀ rc ρ)
    (laidOf F ρ r.run.played.1 r.run.played.2.1 r.run.played.2.2)
  rw [show viewsOff F ρ (stF F H w₀ rc ρ)
      (laidOf F ρ r.run.played.1 r.run.played.2.1 r.run.played.2.2) = _ from
    views_back hRO c₁ c₂ c₃]
  unfold outcomeC
  rw [hsil, hr]
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, -, -, -, -, -, -, -, -, rfl⟩ := runC_parts hr
  rfl

/-- A corollary. No simulator occurs in its conclusion; the G of `Owed` holds them all the same.
Under `Owed` and `G.owns`: two inputs of the relation with one x, at one list of challenges that the
rounds can draw and that is outside the silent set of either, and at which the stored tables'
columns that the declared rounds read are the same: over uniform coins of a run the two outcomes
have one distribution. That any two indices share x and these columns is not said. No file of this
folder uses it. -/
theorem rule_same (hO : Owed F Bk H G Rel) (hE : G.owns = true) :
    ∀ w₀ rc w₀' rc' x, Rel w₀ rc x → Rel w₀' rc' x → ∀ ρ : Draws, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none → silentAt F (G.prover H) w₀' rc' x ρ = none →
      storedShown (H.storedWords w₀ rc) (storedAsks F ρ) =
        storedShown (H.storedWords w₀' rc') (storedAsks F ρ) →
      (unif (Coins Bk)).map (fun k => outcomeC F Bk (G.prover H) w₀ rc x k ρ) =
        (unif (Coins Bk)).map (fun k => outcomeC F Bk (G.prover H) w₀' rc' x k ρ) := by
  intro w₀ rc w₀' rc' x h h' ρ hρ hs hs' hst
  rw [rule_views hO hE w₀ rc x h ρ hρ hs, rule_views hO hE w₀' rc' x h' ρ hρ hs', hst]

end ProofFile.Honest

#print axioms ProofFile.Honest.row_law
#print axioms ProofFile.Honest.rule_laid
#print axioms ProofFile.Honest.rule_views
#print axioms ProofFile.Honest.rule_same
