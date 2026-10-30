-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean: the rule for `Owed` (Honest/Owed.lean) at a file:
from `Good` for each list of parts, invariants for the three chains, and two hypotheses for each
side, to the structure of hypotheses that the rule for lists of parts takes
(Honest/Law/Rule/Row.lean). `Owed` has eight fields. Four are passed through; `good` is brought into
the form with the field `opened` beside each list's two conditions (`Lettered.goodAt_withField`,
Honest/FieldFree.lean); the test on the places follows from the tests on the plan; that the run goes
through is `runC_returns` (Honest/Law/RunsFile.lean) with `planServes` (Honest/Law/PlanGives.lean);
what each part is owed at each run is given by the three lemmas of Honest/Law/OwedParts.lean.

What this is. A conditional lemma on this folder's own functions, at parameters F Bk H G Rel. Its
conclusion is a definition of this folder, a structure of hypotheses: no property, and none of the
library's goals. There is no probability in it. Its hypotheses are proved here of no description.

Met trivially, in seven ways; nothing here excludes any of them.
  (1) Rel := False, or narrower than what is to be spoken of; a Rel that fixes the index.
  (2) An invariant that cannot hold at the start: then T cannot be built.
  (3) A book at which `ready` returns an error: hready fails.
  (4) On is a parameter that the side's author chooses: at On := the equation of `Good.exact` itself
      that field says nothing and all content moves into `OnDebts`; at On := True `OnDebts` holds
      trivially and `Good.exact` must hold at every state. So `Good` and `OnDebts` are supplied
      together, at one On, or neither counts. Likewise for bud: at bud := False `Good.exact` and
      `Good.fresh` hold vacuously and `BudDebts` cannot be proved; at bud := True `BudDebts` holds
      trivially.
  (5) Sides without lists of parts, or lists after a sub-protocol that always rejects: On is owed of
      called parts alone, so the resulting `Owed` says little: what guards against that is the rule
      for acceptance at the same F Bk H G.
  (6) Nothing of `Good.acc`, of a fall or of how many lists a stop takes is in this rule.
  (7) At a list whose parameter A is False `Good.plays` and `Good.acc` hold vacuously: these two
      fields go into the form with the field, and nothing after this rule reads them: for `Owed`
      what counts of `Good` is fits, exact and fresh.

  1  `Side.roundsTo`, `side_place`   the rounds of a list's parts before a part; a side's place
  2  `BudDebts`, `OnDebts`   the two hypotheses for each side, gathered over a description's lists
     of parts
  3  `PartsStand`   where the parts' rounds are, and that the book gives them their coins: generic;
     no kind's author has to prove it
  4  `owed_of_threads`   the rule

Limits.
  * `PartsStand` is a hypothesis in this file: it speaks of the `Step`s of `ready` and the book, and
    is proved once, generally, in Honest/Law/StandsFile.lean.
  * That `ready` returns at all coins (hready) is a hypothesis here; Honest/Law/ReadyAny.lean proves
    it from one return.
  * `OnDebts` runs over more values of `front` than runs produce: nothing in it fixes how the rounds
    before are cut into p₀, p₁ and p, which round has which table, or that ρ's challenges are the
    rounds' own. So, to be provable through it, On may read of `front`: what has been seen, the
    columns listed of the available trees, the stored columns; not the chain number of a round
    without a root, how roots are grouped into rounds, how many trees are listed beyond the
    available ones, or whether a given position is listed.
  * `OnDebts` knows of the state's field `opened` what the invariant says of it, and no more: an On
    that reads the field wants invariants that pin it.
  * `good` is asked in the plain form, at `earlierOf F` of each chain (Honest/Owed.lean). That is
    more than `Owed.good` asks: a list with a part that reads the field and errs at `none` meets it
    only at an A that pins the field itself, or vacuously (Honest/FieldFree.lean, Limits; the
    lighter form: `Lettered.goodAt_field`, Honest/FieldOwed.lean).
  * Among the hypotheses that the prose above does not name: `sealPlain` (the first chain's last
    declared round declares no item except roots, and no root): `owed_of_threads`;
    `ProverCoinCounts.word … = none` (every test on the book passes): `owed_of_threads`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Owed
import Johnson.Desc.ProofFile.Honest.FieldFree
import Johnson.Desc.ProofFile.Honest.Law.OwedParts
import Johnson.Desc.ProofFile.Honest.Law.PlanGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X S Cl V W Y Pb : Type}

/-! ## 1 Small ones -/

/-- The rounds of a list's parts before part number j: as `membersOf` cuts the list. -/
def Side.roundsTo (σ : Side S Cl V W Y Pb) (j : Nat) : Nat :=
  ((σ.row.take j).map fun x => x.1.moves.length).sum

theorem side_place {Bk : ProverCoinCounts} {L : Lettered Bk S Cl V W Y Pb} {bs : List (Block S Cl)}
    {fs : List (Fall S)} {σ : Side S Cl V W Y Pb} (h : L.side bs fs = some σ) :
    σ.block.place = L.place := by
  unfold Lettered.side Side.seated at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact beq_iff_eq.1 (List.find?_some (p := fun b : Block S Cl => b.place == L.place) hb)

/-! ## 2 The two hypotheses for each side -/

section
variable (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X)

/-- **`bud`, at every part of every list, at every list of challenges that the rounds can draw**,
those at which a part stops among them: at the part's own section of its chain's challenges and at
the positions that the declared rounds read of its tables. A condition on the description, the
lists' cut and the challenges: no input, no coin, no run. A `bud` that relies on a stop cannot be
proved so; a count can. It is a structure of hypotheses: to be proved by the sides' authors, beside
`Good`. -/
structure BudDebts : Prop where
  bud₁ : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
    F.first.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
    L.bud u.number ((ρ.first.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
        (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum)
  bud₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
    F.shared.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
    L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
        (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum)
  bud₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
    F.second.blocksInOrder = pre ++ σ.block :: t →
    n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
    L.bud u.number ((ρ.second.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 2) (u.rounds.map (·.2.length))
        (((rowsOfChain F.second.blocksInOrder).take n).map (·.2.length)).sum)

variable {F Bk H G}

/-- **On follows from the invariant's condition at the state before the part**: at one input, one
run's coins and one family of invariants. `p` (`p₀`, `p₁`): rounds as produced before the part in
its own chain (in the two earlier chains). What the part is shown of them is said outright
(`laidOf`, Honest/Law/Rule/Words.lean). It is a structure of hypotheses: to be proved by the sides'
authors, beside `Good`, at the same parameter On. -/
structure OnDebts {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) : Prop where
  on₁ : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.first.blocksInOrder = pre ++ σ.block :: t → ∀ ρ p m ca, ρ.due F = true →
    InsideOf .own Bk 0 (G.prover H).first σ.block (T.I₁ pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) p) →
    m.seen = roundsOf p →
    carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
    L.On u ca m ((laidOf F ρ p [] []).front 0
      (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))
  on₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.shared.blocksInOrder = pre ++ σ.block :: t → ∀ ρ p m ca, ρ.due F = true →
    InsideOf .shared Bk 1 (G.prover H).shared σ.block (T.I₂ pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) p) →
    m.seen = roundsOf p →
    carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
    L.On u ca m ((laidOf F ρ [] p []).front 1
      (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))
  on₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.second.blocksInOrder = pre ++ σ.block :: t → ∀ ρ p₀ p₁ p m ca, ρ.due F = true →
    InsideOf .own Bk 2 (G.prover H).second σ.block (T.I₃ pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (taken₃ p₀ p₁) p) →
    m.seen = roundsOf p₀ ++ roundsOf p₁ ++ roundsOf p →
    carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca →
    L.On u ca m ((laidOf F ρ p₀ p₁ p).front 2
      (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))

/-! ## 3 Where the parts' rounds are -/

/-- **Every part of every list is in one section of its chain's `Step`s, after the rounds of the
sub-protocols and of the list's parts before it; and the book gives it its carried blocks.** Of what
`ready` has prepared at one run's coins. It is a structure of hypotheses; no kind's author has to
prove it. -/
structure PartsStand (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (k : Coins Bk)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Prop where
  at₁ : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members,
    (∃ pre t, StandsAt F.first.blocksInOrder R.first σ u pre t (σ.roundsTo u.number)) ∧
      ∃ ca, carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca
  at₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
    (∃ pre t, StandsAt F.shared.blocksInOrder R.shared σ u pre t (σ.roundsTo u.number)) ∧
      ∃ ca, carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca
  at₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members,
    (∃ pre t, StandsAt F.second.blocksInOrder R.second σ u pre t (σ.roundsTo u.number)) ∧
      ∃ ca, carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca

end

/-! ## 4 The rule -/

/-- **The rule for `Owed` at a file.** A conditional lemma on this folder's own functions, at
parameters. Its conclusion is a definition of this folder, a structure of hypotheses: no property,
and none of the library's goals. The seven ways to meet it trivially are in this file's head. -/
theorem owed_of_threads {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (good : (∀ L ∈ G.first,
        L.goodAt (earlierOf F 0) .own F.first.blocksInOrder (orderOf F) 0 0 G.falls₁) ∧
      (∀ L ∈ G.shared,
        L.goodAt (earlierOf F 1) .shared F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂) ∧
      ∀ L ∈ G.second,
        L.goodAt (earlierOf F 2) .own F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (hW : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      PartsStand G k R)
    (hbud : BudDebts F Bk G)
    (hon : ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R), OnDebts (T w₀ rc x hrel k R hR)) :
    Owed F Bk H G Rel where
  plan := plan
  book := book
  places := ((F.planOk_ok).1 plan).places
  seats := seats
  good := ⟨fun L hL => Lettered.goodAt_withField (good.1 L hL),
    fun L hL => Lettered.goodAt_withField (good.2.1 L hL),
    fun L hL _ _ => Lettered.goodAt_withField (good.2.2 L hL)⟩
  input := input
  runs := fun w₀ rc x hrel k ρ hρ hsil => by
    obtain ⟨R, hR⟩ := hready w₀ rc x hrel k
    exact runC_returns hR hq hρ hsil (planServes hR plan hroot (hst w₀ rc x hrel))
      (T w₀ rc x hrel k R hR).I₁ (T w₀ rc x hrel k R hR).I₂ (T w₀ rc x hrel k R hR).I₃
      (T w₀ rc x hrel k R hR).h₁ (T w₀ rc x hrel k R hR).h₂ (T w₀ rc x hrel k R hR).h₃
      (T w₀ rc x hrel k R hR).a₁ (T w₀ rc x hrel k R hR).a₂ (T w₀ rc x hrel k R hR).a₃
  owed := fun w₀ rc x hrel k ρ r hρ hsil h => by
    obtain ⟨R, hR⟩ := hready w₀ rc x hrel k
    have hPS := planServes hR plan hroot (hst w₀ rc x hrel)
    exact ⟨fun L hL σ hσ u hu => by
      obtain ⟨⟨pre, t, S⟩, hl⟩ := (hW w₀ rc x hrel k R hR).at₁ L hL σ hσ u hu
      exact owed_part_first h hR plan hρ hsil (T w₀ rc x hrel k R hR) (side_place hσ) S rfl hl
        (hbud.bud₁ L hL σ hσ u hu pre t _ S.cut rfl ρ hρ)
        (fun m ca hin hs hc =>
          (hon w₀ rc x hrel k R hR).on₁ L hL σ hσ u hu pre t S.cut ρ _ m ca hρ hin hs hc),
      fun L hL σ hσ u hu => by
      obtain ⟨⟨pre, t, S⟩, hl⟩ := (hW w₀ rc x hrel k R hR).at₂ L hL σ hσ u hu
      exact owed_part_shared h hR plan hρ hsil (T w₀ rc x hrel k R hR) (side_place hσ) S rfl hl
        (hbud.bud₂ L hL σ hσ u hu pre t _ S.cut rfl ρ hρ)
        (fun m ca hin hs hc =>
          (hon w₀ rc x hrel k R hR).on₂ L hL σ hσ u hu pre t S.cut ρ _ m ca hρ hin hs hc),
      fun L hL σ hσ u hu => by
      obtain ⟨⟨pre, t, S⟩, hl⟩ := (hW w₀ rc x hrel k R hR).at₃ L hL σ hσ u hu
      exact owed_part_second h hR plan hρ hsil hPS (T w₀ rc x hrel k R hR) (side_place hσ) S rfl hl
        (hbud.bud₃ L hL σ hσ u hu pre t _ S.cut rfl ρ hρ)
        (fun m ca hin hs hc =>
          (hon w₀ rc x hrel k R hR).on₃ L hL σ hσ u hu pre t S.cut ρ _ _ _ m ca hρ hin hs hc)⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.side_place
#print axioms ProofFile.Honest.owed_of_threads
#print axioms ProofFile.Honest.Side.roundsTo
#print axioms ProofFile.Honest.BudDebts
#print axioms ProofFile.Honest.OnDebts
#print axioms ProofFile.Honest.PartsStand
