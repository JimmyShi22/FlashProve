--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/UseByKind.lean: "ON AT THE RUN, LIST BY LIST", CUT KIND BY KIND. General in
the kind, the description, the book, the lists and the prover. The rule that ends in `Owed` at a run
(`owed_mute_of_threads_at_run`, Honest/Law/OwedAtRun.lean) asks of EVERY list of parts of the three chains,
beside `Good` and `BudDebts`, that the list's On holds at a run's own state and front before each part that
the run has called (`OnAtRun₁`, `OnAtRun₂`, `OnAtRun₃`). Here that is cut at the kind of the list's place,
so that a kind's authors can pay their share alone, and the shares of all kinds are gathered back. The
like cut of `BudDebts` is other authors' (`KindBud`, Johnson/M1/BudGather.lean).

WHAT IT IS NOT. Definitions, and lemmas that sort hypotheses. No kind is named and nothing is paid. A kind
of which the lists hold no list pays its share emptily. "On holds always" is lawful only where the
field `exact` of `Good` has been shown at that On: an On that asks nothing makes `exact` ask the most.
Nothing on soundness, completeness or hiding.

  `KindOnAtRun`    `OnAtRun₁`, `₂`, `₃` at the lists at a place of one kind, at one run
  `onAtRun_of_kinds`   all kinds' shares are the rule's three "at every list"
  `kindOnAtRun_none`   a kind with no list pays for want of a list
  `KindOnAtEveryRun`, `onAtEveryRun_of_kinds`   the same with the rule's own prefix, at ONE family of invariants
        for all kinds: the shares of all kinds are the rule's premise hon, to the letter
  `owed_mute_of_threads_at_run_by_kinds`   the rule itself, taking that premise kind by kind
  `onAtRun₁_of_always`, `₂`, `₃`   a list whose On holds always meets it at every run
  `ListsOfTheKindBear`   the lists of one kind are rows of a given list of rows of the first chain, and no
        list of that kind stands in the other two chains
  `kindOnAtRun_of_rows`   under it: the kind's share, where On holds always at each row
-/
import Johnson.Desc.ProofFile.Honest.Law.OwedAtRun
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 On, at a run -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **One kind's share of "On at the run, list by list"**, at one family of invariants T, one list of
challenges ρ and one run r. A definition, meant as a hypothesis or as a theorem's end. -/
structure KindOnAtRun (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F)
    (κ : KindName) : Prop where
  on₁ : ∀ L ∈ G.first, L.place.kind = κ → OnAtRun₁ (G := G) (H := H) T ρ r L
  on₂ : ∀ L ∈ G.shared, L.place.kind = κ → OnAtRun₂ (G := G) (H := H) T ρ r L
  on₃ : ∀ L ∈ G.second, L.place.kind = κ → OnAtRun₃ (G := G) (H := H) T ρ r L

/-- **All kinds' shares are the rule's three "at every list".** -/
theorem onAtRun_of_kinds {T : ThreadsP F Bk (G.prover H) w₀ rc x k R} {ρ : Draws} {r : RunC F}
    (h : ∀ κ, KindOnAtRun (G := G) (H := H) T ρ r κ) :
    (∀ L ∈ G.first, OnAtRun₁ (G := G) (H := H) T ρ r L) ∧
      (∀ L ∈ G.shared, OnAtRun₂ (G := G) (H := H) T ρ r L) ∧
      ∀ L ∈ G.second, OnAtRun₃ (G := G) (H := H) T ρ r L :=
  ⟨fun L hL => (h L.place.kind).on₁ L hL rfl, fun L hL => (h L.place.kind).on₂ L hL rfl,
    fun L hL => (h L.place.kind).on₃ L hL rfl⟩

/-- A kind of which the lists hold no list pays its share, for want of a list. `KindName` has sixteen
members; the lists of a description hold lists of fewer kinds. -/
theorem kindOnAtRun_none (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F)
    {κ : KindName} (h₁ : ∀ L ∈ G.first, L.place.kind ≠ κ) (h₂ : ∀ L ∈ G.shared, L.place.kind ≠ κ)
    (h₃ : ∀ L ∈ G.second, L.place.kind ≠ κ) : KindOnAtRun (G := G) (H := H) T ρ r κ :=
  ⟨fun L hL e => absurd e (h₁ L hL), fun L hL e => absurd e (h₂ L hL),
    fun L hL e => absurd e (h₃ L hL)⟩

/-- **A list of the first chain whose On holds always meets it at every run.** -/
theorem onAtRun₁_of_always (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (always : ∀ u ca m front, L.On u ca m front) : OnAtRun₁ (G := G) (H := H) T ρ r L :=
  fun _ _ u _ _ _ _ m ca _ _ _ _ _ _ => always u ca m _

/-- The same of a list of the shared chain. -/
theorem onAtRun₂_of_always (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    (always : ∀ u ca m front, L.On u ca m front) : OnAtRun₂ (G := G) (H := H) T ρ r L :=
  fun _ _ u _ _ _ _ m ca _ _ _ _ _ _ => always u ca m _

/-- The same of a list of the second chain. -/
theorem onAtRun₃_of_always (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F)
    {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (always : ∀ u ca m front, L.On u ca m front) : OnAtRun₃ (G := G) (H := H) T ρ r L :=
  fun _ _ u _ _ _ _ m ca _ _ _ _ _ _ => always u ca m _

end

/-! ## 2 The rule's whole premise, cut by kind -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X}

/-- **One kind's share of the rule's premise on On, with the premise's own prefix**: at ONE family of
invariants T, which is the same for all kinds: at every input of the relation, all coins, every return
of `ready`, every due list of challenges at which the honest side is not silent, and every run that
returned. A definition, meant as a hypothesis or as a theorem's end. -/
def KindOnAtEveryRun (Rel : W₀ → Rc → Xi → Prop)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R) (κ : KindName) : Prop :=
  ∀ w₀ rc x (hrel : Rel w₀ rc x) k R (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) ρ r,
    ρ.due F = true → silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
    KindOnAtRun (G := G) (H := H) (T w₀ rc x hrel k R hR) ρ r κ

/-- **All kinds' shares are the premise hon of `owed_of_threads_at_run` and of
`owed_mute_of_threads_at_run`** (Honest/Law/OwedAtRun.lean), to the letter. -/
theorem onAtEveryRun_of_kinds {Rel : W₀ → Rc → Xi → Prop}
    {T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R}
    (h : ∀ κ, KindOnAtEveryRun (G := G) (H := H) Rel T κ) :
    ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) ρ r, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
      (∀ L ∈ G.first, OnAtRun₁ (T w₀ rc x hrel k R hR) ρ r L) ∧
      (∀ L ∈ G.shared, OnAtRun₂ (T w₀ rc x hrel k R hR) ρ r L) ∧
      ∀ L ∈ G.second, OnAtRun₃ (T w₀ rc x hrel k R hR) ρ r L :=
  fun w₀ rc x hrel k R hR ρ r due silent run =>
    onAtRun_of_kinds fun κ => h κ w₀ rc x hrel k R hR ρ r due silent run

/-- **The rule at the muted lists, with its premise on On taken kind by kind.** All other premises are the
rule's own, word for word. It is here so that Lean holds the end of `onAtEveryRun_of_kinds` against the
rule's premise. -/
theorem owed_mute_of_threads_at_run_by_kinds {Rel : W₀ → Rc → Xi → Prop}
    (plan : F.planOk = true) (book : Bk.word F = none) (seats : G.seated = true)
    (hq : sealPlain F = true) (hroot : rootedAll F (G.prover H) = true)
    (hand₁ : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder L.place) .own σ Bk (orderOf F) 0 0 A' B'
        L.On L.bud)
    (hand₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
        A' B' L.On L.bud)
    (hand₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk
        (orderOf F) 2 F.lastChainFirstTreeNumber A' B' L.On L.bud)
    (input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true)
    (hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
      ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W)
    (hready : ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (T : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP F Bk (G.prover H) w₀ rc x k R)
    (hW : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk (G.prover H) w₀ rc x k = .ok R →
      PartsStand G k R)
    (hbud : BudDebts F Bk G)
    (on : ∀ κ, KindOnAtEveryRun (G := G) (H := H) Rel T κ) :
    Owed F Bk H G.mute Rel :=
  owed_mute_of_threads_at_run plan book seats hq hroot hand₁ hand₂ hand₃ input hst hready T hW hbud
    (onAtEveryRun_of_kinds on)

end

/-! ## 3 A kind whose lists are a lot's rows in the first chain -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X)

/-- **The lists of one kind are rows of a given list, in the first chain alone**: each list of the first
chain at a place of the kind is, its A and B forgotten, one of the rows (place, parts, simulators, On
and bud); no list of the kind stands in the shared or the second chain. A condition on the lists G:
whoever lays G owes it. Where G has no list of the kind it holds, and says nothing. -/
structure ListsOfTheKindBear (κ : KindName)
    (rows : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)) : Prop where
  first : ∀ L ∈ G.first, L.place.kind = κ → L.bare ∈ rows
  noneShared : ∀ L ∈ G.shared, L.place.kind ≠ κ
  noneSecond : ∀ L ∈ G.second, L.place.kind ≠ κ

variable {G}

/-- CONDITIONAL. **The kind's share of "On at the run", where On holds always at each list that bears a
row**: at every family of invariants, every list of challenges and every run. -/
theorem kindOnAtRun_of_rows {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {κ : KindName}
    {rows : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)}
    (bear : ListsOfTheKindBear G κ rows)
    (always : ∀ L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      L.bare ∈ rows → ∀ u ca m front, L.On u ca m front)
    (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) (ρ : Draws) (r : RunC F) :
    KindOnAtRun (G := G) (H := H) T ρ r κ :=
  ⟨fun L hL hk => onAtRun₁_of_always T ρ r (always L (bear.first L hL hk)),
    fun L hL hk => absurd hk (bear.noneShared L hL),
    fun L hL hk => absurd hk (bear.noneSecond L hL)⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.KindOnAtRun
#print axioms ProofFile.Honest.onAtRun_of_kinds
#print axioms ProofFile.Honest.kindOnAtRun_none
#print axioms ProofFile.Honest.KindOnAtEveryRun
#print axioms ProofFile.Honest.onAtEveryRun_of_kinds
#print axioms ProofFile.Honest.owed_mute_of_threads_at_run_by_kinds
#print axioms ProofFile.Honest.onAtRun₁_of_always
#print axioms ProofFile.Honest.onAtRun₂_of_always
#print axioms ProofFile.Honest.onAtRun₃_of_always
#print axioms ProofFile.Honest.ListsOfTheKindBear
#print axioms ProofFile.Honest.kindOnAtRun_of_rows
