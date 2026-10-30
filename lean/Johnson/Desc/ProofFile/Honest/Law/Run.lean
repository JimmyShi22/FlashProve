-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Run.lean: which tests the three views of a run of `run`
(Honest/Frame.lean) pass by themselves. The lemmas are general in the description, the book and the
prover.

The head of Honest/Law/Kept.lean divides a description's acceptance into four: the tests on the
plan, the test on the instance, `fitsAll` (every word below the prime; each whole chain's
book-keeping), and `Decided` (what the sub-protocols, the second chain's start and the last test
decide). Here the third is proved of a run's views (`run_fits`).

  1  `unfit_ok`   on `Except`
  2  `ready_ok`, `ends_ok`, `run_parts`, `seal_back`   what a run that goes through consists of
  3  `steps_decl`, `yields_drawn`, `chain_kept`, `chain_words`   one chain
  4  `halved`, `halvedAll`, `itemsFall_of_halved`   with no stored run to fall back on: a prover's
     side is defined wherever a round declares an item other than a root
  5  `run_words`, `run_fits`, `run_yes_iff`   a run with no stored run to fall back on
  6  `run_fits_back`, `run_yes_iff_back`   a run that falls back on a stored run which itself passes
     `fitsAll`

Limits.
  * Every lemma starts from a run that has gone through: none says that one does.
  * `run_yes_iff` is an equivalence: no acceptance is concluded.
  * The lemmas of section 6 are a control on the small lemmas, not a case of `run_fits`: that a
    prover's side is defined wherever an item is declared is not among their hypotheses, and what
    was fallen back on passes because the stored run does.
  * `run_words`, `run_fits` and `run_yes_iff` are at challenges that pass `Draws.due`; `run_yes_iff`
    and `run_yes_iff_back` also take `F.planOk = true`.
  * Hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these coins):
    `ready_ok`; `drawsFit` (`drawFit` round by round, and as many challenges as rounds):
    `chain_kept`, `chain_words`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Kept
import Johnson.Desc.ProofFile.Honest.Law.Steps
import Johnson.Desc.ProofFile.Honest.Law.Cols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W X W₀ Rc Ky Tr X₀ : Type}

/-! ## 1 On `Except` -/

theorem unfit_ok {α : Type} {e : Except String α} {y : α} (h : unfit e = .ok y) : e = .ok y := by
  cases e with
  | error s => cases h
  | ok a =>
    have h' : (Except.ok a : Except Refusal α) = .ok y := h
    exact congrArg Except.ok (Except.ok.inj h')

/-! ## 2 What a run that goes through consists of -/

theorem ready_ok {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : ready F B H w₀ rc x c = .ok R) :
    readyTests F B H w₀ = .ok () ∧ ∃ tr, H.trace w₀ x = some tr ∧ R.own = ⟨w₀, rc, x, tr⟩ ∧
      R.common = ⟨w₀, rc, H.key x⟩ ∧
      chainSteps B (B.rowsOf 0) (c.look 0) (Face.own.sees R.own) F.first.blocksInOrder H.first =
        .ok R.first ∧
      chainSteps B (B.rowsOf 1) (sharedLook B c.shared) (Face.shared.sees R.common) F.shared.blocksInOrder
        H.shared = .ok R.shared ∧
      chainSteps B (B.rowsOf 2) (c.look 2) (Face.own.sees R.own) F.second.blocksInOrder H.second =
        .ok R.second := by
  unfold ready at h
  obtain ⟨u, ht, h⟩ := exBind_ok h
  cases htr : H.trace w₀ x with
  | none =>
    rw [htr] at h
    exact (error_ne_ok h).elim
  | some tr =>
    rw [htr] at h
    obtain ⟨m₁, h1, h⟩ := exBind_ok h
    obtain ⟨m₂, h2, h⟩ := exBind_ok h
    obtain ⟨m₃, h3, h⟩ := exMap_ok h
    subst h
    exact ⟨ht, tr, rfl, rfl, rfl, unfit_ok h1, unfit_ok h2, unfit_ok h3⟩

theorem ends_ok {R : Ready W₀ Rc Xi Ky Tr X₀ X} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {ρ₁ ρ₂ : List Fmt.Drawn} {b₁ b₂ : List Fmt.RoundView}
    {r₁ : List Played × Mid (Local W₀ Rc Xi Tr) X} {r₂ : List Played × Mid (Common W₀ Rc Ky) X₀}
    (h : R.ends H ρ₁ ρ₂ b₁ b₂ = .ok (r₁, r₂)) :
    play R.first ρ₁ b₁ (R.start₁ H) = .ok r₁ ∧ sealQuiet r₁.1 = true ∧
      play R.shared ρ₂ b₂ (R.start₂ H) = .ok r₂ := by
  unfold Ready.ends at h
  obtain ⟨a, ha, h⟩ := exBind_ok h
  obtain ⟨y, hy, hs⟩ := exBind_ok ha
  obtain ⟨b, hb, h⟩ := exMap_ok h
  unfold sealTest at hs
  obtain ⟨hq, hs⟩ := exIte_ok hs
  cases hs
  cases h
  exact ⟨hy, by simpa using hq, hb⟩

/-- **What a run that goes through consists of.** -/
theorem run_parts {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {back : Option Views} {r : Run}
    (h : run F B H w₀ rc x c ρ back = .ok r) :
    ∃ R r₁ r₂ r₃ c₁ c₂ c₃, ready F B H w₀ rc x c = .ok R ∧
      (back.map fun U => ρ.same (drawsOf U)).getD true = true ∧
      play R.first ρ.first ((back.map fun (U : Views) => U.1).getD (⟨[], []⟩ : Fmt.View)).rounds
        (R.start₁ H) = .ok r₁ ∧
      sealQuiet r₁.1 = true ∧
      play R.shared ρ.shared
        ((back.map fun (U : Views) => U.2.1).getD (⟨[], []⟩ : Fmt.View)).rounds (R.start₂ H) =
        .ok r₂ ∧
      play R.second ρ.second
        ((back.map fun (U : Views) => U.2.2).getD (⟨[], []⟩ : Fmt.View)).rounds
        (R.start₃ H r₁.2 r₂.2) = .ok r₃ ∧
      fillCols (readsOf 0 0 (H.storedWords w₀ rc) (treeOwn r₁.1) F.roundsDeclaredByBlocks.1 ρ.first)
        ((back.map fun (U : Views) => U.1).getD (⟨[], []⟩ : Fmt.View)).opened = .ok c₁ ∧
      fillCols (readsOf 1 0 (H.storedWords w₀ rc) (treeOwn r₂.1) F.roundsDeclaredByBlocks.2.1 ρ.shared)
        ((back.map fun (U : Views) => U.2.1).getD (⟨[], []⟩ : Fmt.View)).opened = .ok c₂ ∧
      fillCols (readsOf 2 F.lastChainFirstTreeNumber (H.storedWords w₀ rc) (treeThird r₁.1 r₂.1 r₃.1) F.roundsDeclaredByBlocks.2.2
        ρ.second) ((back.map fun (U : Views) => U.2.2).getD (⟨[], []⟩ : Fmt.View)).opened = .ok c₃ ∧
      r = ⟨(r₁.1, r₂.1, r₃.1),
        (readsOf 0 0 (H.storedWords w₀ rc) (treeOwn r₁.1) F.roundsDeclaredByBlocks.1 ρ.first,
          readsOf 1 0 (H.storedWords w₀ rc) (treeOwn r₂.1) F.roundsDeclaredByBlocks.2.1 ρ.shared,
          readsOf 2 F.lastChainFirstTreeNumber (H.storedWords w₀ rc) (treeThird r₁.1 r₂.1 r₃.1) F.roundsDeclaredByBlocks.2.2
            ρ.second),
        (⟨(roundsOf r₁.1).dropLast, c₁⟩, ⟨roundsOf r₂.1, c₂⟩, ⟨roundsOf r₃.1, c₃⟩)⟩ := by
  unfold run at h
  obtain ⟨R, hR, h⟩ := exBind_ok h
  obtain ⟨hs, h⟩ := exIte_ok h
  obtain ⟨⟨r₁, r₂⟩, hE, h⟩ := exBind_ok h
  obtain ⟨r₃, h3, h⟩ := exBind_ok h
  obtain ⟨c₁, f1, h⟩ := exBind_ok h
  obtain ⟨c₂, f2, h⟩ := exBind_ok h
  obtain ⟨c₃, f3, h⟩ := exMap_ok h
  obtain ⟨h1, hq, h2⟩ := ends_ok hE
  exact ⟨R, r₁, r₂, r₃, c₁, c₂, c₃, hR, by simpa using hs, h1, hq, h2, h3, unfit_ok f1,
    unfit_ok f2, unfit_ok f3, h.symm⟩

/-- The round that `run` drops from the first view is the one that `withEmptySealRound` puts back. -/
theorem seal_back {l : List Played} (h : sealQuiet l = true) :
    (roundsOf l).dropLast ++ [⟨[], ⟨[], [], [], none⟩⟩] = roundsOf l := by
  unfold sealQuiet at h
  cases hl : l.getLast? with
  | none =>
    rw [hl] at h
    simp at h
  | some p =>
    rw [hl] at h
    simp at h
    obtain ⟨⟨hv, _⟩, hd⟩ := h
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hl
    simp [roundsOf, hv, hd]

/-! ## 3 One chain -/

theorem rows_decl (g : Block S Cl → Bool) : ∀ (bs : List (Block S Cl)),
    (∀ b ∈ bs, b.oracles.length = b.rounds.length) →
    (bs.flatMap fun b => (b.rounds.zip b.oracles).map fun z => (z.1, z.2, b.place, g b)).map
      (·.1) = bs.flatMap (·.rounds)
  | [], _ => rfl
  | b :: bs, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_map,
      rows_decl g bs fun b' hb' => h b' (List.mem_cons_of_mem _ hb')]
    exact congrArg (· ++ _) ((map_zip_fst (fun (d : Fmt.DeclaredRound) => d) b.rounds b.oracles
      (Nat.le_of_eq (h b List.mem_cons_self).symm)).trans (List.map_id' _))

/-- The rounds that `chainSteps` prepares declare the sub-protocols' rounds, concatenated. -/
theorem steps_decl {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {bs : List (Block S Cl)} {hs : List (Placed V W X)} {ss : List (Step W X)}
    (h : chainSteps B rows look v bs hs = .ok ss) :
    ss.map (·.decl) = bs.flatMap (·.rounds) := by
  obtain ⟨h1, h2⟩ := chainSteps_rows bs hs ss h
  have h3 := congrArg (List.map (·.1)) h2
  rw [List.map_map, rows_decl _ bs h1] at h3
  exact h3

theorem yields_drawn : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → (roundsOf ps).map (·.drawn) = ds := by
  intro ss
  induction ss with
  | nil =>
    intro ds back ps h
    cases ds <;> cases ps <;> first | rfl | simp [Yields] at h
  | cons s ss ih =>
    intro ds back ps h
    cases ds with
    | nil => simp [Yields] at h
    | cons d ds =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        simp only [Yields] at h
        have e1 : p.drawn = d := h.1.1
        have e2 := ih ds back.tail ps h.2
        show p.drawn :: (roundsOf ps).map (·.drawn) = d :: ds
        rw [e1, e2]

/-- **One chain's book-keeping.** -/
theorem chain_kept {ss : List (Step W X)} {ds : List Fmt.Drawn} {back : List Fmt.RoundView}
    {m : Mid W X} {y : List Played × Mid W X} {decls : List Fmt.DeclaredRound} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {bc c : List OpenedColumn} (hd : ss.map (·.decl) = decls) (hp : play ss ds back m = .ok y)
    (hf : drawsFit decls (ds.map bare) = true) (hi : itemsFall ss back = true)
    (hc : fillCols (readsOf chain ft stored tree decls ds) bc = .ok c) :
    kept ft decls ⟨roundsOf y.1, c⟩ = true := by
  subst hd
  have hs := play_yields _ _ _ _ _ hp
  rw [kept_iff]
  refine ⟨roundsFit_of_yields _ _ _ _ hs hf hi, ?_⟩
  rw [fillCols_kept _ _ _ hc, readsOf_wants, yields_drawn _ _ _ _ hs]

theorem okViewW_split (R : List Fmt.RoundView) (c : List OpenedColumn) :
    viewWordsBelowPrime ⟨R, c⟩ = true ↔ viewWordsBelowPrime ⟨R, []⟩ = true ∧ ∀ x ∈ c, ∀ a ∈ x.2.2, a < fieldPrimeWord := by
  simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]

theorem okViewW_dropLast {R : List Fmt.RoundView} (h : viewWordsBelowPrime ⟨R, []⟩ = true) :
    viewWordsBelowPrime ⟨R.dropLast, []⟩ = true := by
  simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true, List.all_eq_true] at h ⊢
  exact fun r hr => h r (List.mem_of_mem_dropLast hr)

/-- **One chain's words.** -/
theorem chain_words {ss : List (Step W X)} {ds : List Fmt.Drawn} {back : List Fmt.RoundView}
    {m : Mid W X} {y : List Played × Mid W X} {decls : List Fmt.DeclaredRound} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {bc c : List OpenedColumn} (hd : ss.map (·.decl) = decls) (hp : play ss ds back m = .ok y)
    (hf : drawsFit decls (ds.map bare) = true) (hb : viewWordsBelowPrime ⟨back, bc⟩ = true)
    (hs : ∀ i x u, stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hc : fillCols (readsOf chain ft stored tree decls ds) bc = .ok c) :
    viewWordsBelowPrime ⟨roundsOf y.1, []⟩ = true ∧ ∀ x ∈ c, ∀ a ∈ x.2.2, a < fieldPrimeWord := by
  subst hd
  obtain ⟨hb1, hb2⟩ := (okViewW_split back bc).1 hb
  exact ⟨okViewW_of_yields _ _ _ _ (play_yields _ _ _ _ _ hp) hf hb1,
    fillCols_words _ _ _ (readsOf_words chain ft stored tree hs _ _) hb2 hc⟩

theorem storedWords_lt (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) :
    ∀ i x u, H.storedWords w₀ rc i x = some u → ∀ a ∈ u, a < fieldPrimeWord := by
  intro i x u hu a ha
  unfold Prover.storedWords at hu
  obtain ⟨l, _, rfl⟩ := Option.map_eq_some_iff.1 hu
  obtain ⟨z, _, rfl⟩ := List.mem_map.1 ha
  exact ofF_lt z

/-! ## 4 With no stored run to fall back on -/

/-- A prover's side is defined at every sub-protocol one of whose rounds declares an item other than
a root. -/
def halved (bs : List (Block S Cl)) (hs : List (Placed V W X)) : Bool :=
  bs.all fun b => (hs.any fun h => h.place == b.place) ||
    b.rounds.all fun d => (d.items.filter (· != .root)).isEmpty
/- `halved` at each of the three chains. -/
def halvedAll (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Bool :=
  halved F.first.blocksInOrder H.first && halved F.shared.blocksInOrder H.shared && halved F.second.blocksInOrder H.second

theorem itemsFall_nil : ∀ ss : List (Step W X), itemsFall ss [] =
    ss.all fun s => s.move.isSome || (s.decl.items.filter (· != .root)).isEmpty
  | [] => rfl
  | s :: ss => by
    have h : (([] : List Fmt.ItemValue).map itemOf == s.decl.items.filter (· != .root)) =
        (s.decl.items.filter (· != .root)).isEmpty := by
      cases (s.decl.items.filter (· != .root)) <;> rfl
    show ((s.move.isSome ||
      (([] : List Fmt.ItemValue).map itemOf == s.decl.items.filter (· != .root))) &&
        itemsFall ss []) = _
    rw [h, itemsFall_nil ss]
    rfl

theorem itemsFall_of_halved {B : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {bs : List (Block S Cl)}
    {hs : List (Placed V W X)} {ss : List (Step W X)}
    (h : chainSteps B rows look v bs hs = .ok ss) (h4 : halved bs hs = true) :
    itemsFall ss [] = true := by
  obtain ⟨-, h2⟩ := chainSteps_rows bs hs ss h
  rw [itemsFall_nil]
  have e : (ss.all fun s => s.move.isSome || (s.decl.items.filter (· != .root)).isEmpty) =
      (ss.map fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)).all
        fun z => z.2.2.2 || (z.1.items.filter (· != .root)).isEmpty := by
    rw [List.all_map]
    rfl
  rw [e, h2, List.all_eq_true]
  intro z hz
  obtain ⟨b, hb, hz⟩ := List.mem_flatMap.1 hz
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
  have hb4 := List.all_eq_true.1 h4 b hb
  rcases Bool.or_eq_true_iff.1 hb4 with h5 | h5
  · exact Bool.or_eq_true_iff.2 (Or.inl h5)
  · exact Bool.or_eq_true_iff.2 (Or.inr (List.all_eq_true.1 h5 y.1
      (List.of_mem_zip (a := y.1) (b := y.2) hy).1))

/-! ## 5 A run with no stored run to fall back on -/

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : Run} {U : Views}

theorem okViewW_nil : viewWordsBelowPrime ⟨[], []⟩ = true := rfl

/-- **Every word of a run's three views is below the prime.** -/
theorem run_words (hr : run F B H w₀ rc x c ρ none = .ok r) (hρ : ρ.due F = true) :
    viewWordsBelowPrime r.views.1 = true ∧ viewWordsBelowPrime r.views.2.1 = true ∧ viewWordsBelowPrime r.views.2.2 = true := by
  obtain ⟨R, r₁, r₂, r₃, c₁, c₂, c₃, hR, -, p1, -, p2, p3, f1, f2, f3, rfl⟩ := run_parts hr
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  simp only [Draws.due, Bool.and_eq_true] at hρ
  obtain ⟨⟨⟨d1', d2'⟩, d3'⟩, -⟩ := hρ
  have d1 := drawsFit_bare _ _ d1'
  have d2 := drawsFit_bare _ _ d2'
  have d3 := drawsFit_bare _ _ d3'
  obtain ⟨a1, b1⟩ := chain_words (steps_decl s1) p1 d1 okViewW_nil (storedWords_lt H w₀ rc) f1
  obtain ⟨a2, b2⟩ := chain_words (steps_decl s2) p2 d2 okViewW_nil (storedWords_lt H w₀ rc) f2
  obtain ⟨a3, b3⟩ := chain_words (steps_decl s3) p3 d3 okViewW_nil (storedWords_lt H w₀ rc) f3
  exact ⟨(okViewW_split _ _).2 ⟨okViewW_dropLast a1, b1⟩, (okViewW_split _ _).2 ⟨a2, b2⟩,
    (okViewW_split _ _).2 ⟨a3, b3⟩⟩

/-- **A run's three views pass all six tests of `fitsAll`.** -/
theorem run_fits (hr : run F B H w₀ rc x c ρ none = .ok r) (hρ : ρ.due F = true)
    (h4 : halvedAll F H = true) : fitsAll F r.views = true := by
  obtain ⟨w1, w2, w3⟩ := run_words hr hρ
  obtain ⟨R, r₁, r₂, r₃, c₁, c₂, c₃, hR, -, p1, hq, p2, p3, f1, f2, f3, rfl⟩ := run_parts hr
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  simp only [Draws.due, Bool.and_eq_true] at hρ
  obtain ⟨⟨⟨d1', d2'⟩, d3'⟩, -⟩ := hρ
  have d1 := drawsFit_bare _ _ d1'
  have d2 := drawsFit_bare _ _ d2'
  have d3 := drawsFit_bare _ _ d3'
  simp only [halvedAll, Bool.and_eq_true] at h4
  obtain ⟨⟨a1, a2⟩, a3⟩ := h4
  have k1 := chain_kept (steps_decl s1) p1 d1 (itemsFall_of_halved s1 a1) f1
  have k2 := chain_kept (steps_decl s2) p2 d2 (itemsFall_of_halved s2 a2) f2
  have k3 := chain_kept (steps_decl s3) p3 d3 (itemsFall_of_halved s3 a3) f3
  have e1 : withEmptySealRound ⟨(roundsOf r₁.1).dropLast, c₁⟩ = ⟨roundsOf r₁.1, c₁⟩ :=
    congrArg (fun rs => (⟨rs, c₁⟩ : Fmt.View)) (seal_back hq)
  simp only [fitsAll, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, ?_⟩, k2⟩, k3⟩
  show kept 0 F.roundsDeclaredByBlocks.1 (withEmptySealRound ⟨(roundsOf r₁.1).dropLast, c₁⟩) = true
  rw [e1]
  exact k1

/-- **On a run's views the description accepts if and only if the test on the instance passes and
`Decided` holds.** -/
theorem run_yes_iff (hr : run F B H w₀ rc x c ρ none = .ok r) (hp : F.planOk = true)
    (hρ : ρ.due F = true) (h4 : halvedAll F H = true) :
    F.run x r.views.1 r.views.2.1 r.views.2.2 = true ↔
      F.okStart x = true ∧ Decided F x r.views := by
  rw [run_iff_fits]
  exact ⟨fun h => ⟨h.2.1, h.2.2.2⟩, fun h => ⟨hp, h.1, run_fits hr hρ h4, h.2⟩⟩

end

/-! ## 6 A run that falls back on a stored run -/

theorem itemsFall_of_fit : ∀ (ss : List (Step W X)) (rs : List Fmt.RoundView),
    roundsFit (ss.map (·.decl)) rs = true → itemsFall ss rs = true
  | [], _, _ => rfl
  | _ :: _, [], h => by simp [roundsFit] at h
  | s :: ss, r :: rs, h => by
    have h' : roundsFit (s.decl :: ss.map (·.decl)) (r :: rs) = true := h
    simp only [roundsFit, Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨⟨⟨⟨a1, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, a8⟩ := h'
    show ((s.move.isSome || (r.vals.map itemOf == s.decl.items.filter (· != .root))) &&
      itemsFall ss rs) = true
    rw [a1, itemsFall_of_fit ss rs a8]
    simp

theorem itemsFall_seal (e : Fmt.Drawn) : ∀ (ss : List (Step W X)) (rs : List Fmt.RoundView),
    itemsFall ss (rs ++ [⟨[], e⟩]) = itemsFall ss rs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: ss, r :: rs => by
    show ((s.move.isSome || (r.vals.map itemOf == s.decl.items.filter (· != .root))) &&
      itemsFall ss (rs ++ [⟨[], e⟩])) =
        ((s.move.isSome || (r.vals.map itemOf == s.decl.items.filter (· != .root))) &&
          itemsFall ss rs)
    rw [itemsFall_seal e ss rs]

theorem drawsFit_of_fit : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true → viewWordsBelowPrime ⟨rs, []⟩ = true →
    drawsFit ds ((rs.map (·.drawn)).map bare) = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [roundsFit] at h
  | _ :: _, [], h, _ => by simp [roundsFit] at h
  | d :: ds, r :: rs, h, hw => by
    simp only [roundsFit, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨-, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := h
    simp only [viewWordsBelowPrime, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hw
    obtain ⟨⟨e1, -⟩, e2⟩ := hw
    have ih := drawsFit_of_fit ds rs a8 (by
      simp only [viewWordsBelowPrime, List.all_nil, Bool.and_true]
      exact e2)
    show (drawFit d (bare r.drawn) && drawsFit ds ((rs.map (·.drawn)).map bare)) = true
    rw [ih, Bool.and_true]
    simp only [drawFit, Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨⟨⟨a2, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, e1⟩, by simp [bare]⟩

theorem okViewW_sealed {R : List Fmt.RoundView} (h : viewWordsBelowPrime ⟨R, []⟩ = true) :
    viewWordsBelowPrime ⟨R ++ [⟨[], ⟨[], [], [], none⟩⟩], []⟩ = true := by
  have e : viewWordsBelowPrime ⟨R ++ [⟨[], ⟨[], [], [], none⟩⟩], []⟩ =
      (viewWordsBelowPrime ⟨R, []⟩ && viewWordsBelowPrime ⟨[⟨[], ⟨[], [], [], none⟩⟩], []⟩) := by
    simp only [viewWordsBelowPrime, List.all_append, List.all_nil, Bool.and_true]
  rw [e, h]
  rfl

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : Run} {U : Views}

/-- **If the stored run passes `fitsAll`, so do the views of a run that falls back on it.** -/
theorem run_fits_back (hr : run F B H w₀ rc x c ρ (some U) = .ok r) (hU : fitsAll F U = true) :
    fitsAll F r.views = true := by
  obtain ⟨R, r₁, r₂, r₃, c₁, c₂, c₃, hR, hsame, p1, hq, p2, p3, f1, f2, f3, rfl⟩ := run_parts hr
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  simp only [fitsAll, Bool.and_eq_true] at hU
  obtain ⟨⟨⟨⟨⟨u1, u2⟩, u3⟩, k1⟩, k2⟩, k3⟩ := hU
  have hsame' : ρ.same (drawsOf U) = true := hsame
  simp only [Draws.same, drawsOf, Bool.and_eq_true, beq_iff_eq] at hsame'
  obtain ⟨⟨e1, e2⟩, e3⟩ := hsame'
  obtain ⟨g1, -⟩ := (kept_iff 0 F.roundsDeclaredByBlocks.1 (withEmptySealRound U.1).rounds (withEmptySealRound U.1).opened).1 k1
  obtain ⟨g2, -⟩ := (kept_iff 0 F.roundsDeclaredByBlocks.2.1 U.2.1.rounds U.2.1.opened).1 k2
  obtain ⟨g3, -⟩ := (kept_iff F.lastChainFirstTreeNumber F.roundsDeclaredByBlocks.2.2 U.2.2.rounds U.2.2.opened).1 k3
  have v1 := ((okViewW_split U.1.rounds U.1.opened).1 u1).1
  have v2 := ((okViewW_split U.2.1.rounds U.2.1.opened).1 u2).1
  have v3 := ((okViewW_split U.2.2.rounds U.2.2.opened).1 u3).1
  have d1 : drawsFit F.roundsDeclaredByBlocks.1 (ρ.first.map bare) = true := by
    have h0 := drawsFit_of_fit F.roundsDeclaredByBlocks.1 (U.1.rounds ++ [⟨[], ⟨[], [], [], none⟩⟩]) g1
      (okViewW_sealed v1)
    rw [e1]
    rw [List.map_append] at h0
    exact h0
  have d2 : drawsFit F.roundsDeclaredByBlocks.2.1 (ρ.shared.map bare) = true := by
    rw [e2]
    exact drawsFit_of_fit _ _ g2 v2
  have d3 : drawsFit F.roundsDeclaredByBlocks.2.2 (ρ.second.map bare) = true := by
    rw [e3]
    exact drawsFit_of_fit _ _ g3 v3
  have i1 : itemsFall R.first U.1.rounds = true := by
    rw [← itemsFall_seal ⟨[], [], [], none⟩]
    exact itemsFall_of_fit _ _ (by rw [steps_decl s1]; exact g1)
  have i2 : itemsFall R.shared U.2.1.rounds = true :=
    itemsFall_of_fit _ _ (by rw [steps_decl s2]; exact g2)
  have i3 : itemsFall R.second U.2.2.rounds = true :=
    itemsFall_of_fit _ _ (by rw [steps_decl s3]; exact g3)
  have n1 := chain_kept (steps_decl s1) p1 d1 i1 f1
  have n2 := chain_kept (steps_decl s2) p2 d2 i2 f2
  have n3 := chain_kept (steps_decl s3) p3 d3 i3 f3
  obtain ⟨a1, b1⟩ := chain_words (steps_decl s1) p1 d1 u1 (storedWords_lt H w₀ rc) f1
  obtain ⟨a2, b2⟩ := chain_words (steps_decl s2) p2 d2 u2 (storedWords_lt H w₀ rc) f2
  obtain ⟨a3, b3⟩ := chain_words (steps_decl s3) p3 d3 u3 (storedWords_lt H w₀ rc) f3
  have q1 : withEmptySealRound ⟨(roundsOf r₁.1).dropLast, c₁⟩ = ⟨roundsOf r₁.1, c₁⟩ :=
    congrArg (fun rs => (⟨rs, c₁⟩ : Fmt.View)) (seal_back hq)
  simp only [fitsAll, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨(okViewW_split _ _).2 ⟨okViewW_dropLast a1, b1⟩, (okViewW_split _ _).2 ⟨a2, b2⟩⟩,
    (okViewW_split _ _).2 ⟨a3, b3⟩⟩, ?_⟩, n2⟩, n3⟩
  show kept 0 F.roundsDeclaredByBlocks.1 (withEmptySealRound ⟨(roundsOf r₁.1).dropLast, c₁⟩) = true
  rw [q1]
  exact n1

/-- The counterpart of `run_yes_iff`. -/
theorem run_yes_iff_back (hr : run F B H w₀ rc x c ρ (some U) = .ok r) (hp : F.planOk = true)
    (hU : fitsAll F U = true) :
    F.run x r.views.1 r.views.2.1 r.views.2.2 = true ↔
      F.okStart x = true ∧ Decided F x r.views := by
  rw [run_iff_fits]
  exact ⟨fun h => ⟨h.2.1, h.2.2.2⟩, fun h => ⟨hp, h.1, run_fits_back hr hU, h.2⟩⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.unfit_ok
#print axioms ProofFile.Honest.ready_ok
#print axioms ProofFile.Honest.ends_ok
#print axioms ProofFile.Honest.run_parts
#print axioms ProofFile.Honest.seal_back
#print axioms ProofFile.Honest.rows_decl
#print axioms ProofFile.Honest.steps_decl
#print axioms ProofFile.Honest.yields_drawn
#print axioms ProofFile.Honest.chain_kept
#print axioms ProofFile.Honest.okViewW_split
#print axioms ProofFile.Honest.okViewW_dropLast
#print axioms ProofFile.Honest.chain_words
#print axioms ProofFile.Honest.storedWords_lt
#print axioms ProofFile.Honest.itemsFall_nil
#print axioms ProofFile.Honest.itemsFall_of_halved
#print axioms ProofFile.Honest.okViewW_nil
#print axioms ProofFile.Honest.run_words
#print axioms ProofFile.Honest.run_fits
#print axioms ProofFile.Honest.run_yes_iff
#print axioms ProofFile.Honest.itemsFall_of_fit
#print axioms ProofFile.Honest.itemsFall_seal
#print axioms ProofFile.Honest.drawsFit_of_fit
#print axioms ProofFile.Honest.okViewW_sealed
#print axioms ProofFile.Honest.run_fits_back
#print axioms ProofFile.Honest.run_yes_iff_back
