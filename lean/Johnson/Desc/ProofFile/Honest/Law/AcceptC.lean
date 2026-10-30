-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/AcceptC.lean: the rule for a file's acceptance, over `runC`
(Honest/Walk.lean): from the conditions on the sub-protocols to the description's acceptance. This
is the lemma `runC_accepts`. If `runC` has returned a run, `ready` has returned, and the executable
tests `planOk`, `okStart` and `Draws.due` pass and `silentAt` is `none`; if the two conditions hold
at every sub-protocol of the three flat lists (`PlaysOn`, `SaysYes`: Honest/Law/ThreadC.lean), from
the invariant before it to the one after it; if the invariants hold at the two starts, give the
second chain's start and go through it, and give the last test's acceptance; and if no fall fires
along that run: then no sub-protocol has rejected, and the description accepts the run's views.

What this is. A conditional lemma on this folder's own functions, pointwise: at one input, one run's
coins and one list of challenges. Its hypotheses are proved here of no description. Its conclusion
is that `FileDescription.run` accepts, at a parameter F. That is one test of the verdict of the file's
interactive oracle reduction (`FileDescription.toIOR`), which `FileDescription.out_eq`
(Johnson/Desc/BlockSlot.lean) unfolds into nine tests. It is not a verifier's acceptance: the tests
on the proof-of-work bits, on the completeness of the draws, on the stored string's positions and on
the three rounds without a challenge are not reached. It is none of the library's goals, and it says
nothing of how likely a stop or a fall is.

  1  `fallFree`   no fall fires along a chain's view: by the sub-protocols' numbers, along the
     verifier's own steps
  2  `settle_cols`, `walk_grows`, `bind_grows`   a walk only appends to what it has produced (the
     columns' half stands also as `settle_cols_prefix`, `walk_cols_prefix`: Honest/WalkOpened.lean)
  3  `chain_accepts`   one chain
  4  `ColsLt`, `settle_lt`, `walk_lt`, `start_lt`   the columns' words
  5  `runC_accepts`   the file

The rule can hold vacuously in four ways, and nothing here excludes any of them.
  * Invariants that cannot be entered: they hold at no start.
  * A fall that fires too often. The falls are free parameters. One that always fires makes
    `SaysYes` hold vacuously, and "no fall fires" fails: the rule says nothing. One that fires
    exactly where the sub-protocol's own step will reject makes `SaysYes` hold trivially, and "no
    fall fires" then is "no sub-protocol rejects": a hypothesis that contains the conclusion. At a
    sub-protocol without a round that is easy: its step reads the state alone, and so does its fall.
  * A prover that stops at every list of challenges: `silentAt` is never `none`.
  * A book at which `ready` returns an error at every coin.
What a fall costs is its share (`Fall.share`, Honest/Side.lean): a stated number, which nothing
compares with the test. Whoever writes a fall names the verifier's own tests that it excuses.

Limits.
  * That `runC` returns is a hypothesis (Honest/Law/RunsFile.lean has a rule for it): so neither
    `sealPlain` nor `PlanServes` is assumed here.
  * Nothing is said on how likely a stop or a fall is.
  * The invariants at the starts are asked at the states as `ChainProgress.start` lays them: the field
    `opened` is `some []` at the first and the shared chain, and at the second chain, where the two
    ends' fields hold columns, these joined.
  * `PlaysOn` and `SaysYes` are asked at every state that the invariant allows, at every value of
    the field `opened` too: at a prover with a part that reads the columns and errs at `none` (its
    duty: Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant that lets `none` through
    before that part's sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits).
  * Hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round, and as many
    challenges as rounds): `chain_accepts`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunsFile
import Johnson.Desc.ProofFile.Honest.Law.RunC
import Johnson.Desc.ProofFile.Honest.Law.WalkMid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W Y Pb W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 No fall fires -/

/-- **No fall fires along a chain's rounds and columns.** `fl`: the sub-protocols' falls, by the
sub-protocol's number, from 0. Each is asked at the verifier's state before its sub-protocol and at
the sub-protocol's own challenges; the next one, after the sub-protocol's own step has accepted. A
definition, meant as a hypothesis. The falls are free parameters: at falls that fire where the
sub-protocols' own steps reject it says that no sub-protocol rejects (this file's head, the second
way). -/
def fallFree (ft : Nat) : List (Block S Cl) → (Nat → S → List Fmt.Drawn → Option String) → S →
    List Fmt.RoundView → List OpenedColumn → Prop
  | [], _, _, _, _ => True
  | b :: l, fl, s, rs, cols =>
    fl 0 s ((rs.take b.rounds.length).map (·.drawn)) = none ∧
      ∀ s' k, b.step ft s (rs.take b.rounds.length) cols = .ok (s', k) →
        fallFree ft l (fun j => fl (j + 1)) s' (rs.drop b.rounds.length) (cols.drop k)

/-! ## 2 A walk only appends to what it has produced -/

theorem settle_cols (L : Lay) : ∀ (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y),
    ChainProgress.settle L todo z = .ok z' → ∃ cs, z'.cols = z.cols ++ cs
  | [], z, z', hs => by
    simp only [ChainProgress.settle] at hs
    cases hs
    exact ⟨[], (List.append_nil _).symm⟩
  | b :: t, z, z', hs => by
    by_cases hlt : z.own.length < b.rounds.length
    · rw [settle_wait L b t z hlt] at hs
      cases hs
      exact ⟨[], (List.append_nil _).symm⟩
    · obtain ⟨cols, -, hs'⟩ := settle_ask_ok hlt hs
      have g := settle_cols L t _ z' hs'
      obtain ⟨cs, e⟩ := g
      exact ⟨cols ++ cs, by rw [e]; exact List.append_assoc _ _ _⟩

theorem walk_grows (L : Lay) : ∀ (l : List (Step W Y)) (d : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y), walk L l d z = .ok z' →
    ∃ ps cs, z'.laid = z.laid ++ ps ∧ z'.cols = z.cols ++ cs
  | [], [], z, z', h => by
    rw [walk_nil_ok h]
    exact ⟨[], [], (List.append_nil _).symm, (List.append_nil _).symm⟩
  | [], _ :: _, _, _, h => by simp [walk] at h
  | _ :: _, [], _, _, h => by simp [walk] at h
  | s :: l, d₀ :: d, z, z', h => by
    obtain ⟨x, z₁, -, hz, hw⟩ := walk_cons_ok h
    obtain ⟨ps, cs, e1, e2⟩ := walk_grows L l d z₁ z' hw
    obtain ⟨m', -, hs⟩ := heard_ok hz
    have g := settle_cols L z.todo _ z₁ hs
    obtain ⟨cs₁, e3⟩ := g
    have e3' : z₁.cols = z.cols ++ cs₁ := e3
    refine ⟨⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d₀⟩ :: ps, cs₁ ++ cs, ?_,
      ?_⟩
    · rw [e1, heard_laid hz, List.append_assoc]
      rfl
    · rw [e2, e3', List.append_assoc]

theorem bind_grows (L : Lay) {t : List (Block S Cl)} {l : List (Step W Y)} {d : List Fmt.Drawn}
    {z z' : ChainProgress S Cl W Y} (h : (ChainProgress.settle L t z).bind (walk L l d) = .ok z') :
    ∃ ps cs, z'.laid = z.laid ++ ps ∧ z'.cols = z.cols ++ cs := by
  obtain ⟨a, h1, h2⟩ := exBind_ok h
  obtain ⟨cs₁, e1⟩ := settle_cols L t z a h1
  have e0 := settle_laid L t z a h1
  obtain ⟨ps, cs, e2, e3⟩ := walk_grows L l d a z' h2
  exact ⟨ps, cs₁ ++ cs, by rw [e2, e0], by rw [e3, e1, List.append_assoc]⟩

/-! ## 3 One chain -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **One chain.** Where its walk has returned and no fall fires along what it has produced, no
sub-protocol has rejected: at its end the walk holds the prover's run, the verifier's state and the
last invariant. Its other hypotheses: the two conditions at every sub-protocol (`PlaysOn`,
`SaysYes`); the first invariant at the walk's state; no stop (`chainStopAt … = none`); `chainSteps`
returns at k; the `Lay`'s look-up of a tree is that of `envOf`; a round without a move is under the
part 0; no round of the next sub-protocol has been produced (`z.own = []`); v is what the face shows
of the state's input. -/
theorem chain_accepts (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (k : Coins Bk) (v : Option V) :
    ∀ (bs : List (Block S Cl)) (I : Nat → Coins Bk → S → Mid W Y → Env → Prop)
      (fl : Nat → S → List Fmt.Drawn → Option String),
    (∀ j b, bs[j]? = some b → PlaysOn φ Bk L.chain L.firstTree hs b (I j) (I (j + 1))) →
    (∀ j b, bs[j]? = some b → SaysYes φ Bk L.chain L.firstTree hs b (fl j) (I j)) →
    ∀ (l : List (Step W Y)) (z z' : ChainProgress S Cl W Y) (ds : List Fmt.Drawn) (s : S) (m : Mid W Y),
    (∀ u ∈ l, u.move.isSome = false → u.addr.part = 0) → z.own = [] → z.mid = some m →
    z.ver = some s → φ.sees m.st.input = v → I 0 k s m (envOf L.stored taken z.laid) →
    chainStopAt v bs hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v bs hs = .ok l →
    drawsFit (bs.flatMap (·.rounds)) ds = true →
    (ChainProgress.settle L bs z).bind (walk L l ds) = .ok z' →
    fallFree L.firstTree bs fl s ((roundsOf z'.laid).drop z.laid.length)
      (z'.cols.drop z.cols.length) →
    ∃ s' m', z'.ver = some s' ∧ z'.mid = some m' ∧
      I bs.length k s' m' (envOf L.stored taken z'.laid)
  | [], I, fl, _, _, l, z, z', ds, s, m, _, ho, hm, hv, _, h0, _, hl, hd, hz, _ => by
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [drawsFit] at hd
    subst hds
    simp only [chainSteps] at hl
    cases hl
    have hz' : (Except.ok { z with todo := [] } : Except Refusal (ChainProgress S Cl W Y)) = .ok z' := hz
    cases hz'
    exact ⟨s, m, hv, hm, h0⟩
  | b :: t, I, fl, h, hy, l, z, z', ds, s, m, hp0, ho, hm, hv, hsee, h0, hst, hl, hd, hz, hff => by
    have hl' : chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v ([b] ++ t) hs = .ok l := hl
    rw [chainSteps_append] at hl'
    obtain ⟨l₁, hl₁, hl'⟩ := exBind_ok hl'
    obtain ⟨l₂, hl₂, rfl⟩ := exMap_ok hl'
    rw [List.flatMap_cons, drawsFit_append, Bool.and_eq_true] at hd
    obtain ⟨hd₁, hd₂⟩ := hd
    have hdecl : l₁.map (·.decl) = b.rounds := by
      have e := steps_decl hl₁
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
      exact e
    have hn : l₁.length = b.rounds.length := by rw [← hdecl, List.length_map]
    have hlen₁ : (ds.take b.rounds.length).length = l₁.length := by
      rw [drawsFit_length _ _ hd₁, hn]
    have hW : walk L (l₁ ++ l₂) ds = fun a : ChainProgress S Cl W Y =>
        (walk L l₁ (ds.take b.rounds.length) a).bind (walk L l₂ (ds.drop b.rounds.length)) := by
      funext a
      have e' := walk_append L l₂ (ds.drop b.rounds.length) l₁ (ds.take b.rounds.length) a hlen₁
      rw [List.take_append_drop] at e'
      exact e'
    rw [hW] at hz
    have hst' : ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt v g.parts m.loc (ds.take b.rounds.length)).or
          (chainStopAt v t hs (m.loc ++ ds.take b.rounds.length)
            (ds.drop b.rounds.length)) = none := hst
    obtain ⟨hs₁, hs₂⟩ := or_none hst'
    have hs₁' : chainStopAt v [b] hs m.loc (ds.take b.rounds.length) = none := by
      show ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt v g.parts m.loc
          ((ds.take b.rounds.length).take b.rounds.length)).or (none : Option Why) = none
      rw [List.take_take, Nat.min_self, hs₁]
      rfl
    obtain ⟨y, cols, p₁, f₁, hB⟩ := h 0 b (by simp) k s m _ (ds.take b.rounds.length) l₁ h0 hd₁
      (by rw [hsee]; exact hs₁') (by rw [hsee]; exact hl₁)
    obtain ⟨e1, e2, -⟩ := play_mid _ _ _ _ _ p₁
    have Y₁ := play_yields _ _ _ _ _ p₁
    have hyl : y.1.length = b.rounds.length := by rw [yields_length _ _ _ _ Y₁, hn]
    have hdr' : (roundsOf y.1).map (·.drawn) = ds.take b.rounds.length := yields_drawn _ _ _ _ Y₁
    have hdr : y.1.map (·.drawn) = ds.take b.rounds.length := by
      have e := hdr'
      unfold roundsOf at e
      rw [List.map_map] at e
      exact e
    have hE : (envOf L.stored taken z.laid).add y.1 = envOf L.stored taken (z.laid ++ y.1) :=
      envOf_add _ _ _ _
    have f₁' : fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
        (y.1.map (·.drawn))) [] = .ok cols := by
      rw [hdr, hL]
      rw [hE] at f₁
      exact f₁
    have hlay : lays l₁ (ds.take b.rounds.length) z.mid = .ok (y.1, some y.2) := by
      rw [hm]
      exact lays_of_play _ _ _ _ (fun u hu => hp0 u (List.mem_append_left _ hu)) p₁
    rw [member_laid L b t z l₁ _ (y.1, some y.2) cols ho hn hlay f₁'] at hz
    obtain ⟨ps, cs, g1, g2⟩ := bind_grows L hz
    have g1' : z'.laid = z.laid ++ y.1 ++ ps := g1
    have g2' : z'.cols = z.cols ++ cols ++ cs := g2
    have r0 : (roundsOf z'.laid).drop z.laid.length = roundsOf y.1 ++ roundsOf ps := by
      rw [g1', roundsOf_append, roundsOf_append, List.append_assoc,
        List.drop_left' (roundsOf_length _)]
    have c0 : z'.cols.drop z.cols.length = cols ++ cs := by
      rw [g2', List.append_assoc, List.drop_left' rfl]
    rw [r0, c0] at hff
    have hrn : (roundsOf y.1).length = b.rounds.length := by rw [roundsOf_length, hyl]
    obtain ⟨ff1, ff2⟩ := hff
    rw [List.take_left' hrn] at ff1 ff2
    rw [List.drop_left' hrn] at ff2
    rw [hdr'] at ff1
    obtain ⟨s', n', hstep⟩ := hy 0 b (by simp) k s m _ (ds.take b.rounds.length) l₁ y cols h0 hd₁
      (by rw [hsee]; exact hs₁') ff1 (by rw [hsee]; exact hl₁) p₁ f₁
    have hwant : (b.want L.firstTree (roundsOf y.1)).length = cols.length := by
      have e := congrArg List.length (fillCols_kept _ _ _ f₁)
      rw [readsOf_wants, List.length_map] at e
      unfold Block.want
      rw [hdr']
      exact e.symm
    have hn' : n' = cols.length := by
      have e := ((step_iff L.firstTree b s s' _ _ n').1 hstep).2.2
      rw [e]
      exact hwant
    have hstep' : b.step L.firstTree s (roundsOf y.1) (cols ++ cs) = .ok (s', n') := by
      rw [step_more L.firstTree b s _ cols cs (Nat.le_of_eq hwant)]
      exact hstep
    have ff3 := ff2 s' n' hstep'
    rw [hn', List.drop_left' rfl] at ff3
    have hj : judge L.firstTree b s (roundsOf y.1) cols = some s' := by
      unfold judge
      rw [hstep]
      rfl
    have hB' := hB s' n' hstep
    rw [hE] at hB'
    have hver : (z.askedO L b (y.1, some y.2) cols).ver = some s' := by
      show (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols) = some s'
      rw [hv]
      exact hj
    have hmid : (z.askedO L b (y.1, some y.2) cols).mid = some (y.2.took cols) := by
      show (if (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols).isSome
        then some (y.2.took cols) else none) = some (y.2.took cols)
      rw [hv]
      show (if (judge L.firstTree b s (roundsOf y.1) cols).isSome then some (y.2.took cols)
        else none) = _
      rw [hj]
      rfl
    refine chain_accepts L taken hL k v t (fun j => I (j + 1)) (fun j => fl (j + 1))
      (fun j b' hj' => h (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj'))
      (fun j b' hj' => hy (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj')) l₂
      (z.askedO L b (y.1, some y.2) cols) z' (ds.drop b.rounds.length) s' (y.2.took cols)
      (fun u hu => hp0 u (List.mem_append_right _ hu)) rfl hmid hver
      (by
        show φ.sees y.2.st.input = v
        rw [e1]
        exact hsee)
      hB'
      (by
        show chainStopAt v t hs y.2.loc _ = none
        rw [e2]
        exact hs₂)
      hl₂ hd₂ hz ?_
    show fallFree L.firstTree t (fun j => fl (j + 1)) s'
      ((roundsOf z'.laid).drop (z.laid ++ y.1).length) (z'.cols.drop (z.cols ++ cols).length)
    have r1 : (roundsOf z'.laid).drop (z.laid ++ y.1).length = roundsOf ps := by
      rw [g1', roundsOf_append, List.drop_left' (roundsOf_length _)]
    have c1 : z'.cols.drop (z.cols ++ cols).length = cs := by
      rw [g2', List.drop_left' rfl]
    rw [r1, c1]
    exact ff3

end

/-! ## 4 The columns' words -/

/-- Every word of every column filled is below the prime. -/
def ColsLt (z : ChainProgress S Cl W Y) : Prop := ∀ x ∈ z.cols, ∀ a ∈ x.2.2, a < fieldPrimeWord

theorem settle_lt (L : Lay) (hs : ∀ i x u, L.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord) :
    ∀ (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y), ColsLt z →
    ChainProgress.settle L todo z = .ok z' → ColsLt z'
  | [], z, z', h, hz => by
    simp only [ChainProgress.settle] at hz
    cases hz
    exact h
  | b :: t, z, z', h, hz => by
    by_cases hlt : z.own.length < b.rounds.length
    · rw [settle_wait L b t z hlt] at hz
      cases hz
      exact h
    · obtain ⟨cols, hc, hz'⟩ := settle_ask_ok hlt hz
      have hcl := fillCols_words _ _ _ (readsOf_words L.chain L.firstTree L.stored
        (L.tree z.laid) hs _ _) (fun x hx => by cases hx) hc
      have key := fun (z₁ : ChainProgress S Cl W Y) (g1 : ChainProgress.settle L t z₁ = .ok z') (g2 : ColsLt z₁) =>
        settle_lt L hs t z₁ z' g2 g1
      refine key _ hz' ?_
      intro x hx
      have hx' : x ∈ z.cols ++ cols := hx
      rcases List.mem_append.1 hx' with g | g
      · exact h x g
      · exact hcl x g

theorem walk_lt (L : Lay) (hs : ∀ i x u, L.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord) :
    ∀ (l : List (Step W Y)) (d : List Fmt.Drawn) (z z' : ChainProgress S Cl W Y), ColsLt z →
    walk L l d z = .ok z' → ColsLt z'
  | [], [], z, z', h, hw => by
    rw [walk_nil_ok hw]
    exact h
  | [], _ :: _, _, _, _, hw => by simp [walk] at hw
  | _ :: _, [], _, _, _, hw => by simp [walk] at hw
  | s :: l, d₀ :: d, z, z', h, hw => by
    obtain ⟨x, z₁, -, hz, hw₁⟩ := walk_cons_ok hw
    obtain ⟨m', -, hs'⟩ := heard_ok hz
    have key := fun (u : ChainProgress S Cl W Y) (g1 : ChainProgress.settle L z.todo u = .ok z₁) (g2 : ColsLt u) =>
      settle_lt L hs z.todo u z₁ g2 g1
    exact walk_lt L hs l d z₁ z' (key _ hs' h) hw₁

theorem start_lt (L : Lay) (hs : ∀ i x u, L.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (bs : List (Block S Cl)) (mo : Option (Mid W Y)) (v : Option S) {a : ChainProgress S Cl W Y}
    {front : List OpenedColumn} (h : ChainProgress.start L bs mo v front = .ok a) : ColsLt a := by
  unfold ChainProgress.start at h
  have key := fun (u : ChainProgress S Cl W Y) (g1 : ChainProgress.settle L bs u = .ok a) (g2 : ColsLt u) =>
    settle_lt L hs bs u a g2 g1
  exact key _ h (fun x hx => by cases hx)

/-! ## 5 The file -/

/-- **The rule for a file's acceptance: from the conditions on the sub-protocols to the
description's acceptance.** A conditional lemma on this folder's own functions, pointwise. Its
conclusion is that `FileDescription.run` accepts, one of the nine tests of the verdict of the file's
interactive oracle reduction: not a verifier's acceptance. It is none of the library's goals. -/
theorem runC_accepts {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hp : F.planOk = true) (hx : F.okStart x = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none)
    (I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (fl₁ : Nat → F.S₁ → List Fmt.Drawn → Option String)
    (fl₂ : Nat → F.S₂ → List Fmt.Drawn → Option String)
    (fl₃ : Nat → F.S₃ → List Fmt.Drawn → Option String)
    (h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1)))
    (h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      PlaysOn .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1)))
    (h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1)))
    (y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → SaysYes .own Bk 0 0 H.first b (fl₁ j) (I₁ j))
    (y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b → SaysYes .shared Bk 1 0 H.shared b (fl₂ j) (I₂ j))
    (y₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYes .own Bk 2 F.lastChainFirstTreeNumber H.second b (fl₃ j) (I₃ j))
    (a₁ : I₁ 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₂ : I₂ 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
        I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂))
    (fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
      F.fin x e₁ e₂ e₃ = true)
    (n₁ : fallFree 0 F.first.blocksInOrder fl₁ (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      r.run.views.1.opened)
    (n₂ : fallFree 0 F.shared.blocksInOrder fl₂ (F.start₂ (F.pub x)) r.run.views.2.1.rounds
      r.run.views.2.1.opened)
    (n₃ : ∀ e₁ e₂ s₃, r.ends.1 = some e₁ → r.ends.2.1 = some e₂ →
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      fallFree F.lastChainFirstTreeNumber F.second.blocksInOrder fl₃ s₃ r.run.views.2.2.rounds r.run.views.2.2.opened) :
    (∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨-, tr, htr, hown, hcom, s1, s2, s3⟩ := ready_ok hR
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hρ
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, -⟩ := hρ
  unfold silentAt at hsil
  rw [htr] at hsil
  have hsil' : (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder
      H.first [] ρ.first).or
      ((chainStopAt (Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder
        H.shared [] ρ.shared).or
        (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second
          ρ.first ρ.second)) = none := hsil
  obtain ⟨t1, t23⟩ := or_none hsil'
  obtain ⟨t2, t3⟩ := or_none t23
  rw [← hown] at t1 t3
  rw [← hcom] at t2
  have hyes := runC_yes_iff h
  obtain ⟨R', b₁, z₁, b₂, z₂, b₃, z₃, hR', hb₁, hw₁, hq, hb₂, hw₂, hb₃, hw₃, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) ps [] []).1).symm
  have hseal := seal_back hq
  have hst := storedWords_lt H w₀ rc
  -- the first chain
  have X₁ : (ChainProgress.settle ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
      ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
        F.first.blocksInOrder, []⟩).bind
      (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first) = .ok z₁ := by
    have e : ChainProgress.settle ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
        ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
          F.first.blocksInOrder, []⟩ = .ok b₁ := hb₁
    rw [e]
    exact hw₁
  have n₁' : fallFree 0 F.first.blocksInOrder fl₁ (F.start₁ (F.pub x)) (roundsOf z₁.laid) z₁.cols := by
    have e : (withEmptySealRound (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩ : Fmt.View)).rounds =
        roundsOf z₁.laid := hseal
    have n := n₁
    rw [show (withEmptySealRound (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩ : Fmt.View)).rounds =
      roundsOf z₁.laid from e] at n
    exact n
  obtain ⟨e₁, m₁, v1, q1, i1⟩ := chain_accepts (φ := Face.own) (hs := H.first)
    ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.own.sees R.own)
    F.first.blocksInOrder I₁ fl₁ h₁ y₁ R.first _ z₁ ρ.first (F.start₁ (F.pub x))
    { R.start₁ H with opened := some [] }
    (steps_part0 _ _ s1) rfl rfl rfl rfl a₁ t1 s1 d1 X₁ n₁'
  -- the shared chain
  have X₂ : (ChainProgress.settle ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
      ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
        F.shared.blocksInOrder, []⟩).bind
      (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared) = .ok z₂ := by
    have e : ChainProgress.settle ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
        ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
          F.shared.blocksInOrder, []⟩ = .ok b₂ := hb₂
    rw [e]
    exact hw₂
  obtain ⟨e₂, m₂, v2, q2, i2⟩ := chain_accepts (φ := Face.shared) (hs := H.shared)
    ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.shared.sees R.common)
    F.shared.blocksInOrder I₂ fl₂ h₂ y₂ R.shared _ z₂ ρ.shared (F.start₂ (F.pub x))
    { R.start₂ H with opened := some [] }
    (steps_part0 _ _ s2) rfl rfl rfl rfl a₂ t2 s2 d2 X₂ n₂
  -- the second chain's start
  have inv₁ : z₁.Inv [] := walk_inv _ [] _ _ b₁ z₁ (start_inv hb₁) hw₁
  have inv₂ : z₂.Inv [] := walk_inv _ [] _ _ b₂ z₂ (start_inv hb₂) hw₂
  obtain ⟨s₃, hs₃, i0⟩ := a₃ _ _ _ _ _ _ z₁.cols z₂.cols i1 i2 (inv₁ m₁ q1) (inv₂ m₂ q2)
  rw [envThird_eq] at i0
  have hdoor : door₃ F x z₁.ver z₂.ver = some s₃ := by
    rw [v1, v2]
    show (F.start₃ (F.pub x) e₁ e₂).toOption = some s₃
    rw [hs₃]
    rfl
  have l1 : m₁.loc = ρ.first := (walk_mid hb₁ hw₁ q1).2.1
  -- the second chain
  have hL₃ : ∀ ps, treeThird z₁.laid z₂.laid ps =
      (envOf (H.storedWords w₀ rc) (taken₃ z₁.laid z₂.laid) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) z₁.laid z₂.laid ps).2).symm
  have X₃ : (ChainProgress.settle ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
      F.second.blocksInOrder
      ⟨some { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) }, some s₃, none, [], [],
        [], F.second.blocksInOrder, []⟩).bind
      (walk ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ R.second
        ρ.second) = .ok z₃ := by
    have e := hb₃
    rw [q1, q2, hdoor] at e
    have e' : ChainProgress.settle ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
        F.second.blocksInOrder
        ⟨some { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) }, some s₃, none, [], [],
          [], F.second.blocksInOrder, []⟩ = .ok b₃ := e
    rw [e']
    exact hw₃
  obtain ⟨e₃, m₃, v3, -, i3⟩ := chain_accepts (φ := Face.own) (hs := H.second)
    ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ (taken₃ z₁.laid z₂.laid) hL₃
    k (Face.own.sees R.own) F.second.blocksInOrder I₃ fl₃ h₃ y₃ R.second _ z₃ ρ.second s₃
    { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) } (steps_part0 _ _ s3) rfl rfl rfl
    rfl i0
    (by
      show chainStopAt (Face.own.sees R.own) F.second.blocksInOrder H.second m₁.loc ρ.second = none
      rw [l1]
      exact t3)
    s3 d3 X₃ (n₃ e₁ e₂ s₃ v1 v2 hs₃)
  have hends : ((z₁.ver, z₂.ver, z₃.ver) : Option F.S₁ × Option F.S₂ × Option F.S₃) =
      (some e₁, some e₂, some e₃) := by rw [v1, v2, v3]
  refine ⟨⟨e₁, e₂, e₃, hends⟩, hyes.2 ⟨hp, hx, ?_, ?_, ?_, e₁, e₂, e₃, hends,
    fin _ _ _ _ _ _ _ _ _ i1 i2 i3⟩⟩
  · exact (okViewW_split _ _).2 ⟨okViewW_dropLast (walk_said _ _ _ b₁ z₁ (drawsFit_elems _ _ d1)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₁)).trans rfl) hw₁),
      walk_lt _ hst _ _ b₁ z₁ (start_lt _ hst _ _ _ hb₁) hw₁⟩
  · exact (okViewW_split _ _).2 ⟨walk_said _ _ _ b₂ z₂ (drawsFit_elems _ _ d2)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₂)).trans rfl) hw₂,
      walk_lt _ hst _ _ b₂ z₂ (start_lt _ hst _ _ _ hb₂) hw₂⟩
  · exact (okViewW_split _ _).2 ⟨walk_said _ _ _ b₃ z₃ (drawsFit_elems _ _ d3)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₃)).trans rfl) hw₃,
      walk_lt _ hst _ _ b₃ z₃ (start_lt _ hst _ _ _ hb₃) hw₃⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.settle_cols
#print axioms ProofFile.Honest.walk_grows
#print axioms ProofFile.Honest.bind_grows
#print axioms ProofFile.Honest.chain_accepts
#print axioms ProofFile.Honest.settle_lt
#print axioms ProofFile.Honest.walk_lt
#print axioms ProofFile.Honest.start_lt
#print axioms ProofFile.Honest.runC_accepts
#print axioms ProofFile.Honest.fallFree
#print axioms ProofFile.Honest.ColsLt
