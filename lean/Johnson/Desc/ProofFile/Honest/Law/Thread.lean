-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Thread.lean: from a condition on each sub-protocol of a
description's three flat lists to a whole run of `run` (Honest/Frame.lean) that goes through, with
every sub-protocol's decision, the second chain's start and the last test accepting. The main lemma
is `run_of_passes`. A proof file has three chains, run in this order: the first (number 0), the
shared (1) and the second (2).

What these are. Conditional lemmas on this folder's own functions. They are pointwise: at one input,
one run's coins and one list of challenges. Their conclusion is that `run` returns and `Decided`
(Honest/Law/Kept.lean) holds of its views. That is a statement on the parts of `FileDescription.run`, not
on a verifier's acceptance: the tests on the proof-of-work bits, on the completeness of the draws,
on the stored string's positions and on the three rounds without a challenge are not reached. Their
hypotheses (the invariants I₁, I₂, I₃, the condition at every sub-protocol, the conditions where the
chains begin and meet) are proved here of no description. They are none of the library's goals, and
no goal follows from them without what is listed under Limits.

  1  `Passes`   the condition on one sub-protocol, with a prover's side or without: a definition,
     meant as a hypothesis; `Passes.mono`: the condition still holds with a stronger A and a weaker
     B; `Passes.family`: from a family of such conditions, the one that the state before the
     sub-protocol chooses
  2  `bareSteps`, `steps_one_none`, `steps_one_half`, `play_bare_ok`   the `Step`s that `chainSteps`
     prepares for one sub-protocol
  3  `passes_of_bare`   a sub-protocol without a prover's side, with rounds or without: `play` goes
     through by itself; `passes_of_quiet`: a sub-protocol without a round and without a prover's
     side: one condition on its `decide`
  4  `chain_passes`   one chain: I j holds before sub-protocol number j
  5  `envThird`, `sealPlain`, `run_of_passes`   the file

Limits.
  * `Passes` asks for its sub-protocol's acceptance at every list of challenges that the
    sub-protocol's rounds can draw and at which nothing of it stops. One list at which its `decide`
    rejects makes its A false everywhere, and that runs back to the chain's start.
  * An invariant I may narrow the coins: the rule then speaks at these coins alone.
  * The last test has to accept at every triple of end states that satisfy the three last
    invariants, not only at the run's own: the three are not tied to one list of challenges.
  * Nothing is said on how likely a stop is.
  * No fall: `Passes` has no parameter for a fall (`Fall`, Honest/Side.lean: an event at which a
    sub-protocol may reject an honest run). A place at which there is one has no condition of this
    form; for such places see `PlaysOn` and `SaysYes` (Honest/Law/ThreadC.lean). No lemma here goes
    from `Good` (Honest/Side.lean) to `Passes`: `Good` ends at the state that has taken the
    sub-protocol's columns (`y.2.took cols`), `Passes` at the state as `play` leaves it, and `play`
    does not turn the field `opened`; at `opened = none`, the one value at `run`'s states, the two
    are one state, and no lemma here says so.
  * `Passes` holds vacuously at a sub-protocol for which `chainSteps … [b] hs` returns an error (the
    book lends nothing there; a prover's side that does not fit): that it returns is among its
    hypotheses. In `run_of_passes` `ready` supplies it; whoever proves the condition for one
    sub-protocol has to prove that beside it.
  * Hypotheses that the prose above does not name: `Env.Tight`, or its text (no tree of the chain's
    own is available beyond those that it has sent): `chain_passes`.
  * `run` hands no columns: the hypotheses a₁, a₂ and a₃ of `run_of_passes` are asked at states with
    `opened = none`, and `play` carries that. An invariant that says what the field holds
    (`FieldAt`, Honest/Field.lean) is false there. At a prover with a part that reads the field and
    errs at `none` (Honest/Frame.lean, `Seen.opened`) the hypotheses cannot be met together: the
    lemma says nothing of such a prover.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W Y Pb W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The condition on one sub-protocol -/

/-- The condition on one sub-protocol, with a prover's side or without: from A to B, at the `Step`s
that `chainSteps` itself prepares for this one sub-protocol. From coins, a verifier's state, a state
of the prover's run and available tables that satisfy A, at challenges that its rounds can draw and
at which nothing of it stops: `play` returns, the columns are filled, its `decide` accepts, and B
holds after it. It is a definition, meant as a hypothesis. Nothing is claimed of it, and it is none
of the library's goals. -/
def Passes (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : Nat) (hs : List (Placed V W Y))
    (b : Block S Cl) (A B : Coins Bk → S → Mid W Y → Env → Prop) : Prop :=
  ∀ k s m E ds l, A k s m E → drawsFit b.rounds ds = true →
    chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs = .ok l →
    ∃ (y : List Played × Mid W Y) (cols : List OpenedColumn) (s' : S), play l ds [] m = .ok y ∧
      fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] = .ok cols ∧
      b.decide s ((roundsOf y.1).map noDigest)
        (regroup ((groupsOf ft b.rounds ds).map (·.length)) cols) = .ok s' ∧
      B k s' y.2 (E.add y.1)

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat} {hs : List (Placed V W Y)}
  {b : Block S Cl}

theorem Passes.mono {A A' B B' : Coins Bk → S → Mid W Y → Env → Prop}
    (h : Passes φ Bk chain ft hs b A B) (hA : ∀ k s m E, A' k s m E → A k s m E)
    (hB : ∀ k s m E, B k s m E → B' k s m E) : Passes φ Bk chain ft hs b A' B' := by
  intro k s m E ds l hA' hd hst hl
  obtain ⟨y, cols, s', h1, h2, h3, h4⟩ := h k s m E ds l (hA _ _ _ _ hA') hd hst hl
  exact ⟨y, cols, s', h1, h2, h3, hB _ _ _ _ h4⟩

/-- From a family of such conditions: g may hold the state before the sub-protocol, so that B g can
say what the sub-protocol has left unchanged. -/
theorem Passes.family {G : Type} {A B : G → Coins Bk → S → Mid W Y → Env → Prop}
    {I I' : Coins Bk → S → Mid W Y → Env → Prop}
    (h : ∀ g, Passes φ Bk chain ft hs b (A g) (B g))
    (hI : ∀ k s m E, I k s m E →
      ∃ g, A g k s m E ∧ ∀ s' m' E', B g k s' m' E' → I' k s' m' E') :
    Passes φ Bk chain ft hs b I I' := by
  intro k s m E ds l h0 hd hst hl
  obtain ⟨g, hA, hB⟩ := hI k s m E h0
  obtain ⟨y, cols, s', h1, h2, h3, h4⟩ := h g k s m E ds l hA hd hst hl
  exact ⟨y, cols, s', h1, h2, h3, hB _ _ _ h4⟩

end

/-! ## 2 The `Step`s of one sub-protocol -/

/-- The `Step`s of a sub-protocol at whose place no prover's side is defined. -/
def bareSteps (b : Block S Cl) : List (Step W Y) :=
  (b.rounds.zip b.oracles).map fun r =>
    (⟨b.name, ⟨b.place, 0⟩, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ : Step W Y)

section
variable {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option V}
  {b : Block S Cl} {hs : List (Placed V W Y)} {l : List (Step W Y)}

theorem steps_one_none (hf : (hs.find? fun g => g.place == b.place) = none)
    (h : chainSteps Bk rows look v [b] hs = .ok l) : l = bareSteps b := by
  simp only [chainSteps, hf] at h
  obtain ⟨-, h⟩ := exIte_ok h
  obtain ⟨z, hz, rfl⟩ := exMap_ok h
  cases hz
  exact List.append_nil _

theorem steps_one_half {g : Placed V W Y}
    (hf : (hs.find? fun g => g.place == b.place) = some g)
    (h : chainSteps Bk rows look v [b] hs = .ok l) :
    ∃ c, lendRow Bk rows look b.place g.parts 0 = .ok c ∧ l = g.steps b v c := by
  simp only [chainSteps, hf] at h
  obtain ⟨-, h⟩ := exIte_ok h
  obtain ⟨-, h⟩ := exIte_ok h
  obtain ⟨-, h⟩ := exIte_ok h
  obtain ⟨-, h⟩ := exIte_ok h
  obtain ⟨-, h⟩ := exIte_ok h
  obtain ⟨c, hc, h⟩ := exBind_ok h
  obtain ⟨z, hz, rfl⟩ := exMap_ok h
  cases hz
  refine ⟨c, ?_, List.append_nil _⟩
  cases hl : lendRow Bk rows look b.place g.parts 0 with
  | error e =>
    rw [hl] at hc
    cases hc
  | ok c' =>
    rw [hl] at hc
    cases hc
    rfl

end

theorem play_bare_ok : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn) (m : Mid W Y),
    (∀ s ∈ ss, s.move = none ∧ s.bad = (fun _ _ => none) ∧ s.hid = fun _ _ => none) →
    ds.length = ss.length → ∃ y, play ss ds [] m = .ok y
  | [], [], m, _, _ => ⟨([], m), rfl⟩
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | s :: ss, d :: ds, m, hs, hl => by
    obtain ⟨h1, h2, h3⟩ := hs s List.mem_cons_self
    have ht : s.tell none m = .ok ⟨[], List.replicate s.decl.entry.roots none, false⟩ := by
      simp [Step.tell, Step.stop, h1, h2, h3]
    have hh : s.hear ⟨[], List.replicate s.decl.entry.roots none, false⟩ d m =
        .ok ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩ := by
      simp [Step.hear, h1]
    obtain ⟨y, hy⟩ := play_bare_ok ss ds
      ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩
      (fun s' h' => hs s' (List.mem_cons_of_mem _ h')) (Nat.succ.inj hl)
    refine ⟨(⟨s.name, s.addr.place, 0, false, [], List.replicate s.decl.entry.roots none, d⟩ ::
      y.1, y.2), ?_⟩
    simp [play, ht, hh, hy, Except.bind, Except.map]

/-! ## 3 Two ways to the condition on a sub-protocol -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat} {hs : List (Placed V W Y)}

theorem or_none {α : Type} {a b : Option α} (h : a.or b = none) : a = none ∧ b = none := by
  cases a with
  | some _ => cases h
  | none => exact ⟨rfl, h⟩

variable {b : Block S Cl}

/-- A sub-protocol without a prover's side, with rounds or without: `play` goes through by itself;
the rest is a hypothesis on what it returns. -/
theorem passes_of_bare {A B : Coins Bk → S → Mid W Y → Env → Prop}
    (hf : (hs.find? fun g => g.place == b.place) = none)
    (h : ∀ k s m E ds y, A k s m E → drawsFit b.rounds ds = true →
      play (bareSteps b) ds [] m = .ok y →
      ∃ (cols : List OpenedColumn) (s' : S),
        fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] =
          .ok cols ∧
        b.decide s ((roundsOf y.1).map noDigest)
          (regroup ((groupsOf ft b.rounds ds).map (·.length)) cols) = .ok s' ∧
        B k s' y.2 (E.add y.1)) :
    Passes φ Bk chain ft hs b A B := by
  intro k s m E ds l hA hd _ hl
  have ho := (chainSteps_rows [b] hs l hl).1 b List.mem_cons_self
  obtain rfl := steps_one_none hf hl
  obtain ⟨y, hy⟩ := play_bare_ok (bareSteps (W := W) (Y := Y) b) ds m
    (fun s' hs' => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs'
      exact ⟨rfl, rfl, rfl⟩)
    (by
      rw [drawsFit_length _ _ hd]
      simp [bareSteps, ho])
  obtain ⟨cols, s', h1, h2, h3⟩ := h k s m E ds y hA hd hy
  exact ⟨y, cols, s', hy, h1, h2, h3⟩

/-- A sub-protocol without a round and without a prover's side (for example the blocks of no kind
that the library adds to a chain's list, such as the one where a segment starts). -/
theorem passes_of_quiet {A B : Coins Bk → S → Mid W Y → Env → Prop} (hr : b.rounds = [])
    (hf : (hs.find? fun g => g.place == b.place) = none)
    (h : ∀ k s m E, A k s m E → ∃ s', b.decide s [] [] = .ok s' ∧ B k s' m (E.add [])) :
    Passes φ Bk chain ft hs b A B := by
  refine passes_of_bare hf fun k s m E ds y hA hd hy => ?_
  rw [hr] at hd
  have hds : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => simp [drawsFit] at hd
  subst hds
  have hb : bareSteps (W := W) (Y := Y) b = [] := by simp [bareSteps, hr]
  rw [hb] at hy
  simp only [play] at hy
  cases hy
  obtain ⟨s', h1, h2⟩ := h k s m E hA
  refine ⟨[], s', ?_, ?_, h2⟩
  · rw [hr]
    rfl
  · rw [hr]
    exact h1

/-! ## 4 One chain -/

/-- **One chain.** `I j`: what holds before sub-protocol number j; `I bs.length`: after the last. -/
theorem chain_passes : ∀ (bs : List (Block S Cl))
    (I : Nat → Coins Bk → S → Mid W Y → Env → Prop),
    (∀ j b, bs[j]? = some b → Passes φ Bk chain ft hs b (I j) (I (j + 1))) →
    ∀ (k : Coins Bk) (s : S) (m : Mid W Y) (E : Env) (ds : List Fmt.Drawn) (l : List (Step W Y)),
    E.Tight → I 0 k s m E → drawsFit (bs.flatMap (·.rounds)) ds = true →
    chainStopAt (φ.sees m.st.input) bs hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) bs hs = .ok l →
    ∃ (y : List Played × Mid W Y) (cols : List OpenedColumn) (s' : S), play l ds [] m = .ok y ∧
      fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree (bs.flatMap (·.rounds)) ds)
        [] = .ok cols ∧
      decides ft bs s (roundsOf y.1) cols = .ok s' ∧ I bs.length k s' y.2 (E.add y.1)
  | [], I, _, k, s, m, E, ds, l, hE, h0, hd, _, hl => by
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [drawsFit] at hd
    subst hds
    simp only [chainSteps] at hl
    cases hl
    refine ⟨([], m), [], s, rfl, rfl, rfl, ?_⟩
    show I 0 k s m (E.add [])
    rw [Env.add_nil E hE]
    exact h0
  | b :: bs, I, h, k, s, m, E, ds, l, hE, h0, hd, hst, hl => by
    have hl' : chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) ([b] ++ bs) hs =
        .ok l := hl
    rw [chainSteps_append] at hl'
    obtain ⟨l₁, hl₁, hl'⟩ := exBind_ok hl'
    obtain ⟨l₂, hl₂, rfl⟩ := exMap_ok hl'
    rw [List.flatMap_cons, drawsFit_append, Bool.and_eq_true] at hd
    obtain ⟨hd₁, hd₂⟩ := hd
    have hst' : ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt (φ.sees m.st.input) g.parts m.loc (ds.take b.rounds.length)).or
          (chainStopAt (φ.sees m.st.input) bs hs (m.loc ++ ds.take b.rounds.length)
            (ds.drop b.rounds.length)) = none := hst
    obtain ⟨hs₁, hs₂⟩ := or_none hst'
    have hs₁' : chainStopAt (φ.sees m.st.input) [b] hs m.loc (ds.take b.rounds.length) = none := by
      show ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt (φ.sees m.st.input) g.parts m.loc
          ((ds.take b.rounds.length).take b.rounds.length)).or (none : Option Why) = none
      rw [List.take_take, Nat.min_self, hs₁]
      rfl
    obtain ⟨y₁, c₁, s₁, p₁, f₁, g₁, i₁⟩ :=
      h 0 b (by simp) k s m E (ds.take b.rounds.length) l₁ h0 hd₁ hs₁' hl₁
    obtain ⟨e1, e2, -⟩ := play_mid _ _ _ _ _ p₁
    obtain ⟨y₂, c₂, s₂, p₂, f₂, g₂, i₂⟩ := chain_passes bs (fun j => I (j + 1))
      (fun j b' hj => h (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj)) k s₁ y₁.2
      (E.add y₁.1) (ds.drop b.rounds.length) l₂ (Env.add_tight hE _) i₁ hd₂
      (by rw [e1, e2]; exact hs₂) (by rw [e1]; exact hl₂)
    have hn : l₁.length = b.rounds.length := by
      have e := congrArg List.length (steps_decl hl₁)
      rw [List.length_map, List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
      exact e
    have hlen₁ : (ds.take b.rounds.length).length = l₁.length := by
      rw [drawsFit_length _ _ hd₁, hn]
    have Y₁ := play_yields _ _ _ _ _ p₁
    have hro : roundsOf (y₁.1 ++ y₂.1) = roundsOf y₁.1 ++ roundsOf y₂.1 := by
      unfold roundsOf
      rw [List.map_append]
    have hrn : (roundsOf y₁.1).length = b.rounds.length := by
      unfold roundsOf
      rw [List.length_map, yields_length _ _ _ _ Y₁, hn]
    refine ⟨(y₁.1 ++ y₂.1, y₂.2), c₁ ++ c₂, s₂, ?_, ?_, ?_, ?_⟩
    · have e := play_append l₁ l₂ (ds.take b.rounds.length) (ds.drop b.rounds.length) [] m hlen₁
      rw [List.take_append_drop] at e
      rw [e, p₁]
      show (play l₂ (ds.drop b.rounds.length) (([] : List Fmt.RoundView).drop l₁.length) y₁.2).map _ = _
      rw [List.drop_nil, p₂]
      rfl
    · have e := readsOf_append chain ft (E.add (y₁.1 ++ y₂.1)).stored (E.add (y₁.1 ++ y₂.1)).tree
        b.rounds (bs.flatMap (·.rounds)) (ds.take b.rounds.length) (ds.drop b.rounds.length)
        (drawsFit_length _ _ hd₁).symm
      rw [List.take_append_drop] at e
      have f₁' : fillCols (readsOf chain ft (E.add (y₁.1 ++ y₂.1)).stored
          (E.add (y₁.1 ++ y₂.1)).tree b.rounds (ds.take b.rounds.length)) [] = .ok c₁ :=
        fillCols_mono (fun z pt hz => Env.add_prefix E y₁.1 y₂.1 z pt hz) _ _ _ f₁
      have f₂' : fillCols (readsOf chain ft (E.add (y₁.1 ++ y₂.1)).stored
          (E.add (y₁.1 ++ y₂.1)).tree (bs.flatMap (·.rounds)) (ds.drop b.rounds.length)) [] =
          .ok c₂ := by
        rw [← Env.add_add]
        exact f₂
      show fillCols (readsOf chain ft (E.add (y₁.1 ++ y₂.1)).stored (E.add (y₁.1 ++ y₂.1)).tree
        ((b :: bs).flatMap (·.rounds)) ds) [] = .ok (c₁ ++ c₂)
      rw [List.flatMap_cons, e, fillCols_append, f₁']
      show (fillCols _ (([] : List OpenedColumn).drop _)).map _ = _
      rw [List.drop_nil, f₂']
      rfl
    · have r1 : (roundsOf (y₁.1 ++ y₂.1)).take b.rounds.length = roundsOf y₁.1 := by
        rw [hro]
        exact List.take_left' hrn
      have r2 : (roundsOf (y₁.1 ++ y₂.1)).drop b.rounds.length = roundsOf y₂.1 := by
        rw [hro]
        exact List.drop_left' hrn
      have r3 : (roundsOf y₁.1).map (·.drawn) = ds.take b.rounds.length :=
        yields_drawn _ _ _ _ Y₁
      have k1 : ((groupsOf ft b.rounds (ds.take b.rounds.length)).flatMap id).length =
          c₁.length := by
        have e := congrArg List.length (fillCols_kept _ _ _ f₁)
        rw [readsOf_wants, List.length_map] at e
        exact e.symm
      have t1 : (c₁ ++ c₂).take c₁.length = c₁ := List.take_left' rfl
      have t2 : (c₁ ++ c₂).drop c₁.length = c₂ := List.drop_left' rfl
      show (b.decide s (((roundsOf (y₁.1 ++ y₂.1)).take b.rounds.length).map noDigest)
        (regroup ((groupsOf ft b.rounds
          (((roundsOf (y₁.1 ++ y₂.1)).take b.rounds.length).map (·.drawn))).map (·.length))
          ((c₁ ++ c₂).take ((groupsOf ft b.rounds
            (((roundsOf (y₁.1 ++ y₂.1)).take b.rounds.length).map (·.drawn))).flatMap
              id).length))).bind (fun s' =>
        decides ft bs s' ((roundsOf (y₁.1 ++ y₂.1)).drop b.rounds.length)
          ((c₁ ++ c₂).drop ((groupsOf ft b.rounds
            (((roundsOf (y₁.1 ++ y₂.1)).take b.rounds.length).map (·.drawn))).flatMap
              id).length)) = .ok s₂
      rw [r1, r2, r3, k1, t1, t2, g₁]
      exact g₂
    · show I (bs.length + 1) k s₂ y₂.2 (E.add (y₁.1 ++ y₂.1))
      rw [← Env.add_add]
      exact i₂

end

/-! ## 5 The file -/

/-- The available tables at the second chain's start: none of its own yet; those of the two earlier
chains to take over. -/
def envThird (E₁ E₂ : Env) : Env :=
  ⟨E₁.stored, (fun s => match s with
      | .own _ => none
      | .taken ch j =>
        if ch == 0 then E₁.tree (.own j) else if ch == 1 then E₂.tree (.own j) else none),
    0⟩

/-- The first chain's last declared round declares no item except roots, and no root: an executable
test; false where the first chain declares no round. -/
def sealPlain (F : FileDescription Xi) : Bool :=
  (F.roundsDeclaredByBlocks.1.getLast?.map fun d =>
    (d.items.filter (· != .root)).isEmpty && d.entry.roots == 0).getD false

/-- **The rule for a file.** A conditional lemma on this folder's own functions, at one input, one
run's coins and one list of challenges. If `ready` has returned, the description passes `planOk` and
`sealPlain`, the challenges are such as the rounds can draw and nothing stops; if the condition
holds at every sub-protocol of the three flat lists, from the invariant before it to the one after
it; and if the invariants hold at the two starts, give the second chain's start, and give the last
test's acceptance: then the run goes through, and `Decided` holds of its views. It says nothing of a
verifier's acceptance, and it is none of the library's goals. -/
theorem run_of_passes {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H w₀ rc x k = .ok R) (hp : F.planOk = true) (hq : sealPlain F = true)
    (hρ : ρ.due F = true) (hsil : silentAt F H w₀ rc x ρ = none)
    (I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → Passes .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1)))
    (h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      Passes .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1)))
    (h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      Passes .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1)))
    (a₁ : I₁ 0 k (F.start₁ (F.pub x)) (R.start₁ H)
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₂ : I₂ 0 k (F.start₂ (F.pub x)) (R.start₂ H)
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧ I₃ 0 k s₃ (R.start₃ H m₁ m₂) (envThird E₁ E₂))
    (fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
      F.fin x e₁ e₂ e₃ = true) :
    ∃ r, run F Bk H w₀ rc x k ρ none = .ok r ∧ Decided F x r.views := by
  obtain ⟨-, tr, htr, hown, hcom, s1, s2, s3⟩ := ready_ok hR
  have P := (F.planOk_ok).1 hp
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hρ
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, d4⟩ := hρ
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
  -- the first chain
  obtain ⟨y₁, c₁, e₁, p₁, f₁, g₁, i₁⟩ := chain_passes (φ := Face.own) (chain := 0) (ft := 0)
    F.first.blocksInOrder I₁ h₁ k (F.start₁ (F.pub x)) (R.start₁ H)
    (envOf (H.storedWords w₀ rc) (fun _ _ => none) []) ρ.first R.first (envOf_tight _ _ _) a₁ d1 t1
    s1
  -- the shared chain
  obtain ⟨y₂, c₂, e₂, p₂, f₂, g₂, i₂⟩ := chain_passes (φ := Face.shared) (chain := 1) (ft := 0)
    F.shared.blocksInOrder I₂ h₂ k (F.start₂ (F.pub x)) (R.start₂ H)
    (envOf (H.storedWords w₀ rc) (fun _ _ => none) []) ρ.shared R.shared (envOf_tight _ _ _) a₂ d2
    t2 s2
  -- the second chain's start
  obtain ⟨s₃, hs₃, i₀⟩ := a₃ _ _ _ _ _ _ i₁ i₂
  obtain ⟨-, l1, -⟩ := play_mid _ _ _ _ _ p₁
  have l1' : y₁.2.loc = ρ.first := l1
  have tight₃ : (envThird ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y₁.1)
      ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y₂.1)).Tight := fun _ _ => rfl
  -- the second chain
  obtain ⟨y₃, c₃, e₃, p₃, f₃, g₃, i₃⟩ := chain_passes (φ := Face.own) (chain := 2)
    (ft := F.lastChainFirstTreeNumber) F.second.blocksInOrder I₃ h₃ k s₃ (R.start₃ H y₁.2 y₂.2) _ ρ.second R.second
    tight₃ i₀ d3
    (by
      show chainStopAt (Face.own.sees R.own) F.second.blocksInOrder H.second y₁.2.loc ρ.second = none
      rw [l1']
      exact t3)
    s3
  -- the available tables are the run's look-ups
  have T₁ : ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y₁.1).tree = treeOwn y₁.1 := by
    rw [envOf_add, List.nil_append]
    exact (envOf_tree _ y₁.1 [] []).1
  have T₂ : ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y₂.1).tree = treeOwn y₂.1 := by
    rw [envOf_add, List.nil_append]
    exact (envOf_tree _ y₂.1 [] []).1
  have T₃ : ((envThird ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y₁.1)
      ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y₂.1)).add y₃.1).tree =
      treeThird y₁.1 y₂.1 y₃.1 := by
    funext z
    cases z with
    | own n =>
      show (if n < 0 then none else ((tablesOf y₃.1)[n - 0]?).bind id) = _
      rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero]
      rfl
    | taken ch j =>
      show (if ch == 0 then
          ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y₁.1).tree (.own j)
        else if ch == 1 then
          ((envOf (H.storedWords w₀ rc) (fun _ _ => none) []).add y₂.1).tree (.own j)
        else none) = _
      rw [T₁, T₂]
      rfl
  rw [T₁] at f₁
  rw [T₂] at f₂
  rw [T₃] at f₃
  -- the sealing round
  have hne : R.first ≠ [] := by
    intro h0
    have e := steps_decl s1
    rw [h0] at e
    have e' : F.roundsDeclaredByBlocks.1 = [] := e.symm
    simp [sealPlain, e'] at hq
  obtain ⟨ss, sL, hss⟩ := exists_snoc R.first hne
  obtain ⟨dsA, hdsA⟩ := List.getLast?_eq_some_iff.1 d4
  have hdecl : F.roundsDeclaredByBlocks.1 = ss.map (·.decl) ++ [sL.decl] := by
    rw [show F.roundsDeclaredByBlocks.1 = R.first.map (·.decl) from (steps_decl s1).symm, hss, List.map_append]
    rfl
  have hq' : (sL.decl.items.filter (· != .root)) = [] ∧ sL.decl.entry.roots = 0 := by
    simpa [sealPlain, hdecl] using hq
  have hlen : ss.length = dsA.length := by
    have e := drawsFit_length _ _ d1
    rw [hdecl, hdsA] at e
    simp at e
    exact e.symm
  have hor : sL.oracles = [] := by
    have e := steps_shaped s1 P.blocks₁ sL (by rw [hss]; simp)
    rw [hq'.2] at e
    exact List.eq_nil_of_length_eq_zero e
  have Y₁ := play_yields _ _ _ _ _ p₁
  rw [hss, hdsA] at Y₁
  have hseal : sealQuiet y₁.1 = true := seal_quiet Y₁ hlen hq'.1 hor hq'.2
  obtain ⟨r, hr, hv⟩ := run_back hR p₁ hseal p₂ p₃ f₁ f₂ f₃
  refine ⟨r, hr, e₁, e₂, s₃, e₃, ?_, ?_, hs₃, ?_, fin _ _ _ _ _ _ _ _ _ i₁ i₂ i₃⟩
  · rw [hv]
    show decides 0 F.first.blocksInOrder (F.start₁ (F.pub x))
      ((roundsOf y₁.1).dropLast ++ [⟨[], ⟨[], [], [], none⟩⟩]) c₁ = .ok e₁
    rw [seal_back hseal]
    exact g₁
  · rw [hv]
    exact g₂
  · rw [hv]
    exact g₃

end ProofFile.Honest

#print axioms ProofFile.Honest.Passes.mono
#print axioms ProofFile.Honest.Passes.family
#print axioms ProofFile.Honest.steps_one_none
#print axioms ProofFile.Honest.steps_one_half
#print axioms ProofFile.Honest.play_bare_ok
#print axioms ProofFile.Honest.or_none
#print axioms ProofFile.Honest.passes_of_bare
#print axioms ProofFile.Honest.passes_of_quiet
#print axioms ProofFile.Honest.chain_passes
#print axioms ProofFile.Honest.run_of_passes
#print axioms ProofFile.Honest.Passes
#print axioms ProofFile.Honest.bareSteps
#print axioms ProofFile.Honest.envThird
#print axioms ProofFile.Honest.sealPlain
