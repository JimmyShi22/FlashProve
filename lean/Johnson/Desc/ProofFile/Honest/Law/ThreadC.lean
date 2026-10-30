-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ThreadC.lean: the rule for one chain, for the honest prover of
Honest/Walk.lean, which asks the description's own step on what it has sent. Two conditions on each
sub-protocol of a chain's flat list; from the first, what the chain's walk does. A walk (`ChainProgress`,
`walk`) goes through a chain's rounds one at a time and carries both the state of the prover's run
and the verifier's state. The main lemma is `chain_walks`.

What these are. Conditional lemmas on this folder's own functions. They are pointwise: at one run's
coins and one list of challenges. Their hypotheses (the invariants, the first condition at every
sub-protocol) are proved here of no description. They say nothing of a verifier's acceptance, and
they are none of the library's goals.

  1  `PlaysOn`   the first condition on one sub-protocol, at all coins, fall or not: from A, outside
     the stops, its rounds are played and its columns filled; and if its own step accepts them, B
     holds after it, at the state that has taken these columns (`Mid.took`); `SaysYes`: the second
     condition: outside the stops and outside its fall its own step accepts (no lemma of this file
     takes it as a hypothesis: those of Honest/Law/AcceptC.lean, Honest/Law/FallFree.lean and
     Honest/Law/ThreadStratC.lean do); `plays_of_good`, `yes_of_good`: from `Good.plays` and
     `Good.acc` (Honest/Side.lean), at any value of `Good`'s parameter `pre`
  2  `walk_append`, `settle_todo`, `ChainProgress.asked`, `member_walks`   one sub-protocol of the walk
  3  `chain_walks`   one chain: the walk goes on, and the invariant holds, as long as the
     sub-protocols' own steps accept; at the first that rejects it has nothing more to play

Limits.
  * What the walk does after the first rejection (that the substitutes' columns are available) is
    not proved here.
  * The invariants may narrow the coins: the rule then speaks at these alone.
  * Both conditions are asked at every value of `m.opened` that A allows, `none` too. At a
    sub-protocol with a part that reads the field and errs at `none` (Honest/Frame.lean,
    `Seen.opened`), `PlaysOn` at an A that leaves the field free is met only vacuously.
  * Both conditions hold vacuously at a sub-protocol for which `chainSteps … [b] hs` returns an
    error (the book lends nothing there; a prover's side that does not fit): that it returns is
    among their hypotheses. In the rules for a file `ready` supplies it; whoever proves a condition
    for one sub-protocol has to prove that beside it.
  * Nothing is said on how likely a stop or a fall is.
  * Among the hypotheses that the prose above does not name, lemma by lemma. `stop_one`: `drawsFit`
    (`drawFit` round by round, and as many challenges as rounds); the list `hs` holds the side's own
    half at its place. `plays_of_good`, `yes_of_good`: that same condition on `hs`. `chain_walks`:
    `drawsFit`; `L.tree` is that of `envOf`; `z.own = []`; `z.mid = some m`, `z.ver = some s`;
    `chainSteps` returns over the whole list at k; no stop (`chainStopAt … = none`); a round without
    a move is under the part 0. `member_walks`: `z.own = []`; `l.length = b.rounds.length`; both
    states are there (`z.mid = some m`, `z.ver = some s`); a round without a move is under the part
    0.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.WalkOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Pb : Type}

/-! ## 1 The two conditions on a sub-protocol -/

/-- The first condition on one sub-protocol, with a prover's side or without, at all coins, fall or
not. From A, at challenges that its rounds can draw and at which nothing of it stops: `play` returns
and the columns are filled; and if the sub-protocol's own step accepts them, B holds after it, at
the state that has taken these columns (`y.2.took cols`). It is a definition, meant as a hypothesis.
Nothing is claimed of it, and it is none of the library's goals. -/
def PlaysOn (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : Nat) (hs : List (Placed V W Y))
    (b : Block S Cl) (A B : Coins Bk → S → Mid W Y → Env → Prop) : Prop :=
  ∀ k s m E ds l, A k s m E → drawsFit b.rounds ds = true →
    chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs = .ok l →
    ∃ (y : List Played × Mid W Y) (cols : List OpenedColumn), play l ds [] m = .ok y ∧
      fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] = .ok cols ∧
      ∀ s' n, b.step ft s (roundsOf y.1) cols = .ok (s', n) → B k s' (y.2.took cols) (E.add y.1)

/-- The second condition: outside the stops and outside its fall its own step accepts. `fall`: a
test on the verifier's state before the sub-protocol and on the sub-protocol's own challenges. A
definition, meant as a hypothesis. -/
def SaysYes (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : Nat) (hs : List (Placed V W Y))
    (b : Block S Cl) (fall : S → List Fmt.Drawn → Option String)
    (A : Coins Bk → S → Mid W Y → Env → Prop) : Prop :=
  ∀ k s m E ds l y cols, A k s m E → drawsFit b.rounds ds = true →
    chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none → fall s ds = none →
    chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs = .ok l →
    play l ds [] m = .ok y →
    fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] = .ok cols →
    ∃ s' n, b.step ft s (roundsOf y.1) cols = .ok (s', n)

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat} {hs : List (Placed V W Y)}

theorem stop_one {σ : Side S Cl V W Y Pb} {m : Mid W Y} {ds : List Fmt.Drawn}
    (hf : (hs.find? fun g => g.place == σ.block.place) = some σ.half)
    (hd : drawsFit σ.block.rounds ds = true)
    (hst : chainStopAt (φ.sees m.st.input) [σ.block] hs m.loc ds = none) :
    σ.stopAt φ m.st.input m.loc ds = none := by
  have hlen := drawsFit_length _ _ hd
  have hst' : ((hs.find? fun g => g.place == σ.block.place).bind fun g =>
      rowStopAt (φ.sees m.st.input) g.parts m.loc (ds.take σ.block.rounds.length)).or
        (none : Option Why) = none := hst
  rw [hf, ← hlen, List.take_length] at hst'
  exact (or_none hst').1

theorem plays_of_good {σ : Side S Cl V W Y Pb} {ord : List Place}
    {A B : Coins Bk → S → Mid W Y → Env → Prop}
    {On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (h : Good pre φ σ Bk ord chain ft A B On bud)
    (hf : (hs.find? fun g => g.place == σ.block.place) = some σ.half) :
    PlaysOn φ Bk chain ft hs σ.block A B := by
  intro k s m E ds l hA hd hst hl
  obtain ⟨c, y, cols, a1, a2, a3, a4⟩ := h.plays k s m E ds hA hd (stop_one hf hd hst)
  obtain ⟨c', hc', rfl⟩ := steps_one_half hf hl
  rw [a1] at hc'
  cases hc'
  exact ⟨y, cols, a2, a3, a4⟩

theorem yes_of_good {σ : Side S Cl V W Y Pb} {ord : List Place}
    {A B : Coins Bk → S → Mid W Y → Env → Prop}
    {On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (h : Good pre φ σ Bk ord chain ft A B On bud)
    (hf : (hs.find? fun g => g.place == σ.block.place) = some σ.half) :
    SaysYes φ Bk chain ft hs σ.block σ.fall A := by
  intro k s m E ds l y cols hA hd hst hfall hl hy hc
  obtain ⟨c, hc', rfl⟩ := steps_one_half hf hl
  exact h.acc k s m E ds hA hd (stop_one hf hd hst) hfall c y cols hc' hy hc

end

/-! ## 2 One sub-protocol of the walk -/

theorem walk_append (L : Lay) (l₂ : List (Step W Y)) (d₂ : List Fmt.Drawn) :
    ∀ (l₁ : List (Step W Y)) (d₁ : List Fmt.Drawn) (z : ChainProgress S Cl W Y), d₁.length = l₁.length →
    walk L (l₁ ++ l₂) (d₁ ++ d₂) z = (walk L l₁ d₁ z).bind (walk L l₂ d₂)
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | s :: l₁, d :: d₁, z, h => by
    show ((z.say s).bind fun x => (z.heard L s x d).bind fun z' =>
      walk L (l₁ ++ l₂) (d₁ ++ d₂) z') =
      ((z.say s).bind fun x => (z.heard L s x d).bind fun z' => walk L l₁ d₁ z').bind
        (walk L l₂ d₂)
    cases z.say s with
    | error e => rfl
    | ok x =>
      show ((z.heard L s x d).bind fun z' => walk L (l₁ ++ l₂) (d₁ ++ d₂) z') =
        ((z.heard L s x d).bind fun z' => walk L l₁ d₁ z').bind (walk L l₂ d₂)
      cases z.heard L s x d with
      | error e => rfl
      | ok z' => exact walk_append L l₂ d₂ l₁ d₁ z' (Nat.succ.inj h)

/-- What `ChainProgress.settle` is given as "not yet asked" in the walk's own field does not matter: it
writes that field. -/
theorem settle_todo' (L : Lay) : ∀ (t : List (Block S Cl)) (mid : Option (Mid W Y))
    (ver : Option S) (refused : Option Place) (laid : List Played) (reads : List Read)
    (cols : List OpenedColumn) (q q' : List (Block S Cl)) (own : List Played),
    ChainProgress.settle L t ⟨mid, ver, refused, laid, reads, cols, q, own⟩ =
      ChainProgress.settle L t ⟨mid, ver, refused, laid, reads, cols, q', own⟩
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | b :: t, mid, ver, refused, laid, reads, cols, q, q', own => by
    by_cases h : own.length < b.rounds.length
    · rw [settle_wait L b t ⟨mid, ver, refused, laid, reads, cols, q, own⟩ h,
        settle_wait L b t ⟨mid, ver, refused, laid, reads, cols, q', own⟩ h]
    · rw [settle_ask L b t ⟨mid, ver, refused, laid, reads, cols, q, own⟩ h,
        settle_ask L b t ⟨mid, ver, refused, laid, reads, cols, q', own⟩ h]
      congr 1
      funext c
      exact settle_todo' L t _ _ _ _ _ _ q q' _

theorem settle_todo (L : Lay) (q : List (Block S Cl)) (t : List (Block S Cl))
    (z : ChainProgress S Cl W Y) : ChainProgress.settle L t { z with todo := q } = ChainProgress.settle L t z :=
  settle_todo' L t z.mid z.ver z.refused z.laid z.reads z.cols q z.todo z.own

/-- The walk after a sub-protocol that has been played and asked. `y`: its played rounds, and the
state of the prover's run after them. `cols`: its columns; where it accepts, the state takes them
(`Mid.took`). -/
def ChainProgress.asked (L : Lay) (z : ChainProgress S Cl W Y) (b : Block S Cl) (s : S)
    (y : List Played × Mid W Y) (cols : List OpenedColumn) : ChainProgress S Cl W Y :=
  { z with
    ver := judge L.firstTree b s (roundsOf y.1) cols
    mid := if (judge L.firstTree b s (roundsOf y.1) cols).isSome then some (y.2.took cols) else none
    refused := z.refused.or
      (if (judge L.firstTree b s (roundsOf y.1) cols).isNone then some b.place else none)
    laid := z.laid ++ y.1
    reads := z.reads ++ readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
      (y.1.map (·.drawn))
    cols := z.cols ++ cols, own := [] }

/-- **One sub-protocol of the walk**: where its rounds are played and its columns filled, the walk
over them is the walk after the sub-protocol, asked (`ChainProgress.asked`). `K`: what follows. -/
theorem member_walks (L : Lay) (b : Block S Cl) (t : List (Block S Cl)) (z : ChainProgress S Cl W Y)
    (s : S) (m : Mid W Y) (l : List (Step W Y)) (ds : List Fmt.Drawn)
    (y : List Played × Mid W Y) (cols : List OpenedColumn) (ho : z.own = []) (hm : z.mid = some m)
    (hv : z.ver = some s) (hl : l.length = b.rounds.length)
    (hp : ∀ u ∈ l, u.move.isSome = false → u.addr.part = 0) (hy : play l ds [] m = .ok y)
    (hc : fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
      (y.1.map (·.drawn))) [] = .ok cols)
    (K : ChainProgress S Cl W Y → Except Refusal (ChainProgress S Cl W Y)) :
    ((ChainProgress.settle L (b :: t) z).bind fun a => (walk L l ds a).bind K) =
      (ChainProgress.settle L t (z.asked L b s y cols)).bind K := by
  have hyl : y.1.length = l.length := yields_length _ _ _ _ (play_yields _ _ _ _ _ hy)
  cases l with
  | nil =>
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [play] at hy
    subst hds
    simp only [play] at hy
    cases hy
    have hn : ¬ z.own.length < b.rounds.length := by
      rw [← hl]
      exact Nat.not_lt_zero _
    have hc' : fillCols (readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds
        (z.own.map (·.drawn))) [] = .ok cols := by
      rw [ho]
      simpa using hc
    rw [settle_ask L b t z hn, hc']
    show ((ChainProgress.settle L t _).bind fun a => (walk L [] [] a).bind K) = _
    have e : (fun a : ChainProgress S Cl W Y => (walk L [] [] a).bind K) = K := by
      funext a
      simp only [walk]
      rfl
    rw [e]
    refine congrArg (fun w => (ChainProgress.settle L t w).bind K) ?_
    unfold ChainProgress.asked
    simp [ho, hm, hv, roundsOf]
  | cons u l' =>
    have hlt : z.own.length < b.rounds.length := by
      rw [ho, ← hl]
      exact Nat.succ_pos _
    rw [settle_wait L b t z hlt]
    show (walk L (u :: l') ds { z with todo := b :: t }).bind K = _
    rw [member_on (u :: l') ds { z with todo := b :: t } (y.1, some y.2) rfl
      (by
        show z.own.length + (u :: l').length = b.rounds.length
        rw [ho, ← hl]
        exact Nat.zero_add _)
      (by simp)
      (by
        show lays (u :: l') ds z.mid = _
        rw [hm]
        exact lays_of_play _ _ _ _ hp hy)]
    have hn : ¬ (ChainProgress.grown { z with todo := b :: t } (y.1, some y.2)).own.length <
        b.rounds.length := by
      show ¬ (z.own ++ y.1).length < b.rounds.length
      rw [ho, List.nil_append, hyl, hl]
      exact Nat.lt_irrefl _
    have hc' : fillCols (readsOf L.chain L.firstTree L.stored
        (L.tree (ChainProgress.grown { z with todo := b :: t } (y.1, some y.2)).laid) b.rounds
        ((ChainProgress.grown { z with todo := b :: t } (y.1, some y.2)).own.map (·.drawn))) [] =
        .ok cols := by
      show fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
        ((z.own ++ y.1).map (·.drawn))) [] = .ok cols
      rw [ho, List.nil_append]
      exact hc
    rw [settle_ask L b t _ hn, hc']
    show (ChainProgress.settle L t _).bind K = _
    refine congrArg (fun w : Except Refusal (ChainProgress S Cl W Y) => w.bind K) ?_
    rw [← settle_todo L (b :: t) t (z.asked L b s y cols)]
    refine congrArg (ChainProgress.settle L t) ?_
    unfold ChainProgress.asked ChainProgress.grown
    simp [ho, hv]

/-! ## 3 One chain -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **One chain.** The walk goes on, and the invariant holds, as long as the sub-protocols' own
steps accept. Either it comes to the chain's end with the prover's run, the verifier's state and the
last invariant; or it is after a sub-protocol that has rejected, with nothing more to play, before
the sub-protocols `t` that are left, their rounds `l₂` and challenges `d₂`. `taken`: the look-up of
a tree that is taken over. -/
theorem chain_walks (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) :
    ∀ (bs : List (Block S Cl)) (I : Nat → Coins Bk → S → Mid W Y → Env → Prop),
    (∀ j b, bs[j]? = some b → PlaysOn φ Bk L.chain L.firstTree hs b (I j) (I (j + 1))) →
    ∀ (k : Coins Bk) (s : S) (m : Mid W Y) (z : ChainProgress S Cl W Y) (ds : List Fmt.Drawn)
      (l : List (Step W Y)), z.own = [] → z.mid = some m → z.ver = some s →
    I 0 k s m (envOf L.stored taken z.laid) → drawsFit (bs.flatMap (·.rounds)) ds = true →
    chainStopAt (φ.sees m.st.input) bs hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) (φ.sees m.st.input) bs hs = .ok l →
    (∀ u ∈ l, u.move.isSome = false → u.addr.part = 0) →
    (∃ z' s' m', (ChainProgress.settle L bs z).bind (walk L l ds) = .ok z' ∧ z'.ver = some s' ∧
      z'.mid = some m' ∧ I bs.length k s' m' (envOf L.stored taken z'.laid)) ∨
    (∃ (t : List (Block S Cl)) (l₂ : List (Step W Y)) (d₂ : List Fmt.Drawn) (zr : ChainProgress S Cl W Y),
      (ChainProgress.settle L bs z).bind (walk L l ds) = (ChainProgress.settle L t zr).bind (walk L l₂ d₂) ∧
      zr.mid = none ∧ zr.ver = none ∧ zr.own = [] ∧ (∃ pre, bs = pre ++ t) ∧
      l₂.map (·.decl) = t.flatMap (·.rounds) ∧ d₂.length = l₂.length)
  | [], I, _, k, s, m, z, ds, l, ho, hm, hv, h0, hd, _, hl, _ => by
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [drawsFit] at hd
    subst hds
    simp only [chainSteps] at hl
    cases hl
    exact Or.inl ⟨{ z with todo := [] }, s, m, rfl, hv, hm, h0⟩
  | b :: t, I, h, k, s, m, z, ds, l, ho, hm, hv, h0, hd, hst, hl, hp => by
    have hl' : chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) (φ.sees m.st.input) ([b] ++ t)
        hs = .ok l := hl
    rw [chainSteps_append] at hl'
    obtain ⟨l₁, hl₁, hl'⟩ := exBind_ok hl'
    obtain ⟨l₂, hl₂, rfl⟩ := exMap_ok hl'
    rw [List.flatMap_cons, drawsFit_append, Bool.and_eq_true] at hd
    obtain ⟨hd₁, hd₂⟩ := hd
    have hst' : ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt (φ.sees m.st.input) g.parts m.loc (ds.take b.rounds.length)).or
          (chainStopAt (φ.sees m.st.input) t hs (m.loc ++ ds.take b.rounds.length)
            (ds.drop b.rounds.length)) = none := hst
    obtain ⟨hs₁, hs₂⟩ := or_none hst'
    have hs₁' : chainStopAt (φ.sees m.st.input) [b] hs m.loc (ds.take b.rounds.length) = none := by
      show ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt (φ.sees m.st.input) g.parts m.loc
          ((ds.take b.rounds.length).take b.rounds.length)).or (none : Option Why) = none
      rw [List.take_take, Nat.min_self, hs₁]
      rfl
    obtain ⟨y, cols, p₁, f₁, hB⟩ := h 0 b (by simp) k s m _ (ds.take b.rounds.length) l₁ h0 hd₁
      hs₁' hl₁
    obtain ⟨e1, e2, -⟩ := play_mid _ _ _ _ _ p₁
    have hn : l₁.length = b.rounds.length := by
      have e := congrArg List.length (steps_decl hl₁)
      rw [List.length_map, List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
      exact e
    have hlen₁ : (ds.take b.rounds.length).length = l₁.length := by
      rw [drawsFit_length _ _ hd₁, hn]
    have hdr : y.1.map (·.drawn) = ds.take b.rounds.length := by
      have e := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ p₁)
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
    have hX : (ChainProgress.settle L (b :: t) z).bind (walk L (l₁ ++ l₂) ds) =
        (ChainProgress.settle L t (z.asked L b s y cols)).bind
          (walk L l₂ (ds.drop b.rounds.length)) := by
      have e : walk L (l₁ ++ l₂) ds = fun a : ChainProgress S Cl W Y =>
          (walk L l₁ (ds.take b.rounds.length) a).bind (walk L l₂ (ds.drop b.rounds.length)) := by
        funext a
        have e' := walk_append L l₂ (ds.drop b.rounds.length) l₁ (ds.take b.rounds.length) a hlen₁
        rw [List.take_append_drop] at e'
        exact e'
      rw [e]
      exact member_walks L b t z s m l₁ _ y cols ho hm hv hn
        (fun u hu => hp u (List.mem_append_left _ hu)) p₁ f₁' _
    rw [hX]
    cases hj : judge L.firstTree b s (roundsOf y.1) cols with
    | none =>
      refine Or.inr ⟨t, l₂, ds.drop b.rounds.length, z.asked L b s y cols, rfl, ?_, hj, rfl,
        ⟨[b], rfl⟩, steps_decl hl₂, ?_⟩
      · show (if (judge L.firstTree b s (roundsOf y.1) cols).isSome then some (y.2.took cols)
          else none) = none
        rw [hj]
        rfl
      · rw [drawsFit_length _ _ hd₂, ← steps_decl hl₂, List.length_map]
    | some s' =>
      have hstep : ∃ n, b.step L.firstTree s (roundsOf y.1) cols = .ok (s', n) := by
        unfold judge at hj
        cases hs' : b.step L.firstTree s (roundsOf y.1) cols with
        | error e =>
          rw [hs'] at hj
          cases hj
        | ok w =>
          rw [hs'] at hj
          cases hj
          exact ⟨w.2, rfl⟩
      obtain ⟨n, hstep⟩ := hstep
      have hB' := hB s' n hstep
      rw [hE] at hB'
      have hmid : (z.asked L b s y cols).mid = some (y.2.took cols) := by
        show (if (judge L.firstTree b s (roundsOf y.1) cols).isSome then some (y.2.took cols)
          else none) = _
        rw [hj]
        rfl
      rcases chain_walks L taken hL t (fun j => I (j + 1))
        (fun j b' hj' => h (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj')) k s'
        (y.2.took cols) (z.asked L b s y cols) (ds.drop b.rounds.length) l₂ rfl hmid hj hB' hd₂
        (by
          show chainStopAt (φ.sees y.2.st.input) t hs y.2.loc _ = none
          rw [e1, e2]
          exact hs₂)
        (by
          show chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) (φ.sees y.2.st.input) t hs = _
          rw [e1]
          exact hl₂)
        (fun u hu => hp u (List.mem_append_right _ hu)) with
        ⟨z', s'', m', a1, a2, a3, a4⟩ | ⟨t', l₃, d₃, zr, a1, a2, a3, a4, ⟨pre, a5⟩, a6, a7⟩
      · exact Or.inl ⟨z', s'', m', a1, a2, a3, a4⟩
      · exact Or.inr ⟨t', l₃, d₃, zr, a1, a2, a3, a4, ⟨b :: pre, by rw [a5]; rfl⟩, a6, a7⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.stop_one
#print axioms ProofFile.Honest.plays_of_good
#print axioms ProofFile.Honest.yes_of_good
#print axioms ProofFile.Honest.walk_append
#print axioms ProofFile.Honest.settle_todo'
#print axioms ProofFile.Honest.settle_todo
#print axioms ProofFile.Honest.member_walks
#print axioms ProofFile.Honest.chain_walks
#print axioms ProofFile.Honest.PlaysOn
#print axioms ProofFile.Honest.SaysYes
#print axioms ProofFile.Honest.ChainProgress.asked
