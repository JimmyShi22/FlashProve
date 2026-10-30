-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunsC.lean: a chain's walk (Honest/Walk.lean) returns, outside the
stops, whatever the verifier's own steps decide, at coins at which the first invariant holds at the
walk's state, or after a rejection. This is the lemma `chain_returns`. As long as the steps accept
it follows from the first condition on each sub-protocol (`PlaysOn`, Honest/Law/ThreadC.lean). After
the first rejection it follows from what the plan declares: the substitutes are always produced, and
every column that a later sub-protocol reads is available, whether of a real table that was sent
earlier, of a substitute's table, of a stored table or of a tree that is taken over.

What this is. A conditional lemma on this folder's own functions, pointwise in the coins and the
challenges. It says nothing of a verifier's acceptance, and it is none of the library's goals.

  1  `lays_length`, `ChainProgress.askedO`, `member_laid`   one sub-protocol of the walk, played or
     substituted
  2  `TablesFit`, `tablesFit_nil`, `tablesFit_append`, `tablesFit_round`, `tablesFit_play`,
     `tablesFit_subs`   the tables produced are the oracle messages declared so far: all available,
     each of the declared width
  3  `InTime`, `Served`, `member_served`   what the plan declares of a chain's rounds; so a
     sub-protocol's columns are available
  4  `chain_returns`   one chain

Limits.
  * `InTime` and `Served` are hypotheses here: that a description's tests on the plan give them is
    not proved in this file.
  * Hypotheses besides `InTime` and `Served`: `L.tree` is that of `envOf`; each round declares as
    many oracle messages as its entry counts roots; a round without a move declares no root and is
    under the part 0; `chainSteps` returns at k; the challenges are such as the rounds can draw
    (`drawsFit`).
  * Nothing is said on how likely a stop or a rejection is.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ThreadC
import Johnson.Desc.ProofFile.Honest.Law.Fill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Pb : Type}

/-! ## 1 One sub-protocol, played or substituted -/

theorem lays_length : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (m : Option (Mid W Y))
    (y : List Played × Option (Mid W Y)), lays l ds m = .ok y →
    y.1.length = l.length ∧ y.1.map (·.drawn) = ds
  | [], [], _, y, h => by
    simp only [lays] at h
    cases h
    exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h => by simp [lays] at h
  | _ :: _, [], _, _, h => by simp [lays] at h
  | s :: l, d :: ds, m, y, h => by
    simp only [lays] at h
    obtain ⟨x, -, h⟩ := exBind_ok h
    obtain ⟨m', -, h⟩ := exBind_ok h
    obtain ⟨y', hy', rfl⟩ := exMap_ok h
    obtain ⟨a, b⟩ := lays_length l ds m' y' hy'
    exact ⟨congrArg (· + 1) a, congrArg (d :: ·) b⟩

/-- The walk after a sub-protocol whose rounds have been produced, real or substitutes, and that has
been asked. Where it accepts, the state of the prover's run has taken its columns (`Mid.took`).
(`ChainProgress.asked`, Honest/Law/ThreadC.lean, is this at a walk that is still played.) -/
def ChainProgress.askedO (L : Lay) (z : ChainProgress S Cl W Y) (b : Block S Cl)
    (y : List Played × Option (Mid W Y)) (cols : List OpenedColumn) : ChainProgress S Cl W Y :=
  { z with
    ver := z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols
    mid := if (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols).isSome
      then y.2.map (·.took cols) else none
    refused := z.refused.or
      (if z.ver.isSome && (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols).isNone
        then some b.place else none)
    laid := z.laid ++ y.1
    reads := z.reads ++ readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
      (y.1.map (·.drawn))
    cols := z.cols ++ cols, own := [] }

/-- **One sub-protocol of the walk**, played or substituted: where its rounds are produced and its
columns filled, the walk over them is the walk after the sub-protocol, asked (`ChainProgress.askedO`). `K`:
what follows. -/
theorem member_laid (L : Lay) (b : Block S Cl) (t : List (Block S Cl)) (z : ChainProgress S Cl W Y)
    (l : List (Step W Y)) (ds : List Fmt.Drawn) (y : List Played × Option (Mid W Y))
    (cols : List OpenedColumn) (ho : z.own = []) (hl : l.length = b.rounds.length)
    (hy : lays l ds z.mid = .ok y)
    (hc : fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
      (y.1.map (·.drawn))) [] = .ok cols)
    (K : ChainProgress S Cl W Y → Except Refusal (ChainProgress S Cl W Y)) :
    ((ChainProgress.settle L (b :: t) z).bind fun a => (walk L l ds a).bind K) =
      (ChainProgress.settle L t (z.askedO L b y cols)).bind K := by
  have hyl := (lays_length _ _ _ _ hy).1
  cases l with
  | nil =>
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [lays] at hy
    subst hds
    simp only [lays] at hy
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
    unfold ChainProgress.askedO
    simp [ho, roundsOf]
  | cons u l' =>
    have hlt : z.own.length < b.rounds.length := by
      rw [ho, ← hl]
      exact Nat.succ_pos _
    rw [settle_wait L b t z hlt]
    show (walk L (u :: l') ds { z with todo := b :: t }).bind K = _
    rw [member_on (u :: l') ds { z with todo := b :: t } y rfl
      (by
        show z.own.length + (u :: l').length = b.rounds.length
        rw [ho, ← hl]
        exact Nat.zero_add _)
      (by simp) hy]
    have hn : ¬ (ChainProgress.grown { z with todo := b :: t } y).own.length < b.rounds.length := by
      show ¬ (z.own ++ y.1).length < b.rounds.length
      rw [ho, List.nil_append, hyl, hl]
      exact Nat.lt_irrefl _
    have hc' : fillCols (readsOf L.chain L.firstTree L.stored
        (L.tree (ChainProgress.grown { z with todo := b :: t } y).laid) b.rounds
        ((ChainProgress.grown { z with todo := b :: t } y).own.map (·.drawn))) [] = .ok cols := by
      show fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
        ((z.own ++ y.1).map (·.drawn))) [] = .ok cols
      rw [ho, List.nil_append]
      exact hc
    rw [settle_ask L b t _ hn, hc']
    show (ChainProgress.settle L t _).bind K = _
    refine congrArg (fun w : Except Refusal (ChainProgress S Cl W Y) => w.bind K) ?_
    rw [← settle_todo L (b :: t) t (z.askedO L b y cols)]
    refine congrArg (ChainProgress.settle L t) ?_
    unfold ChainProgress.askedO ChainProgress.grown
    simp [ho]

/-! ## 2 The tables produced -/

/-- The tables produced are the oracle messages declared: as many; all available; each of the
declared width. -/
def TablesFit (os : List Oracle) (ps : List Played) : Prop :=
  (tablesOf ps).length = os.length ∧
    ∀ (n : Nat) (o : Oracle), os[n]? = some o →
      ∃ pt : Place × Table, (tablesOf ps)[n]? = some (some pt) ∧ pt.2.words = o.words

theorem tablesFit_nil : TablesFit [] [] := ⟨rfl, fun _ _ h => by simp at h⟩

theorem tablesFit_append {os os' : List Oracle} {ps ps' : List Played} (h : TablesFit os ps)
    (h' : TablesFit os' ps') : TablesFit (os ++ os') (ps ++ ps') := by
  obtain ⟨a1, a2⟩ := h
  obtain ⟨b1, b2⟩ := h'
  refine ⟨by rw [tablesOf_append, List.length_append, List.length_append, a1, b1], ?_⟩
  intro n o hn
  rw [tablesOf_append]
  by_cases hlt : n < os.length
  · rw [List.getElem?_append_left hlt] at hn
    rw [List.getElem?_append_left (by rw [a1]; exact hlt)]
    exact a2 n o hn
  · have hge := Nat.le_of_not_lt hlt
    rw [List.getElem?_append_right hge] at hn
    rw [List.getElem?_append_right (by rw [a1]; exact hge), a1]
    exact b2 _ o hn

/-- One produced round: as many tables as the round declares oracle messages, all available, each
with the declared numbers. -/
theorem tablesFit_round (os : List Oracle) (p : Played) (hl : p.tables.length = os.length)
    (ht : ∀ (n : Nat) (o : Oracle), os[n]? = some o →
      ∃ t : Table, p.tables[n]? = some (some t) ∧ t.words = o.words) :
    TablesFit os [p] := by
  have e : tablesOf [p] = p.tables.map fun t => t.map fun x => (p.place, x) := by
    simp [tablesOf]
  refine ⟨by rw [e, List.length_map, hl], fun n o hn => ?_⟩
  obtain ⟨t, h1, h2⟩ := ht n o hn
  exact ⟨(p.place, t), by rw [e, List.getElem?_map, h1]; rfl, h2⟩

theorem tablesFit_play : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (ps : List Played),
    Yields l ds [] ps → (∀ s ∈ l, s.oracles.length = s.decl.entry.roots) →
    (∀ s ∈ l, s.move.isSome = false → s.decl.entry.roots = 0) →
    TablesFit (l.flatMap (·.oracles)) ps
  | [], [], [], _, _, _ => tablesFit_nil
  | [], [], _ :: _, h, _, _ => by simp [Yields] at h
  | [], _ :: _, _, h, _, _ => by cases ‹List Played› <;> simp [Yields] at h
  | _ :: _, [], _, h, _, _ => by cases ‹List Played› <;> simp [Yields] at h
  | _ :: _, _ :: _, [], h, _, _ => by simp [Yields] at h
  | s :: l, d :: ds, p :: ps, h, ho, hb => by
    simp only [Yields] at h
    obtain ⟨⟨-, -, -, ht, hn⟩, h2⟩ := h
    have ih := tablesFit_play l ds ps h2 (fun s' hs' => ho s' (List.mem_cons_of_mem _ hs'))
      fun s' hs' => hb s' (List.mem_cons_of_mem _ hs')
    have h1 : TablesFit s.oracles [p] := by
      cases hm : s.move.isSome with
      | true =>
        obtain ⟨-, u, hu, -, htb⟩ := ht hm
        simp only [Sending.fits, Bool.and_eq_true, beq_iff_eq] at hu
        have e := congrArg List.length hu.2
        rw [List.length_map, List.length_map] at e
        refine tablesFit_round _ _ (by rw [htb, List.length_map, e]) fun n o hn' => ?_
        have e2 := congrArg (·[n]?) hu.2
        simp only [List.getElem?_map, hn', Option.map_some] at e2
        cases hu' : u.tables[n]? with
        | none =>
          rw [hu'] at e2
          cases e2
        | some t =>
          rw [hu'] at e2
          have e3 : (t.logLength, t.words) = (o.logLength, o.words) := Option.some.inj e2
          exact ⟨t, by rw [htb, List.getElem?_map, hu']; rfl, (Prod.mk.inj e3).2⟩
      | false =>
        have hr := hb s List.mem_cons_self hm
        have hos : s.oracles = [] :=
          List.eq_nil_of_length_eq_zero (by rw [ho s List.mem_cons_self, hr])
        obtain ⟨-, -, htb⟩ := hn hm
        rw [hos]
        refine tablesFit_round _ _ (by rw [htb, hr]; rfl) fun n o hn' => by simp at hn'
    rw [List.flatMap_cons]
    exact tablesFit_append h1 ih

theorem tablesFit_subs : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn), ds.length = l.length →
    TablesFit (l.flatMap (·.oracles)) ((l.zip ds).map fun u => subPlayed u.1 u.2)
  | [], [], _ => tablesFit_nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | s :: l, d :: ds, h => by
    have ih := tablesFit_subs l ds (Nat.succ.inj h)
    have h1 : TablesFit s.oracles [subPlayed s d] := by
      refine tablesFit_round _ _ ?_ fun n o hn => ⟨substituteZeroTable o, ?_, rfl⟩
      · show ((s.oracles.map substituteZeroTable).map some).length = _
        rw [List.length_map, List.length_map]
      · show ((s.oracles.map substituteZeroTable).map some)[n]? = _
        rw [List.getElem?_map, List.getElem?_map, hn]
        rfl
    rw [List.flatMap_cons, List.zip_cons_cons, List.map_cons]
    exact tablesFit_append h1 ih

/-! ## 3 What the plan declares -/

/-- Of a chain's rounds: a tree of the chain's own that a round opens has been declared by that
round at the latest, with the width at which it is opened. Its length is not compared here: `depthC`
(Honest/Law/StratRunC.lean) compares the depth of an opening with the table's length. -/
def InTime (l : List (Step W Y)) : Prop :=
  ∀ r s, l[r]? = some s → ∀ o ∈ s.decl.opens, ∀ n, o.2 = .own n →
    ∃ orc, ((l.take (r + 1)).flatMap (·.oracles))[n]? = some orc ∧ orc.words = o.1.W

/-- Of a chain's rounds: the stored columns that they read, and the trees that they take over, are
available with the declared widths. -/
def Served (L : Lay) (taken : Nat → Nat → Option (Place × Table)) (l : List (Step W Y)) : Prop :=
  ∀ s ∈ l, (∀ t ∈ s.decl.stored, ∀ x, x < 2 ^ t.sh.a →
      ∃ u, L.stored t.item x = some u ∧ u.length = t.sh.W) ∧
    ∀ o ∈ s.decl.opens, ∀ ch j, o.2 = .taken ch j →
      ∃ pt, taken ch j = some pt ∧ pt.2.words = o.1.W

/-- **A sub-protocol's columns are available**, where the tables produced are those declared up to
and including the sub-protocol. `pre`, `cur`, `post`: the chain's rounds before the sub-protocol,
its own, and those after it. -/
theorem member_served (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (pre cur post : List (Step W Y))
    (hI : InTime (pre ++ cur ++ post)) (hS : Served L taken (pre ++ cur ++ post))
    (laid : List Played) (hT : TablesFit ((pre ++ cur).flatMap (·.oracles)) laid)
    (ds : List Fmt.Drawn) :
    ∃ cols, fillCols (readsOf L.chain L.firstTree L.stored (L.tree laid) (cur.map (·.decl)) ds)
      [] = .ok cols := by
  refine filled _ _ _ _ _ _ fun d hd => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hd
  have hmem : s ∈ pre ++ cur ++ post :=
    List.mem_append_left _ (List.mem_append_right _ hs)
  refine ⟨(hS s hmem).1, fun o ho => ?_⟩
  rw [hL]
  cases ho2 : o.2 with
  | taken ch j => exact (hS s hmem).2 o ho ch j ho2
  | own n =>
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hs
    have hilt : i < cur.length := (List.getElem?_eq_some_iff.1 hi).1
    have hr : (pre ++ cur ++ post)[pre.length + i]? = some s := by
      rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, List.getElem?_append_left hilt]
      exact hi
    obtain ⟨orc, h1, h2⟩ := hI _ s hr o ho n ho2
    have hpre : ∃ rest, (pre ++ cur) = (pre ++ cur ++ post).take (pre.length + i + 1) ++ rest := by
      refine ⟨(pre ++ cur).drop (pre.length + i + 1), ?_⟩
      rw [List.take_append_of_le_length (by rw [List.length_append]; omega),
        List.take_append_drop]
    obtain ⟨rest, hrest⟩ := hpre
    have h3 : ((pre ++ cur).flatMap (·.oracles))[n]? = some orc := by
      rw [hrest, List.flatMap_append,
        List.getElem?_append_left (List.getElem?_eq_some_iff.1 h1).1]
      exact h1
    obtain ⟨pt, h4, h5⟩ := hT.2 n orc h3
    refine ⟨pt, ?_, h5.trans h2⟩
    show ((tablesOf laid)[n]?).bind id = some pt
    rw [h4]
    rfl

/-! ## 4 One chain -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **A chain's walk returns**, outside the stops, whatever the sub-protocols' own steps decide, at
coins `k` at which the first invariant holds at the walk's state, or after a rejection. `all`: all
the chain's rounds. `pre`: those before the sub-protocols `bs`; `l`: theirs. `v`: what the second
stops may read. `locEnd`: the challenges that the stops may read at the chain's end. `I`: a family
of relations, a parameter: `I j` before sub-protocol number j, `I bs.length` after the last. Nothing
asks that any of them can be met. An `I j` that leaves the state's field `opened` free asks
`PlaysOn` at every value of it, `none` too; `I (j + 1)` is owed, and holds, where j's own step
accepts, at the state that has taken sub-protocol j's columns (`Mid.took`). At the end the tables
produced are all that the chain declares; and either the walk holds the prover's run, the verifier's
state and the last invariant, or nothing more is played (a sub-protocol has rejected, or the walk
began so). -/
theorem chain_returns (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (all : List (Step W Y))
    (hI : InTime all) (hS : Served L taken all)
    (hsh : ∀ u ∈ all, u.oracles.length = u.decl.entry.roots)
    (hb0 : ∀ u ∈ all, u.move.isSome = false → u.decl.entry.roots = 0)
    (hp0 : ∀ u ∈ all, u.move.isSome = false → u.addr.part = 0) (k : Coins Bk) (v : Option V)
    (locEnd : List Fmt.Drawn) :
    ∀ (bs : List (Block S Cl)) (I : Nat → Coins Bk → S → Mid W Y → Env → Prop),
    (∀ j b, bs[j]? = some b → PlaysOn φ Bk L.chain L.firstTree hs b (I j) (I (j + 1))) →
    ∀ (pre l : List (Step W Y)) (z : ChainProgress S Cl W Y) (ds : List Fmt.Drawn), all = pre ++ l →
    z.own = [] → TablesFit (pre.flatMap (·.oracles)) z.laid →
    chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v bs hs = .ok l →
    drawsFit (bs.flatMap (·.rounds)) ds = true →
    ((∃ s m, z.mid = some m ∧ z.ver = some s ∧ φ.sees m.st.input = v ∧
        I 0 k s m (envOf L.stored taken z.laid) ∧ chainStopAt v bs hs m.loc ds = none ∧
        m.loc ++ ds = locEnd) ∨
      (z.mid = none ∧ z.ver = none)) →
    ∃ z', (ChainProgress.settle L bs z).bind (walk L l ds) = .ok z' ∧
      TablesFit (all.flatMap (·.oracles)) z'.laid ∧
      ((∃ s' m', z'.ver = some s' ∧ z'.mid = some m' ∧
          I bs.length k s' m' (envOf L.stored taken z'.laid) ∧ m'.loc = locEnd) ∨
        (z'.mid = none ∧ z'.ver = none))
  | [], I, _, pre, l, z, ds, hall, ho, hT, hl, hd, hmode => by
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [drawsFit] at hd
    subst hds
    simp only [chainSteps] at hl
    cases hl
    rw [List.append_nil] at hall
    refine ⟨{ z with todo := [] }, rfl, by rw [hall]; exact hT, ?_⟩
    rcases hmode with ⟨s, m, h1, h2, -, h4, -, h6⟩ | h
    · exact Or.inl ⟨s, m, h2, h1, h4, by rw [← h6, List.append_nil]⟩
    · exact Or.inr h
  | b :: t, I, h, pre, l, z, ds, hall, ho, hT, hl, hd, hmode => by
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
    have hall' : all = pre ++ l₁ ++ l₂ := by rw [hall, List.append_assoc]
    have hm₁ : ∀ u ∈ l₁, u ∈ all := fun u hu => by
      rw [hall']
      exact List.mem_append_left _ (List.mem_append_right _ hu)
    have hW : walk L (l₁ ++ l₂) ds = fun a : ChainProgress S Cl W Y =>
        (walk L l₁ (ds.take b.rounds.length) a).bind (walk L l₂ (ds.drop b.rounds.length)) := by
      funext a
      have e' := walk_append L l₂ (ds.drop b.rounds.length) l₁ (ds.take b.rounds.length) a hlen₁
      rw [List.take_append_drop] at e'
      exact e'
    rw [hW]
    -- what the sub-protocol produces, its columns, and the case after it
    have key : ∃ (y : List Played × Option (Mid W Y)) (cols : List OpenedColumn),
        lays l₁ (ds.take b.rounds.length) z.mid = .ok y ∧
        fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
          (y.1.map (·.drawn))) [] = .ok cols ∧
        TablesFit ((pre ++ l₁).flatMap (·.oracles)) (z.laid ++ y.1) ∧
        ((∃ s' m', (z.askedO L b y cols).mid = some m' ∧ (z.askedO L b y cols).ver = some s' ∧
            φ.sees m'.st.input = v ∧ I 1 k s' m' (envOf L.stored taken (z.laid ++ y.1)) ∧
            chainStopAt v t hs m'.loc (ds.drop b.rounds.length) = none ∧
            m'.loc ++ ds.drop b.rounds.length = locEnd) ∨
          ((z.askedO L b y cols).mid = none ∧ (z.askedO L b y cols).ver = none)) := by
      rcases hmode with ⟨s, m, h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2⟩
      · have hst' : ((hs.find? fun g => g.place == b.place).bind fun g =>
            rowStopAt v g.parts m.loc (ds.take b.rounds.length)).or
              (chainStopAt v t hs (m.loc ++ ds.take b.rounds.length)
                (ds.drop b.rounds.length)) = none := h5
        obtain ⟨hs₁, hs₂⟩ := or_none hst'
        have hs₁' : chainStopAt v [b] hs m.loc (ds.take b.rounds.length) = none := by
          show ((hs.find? fun g => g.place == b.place).bind fun g =>
            rowStopAt v g.parts m.loc
              ((ds.take b.rounds.length).take b.rounds.length)).or (none : Option Why) = none
          rw [List.take_take, Nat.min_self, hs₁]
          rfl
        obtain ⟨y, cols, p₁, f₁, hB⟩ := h 0 b (by simp) k s m _ (ds.take b.rounds.length) l₁ h4
          hd₁ (by rw [h3]; exact hs₁') (by rw [h3]; exact hl₁)
        obtain ⟨e1, e2, -⟩ := play_mid _ _ _ _ _ p₁
        have Y₁ := play_yields _ _ _ _ _ p₁
        have hdr : y.1.map (·.drawn) = ds.take b.rounds.length := by
          have e := yields_drawn _ _ _ _ Y₁
          unfold roundsOf at e
          rw [List.map_map] at e
          exact e
        have hE : (envOf L.stored taken z.laid).add y.1 = envOf L.stored taken (z.laid ++ y.1) :=
          envOf_add _ _ _ _
        rw [hE] at f₁
        refine ⟨(y.1, some y.2), cols, ?_, ?_, ?_, ?_⟩
        · rw [h1]
          exact lays_of_play _ _ _ _ (fun u hu => hp0 u (hm₁ u hu)) p₁
        · show fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
            (y.1.map (·.drawn))) [] = .ok cols
          rw [hdr, hL]
          exact f₁
        · rw [List.flatMap_append]
          exact tablesFit_append hT (tablesFit_play _ _ _ Y₁ (fun u hu => hsh u (hm₁ u hu))
            fun u hu => hb0 u (hm₁ u hu))
        · cases hj : judge L.firstTree b s (roundsOf y.1) cols with
          | none =>
            refine Or.inr ⟨?_, ?_⟩
            · show (if (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols).isSome
                then some (y.2.took cols) else none) = none
              rw [h2]
              show (if (judge L.firstTree b s (roundsOf y.1) cols).isSome then some (y.2.took cols)
                else none) = none
              rw [hj]
              rfl
            · show (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols) = none
              rw [h2]
              exact hj
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
            have e1' : (y.2.took cols).st.input = m.st.input := e1
            have e2' : (y.2.took cols).loc = m.loc ++ ds.take b.rounds.length := e2
            refine Or.inl ⟨s', y.2.took cols, ?_, ?_, by rw [e1']; exact h3, hB',
              by rw [e2']; exact hs₂,
              by rw [e2', List.append_assoc, List.take_append_drop]; exact h6⟩
            · show (if (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols).isSome
                then some (y.2.took cols) else none) = some (y.2.took cols)
              rw [h2]
              show (if (judge L.firstTree b s (roundsOf y.1) cols).isSome then some (y.2.took cols)
                else none) = some (y.2.took cols)
              rw [hj]
              rfl
            · show (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols) = some s'
              rw [h2]
              exact hj
      · have hT' : TablesFit ((pre ++ l₁).flatMap (·.oracles))
            (z.laid ++ (l₁.zip (ds.take b.rounds.length)).map fun u => subPlayed u.1 u.2) := by
          rw [List.flatMap_append]
          exact tablesFit_append hT (tablesFit_subs _ _ hlen₁)
        obtain ⟨cols, hc⟩ := member_served L taken hL pre l₁ l₂ (by rw [← hall']; exact hI)
          (by rw [← hall']; exact hS) _ hT'
          (((l₁.zip (ds.take b.rounds.length)).map fun u => subPlayed u.1 u.2).map (·.drawn))
        rw [hdecl] at hc
        refine ⟨((l₁.zip (ds.take b.rounds.length)).map fun u => subPlayed u.1 u.2, none), cols,
          ?_, hc, hT', Or.inr ⟨?_, ?_⟩⟩
        · rw [h1]
          exact lays_none _ _ hlen₁
        · show (if (z.ver.bind fun s => judge L.firstTree b s _ cols).isSome
            then none else none) = none
          split <;> rfl
        · show (z.ver.bind fun s => judge L.firstTree b s _ cols) = none
          rw [h2]
          rfl
    obtain ⟨y, cols, k1, k2, k3, k4⟩ := key
    rw [member_laid L b t z l₁ _ y cols ho hn k1 k2]
    obtain ⟨z', a1, a2, a3⟩ := chain_returns L taken hL all hI hS hsh hb0 hp0 k v locEnd t
      (fun j => I (j + 1))
      (fun j b' hj' => h (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj')) (pre ++ l₁) l₂
      (z.askedO L b y cols) (ds.drop b.rounds.length) hall' rfl k3 hl₂ hd₂ k4
    exact ⟨z', a1, a2, a3⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.lays_length
#print axioms ProofFile.Honest.member_laid
#print axioms ProofFile.Honest.tablesFit_nil
#print axioms ProofFile.Honest.tablesFit_append
#print axioms ProofFile.Honest.tablesFit_round
#print axioms ProofFile.Honest.tablesFit_play
#print axioms ProofFile.Honest.tablesFit_subs
#print axioms ProofFile.Honest.member_served
#print axioms ProofFile.Honest.chain_returns
#print axioms ProofFile.Honest.ChainProgress.askedO
#print axioms ProofFile.Honest.TablesFit
#print axioms ProofFile.Honest.InTime
#print axioms ProofFile.Honest.Served
