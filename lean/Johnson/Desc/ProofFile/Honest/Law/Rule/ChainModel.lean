-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/ChainModel.lean: one chain. Where a chain's walk has gone
through (Honest/Law/Rule/Chain.lean: `Chained`) over `Step`s that are prepared at these coins
(`chainSteps`), under `LookOk` (Honest/Law/Rule/MemberLay.lean) and `FaithAll`, the fold at coins
over the chain's steps, as a session lists them (Honest/Law/Rule/Session.lean: `chainActs`),
produces exactly what the walk's rounds show, and its verifier's state is the walk's
(`chain_model`). Three more hypotheses are facts on the description and the book: no two of the
sub-protocols are at one place; each round has as many oracle messages as its entry has roots; no
part of a cut has 0 rounds. The others tie the `Stand`, the walk's `Core`, the keys and the
challenges at the start; `ChainInv` (Honest/Law/Rule/ChainStep.lean) collects them. What the parts
are handed of opened columns is tied to what has been produced by `TieAt`, carried from one
sub-protocol to the next under `FaithOwn` (Honest/Law/Rule/OpenedStep.lean; `tie_over`). `FaithOwn`
is paid in Honest/Law/Rule/ChainFile.lean (`faithOwn_of`, under `hsrc`, which `model` pays), and
`TieAt` at a chain's start in Honest/Law/Rule/Model.lean.

  1  `lays_tables`, `lays_after`   what a sub-protocol's rounds are; the state of the prover's run
     after them
  2  `FaithAll`, `judge_same`   a definition: each read's words are found in what has been produced;
     the verifier's step on what has been produced is the walk's own
     `tie_over`   `TieAt` over one sub-protocol of a walk
  3  `chain_model`   the chain

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.MemberLay
import Johnson.Desc.ProofFile.Honest.Law.Rule.Chain
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 A sub-protocol's rounds -/

theorem lays_tables : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (m : Option (Mid W Y))
    (y : List Played × Option (Mid W Y)), lays l ds m = .ok y →
    (∀ s ∈ l, s.oracles.length = s.decl.entry.roots) →
    y.1.map (·.tables.length) = l.map (·.oracles.length) ∧ y.1.map (·.drawn) = ds
  | [], [], m, y, h, _ => by
    rw [lays] at h
    cases h
    exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, h, _ => by simp [lays] at h
  | _ :: _, [], _, _, h, _ => by simp [lays] at h
  | s :: l, d :: ds, m, y, h, hs => by
    rw [lays] at h
    obtain ⟨x, hx, h⟩ := exBind_ok h
    obtain ⟨m', -, h⟩ := exBind_ok h
    obtain ⟨y', hy, e⟩ := exMap_ok h
    subst e
    obtain ⟨e1, e2⟩ := lays_tables l ds m' y' hy fun t ht => hs t (List.mem_cons_of_mem _ ht)
    have hl : x.tables.length = s.oracles.length := by
      cases m with
      | none =>
        have ex : x = subTold s.decl s.oracles := (Except.ok.inj hx).symm
        subst ex
        show ((s.oracles.map substituteZeroTable).map some).length = _
        rw [List.length_map, List.length_map]
      | some a =>
        have hx' : s.tell none a = .ok x := hx
        obtain ⟨-, t2, t3⟩ := tell_yields hx'
        cases hm : s.move.isSome with
        | true =>
          obtain ⟨w, hf, -, ht⟩ := t2 hm
          rw [ht, List.length_map, fits_len hf]
        | false =>
          rw [(t3 hm).2, List.length_replicate, hs s (List.mem_cons.2 (Or.inl rfl))]
    refine ⟨?_, ?_⟩
    · show x.tables.length :: y'.1.map (·.tables.length) =
        s.oracles.length :: l.map (·.oracles.length)
      rw [hl, e1]
    · show d :: y'.1.map (·.drawn) = d :: ds
      rw [e2]

/-- The state of the prover's run after a sub-protocol that was played. Its field `opened`:
`lays_opened` (Honest/Law/Rule/OpenedStep.lean). -/
theorem lays_after {l : List (Step W Y)} {ds : List Fmt.Drawn} {m : Mid W Y}
    {y : List Played × Option (Mid W Y)}
    (hp : ∀ s ∈ l, s.move.isSome = false → s.addr.part = 0) (h : lays l ds (some m) = .ok y) :
    ∃ m', y.2 = some m' ∧ m'.st.input = m.st.input ∧ m'.seen = m.seen ++ roundsOf y.1 ∧
      m'.st = dryFold (l.map Step.hand) ds m.st ∧ m'.loc = m.loc ++ ds := by
  obtain ⟨m', e, hpl⟩ := lays_live l ds m y hp h
  obtain ⟨i1, -, i3⟩ := play_mid _ _ _ _ _ hpl
  obtain ⟨d1, d2⟩ := play_dry _ _ _ _ _ hpl
  exact ⟨m', e, i1, i3, d1, d2⟩

/-! ## 2 The verifier's step, on what has been produced -/

/-- **Each read's words are found in what has been produced**, sub-protocol by sub-protocol,
whatever rounds l the chain has produced. `Z₀`: what has been produced before the chain. At
`Laid.front 2`, which `judgeOff` reads, whatever the chain; `FaithOwn`
(Honest/Law/Rule/OpenedStep.lean) is the same at `Laid.front ch`. -/
def FaithAll (ch ft : Nat) (st : List (Nat × Nat × List UInt64)) (tree : Nat → List Nat) (L : Lay)
    (Z₀ : Laid) : List (Block S Cl) → List Fmt.Drawn → Prop
  | [], _ => True
  | b :: bs, ds =>
    (∀ l : List Played,
      ∀ q ∈ readsOf ch ft L.stored (L.tree l) b.rounds (ds.take b.rounds.length), ∀ w,
        q.words = some w →
        ((Z₀.add ch (pairsBy tree l 0)).front 2 st).wordsAt q.bare = some w) ∧
      FaithAll ch ft st tree L Z₀ bs (ds.drop b.rounds.length)

/-- **The verifier's step on what has been produced is the walk's own.** `l₀`: the chain's rounds
before the sub-protocol. `ps`: the sub-protocol's. -/
theorem judge_same (ch ft : Nat) (st : List (Nat × Nat × List UInt64)) (tree : Nat → List Nat)
    (L : Lay) (Z₀ : Laid) (hZ₀ : Z₀.of ch = []) (b : Block S Cl) (own : List Fmt.Drawn)
    (l₀ ps : List Played) (cols : List OpenedColumn) (hps : ps.length = b.rounds.length)
    (hc : fillCols (readsOf ch ft L.stored (L.tree (l₀ ++ ps)) b.rounds own) [] = .ok cols)
    (hf : ∀ q ∈ readsOf ch ft L.stored (L.tree (l₀ ++ ps)) b.rounds own, ∀ w, q.words = some w →
      ((Z₀.add ch (pairsBy tree (l₀ ++ ps) 0)).front 2 st).wordsAt q.bare = some w) (s : S) :
    judgeOff ch ft st b own (Z₀.add ch (pairsBy tree (l₀ ++ ps) 0)) s =
      judge ft b s (roundsOf ps) cols := by
  unfold judgeOff
  rw [← readsOf_bare ch ft L.stored (L.tree (l₀ ++ ps)), colsOff_fill _ _ _ hc hf]
  have e : (Z₀.add ch (pairsBy tree (l₀ ++ ps) 0)).of ch =
      shownBy ch tree l₀ 0 ++ shownBy ch tree ps (0 + (l₀.map (·.tables.length)).sum) := by
    rw [Laid.of_add, hZ₀, List.nil_append, ← shownBy_pairs, shownBy_append]
  show judge ft b s (roundsOff (((Z₀.add ch (pairsBy tree (l₀ ++ ps) 0)).of ch).drop
    (((Z₀.add ch (pairsBy tree (l₀ ++ ps) 0)).of ch).length - b.rounds.length))) cols = _
  rw [e, List.length_append, shownBy_length, shownBy_length, hps, Nat.add_sub_cancel,
    List.drop_left' (shownBy_length ch tree l₀ 0), roundsOff_by]

/-- **`TieAt` over one sub-protocol of a walk.** `Zl`: what has been produced before it. `sb`,
`own`: its `Step`s and challenges. `hf`: the clause of `FaithOwn` at the sub-protocol. -/
theorem tie_over {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {ch ft : Nat}
    {st : List (Nat × Nat × List UInt64)} {tree : Nat → List Nat} {L : Lay} {Z₀ Zl : Laid}
    {b : Block S Cl} {sb : List (Step W Y)} {own : List Fmt.Drawn} {done : List Fmt.DeclaredRound}
    {c : Core S W Y} {y : List Played × Option (Mid W Y)} {cols : List OpenedColumn}
    (h : TieAt earlier ch ft done c.mid (Zl.front ch st))
    (hZ : Zl = Z₀.add ch (pairsBy tree c.laid 0))
    (hpart : ∀ s ∈ sb, s.move.isSome = false → s.addr.part = 0)
    (hy : lays sb own c.mid = .ok y) (hyl : y.1.length = b.rounds.length)
    (hdr : y.1.map (·.drawn) = own)
    (hc : fillCols (readsOf ch ft L.stored (L.tree (c.laid ++ y.1)) b.rounds own) [] = .ok cols)
    (hf : ∀ q ∈ readsOf ch ft L.stored (L.tree (c.laid ++ y.1)) b.rounds own, ∀ w,
      q.words = some w →
      ((Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0)).front ch st).wordsAt q.bare = some w) :
    TieAt earlier ch ft (done ++ b.rounds) (c.next L b y cols).mid
      ((Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0)).front ch st) := by
  have hlaid : Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0) =
      Zl.add ch (pairsBy tree y.1 (c.laid.map (·.tables.length)).sum) := by
    rw [hZ, Laid.add_add, pairsBy_append, Nat.zero_add]
  rw [hlaid, Laid.front_add]
  refine h.next b.rounds _ cols _ ?_ ?_ ?_
  · have e := congrArg List.length (pairs_drawn tree y.1 (c.laid.map (·.tables.length)).sum)
    rw [List.length_map, List.length_map] at e
    rw [e, hyl]
  · intro m₁ hm₁
    have hm₁' : (if (c.next L b y cols).ver.isSome then y.2.map (·.took cols) else none) =
        some m₁ := hm₁
    have hy2 : y.2.map (·.took cols) = some m₁ := by
      by_cases hvs : (c.next L b y cols).ver.isSome = true
      · rw [if_pos hvs] at hm₁'
        exact hm₁'
      · rw [if_neg hvs] at hm₁'
        cases hm₁'
    cases hcm : c.mid with
    | none =>
      rw [hcm] at hy
      have e := lays_sub _ _ _ hy
      rw [e] at hy2
      simp at hy2
    | some m =>
      rw [hcm] at hy
      obtain ⟨m', e, ho⟩ := lays_opened hpart hy
      rw [e] at hy2
      have em : m'.took cols = m₁ := Option.some.inj hy2
      subst em
      refine ⟨m, rfl, ?_⟩
      show m'.opened.map (· ++ cols) = _
      rw [ho]
  · rw [← Laid.front_add, ← hlaid, pairs_drawn, hdr,
      ← readsOf_bare ch ft L.stored (L.tree (c.laid ++ y.1))]
    exact colsOff_fill _ _ _ hc hf

/-! ## 3 The chain -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (k : Coins Bk) (ch ft : Nat) (tree : Nat → List Nat) (tl : Addr → Option Teller)
  (has : Place → Bool) (φ : Face V W Pb) (pb : Pb) (hs : List (Placed V W Y))
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)

/-- **One chain.** `Ve`: which field of a `Stand` holds the chain's verifier's state. `Z₀`: what has
been produced before the chain. `kp`, `dp`: the chain's keys and challenges before the sub-protocols
bs. `bsAll`, `passed`: the chain's whole list, and its sub-protocols before bs. `earlier`: the
earlier chains' declared rounds, as `preOf` (Honest/Rule.lean) takes them. Beside the hypotheses
that the head names: `TieAt` at the rounds of `passed`; `bsAll = passed ++ bs`; no sub-protocol of
`passed` is at a place of bs; `LookOk` at `preOf` of each sub-protocol's place; `FaithOwn`. -/
theorem chain_model {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {bsAll : List (Block S Cl)}
    (Ve : VerAt F S Cl x st ch ft) (L : Lay) (hLc : L.chain = ch)
    (hLf : L.firstTree = ft) (v : Option V) (Z₀ : Laid) (hZ₀ : Z₀.of ch = []) :
    ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)) (ds : List Fmt.Drawn) (c c' : Core S W Y)
      (Z : Stand F) (kp : List (Addr × Option (State W Y → Y))) (dp : List Fmt.Drawn)
      (passed : List (Block S Cl)),
    chainSteps Bk (Bk.rowsOf ch) (k.look ch) v bs hs = .ok ss → Chained L bs ss ds c c' →
    Z.laid = Z₀.add ch (pairsBy tree c.laid 0) → Ve.get Z = c.ver →
    c.mid.isSome = c.ver.isSome →
    (∀ m, c.mid = some m → v = φ.sees m.st.input ∧ m.seen = (Z.laid.front ch st).seen ∧
      m.st = dryFold (kp.map (·.2)) dp m₀.st ∧ m.loc = m₀.loc ++ dp) →
    TieAt earlier ch ft (passed.flatMap (·.rounds)) c.mid (Z.laid.front ch st) →
    keys = kp ++ chainKeys bs hs → dsAll = dp ++ ds → dp.length = kp.length →
    (∀ q ∈ kp, q.1.place ∉ bs.map (·.place)) → bsAll = passed ++ bs →
    (∀ p ∈ passed, p.place ∉ bs.map (·.place)) → (bs.map (·.place)).Nodup →
    (∀ b ∈ bs, ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots) →
    (∀ b ∈ bs, ∀ cs, Bk.cuts.lookup b.place = some cs → ∀ n ∈ cs, n ≠ 0) →
    (∀ b ∈ bs, LookOk R ch tl has φ pb hs keys dsAll m₀ (preOf ch ft earlier bsAll b.place) b) →
    FaithAll ch ft st tree L Z₀ bs ds → FaithOwn ch ft st tree L Z₀ bs ds →
    Kit.real ((chainActs F Bk ch tree tl has Ve.J bs (c.laid.map (·.tables.length)).sum ds).map
        (Act.stage x st R)) k Z =
      Ve.set { Z with laid := Z₀.add ch (pairsBy tree c'.laid 0) } c'.ver
  | [], ss, ds, c, c', Z, kp, dp, _, _, hC, hZ, hv, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _ => by
    rw [Chained] at hC
    obtain ⟨-, -, rfl⟩ := hC
    show Z = _
    rw [← hZ, ← hv]
    exact (Ve.set_get Z).symm
  | b :: bs, ss, ds, c, c', Z, kp, dp, passed, hss, hC, hZ, hv, hmv, hm, htie, hk, hd, hlen, hfr,
      hall, hpass, hnd, hsh, hpos, hlook, hfa, hfc => by
    obtain ⟨ho, l, hl, hcase⟩ := chainSteps_cons_ok hss
    rw [Chained] at hC
    obtain ⟨y, cols, hy, hc, hC'⟩ := hC
    obtain ⟨hf0, hfa'⟩ := hfa
    obtain ⟨hfc0, hfc'⟩ := hfc
    have hpre : preOf ch ft earlier bsAll b.place =
        earlier ++ [(ch, ft, passed.flatMap (·.rounds))] := by
      rw [hall]
      exact preOf_at ch ft earlier passed b bs fun p hp e =>
        hpass p hp (by rw [e]; exact List.mem_cons.2 (Or.inl rfl))
    have hlk := hlook b (List.mem_cons.2 (Or.inl rfl))
    rw [hpre] at hlk
    have hshb := hsh b (List.mem_cons.2 (Or.inl rfl))
    have hzl : (b.rounds.zip b.oracles).length = b.rounds.length := by
      rw [List.length_zip, ho, Nat.min_self]
    -- the sub-protocol's `Step`s
    obtain ⟨sb, hsb, hstates, hpart, hcase'⟩ : ∃ sb : List (Step W Y), ss = sb ++ l ∧
        (sb.map fun s => (s.decl, s.oracles)) = b.rounds.zip b.oracles ∧
        (∀ s ∈ sb, s.move.isSome = false → s.addr.part = 0) ∧
        (((hs.find? fun g => g.place == b.place) = none ∧ sb = bareStepsR b) ∨
          ∃ g c, (hs.find? fun g => g.place == b.place) = some g ∧ g.rounds = b.rounds.length ∧
            Bk.cuts.lookup b.place = some (g.parts.map (·.moves.length)) ∧
            lendRow Bk (Bk.rowsOf ch) (k.look ch) b.place g.parts 0 = .ok c ∧
            sb = g.steps b v c) := by
      rcases hcase with ⟨h1, h2⟩ | ⟨g, cc, h1, h2, h3, h4, h5⟩
      · exact ⟨bareStepsR b, h2, bare_states b, fun s hs' _ => (bare_moves b s hs').2,
          Or.inl ⟨h1, rfl⟩⟩
      · have hmv' : ∀ s ∈ g.steps b v cc, s.move.isSome = false → s.addr.part = 0 := by
          intro s hs' hf
          rw [row_moves g b v cc h2 ho s hs'] at hf
          cases hf
        exact ⟨g.steps b v cc, h5, row_states g b v cc h2 ho, hmv',
          Or.inr ⟨g, cc, h1, h2, h3, h4, rfl⟩⟩
    have hsbl : sb.length = b.rounds.length := by
      have e := congrArg List.length hstates
      rw [List.length_map, hzl] at e
      exact e
    have htake : ss.take b.rounds.length = sb := by rw [hsb]; exact List.take_left' hsbl
    have hdrop : ss.drop b.rounds.length = l := by rw [hsb]; exact List.drop_left' hsbl
    rw [htake] at hy
    rw [hdrop] at hC'
    have hshs : ∀ s ∈ sb, s.oracles.length = s.decl.entry.roots := by
      intro s hs'
      have h1 : (s.decl, s.oracles) ∈ sb.map fun s => (s.decl, s.oracles) :=
        List.mem_map.2 ⟨s, hs', rfl⟩
      rw [hstates] at h1
      exact hshb _ h1
    obtain ⟨ht1, ht2⟩ := lays_tables _ _ _ _ hy hshs
    have hyl := lays_lengthR _ _ _ _ hy
    have hown := lays_draws _ _ _ _ hy
    have horc : sb.map (·.oracles.length) = (b.rounds.zip b.oracles).map (·.2.length) := by
      rw [← hstates, List.map_map]
      rfl
    -- the chain's keys at this sub-protocol
    have hkb : sb.map Step.key = chainKeys [b] hs := by
      have e1 := chainSteps_keys _ _ _ hss
      have e2 := chainSteps_keys _ _ _ hl
      rw [hsb, List.map_append, e2, chainKeys_cons b bs hs] at e1
      exact List.append_cancel_right e1
    have hkbl : (chainKeys [b] hs).length = b.rounds.length := by
      rw [← hkb, List.length_map, hsbl]
    have hds : ds = ds.take b.rounds.length ++ ds.drop b.rounds.length :=
      (List.take_append_drop _ _).symm
    -- what the sub-protocol produces
    have hA := member_lay x st R k ch tree tl has φ pb hs keys dsAll m₀ v b sb
      (ds.take b.rounds.length) (c.laid.map (·.tables.length)).sum c.mid y Z kp
      (chainKeys bs hs) dp (ds.drop b.rounds.length) ho hcase' hy
      (by rw [Ve.live, hv, hmv]) hm htie.member
      (by rw [hk, chainKeys_cons b bs hs, List.append_assoc])
      (by rw [hd, List.append_assoc, ← hds]) hlen
      (fun q hq e => hfr q hq (by rw [e]; exact List.mem_cons.2 (Or.inl rfl))) hshb
      (hpos b (List.mem_cons.2 (Or.inl rfl))) hlk
    -- the verifier's step
    have hlaid : Z.laid.add ch (pairsBy tree y.1 (c.laid.map (·.tables.length)).sum) =
        Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0) := by
      rw [hZ, Laid.add_add, pairsBy_append, Nat.zero_add]
    have hc' : fillCols (readsOf ch ft L.stored (L.tree (c.laid ++ y.1)) b.rounds
        (ds.take b.rounds.length)) [] = .ok cols := by
      rw [← hLc, ← hLf, ← ht2]
      exact hc
    have hJ : ∀ s : S, judgeOff ch ft st b (ds.take b.rounds.length)
        (Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0)) s = judge ft b s (roundsOf y.1) cols :=
      judge_same ch ft st tree L Z₀ hZ₀ b _ c.laid y.1 cols (by rw [hyl, hsbl]) hc'
        (hf0 (c.laid ++ y.1))
    have hver : (c.ver.bind fun s => judgeOff ch ft st b (ds.take b.rounds.length)
        (Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0)) s) = (c.next L b y cols).ver := by
      show _ = c.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols
      rw [hLf]
      exact congrArg (Option.bind c.ver) (funext hJ)
    -- the sub-protocols after it
    have ih := chain_model Ve L hLc hLf v Z₀ hZ₀ bs l (ds.drop b.rounds.length)
      (c.next L b y cols) c'
      (Ve.set { Z with laid := Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0) } (c.next L b y cols).ver)
      (kp ++ chainKeys [b] hs) (dp ++ ds.take b.rounds.length) (passed ++ [b]) hl hC'
      (by rw [Ve.laid_set]; rfl) (Ve.get_set _ _)
      (by
        show (if (c.next L b y cols).ver.isSome then y.2.map (·.took cols) else none).isSome = _
        cases hvn : (c.next L b y cols).ver with
        | none => rfl
        | some s' =>
          have hcv : c.ver.isSome = true := by
            cases hcv : c.ver with
            | some _ => rfl
            | none =>
              have : (c.next L b y cols).ver = none := by
                show (c.ver.bind fun s => _) = none
                rw [hcv]
                rfl
              rw [this] at hvn
              cases hvn
          rw [← hmv] at hcv
          obtain ⟨m, hmm⟩ := Option.isSome_iff_exists.1 hcv
          rw [hmm] at hy
          obtain ⟨m', e, -⟩ := lays_after hpart hy
          show (if (some s').isSome = true then y.2.map (·.took cols) else none).isSome = true
          have hsome : (some s').isSome = true := rfl
          rw [if_pos hsome, e]
          rfl)
      (by
        intro m₁ hm₁
        have hm₁' : (if (c.next L b y cols).ver.isSome then y.2.map (·.took cols) else none) =
            some m₁ := hm₁
        have hy2 : y.2.map (·.took cols) = some m₁ := by
          by_cases hvs : (c.next L b y cols).ver.isSome = true
          · rw [if_pos hvs] at hm₁'
            exact hm₁'
          · rw [if_neg hvs] at hm₁'
            cases hm₁'
        cases hcm : c.mid with
        | none =>
          rw [hcm] at hy
          have e := lays_sub _ _ _ hy
          rw [e] at hy2
          simp at hy2
        | some m =>
          rw [hcm] at hy
          obtain ⟨m', e, a1, a2, a3, a4⟩ := lays_after hpart hy
          obtain ⟨b1, b2, b3, b4⟩ := hm m hcm
          rw [e] at hy2
          have em : m'.took cols = m₁ := Option.some.inj hy2
          subst em
          refine ⟨?_, ?_, ?_, ?_⟩
          · show v = φ.sees m'.st.input
            rw [a1]
            exact b1
          · rw [Ve.laid_set]
            show m'.seen = ((Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0)).front ch st).seen
            rw [← hlaid, Laid.seen_add, pairs_rounds, a2, b2]
          · have hh : sb.map Step.hand = (chainKeys [b] hs).map (·.2) := by
              rw [← hkb, List.map_map]
              rfl
            show m'.st = _
            rw [a3, b3, hh, List.map_append, dryFold_append _ _ _ _ _ (by
              rw [List.length_map, hlen])]
          · show m'.loc = _
            rw [a4, b4, List.append_assoc])
      (by
        rw [Ve.laid_set]
        show TieAt earlier ch ft ((passed ++ [b]).flatMap (·.rounds)) (c.next L b y cols).mid
          ((Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0)).front ch st)
        rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact tie_over htie hZ hpart hy (by rw [hyl, hsbl]) ht2 hc' (hfc0 (c.laid ++ y.1)))
      (by rw [hk, chainKeys_cons b bs hs, List.append_assoc])
      (by rw [hd, List.append_assoc, ← hds])
      (by rw [List.length_append, List.length_append, hlen, hown, hsbl, hkbl])
      (by
        intro q hq
        have hnd' := List.nodup_cons.1 hnd
        rcases List.mem_append.1 hq with hq | hq
        · exact fun hmem => hfr q hq (List.mem_cons_of_mem _ hmem)
        · have := chainKeys_mem hs [b] q hq
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at this
          rw [this]
          exact hnd'.1)
      (by rw [hall]; simp)
      (by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact fun hmem => hpass p hp (List.mem_cons_of_mem _ hmem)
        · rw [List.mem_singleton.1 hp]
          exact (List.nodup_cons.1 hnd).1)
      (List.nodup_cons.1 hnd).2 (fun b' hb' => hsh b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' => hpos b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' => hlook b' (List.mem_cons_of_mem _ hb')) hfa' hfc'
    have hn : ((c.next L b y cols).laid.map (·.tables.length)).sum =
        (c.laid.map (·.tables.length)).sum + ((b.rounds.zip b.oracles).map (·.2.length)).sum := by
      show ((c.laid ++ y.1).map (·.tables.length)).sum = _
      rw [List.map_append, List.sum_append, ht1, horc]
    rw [hn] at ih
    show Kit.real (((stretchesOf (Bk := Bk) ch tree tl has b
        (c.laid.map fun p : Played => p.tables.length).sum
        (ds.take b.rounds.length)).map Act.lay ++ Ve.J b (ds.take b.rounds.length) ::
        chainActs F Bk ch tree tl has Ve.J bs
          ((c.laid.map fun p : Played => p.tables.length).sum +
            ((b.rounds.zip b.oracles).map fun z : Fmt.DeclaredRound × List Oracle => z.2.length).sum)
          (ds.drop b.rounds.length)).map
        (Act.stage x st R)) k Z = _
    rw [List.map_append, List.map_map, Kit.real_append]
    show Kit.real ((chainActs F Bk ch tree tl has Ve.J bs
          ((c.laid.map fun p : Played => p.tables.length).sum +
            ((b.rounds.zip b.oracles).map fun z : Fmt.DeclaredRound × List Oracle => z.2.length).sum)
          (ds.drop b.rounds.length)).map
        (Act.stage x st R)) k
      ((Ve.J b (ds.take b.rounds.length)).add x st
        (Kit.real ((stretchesOf (Bk := Bk) ch tree tl has b
          (c.laid.map fun p : Played => p.tables.length).sum
          (ds.take b.rounds.length)).map fun s => Act.stage x st R (.lay s : Act F)) k Z) _) = _
    rw [hA, Ve.add, Ve.get_laid, hv]
    show Kit.real _ k (Ve.set { Z with laid := (Z.laid.add ch
        (pairsBy tree y.1 (c.laid.map fun p : Played => p.tables.length).sum)) }
      (c.ver.bind (judgeOff ch ft st b (ds.take b.rounds.length)
        (Z.laid.add ch
          (pairsBy tree y.1 (c.laid.map fun p : Played => p.tables.length).sum))))) = _
    rw [hlaid]
    have hver' : c.ver.bind (judgeOff ch ft st b (ds.take b.rounds.length)
        (Z₀.add ch (pairsBy tree (c.laid ++ y.1) 0))) = (c.next L b y cols).ver := hver
    rw [hver', ih, Ve.set_laid]
    exact Ve.set_set _ _ _

end

end ProofFile.Honest

#print axioms ProofFile.Honest.lays_tables
#print axioms ProofFile.Honest.lays_after
#print axioms ProofFile.Honest.judge_same
#print axioms ProofFile.Honest.tie_over
#print axioms ProofFile.Honest.chain_model
#print axioms ProofFile.Honest.FaithAll
