-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/ChainStep.lean: one sub-protocol of a chain, at given coins.
`ChainInv` says what holds before a sub-protocol: as one proposition, those hypotheses of
`chain_model` (Honest/Law/Rule/ChainModel.lean) that speak of the coins, the walk or the place
reached in the chain, with how many trees the chain has sent (`num`), how many rounds it has played
(`lenp`), that each read of the remaining sub-protocols is in a given list `Bq` (`bare`), and what
ties the opened columns that the parts are handed to what has been produced (`tie`, `whole`,
`apart`, `faithC`; Honest/Law/Rule/OpenedStep.lean; at a chain's start they are paid in
Honest/Law/Rule/FileInv.lean). Four hypotheses of `chain_model` are not in it: no place twice, the
roots, the cuts and `LookOk`; `ChainInv.step` takes them beside it. It is preserved over the
sub-protocol (`ChainInv.step`: the step of that lemma's own proof, copied out of it). And where the
verifier has not rejected in the chain and a list of parts is at the sub-protocol, it gives what
holds before the list's first part
(`ChainInv.row`; `RowInv`, Honest/Law/Rule/RowHere.lean). It is the fifth piece of the proof of
`rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainEnd
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowHere

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi S Cl V W Y Pb : Type}

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (ch ft : Nat) (tree : Nat → List Nat) (tl : Addr → Option Teller)
  (has : Place → Bool) (φ : Face V W Pb) (pb : Pb) (hs : List (Placed V W Y))
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)
  (Ve : VerAt F S Cl x st ch ft) (v : Option V) (Bq : List Read)
  (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (bsAll : List (Block S Cl))

/-- **What holds before the sub-protocols bs of a chain, at given coins.** `L`, `Zb`: what the
chain's reads are computed from (`Lay`) and what has been produced before the chain, at these coins.
`n`: how many trees the chain has sent. `bsAll`, `passed`: the chain's whole list, and its
sub-protocols before bs. `earlier`: the earlier chains' declared rounds, as `preOf`
(Honest/Rule.lean) takes them. -/
structure ChainInv (k : Coins Bk) (L : Lay) (Zb : Laid) (bs : List (Block S Cl))
    (ss : List (Step W Y)) (ds : List Fmt.Drawn) (n : Nat) (c c' : Core S W Y) (Z : Stand F)
    (kp : List (Addr × Option (State W Y → Y))) (dp : List Fmt.Drawn)
    (passed : List (Block S Cl)) : Prop where
  lc : L.chain = ch
  lf : L.firstTree = ft
  zb : Zb.of ch = []
  steps : chainSteps Bk (Bk.rowsOf ch) (k.look ch) v bs hs = .ok ss
  chained : Chained L bs ss ds c c'
  laid : Z.laid = Zb.add ch (pairsBy tree c.laid 0)
  ver : Ve.get Z = c.ver
  both : c.mid.isSome = c.ver.isSome
  mid : ∀ m, c.mid = some m → v = φ.sees m.st.input ∧ m.seen = (Z.laid.front ch st).seen ∧
    m.st = dryFold (kp.map (·.2)) dp m₀.st ∧ m.loc = m₀.loc ++ dp
  tie : TieAt earlier ch ft (passed.flatMap (·.rounds)) c.mid (Z.laid.front ch st)
  keys : keys = kp ++ chainKeys bs hs
  all : dsAll = dp ++ ds
  len : dp.length = kp.length
  fresh : ∀ q ∈ kp, q.1.place ∉ bs.map (·.place)
  whole : bsAll = passed ++ bs
  apart : ∀ p ∈ passed, p.place ∉ bs.map (·.place)
  faith : FaithAll ch ft st tree L Zb bs ds
  faithC : FaithOwn ch ft st tree L Zb bs ds
  num : n = (c.laid.map (·.tables.length)).sum
  lenp : c.laid.length = kp.length
  bare : ∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds)) ds, q ∈ Bq

variable {x st R ch ft tree tl has φ pb hs keys dsAll m₀ Ve v Bq earlier bsAll}

/-- **Over one sub-protocol.** -/
theorem ChainInv.step {k : Coins Bk} {L : Lay} {Zb : Laid} {b : Block S Cl}
    {bs : List (Block S Cl)} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {n : Nat}
    {c c' : Core S W Y} {Z : Stand F} {kp : List (Addr × Option (State W Y → Y))}
    {dp : List Fmt.Drawn} {passed : List (Block S Cl)}
    (h : ChainInv x st ch ft tree φ hs keys dsAll m₀ Ve v Bq earlier bsAll k L Zb (b :: bs) ss ds n
      c c' Z kp dp passed)
    (hnd : ((b :: bs).map (·.place)).Nodup)
    (hshb : ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots)
    (hpos : ∀ cs, Bk.cuts.lookup b.place = some cs → ∀ n ∈ cs, n ≠ 0)
    (hlook : LookOk R ch tl has φ pb hs keys dsAll m₀ (preOf ch ft earlier bsAll b.place) b) :
    ∃ (y : List Played × Option (Mid W Y)) (cols : List OpenedColumn) (l : List (Step W Y)),
      Kit.real ((stretchesOf (Bk := Bk) ch tree tl has b n (ds.take b.rounds.length)).map fun s =>
          Act.stage x st R (.lay s : Act F)) k Z =
        { Z with laid := Z.laid.add ch (pairsBy tree y.1 n) } ∧
      ∀ new, ChainInv x st ch ft tree φ hs keys dsAll m₀ Ve v Bq earlier bsAll k L Zb bs l
        (ds.drop b.rounds.length)
        (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum) (c.next L b y cols) c'
        ((Ve.J b (ds.take b.rounds.length)).add x st
          { Z with laid := Z.laid.add ch (pairsBy tree y.1 n) } new)
        (kp ++ chainKeys [b] hs) (dp ++ ds.take b.rounds.length) (passed ++ [b]) := by
  obtain ⟨hLc, hLf, hZ₀, hss, hC, hZ, hv, hmv, hm, htie, hk, hd, hlen, hfr, hall, hpass, hfa, hfc,
    hnum, hlenp, hbare⟩ := h
  subst hnum
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
  rw [hpre] at hlook
  have hzl : (b.rounds.zip b.oracles).length = b.rounds.length := by
    rw [List.length_zip, ho, Nat.min_self]
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
  have hcut : readsOf ch ft (fun _ _ => none) (fun _ => none) ((b :: bs).flatMap (·.rounds)) ds =
      readsOf ch ft (fun _ _ => none) (fun _ => none) b.rounds (ds.take b.rounds.length) ++
      readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds)) (ds.drop
          b.rounds.length) := by
    conv_lhs => rw [← List.take_append_drop b.rounds.length ds, List.flatMap_cons]
    exact readsOf_append ch ft _ _ _ _ _ _ (by rw [hown, hsbl])
  have horc : sb.map (·.oracles.length) = (b.rounds.zip b.oracles).map (·.2.length) := by
    rw [← hstates, List.map_map]
    rfl
  have hkb : sb.map Step.key = chainKeys [b] hs := by
    have e1 := chainSteps_keys _ _ _ hss
    have e2 := chainSteps_keys _ _ _ hl
    rw [hsb, List.map_append, e2, chainKeys_cons b bs hs] at e1
    exact List.append_cancel_right e1
  have hkbl : (chainKeys [b] hs).length = b.rounds.length := by
    rw [← hkb, List.length_map, hsbl]
  have hds : ds = ds.take b.rounds.length ++ ds.drop b.rounds.length :=
    (List.take_append_drop _ _).symm
  have hA := member_lay x st R k ch tree tl has φ pb hs keys dsAll m₀ v b sb
    (ds.take b.rounds.length) (c.laid.map (·.tables.length)).sum c.mid y Z kp
    (chainKeys bs hs) dp (ds.drop b.rounds.length) ho hcase' hy
    (by rw [Ve.live, hv, hmv]) hm htie.member
    (by rw [hk, chainKeys_cons b bs hs, List.append_assoc])
    (by rw [hd, List.append_assoc, ← hds]) hlen
    (fun q hq e => hfr q hq (by rw [e]; exact List.mem_cons.2 (Or.inl rfl))) hshb hpos hlook
  have hlaid : Z.laid.add ch (pairsBy tree y.1 (c.laid.map (·.tables.length)).sum) =
      Zb.add ch (pairsBy tree (c.laid ++ y.1) 0) := by
    rw [hZ, Laid.add_add, pairsBy_append, Nat.zero_add]
  have hc' : fillCols (readsOf ch ft L.stored (L.tree (c.laid ++ y.1)) b.rounds
      (ds.take b.rounds.length)) [] = .ok cols := by
    rw [← hLc, ← hLf, ← ht2]
    exact hc
  have hJ : ∀ s : S, judgeOff ch ft st b (ds.take b.rounds.length)
      (Zb.add ch (pairsBy tree (c.laid ++ y.1) 0)) s = judge ft b s (roundsOf y.1) cols :=
    judge_same ch ft st tree L Zb hZ₀ b _ c.laid y.1 cols (by rw [hyl, hsbl]) hc'
      (hf0 (c.laid ++ y.1))
  have hver : (c.ver.bind fun s => judgeOff ch ft st b (ds.take b.rounds.length)
      (Zb.add ch (pairsBy tree (c.laid ++ y.1) 0)) s) = (c.next L b y cols).ver := by
    show _ = c.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols
    rw [hLf]
    exact congrArg (Option.bind c.ver) (funext hJ)
  have hZ₂ : ∀ new, (Ve.J b (ds.take b.rounds.length)).add x st
      { Z with laid := Z.laid.add ch (pairsBy tree y.1 (c.laid.map (·.tables.length)).sum) } new =
      Ve.set { Z with laid := Zb.add ch (pairsBy tree (c.laid ++ y.1) 0) }
        (c.next L b y cols).ver := by
    intro new
    rw [Ve.add, Ve.get_laid, hv]
    show Ve.set { Z with laid := (Z.laid.add ch
        (pairsBy tree y.1 (c.laid.map fun p : Played => p.tables.length).sum)) }
      (c.ver.bind (judgeOff ch ft st b (ds.take b.rounds.length)
        (Z.laid.add ch
          (pairsBy tree y.1 (c.laid.map fun p : Played => p.tables.length).sum)))) = _
    rw [hlaid]
    have hver' : c.ver.bind (judgeOff ch ft st b (ds.take b.rounds.length)
        (Zb.add ch (pairsBy tree (c.laid ++ y.1) 0))) = (c.next L b y cols).ver := hver
    rw [hver']
  refine ⟨y, cols, l, hA, fun new => ?_⟩
  rw [hZ₂ new]
  exact
    { lc := hLc
      lf := hLf
      zb := hZ₀
      steps := hl
      chained := hC'
      laid := by rw [Ve.laid_set]; rfl
      ver := Ve.get_set _ _
      both := by
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
          rfl
      mid := by
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
            show m'.seen = ((Zb.add ch (pairsBy tree (c.laid ++ y.1) 0)).front ch st).seen
            rw [← hlaid, Laid.seen_add, pairs_rounds, a2, b2]
          · have hh : sb.map Step.hand = (chainKeys [b] hs).map (·.2) := by
              rw [← hkb, List.map_map]
              rfl
            show m'.st = _
            rw [a3, b3, hh, List.map_append, dryFold_append _ _ _ _ _ (by
              rw [List.length_map, hlen])]
          · show m'.loc = _
            rw [a4, b4, List.append_assoc]
      tie := by
        rw [Ve.laid_set]
        show TieAt earlier ch ft ((passed ++ [b]).flatMap (·.rounds)) (c.next L b y cols).mid
          ((Zb.add ch (pairsBy tree (c.laid ++ y.1) 0)).front ch st)
        rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact tie_over htie hZ hpart hy (by rw [hyl, hsbl]) ht2 hc' (hfc0 (c.laid ++ y.1))
      keys := by rw [hk, chainKeys_cons b bs hs, List.append_assoc]
      all := by rw [hd, List.append_assoc, ← hds]
      len := by rw [List.length_append, List.length_append, hlen, hown, hsbl, hkbl]
      fresh := by
        intro q hq
        have hnd' := List.nodup_cons.1 hnd
        rcases List.mem_append.1 hq with hq | hq
        · exact fun hmem => hfr q hq (List.mem_cons_of_mem _ hmem)
        · have := chainKeys_mem hs [b] q hq
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at this
          rw [this]
          exact hnd'.1
      whole := by rw [hall]; simp
      apart := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact fun hmem => hpass p hp (List.mem_cons_of_mem _ hmem)
        · rw [List.mem_singleton.1 hp]
          exact (List.nodup_cons.1 hnd).1
      faith := hfa'
      faithC := hfc'
      num := by
        show _ = ((c.laid ++ y.1).map (·.tables.length)).sum
        rw [List.map_append, List.sum_append, ht1, horc]
      lenp := by
        show (c.laid ++ y.1).length = _
        rw [List.length_append, List.length_append, hlenp, hyl, hsbl, hkbl]
      bare := fun z hz => hbare z (by rw [hcut]; exact List.mem_append.2 (Or.inr hz)) }

/-- **Before the first part of a list**, where the verifier has not rejected in the chain. -/
theorem ChainInv.row {k : Coins Bk} {L : Lay} {Zb : Laid} {bs : List (Block S Cl)}
    {ss : List (Step W Y)} {ds : List Fmt.Drawn} {n : Nat} {c c' : Core S W Y} {Z : Stand F}
    {kp : List (Addr × Option (State W Y → Y))} {dp : List Fmt.Drawn}
    {passed : List (Block S Cl)} (σ : Side S Cl V W Y Pb)
    (h : ChainInv x st ch ft tree φ hs keys dsAll m₀ Ve v Bq earlier bsAll k L Zb (σ.block :: bs) ss
      ds n c c' Z kp dp passed)
    (hnd : ((σ.block :: bs).map (·.place)).Nodup)
    (hshb : ∀ z ∈ σ.block.rounds.zip σ.block.oracles, z.2.length = z.1.entry.roots)
    (hpos : ∀ cs, Bk.cuts.lookup σ.block.place = some cs → ∀ n ∈ cs, n ≠ 0)
    {g : Placed V W Y} (hg : (hs.find? fun g => g.place == σ.block.place) = some g)
    (hparts : g.parts = σ.row.map (·.1)) (hlive : Z.live ch = true) :
    ∃ m cr y la, RowInv st ch ft tree φ σ v keys dsAll m₀ Bq
      (preOf ch ft earlier bsAll σ.block.place) k c'.laid Zb σ.row 0
      (σ.block.rounds.zip σ.block.oracles) (ds.take σ.block.rounds.length) n m Z cr y kp
      (chainKeys bs hs) dp (ds.drop σ.block.rounds.length) c.laid la := by
  obtain ⟨hLc, hLf, hZ₀, hss, hC, hZ, hv, hmv, hm, htie, hk, hd, hlen, hfr, hall, hpass, hfa, hfc,
    hnum, hlenp, hbare⟩ := h
  have hpre : preOf ch ft earlier bsAll σ.block.place =
      earlier ++ [(ch, ft, passed.flatMap (·.rounds))] := by
    rw [hall]
    exact preOf_at ch ft earlier passed σ.block bs fun p hp e =>
      hpass p hp (by rw [e]; exact List.mem_cons.2 (Or.inl rfl))
  obtain ⟨ho, l, hl, hcase⟩ := chainSteps_cons_ok hss
  rw [Chained] at hC
  obtain ⟨y, cols, hy, hc, hC'⟩ := hC
  obtain ⟨suf, hsuf⟩ := chained_laid _ _ _ _ _ hC'
  have hzl : (σ.block.rounds.zip σ.block.oracles).length = σ.block.rounds.length := by
    rw [List.length_zip, ho, Nat.min_self]
  rcases hcase with ⟨h1, -⟩ | ⟨g', cc, h1, hr, hcut, hlend, h5⟩
  · rw [hg] at h1
    cases h1
  have eg : g' = g := Option.some.inj (h1.symm.trans hg)
  subst eg
  obtain ⟨gp, gparts⟩ := g'
  have hparts' : gparts = σ.row.map (·.1) := hparts
  subst hparts'
  have hsl : ((⟨gp, σ.row.map (·.1)⟩ : Placed V W Y).steps σ.block v cc).length =
      σ.block.rounds.length := by
    have e := congrArg List.length (row_states _ σ.block v cc hr ho)
    rw [List.length_map, hzl] at e
    exact e
  have htake : ss.take σ.block.rounds.length =
      (⟨gp, σ.row.map (·.1)⟩ : Placed V W Y).steps σ.block v cc := by
    rw [h5]
    exact List.take_left' hsl
  rw [htake] at hy
  have hown := lays_draws _ _ _ _ hy
  have hrd : readsOf ch ft (fun _ _ => none) (fun _ => none) ((σ.block :: bs).flatMap (·.rounds))
      ds =
      readsOf ch ft (fun _ _ => none) (fun _ => none) σ.block.rounds (ds.take σ.block.rounds.length)
          ++
      readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds)) (ds.drop
          σ.block.rounds.length) := by
    conv_lhs => rw [← List.take_append_drop σ.block.rounds.length ds, List.flatMap_cons]
    exact readsOf_append ch ft _ _ _ _ _ _ (by rw [hown, hsl])
  have hcm : c.mid.isSome = true := by
    rw [hmv, ← hv, ← Ve.live]
    exact hlive
  obtain ⟨m, hmm⟩ := Option.isSome_iff_exists.1 hcm
  rw [hmm] at hy
  obtain ⟨b1, b2, b3, b4⟩ := hm m hmm
  obtain ⟨cs, hW, hF, hL⟩ := htie.member m hmm
  obtain ⟨m', -, hp⟩ := lays_live _ _ m y (fun s hs' hf => by
    rw [row_moves _ σ.block v cc hr ho s hs'] at hf
    cases hf) hy
  have hkeys : chainKeys [σ.block] hs =
      rowKeys σ.block.place (σ.row.map (·.1)) 0 (σ.block.rounds.zip σ.block.oracles) := by
    unfold chainKeys
    rw [List.flatMap_cons, hg, List.flatMap_nil, List.append_nil]
  have hds : ds = ds.take σ.block.rounds.length ++ ds.drop σ.block.rounds.length :=
    (List.take_append_drop _ _).symm
  refine ⟨m, cc, (y.1, m'), suf, ?_⟩
  rw [hpre]
  exact
    { play := hp
      lend := hlend
      sum := by
        have h0 : (⟨gp, σ.row.map (·.1)⟩ : Placed V W Y).rounds = σ.block.rounds.length := hr
        unfold Placed.rounds at h0
        rw [foldl_moves, Nat.zero_add, List.map_map] at h0
        rw [hzl]
        exact h0
      dlen := by rw [hown, hsl, hzl]
      pos := fun q hq =>
        hpos _ hcut _ (List.mem_map.2 ⟨q.1, List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩)
      shape := hshb
      sees := b1
      live := hlive
      seen := b2
      held := ⟨cs, hW, hF⟩
      drawn := hL
      keys := by rw [hk, chainKeys_cons σ.block bs hs, hkeys, List.append_assoc]
      all := by rw [hd, List.append_assoc, ← hds]
      len := hlen
      fresh := fun q hq => Or.inl fun e =>
        hfr q hq (by rw [e]; exact List.mem_cons.2 (Or.inl rfl))
      freshq := fun q hq e => by
        have := chainKeys_mem hs bs q hq
        rw [e] at this
        exact (List.nodup_cons.1 hnd).1 this
      st := b3
      loc := b4
      laid := hZ
      num := hnum
      fin := by
        rw [hsuf]
        rfl
      lenp := hlenp
      bare := fun z hz => hbare z (by
        rw [hrd]
        refine List.mem_append.2 (Or.inl ?_)
        have hzm : (σ.block.rounds.zip σ.block.oracles).map (·.1) = σ.block.rounds :=
          List.map_fst_zip (by rw [ho])
        rw [hzm] at hz
        exact hz) }

end

end ProofFile.Honest

#print axioms ProofFile.Honest.ChainInv.step
#print axioms ProofFile.Honest.ChainInv.row
#print axioms ProofFile.Honest.ChainInv
