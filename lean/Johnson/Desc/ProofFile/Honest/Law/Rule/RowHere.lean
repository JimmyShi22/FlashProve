-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/RowHere.lean: one list of parts: its parts as items
(Honest/Law/Rule/Items.lean), whose stages are those of the list's stretches
(Honest/Law/Rule/Real.lean); and `HereAll` (Honest/Law/Rule/Here.lean) of them, from what holds
before the list at all coins at which the verifier has not rejected in the chain (`row_here`). The
condition on `On` is a hypothesis here (`hOn`): it is given the part's position among its chain's
rounds, and `OpenedAt` (Honest/Law/Rule/OpenedAt.lean) at the part's state. `RowInv`'s fields `held`
and `drawn` are read off `ChainInv.tie` by `ChainInv.row` (Honest/Law/Rule/ChainStep.lean). It is
the fourth piece of the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `SegAt`, `RowInv`, `RowInv.step`   what holds before a part, at given coins; it is preserved
     over the part
  2  `partItem`, `partItem_stage`, `rowItems`, `rowItems_stage`   the items
  3  `row_here`   the main lemma

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowModel
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartCell
import Johnson.Desc.ProofFile.Honest.Law.Rule.Here

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi S Cl V W Y Pb : Type}

/-- **The keys at an address form one contiguous stretch of a chain's keys.** `kp`, `ku`, `kq`:
before it, at it, after it. -/
structure SegAt {β : Type} (keys : List (Addr × β)) (a : Addr) (kp ku kq : List (Addr × β)) :
    Prop where
  eq : keys = kp ++ ku ++ kq
  front : ∀ q ∈ kp, q.1 ≠ a
  own : ∀ q ∈ ku, q.1 = a
  behind : ∀ q ∈ kq, q.1 ≠ a
  pos : ku ≠ []

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (ch ft : Nat) (tree : Nat → List Nat) (φ : Face V W Pb)
  (σ : Side S Cl V W Y Pb) (v : Option V) (keys : List (Addr × Option (State W Y → Y)))
  (dsAll : List Fmt.Drawn) (m₀ : Mid W Y) (pb : Pb)
  (OnG : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop)
  (Bq : List Read) (pr : List (Nat × Nat × List Fmt.DeclaredRound))

/-! ## 1 Before a part, at given coins -/

/-- **What holds before part number j of a list, at given coins, where the verifier has not rejected
in the chain.** `pl`: the chain's rounds at the run's end. `Zb`: what has been produced before the
chain. `lp`: the chain's rounds so far. `la`: those after the list. The rest as in `row_model`
(Honest/Law/Rule/RowModel.lean). `Bq`: a list in which all reads of the list's own rounds lie
(`bare`); the hypothesis `hOn` of `row_here` may use it. `OnG`: the side's parameter `On`, part by
part. `ft`: the number in the label of the chain's first own tree. `num`: n is how many trees the
chain has sent so far. `lenp`: as many rounds so far as keys before. `freshq`: no key after the list
is at its place. `pr`: the declared rounds whose reads the list's parts are handed. `held`: the
state's field is `some` of the columns that what has been produced holds for these reads (`HeldAt`,
Honest/Law/Rule/OpenedAt.lean). `drawn`: it holds a challenge for each of these rounds. -/
structure RowInv (k : Coins Bk) (pl : List Played) (Zb : Laid)
    (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
    (ds : List Fmt.Drawn) (n : Nat) (m : Mid W Y) (Z : Stand F) (c : RowCoins (row.map (·.1)))
    (y : List Played × Mid W Y) (kp kq : List (Addr × Option (State W Y → Y)))
    (dp dq : List Fmt.Drawn) (lp la : List Played) : Prop where
  play : play (rowSteps σ.block.name σ.block.place v (row.map (·.1)) j rs c) ds [] m = .ok y
  lend : lendRow Bk (Bk.rowsOf ch) (k.look ch) σ.block.place (row.map (·.1)) j = .ok c
  sum : (row.map (·.1.moves.length)).sum = rs.length
  dlen : ds.length = rs.length
  pos : ∀ q ∈ row, q.1.moves.length ≠ 0
  shape : ∀ z ∈ rs, z.2.length = z.1.entry.roots
  sees : v = φ.sees m.st.input
  live : Z.live ch = true
  seen : m.seen = (Z.laid.front ch st).seen
  held : ∃ cs : List OpenedColumn, m.opened = some cs ∧ HeldAt pr (Z.laid.front ch st) cs
  drawn : ∀ x ∈ pr, x.2.2.length ≤ ((Z.laid.front ch st).drawnOf x.1).length
  keys : keys = kp ++ rowKeys σ.block.place (row.map (·.1)) j rs ++ kq
  all : dsAll = dp ++ ds ++ dq
  len : dp.length = kp.length
  fresh : ∀ q ∈ kp, q.1.place ≠ σ.block.place ∨ q.1.part < j
  freshq : ∀ q ∈ kq, q.1.place ≠ σ.block.place
  st : m.st = dryFold (kp.map (·.2)) dp m₀.st
  loc : m.loc = m₀.loc ++ dp
  laid : Z.laid = Zb.add ch (pairsBy tree lp 0)
  num : n = (lp.map (·.tables.length)).sum
  fin : pl = lp ++ y.1 ++ la
  lenp : lp.length = kp.length
  bare : ∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (rs.map (·.1)) ds, q ∈ Bq

/-- **Over one part.** -/
theorem RowInv.step {k : Coins Bk} {pl : List Played} {Zb : Laid} {q : Part V W Y × Sim Pb}
    {row : List (Part V W Y × Sim Pb)} {j : Nat} {rs : List (Fmt.DeclaredRound × List Oracle)}
    {ds : List Fmt.Drawn} {n : Nat} {m : Mid W Y} {Z : Stand F}
    {c : RowCoins ((q :: row).map (·.1))} {y : List Played × Mid W Y}
    {kp kq : List (Addr × Option (State W Y → Y))} {dp dq : List Fmt.Drawn}
    {lp la : List Played}
    (h : RowInv st ch ft tree φ σ v keys dsAll m₀ Bq pr k pl Zb (q :: row) j rs ds n m Z c y kp kq
      dp dq lp la)
    (hR : R ch ⟨σ.block.place, j⟩ = partShows φ σ ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ Bk ch pr
      (dryAt keys dsAll m₀ ⟨σ.block.place, j⟩)) (t : Teller) :
    ∃ y₁ y₂ : List Played × Mid W Y,
      ProofFile.Honest.play (q.1.steps σ.block.name ⟨σ.block.place, j⟩ (rs.take q.1.moves.length) v c.1)
        (ds.take q.1.moves.length) [] m = .ok y₁ ∧
      lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨σ.block.place, j⟩ q.1 = .ok c.1 ∧
      (dryAt keys dsAll m₀ ⟨σ.block.place, j⟩).st = m.st ∧
      (dryAt keys dsAll m₀ ⟨σ.block.place, j⟩).loc = m.loc ∧
      y₁.1.map (·.drawn) = ds.take q.1.moves.length ∧
      pl = lp ++ y₁.1 ++ (y₂.1 ++ la) ∧ y₁.1 ≠ [] ∧
      (∀ z ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) ((rs.take q.1.moves.length).map (·.1))
        (ds.take q.1.moves.length), z ∈ Bq) ∧
      SegAt keys ⟨σ.block.place, j⟩ kp (((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
          ((⟨σ.block.place, j⟩ : Addr), some z.2.hand))
        (rowKeys σ.block.place (row.map (·.1)) (j + 1) (rs.drop q.1.moves.length) ++ kq) ∧
      (Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, j⟩, rs.take q.1.moves.length,
        ds.take q.1.moves.length,
        asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n, some t⟩ : Act F)).shows k Z =
        pairsBy tree y₁.1 n ∧
      RowInv st ch ft tree φ σ v keys dsAll m₀ Bq pr k pl Zb row (j + 1) (rs.drop q.1.moves.length)
        (ds.drop q.1.moves.length) (n + ((rs.take q.1.moves.length).map (·.2.length)).sum) y₁.2
        { Z with laid := Z.laid.add ch (pairsBy tree y₁.1 n) } c.2 y₂
        (kp ++ ((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
          ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)) kq (dp ++ ds.take q.1.moves.length) dq
        (lp ++ y₁.1) la := by
  obtain ⟨hp, hl, hsum, hds, hne, hsh, hv, hlive, hseen, ⟨cs, hW, hF⟩, hL, hk, hd, hlen, hfr, hfq,
    hst, hloc, hlaid, hnum, hfin, hlenp, hbare⟩ := h
  simp only [List.map_cons, List.sum_cons] at hsum
  obtain ⟨l1, l2⟩ := lendRow_cons_ok (p := q.1) (ps := row.map (·.1)) hl
  have hq0 : q.1.moves.length ≠ 0 := hne q (List.mem_cons.2 (Or.inl rfl))
  have hle : q.1.moves.length ≤ rs.length := by omega
  have htk : (rs.take q.1.moves.length).length = q.1.moves.length := by
    rw [List.length_take]
    omega
  have htk' : (rs.take q.1.moves.length).length ≤ q.1.moves.length := Nat.le_of_eq htk
  have hdk : (ds.take q.1.moves.length).length = q.1.moves.length := by
    rw [List.length_take]
    omega
  have hp' : ProofFile.Honest.play (q.1.steps σ.block.name ⟨σ.block.place, j⟩
            (rs.take q.1.moves.length) v c.1 ++
            rowSteps σ.block.name σ.block.place v (row.map (·.1)) (j + 1)
              (rs.drop q.1.moves.length) c.2)
      (ds.take q.1.moves.length ++ ds.drop q.1.moves.length) [] m = .ok y := by
    rw [List.take_append_drop]
    exact hp
  rw [play_append _ _ _ _ _ _ (by rw [hdk, steps_len _ _ _ _ _ _ htk', htk])] at hp'
  obtain ⟨y₁, h1, hp'⟩ := exBind_ok hp'
  obtain ⟨y₂, h2, e⟩ := exMap_ok hp'
  subst e
  have h2' : ProofFile.Honest.play (rowSteps σ.block.name σ.block.place v (row.map (·.1)) (j + 1)
            (rs.drop q.1.moves.length) c.2) (ds.drop q.1.moves.length) [] y₁.2 = .ok y₂ := by
    simpa using h2
  obtain ⟨i1, i2, i3⟩ := play_mid _ _ _ _ _ h1
  obtain ⟨d1, d2⟩ := play_dry _ _ _ _ _ h1
  obtain ⟨s1, s2⟩ := play_shape _ _ _ _ _ h1 (steps_shape q.1 σ.block.name ⟨σ.block.place, j⟩
    (rs.take q.1.moves.length) v c.1 htk' fun z hz => hsh z (List.mem_of_mem_take hz))
  rw [steps_orc q.1 σ.block.name ⟨σ.block.place, j⟩ (rs.take q.1.moves.length) v c.1 htk'] at s1
  have hrs0 : rs ≠ [] := by
    intro e
    rw [e] at hle
    exact hq0 (Nat.le_zero.1 hle)
  obtain ⟨h0, rest, hkeys⟩ := rowKeys_head σ.block.place q.1 (row.map (·.1)) j rs hq0 hrs0
  have hk' : keys = kp ++ ((⟨σ.block.place, j⟩ : Addr), h0) :: (rest ++ kq) := by
    rw [hk]
    show kp ++ rowKeys σ.block.place (q.1 :: row.map (·.1)) j rs ++ kq = _
    rw [hkeys, List.append_assoc]
    rfl
  have hdry := dryAt_split (a := ⟨σ.block.place, j⟩) (h := h0) (rest := rest ++ kq)
    (dsAll := dsAll) (dp := dp) (dr := ds ++ dq) m₀ hk'
    (fun z hz e => by
      rcases hfr z hz with h | h
      · exact h (by rw [e])
      · rw [e] at h
        exact Nat.lt_irrefl _ h)
    (by rw [hd, List.append_assoc]) hlen
  have hshow := part_model x st R k ch tree φ σ ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ n
    (ds.take q.1.moves.length) m Z c.1 y₁ (by rw [← hv]; exact h1) l1 htk'
    (fun z hz => hsh z (List.mem_of_mem_take hz)) hlive hseen (OpenedAt.of_halves hW hF)
    (dryAt keys dsAll m₀ ⟨σ.block.place, j⟩)
    (by rw [hdry]; exact hst) (by rw [hdry]; exact hloc) hR t
  have hkp : (q.1.steps σ.block.name ⟨σ.block.place, j⟩ (rs.take q.1.moves.length) v c.1).map
      Step.hand = (((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
        ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)).map (·.2) := by
    rw [← Part.steps_keys q.1 σ.block.name ⟨σ.block.place, j⟩ (rs.take q.1.moves.length) v c.1,
      List.map_map]
    rfl
  have hkl : (((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
      ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)).length = q.1.moves.length := by
    rw [List.length_map, List.length_zip, htk, Nat.min_self]
  have hyl : y₁.1.length = q.1.moves.length := by
    have := congrArg List.length s2
    rw [List.length_map, hdk] at this
    exact this
  have hcut : readsOf ch ft (fun _ _ => none) (fun _ => none) (rs.map (·.1)) ds =
      readsOf ch ft (fun _ _ => none) (fun _ => none) ((rs.take q.1.moves.length).map (·.1))
        (ds.take q.1.moves.length) ++
      readsOf ch ft (fun _ _ => none) (fun _ => none) ((rs.drop q.1.moves.length).map (·.1))
        (ds.drop q.1.moves.length) := by
    conv_lhs => rw [← List.take_append_drop q.1.moves.length rs,
      ← List.take_append_drop q.1.moves.length ds, List.map_append]
    exact readsOf_append ch ft _ _ _ _ _ _ (by rw [List.length_map, htk, hdk])
  refine ⟨y₁, y₂, h1, l1, by rw [hdry]; exact hst.symm, by rw [hdry]; exact hloc.symm, s2, ?_,
    (fun e => hq0 (by rw [← hyl, e]; rfl)),
    fun z hz => hbare z (by rw [hcut]; exact List.mem_append.2 (Or.inl hz)), ?_, hshow, ?_⟩
  · rw [hfin]
    simp only [List.append_assoc]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hk]
      show kp ++ rowKeys σ.block.place (q.1 :: row.map (·.1)) j rs ++ kq = _
      rw [rowKeys]
      simp only [List.append_assoc]
    · intro z hz e
      rcases hfr z hz with h | h
      · exact h (by rw [e])
      · rw [e] at h
        exact Nat.lt_irrefl _ h
    · intro z hz
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
      rfl
    · intro z hz e
      rcases List.mem_append.1 hz with hz | hz
      · have := (rowKeys_mem σ.block.place _ _ _ z hz).2
        rw [e] at this
        exact Nat.lt_irrefl _ this
      · exact hfq z hz (by rw [e])
    · intro e
      have := congrArg List.length e
      rw [hkl] at this
      exact hq0 this
  · exact
      { play := h2'
        lend := l2
        sum := by rw [List.length_drop]; omega
        dlen := by rw [List.length_drop, List.length_drop, hds]
        pos := fun z hz => hne z (List.mem_cons_of_mem _ hz)
        shape := fun z hz => hsh z (List.mem_of_mem_drop hz)
        sees := by rw [i1]; exact hv
        live := hlive
        seen := by
          show y₁.2.seen = ((Z.laid.add ch (pairsBy tree y₁.1 n)).front ch st).seen
          rw [Laid.seen_add, pairs_rounds, i3, hseen]
        held := ⟨cs, by rw [play_opened _ _ _ _ _ h1]; exact hW, by
          show HeldAt pr ((Z.laid.add ch (pairsBy tree y₁.1 n)).front ch st) cs
          rw [Laid.front_add]
          exact hF.more _ hL⟩
        drawn := fun z hz => by
          show z.2.2.length ≤
            (((Z.laid.add ch (pairsBy tree y₁.1 n)).front ch st).drawnOf z.1).length
          rw [Laid.front_add]
          exact Nat.le_trans (hL z hz) (Before.drawnOf_more _ _ _).length_le
        keys := by
          rw [hk]
          show kp ++ rowKeys σ.block.place (q.1 :: row.map (·.1)) j rs ++ kq = _
          rw [rowKeys]
          simp only [List.append_assoc]
        all := by
          conv_lhs => rw [hd, ← List.take_append_drop q.1.moves.length ds]
          simp only [List.append_assoc]
        len := by rw [List.length_append, List.length_append, hlen, hdk, hkl]
        fresh := fun z hz => by
          rcases List.mem_append.1 hz with hz | hz
          · rcases hfr z hz with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
          · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
            exact Or.inr (Nat.lt_succ_self j)
        freshq := hfq
        st := by
          rw [d1, hst, hkp, List.map_append, dryFold_append _ _ _ _ _ (by
            rw [List.length_map, hlen])]
        loc := by rw [d2, hloc, List.append_assoc]
        laid := by
          show Z.laid.add ch (pairsBy tree y₁.1 n) = _
          rw [hlaid, Laid.add_add, pairsBy_append, Nat.zero_add, ← hnum]
        num := by rw [List.map_append, List.sum_append, ← hnum, s1]
        fin := by
          rw [hfin]
          simp only [List.append_assoc]
        lenp := by rw [List.length_append, List.length_append, hlenp, hyl, hkl]
        bare := fun z hz => hbare z (by rw [hcut]; exact List.mem_append.2 (Or.inr hz)) }

/-! ## 2 The items -/

open Classical in
/-- A part's item: its cell, where the part fits the book; otherwise a placeholder: the stretch's
stage, as an item `det`. The function beside it, `fun _ => []`, is a filler and need not be what the
stage shows: `RowOk.det` is not proved of a placeholder, so a caller has to prove `Fit` of every
part. Whether the part fits is decided classically: no program decides it. -/
noncomputable def partItem (u : Member V W Y Pb) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) : Item Bk (Stand F) (List (Shown × Fmt.Drawn)) :=
  if hf : Fit Bk ch ⟨σ.block.place, u.number⟩ u.part then
    .cell (cellAt φ σ u pb ch ft pr (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩) st ds asks
      (OnG u) hf)
  else .det (Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks,
    some ⟨u.sim.takes, u.sim.tell pb⟩⟩ : Act F)) fun _ => []

theorem partItem_stage (u : Member V W Y Pb) (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (hR : R ch ⟨σ.block.place, u.number⟩ =
      partShows φ σ u Bk ch pr (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩)) :
    (partItem (F := F) x st R ch ft φ σ keys dsAll m₀ pb OnG pr u ds asks).stage =
      Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks,
        some ⟨u.sim.takes, u.sim.tell pb⟩⟩ : Act F) := by
  unfold partItem
  split
  · exact cellAt_stage φ σ u pb ch ft pr _ st ds asks (OnG u) _ x R hR
  · rfl

/-- The items of a list of parts, cut as `cutRow` (Honest/Law/Rule/Session.lean) cuts its stretches.
-/
noncomputable def rowItems : List (Part V W Y × Sim Pb) → Nat →
    List (Fmt.DeclaredRound × List Oracle) → Nat → List Fmt.Drawn →
    List (Item Bk (Stand F) (List (Shown × Fmt.Drawn)))
  | [], _, _, _, _ => []
  | q :: row, j, rs, n, ds =>
    partItem x st R ch ft φ σ keys dsAll m₀ pb OnG pr ⟨j, rs.take q.1.moves.length, q.1, q.2⟩
        (ds.take q.1.moves.length)
        (asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n) ::
      rowItems row (j + 1) (rs.drop q.1.moves.length)
        (n + ((rs.take q.1.moves.length).map (·.2.length)).sum) (ds.drop q.1.moves.length)

theorem rowItems_stage (tl : Addr → Option Teller) :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (n : Nat) (ds : List Fmt.Drawn),
    (∀ u ∈ membersOf row j rs, R ch ⟨σ.block.place, u.number⟩ =
      partShows φ σ u Bk ch pr (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩)) →
    (∀ u ∈ membersOf row j rs,
      tl ⟨σ.block.place, u.number⟩ = some ⟨u.sim.takes, u.sim.tell pb⟩) →
    (rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb OnG pr row j rs n ds).map Item.stage =
      (cutRow ch tree tl σ.block.place j (row.map (·.1.moves.length)) rs n ds).map
        fun s => Act.stage x st R (.lay s : Act F)
  | [], _, _, _, _, _, _ => rfl
  | q :: row, j, rs, n, ds, hR, htl => by
    have hu : (⟨j, rs.take q.1.moves.length, q.1, q.2⟩ : Member V W Y Pb) ∈
        membersOf (q :: row) j rs := List.mem_cons.2 (Or.inl rfl)
    have ih := rowItems_stage tl row (j + 1) (rs.drop q.1.moves.length)
      (n + ((rs.take q.1.moves.length).map (·.2.length)).sum) (ds.drop q.1.moves.length)
      (fun u hu' => hR u (List.mem_cons_of_mem _ hu'))
      (fun u hu' => htl u (List.mem_cons_of_mem _ hu'))
    have ht : tl ⟨σ.block.place, j⟩ = some ⟨q.2.takes, q.2.tell pb⟩ := htl _ hu
    show (partItem (F := F) x st R ch ft φ σ keys dsAll m₀ pb OnG pr
        ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ (ds.take q.1.moves.length)
        (asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n)).stage :: _ =
      Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, j⟩, rs.take q.1.moves.length,
        ds.take q.1.moves.length, asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n,
        tl ⟨σ.block.place, j⟩⟩ : Act F) :: _
    rw [partItem_stage x st R ch ft φ σ keys dsAll m₀ pb OnG pr _ _ _ (hR _ hu), ht]
    exact congrArg _ ih

/-! ## 3 The main lemma -/

/-- **One list of parts.** `pre`: the stages before the list's part number j. `pl`, `Zb`: at all
coins, the chain's rounds at the run's end, and what has been produced before the chain. The last
hypothesis: `RowInv`, at all coins at which the verifier has not rejected in the chain there. `hOn`:
the condition on `On` and on the columns that the part's own rounds read, at a part whose position
among the chain's rounds is known; it may use `OpenedAt` at the part's state, at `pr` and
at what has been produced. -/
theorem row_here (Z₀ : Stand F) (pl : Coins Bk → List Played) (Zb : Coins Bk → Laid)
    (hOn : ∀ (k : Coins Bk) (u : Member V W Y Pb) (ds : List Fmt.Drawn) (Z : Stand F)
      (c : u.part.Coins) (m : Mid W Y) (y₁ : List Played × Mid W Y) (lp la : List Played)
      (kp ku kq : List (Addr × Option (State W Y → Y))),
      u ∈ σ.members → Z.live ch = true → Z.laid = (Zb k).add ch (pairsBy tree lp 0) →
      pl k = lp ++ y₁.1 ++ la → y₁.1 ≠ [] → SegAt keys ⟨σ.block.place, u.number⟩ kp ku kq →
      lp.length = kp.length →
      (∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (u.rounds.map (·.1)) ds, q ∈ Bq) →
      lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨σ.block.place, u.number⟩ u.part = .ok c →
      play (u.part.steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds v c) ds [] m = .ok y₁ →
      (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).st = m.st →
      (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩).loc = m.loc →
      m.seen = (Z.laid.front ch st).seen → OpenedAt pr m (Z.laid.front ch st) →
      OnG u c.2.2 m (Z.laid.front ch st) ∧
        (Z.laid.front ch st).holds ch ft (u.rounds.map (·.1)) ds = true) :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (n : Nat) (ds : List Fmt.Drawn)
      (pre : List (Kit.Stage (Coins Bk) (Stand F) (List (Shown × Fmt.Drawn)))),
    (∀ u ∈ membersOf row j rs, u ∈ σ.members) →
    (∀ u ∈ membersOf row j rs, R ch ⟨σ.block.place, u.number⟩ =
      partShows φ σ u Bk ch pr (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩)) →
    (∀ k, (Kit.real pre k Z₀).live ch = true → ∃ m c y kp kq dp dq lp la,
      RowInv st ch ft tree φ σ v keys dsAll m₀ Bq pr k (pl k) (Zb k) row j rs ds n m
        (Kit.real pre k Z₀) c y kp kq dp dq lp la) →
    HereAll Z₀ pre (rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb OnG pr row j rs n ds)
  | [], _, _, _, _, _, _, _, _ => trivial
  | q :: row, j, rs, n, ds, pre, hmem, hR, hinv => by
    have hu : (⟨j, rs.take q.1.moves.length, q.1, q.2⟩ : Member V W Y Pb) ∈
        membersOf (q :: row) j rs := List.mem_cons.2 (Or.inl rfl)
    have hst := partItem_stage (F := F) x st R ch ft φ σ keys dsAll m₀ pb OnG pr
      ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ (ds.take q.1.moves.length)
      (asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n) (hR _ hu)
    refine HereAll.cons (fun C hC => ?_) ?_
    · -- the part's own cell
      intro k hlive
      unfold partItem at hC
      split at hC
      · rename_i hf
        have eC := Item.cell.inj hC
        subst eC
        have hlive' : (Kit.real pre k Z₀).live ch = true := hlive
        obtain ⟨m, c, y, kp, kq, dp, dq, lp, la, hI⟩ := hinv k hlive'
        obtain ⟨y₁, y₂, h1, l1, e1, e2, s2, hfin, hne₁, hbq, hseg, -, -⟩ :=
          RowInv.step x st R ch ft tree φ σ v keys dsAll m₀ Bq pr hI (hR _ hu)
            ⟨q.2.takes, q.2.tell pb⟩
        obtain ⟨cs, hW, hF⟩ := hI.held
        have ho : OpenedAt pr m ((Kit.real pre k Z₀).laid.front ch st) := OpenedAt.of_halves hW hF
        have ho' : m.opened = ((Kit.real pre k Z₀).laid.front ch st).opened
            (readsBefore pr ((Kit.real pre k Z₀).laid.front ch st)) := ho
        have em : (⟨(dryAt keys dsAll m₀ ⟨σ.block.place, j⟩).st,
            (dryAt keys dsAll m₀ ⟨σ.block.place, j⟩).loc,
            ((Kit.real pre k Z₀).laid.front ch st).seen,
            ((Kit.real pre k Z₀).laid.front ch st).opened
              (readsBefore pr ((Kit.real pre k Z₀).laid.front ch st))⟩ : Mid W Y) = m := by
          rw [e1, e2, ← hI.seen, ← ho']
        have hv' : φ.sees (dryAt keys dsAll m₀ ⟨σ.block.place, j⟩).st.input = v := by
          rw [e1]
          exact hI.sees.symm
        obtain ⟨sp, ca, w, g1, g2, g3, g4⟩ := cell_here (F := F) φ σ
          ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ pb ch ft pr
          (dryAt keys dsAll m₀ ⟨σ.block.place, j⟩) st (ds.take q.1.moves.length)
          (asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n)
          (OnG ⟨j, rs.take q.1.moves.length, q.1, q.2⟩) hf k (Kit.real pre k Z₀) c.1 y₁ l1
          (by rw [hv', em]; exact h1) s2
        obtain ⟨o1, o2⟩ := hOn k ⟨j, rs.take q.1.moves.length, q.1, q.2⟩
          (ds.take q.1.moves.length) (Kit.real pre k Z₀) c.1 m y₁ lp (y₂.1 ++ la) kp _ _
          (hmem _ hu) hlive' hI.laid hfin hne₁ hseg hI.lenp hbq l1 h1 e1 e2 hI.seen ho
        refine ⟨sp, ca, w, g1, g2, ⟨?_, o2⟩, g4⟩
        show OnG ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ (castAll hf.ca ca) _ _
        rw [g3, em]
        exact o1
      · cases hC
    · -- the parts after it
      refine row_here Z₀ pl Zb hOn row (j + 1) (rs.drop q.1.moves.length)
        (n + ((rs.take q.1.moves.length).map (·.2.length)).sum) (ds.drop q.1.moves.length) _
        (fun u hu' => hmem u (List.mem_cons_of_mem _ hu'))
        (fun u hu' => hR u (List.mem_cons_of_mem _ hu')) fun k hlive => ?_
      rw [hst, Kit.real_append] at hlive ⊢
      have hlive' : (Kit.real pre k Z₀).live ch = true := hlive
      obtain ⟨m, c, y, kp, kq, dp, dq, lp, la, hI⟩ := hinv k hlive'
      obtain ⟨y₁, y₂, -, -, -, -, -, -, -, -, -, hshow, hI'⟩ :=
        RowInv.step x st R ch ft tree φ σ v keys dsAll m₀ Bq pr hI (hR _ hu)
            ⟨q.2.takes, q.2.tell pb⟩
      refine ⟨y₁.2, c.2, y₂, kp ++ ((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
        ((⟨σ.block.place, j⟩ : Addr), some z.2.hand), kq, dp ++ ds.take q.1.moves.length, dq,
        lp ++ y₁.1, la, ?_⟩
      show RowInv st ch ft tree φ σ v keys dsAll m₀ Bq pr k (pl k) (Zb k) row (j + 1) _ _ _ y₁.2
        { Kit.real pre k Z₀ with laid := ((Kit.real pre k Z₀).laid.add ch
          ((Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, j⟩, rs.take q.1.moves.length,
            ds.take q.1.moves.length,
            asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n,
            some ⟨q.2.takes, q.2.tell pb⟩⟩ : Act F)).shows k (Kit.real pre k Z₀))) } c.2 y₂ _ kq _
        dq _ la
      rw [hshow]
      exact hI'

end

end ProofFile.Honest

#print axioms ProofFile.Honest.RowInv.step
#print axioms ProofFile.Honest.partItem_stage
#print axioms ProofFile.Honest.rowItems_stage
#print axioms ProofFile.Honest.row_here
#print axioms ProofFile.Honest.SegAt
#print axioms ProofFile.Honest.RowInv
#print axioms ProofFile.Honest.partItem
#print axioms ProofFile.Honest.rowItems
