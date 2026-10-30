-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Where.lean: where a part's cell is, without a coin. Of each
cell among a chain's items (Honest/Law/Rule/ChainHere.lean) the lemmas say: of which `Member` of
which side it is the cell; where that part's keys, challenges and rounds are in the chain's; that
the state and the challenges at which the cell is built are those of the dry fold there; that the
part is not stopped there, where the chain's prover's sides do not stop; and that its challenges are
such as its rounds can draw, where the chain's are. It is the seventh piece of the proof of
`rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`). The binders are those of
Honest/Law/Rule/ChainHere.lean; `rsAll`: all the chain's rounds. The dry fold:
Honest/Law/Rule/Dry.lean.

  1  `drawsFit_cut`, `none_of_or`   two small lemmas
  2  `PartCell`   the condition, as a definition
  3  `RowW`, `row_where`   a list of parts
  4  `ChainW`, `chain_where`   a chain

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainHere

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 Two small lemmas -/

theorem drawsFit_cut : ∀ (n : Nat) (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    drawsFit zs ds = true →
    drawsFit (zs.take n) (ds.take n) = true ∧ drawsFit (zs.drop n) (ds.drop n) = true
  | 0, zs, ds, h => ⟨by simp [drawsFit], by simpa using h⟩
  | n + 1, [], [], _ => ⟨by simp [drawsFit], by simp [drawsFit]⟩
  | n + 1, [], _ :: _, h => by simp [drawsFit] at h
  | n + 1, _ :: _, [], h => by simp [drawsFit] at h
  | n + 1, z :: zs, d :: ds, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := drawsFit_cut n zs ds h.2
    refine ⟨?_, ?_⟩
    · simp only [List.take_succ_cons, drawsFit, Bool.and_eq_true]
      exact ⟨h.1, h1⟩
    · simpa using h2

theorem none_of_or {α : Type} {a b : Option α} (h : a.or b = none) : a = none ∧ b = none := by
  cases a with
  | none => exact ⟨rfl, h⟩
  | some _ => cases h

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (ch ft : Nat) (tree : Nat → List Nat) (tl : Addr → Option Teller)
  (has : Place → Bool) (φ : Face V W Pb) (pb : Pb) (hs : List (Placed V W Y))
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)
  (Ve : VerAt F S Cl x st ch ft) (v : Option V)
  (seat : Block S Cl → Option (Side S Cl V W Y Pb × OnT V W Y Pb))
  (rsAll : List (Fmt.DeclaredRound × List Oracle))
  (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (bsAll : List (Block S Cl))

/-! ## 2 The condition -/

/-- **C is the cell of a `Member` of σ, and where that part is in its chain.** `kp`, `dp`, `rp`: the
chain's keys, challenges and rounds before the part; `kq`, `dq`, `rq`: those after it. With the
facts that the head lists. `pr`: the declared rounds whose reads the part is handed. `[]`, `none` in
the clause on `dryAt`: `dryAt`'s fillers; the cell reads neither. -/
def PartCell (pr : List (Nat × Nat × List Fmt.DeclaredRound)) (σ : Side S Cl V W Y Pb)
    (On : OnT V W Y Pb)
    (C : Cell Bk (Stand F) (List (Shown × Fmt.Drawn))) : Prop :=
  ∃ (u : Member V W Y Pb) (dsu : List Fmt.Drawn)
    (kp kq : List (Addr × Option (State W Y → Y))) (dp dq : List Fmt.Drawn)
    (rp rq : List (Fmt.DeclaredRound × List Oracle))
    (hf : Fit Bk ch ⟨σ.block.place, u.number⟩ u.part),
    u ∈ σ.members ∧
    C = cellAt φ σ u pb ch ft pr (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩) st dsu
      (asksFrom tree (u.rounds.map (·.2.length)) (rp.map (·.2.length)).sum) (On u) hf ∧
    keys = kp ++ (u.rounds.zip u.part.moves).map
      (fun z => ((⟨σ.block.place, u.number⟩ : Addr), some z.2.hand)) ++ kq ∧
    dsAll = dp ++ dsu ++ dq ∧ rsAll = rp ++ u.rounds ++ rq ∧
    dp.length = kp.length ∧ rp.length = kp.length ∧ dsu.length = u.rounds.length ∧
    u.rounds.length = u.part.moves.length ∧ u.part.moves.length ≠ 0 ∧
    (∀ q ∈ kp, q.1 ≠ ⟨σ.block.place, u.number⟩) ∧ (∀ q ∈ kq, q.1 ≠ ⟨σ.block.place, u.number⟩) ∧
    dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩ =
      ⟨dryFold (kp.map (·.2)) dp m₀.st, m₀.loc ++ dp, [], none⟩ ∧
    u.part.stopAt v (m₀.loc ++ dp) dsu = none ∧ drawsFit (u.rounds.map (·.1)) dsu = true

/-! ## 3 A list of parts -/

/-- A structure of hypotheses, without a coin, on what comes before part number j of σ's list;
`row_where` takes it and carries it along the list. -/
structure RowW (σ : Side S Cl V W Y Pb) (row : List (Part V W Y × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (ds : List Fmt.Drawn) (n : Nat)
    (kp kq : List (Addr × Option (State W Y → Y))) (dp dq : List Fmt.Drawn)
    (rp rq : List (Fmt.DeclaredRound × List Oracle)) : Prop where
  keys : keys = kp ++ rowKeys σ.block.place (row.map (·.1)) j rs ++ kq
  all : dsAll = dp ++ ds ++ dq
  rounds : rsAll = rp ++ rs ++ rq
  len : dp.length = kp.length
  lenr : rp.length = kp.length
  freshp : ∀ q ∈ kp, q.1.place ≠ σ.block.place ∨ q.1.part < j
  freshq : ∀ q ∈ kq, q.1.place ≠ σ.block.place
  sum : (row.map (·.1.moves.length)).sum = rs.length
  dlen : ds.length = rs.length
  pos : ∀ q ∈ row, q.1.moves.length ≠ 0
  stop : rowStopAt v (row.map (·.1)) (m₀.loc ++ dp) ds = none
  fit : drawsFit (rs.map (·.1)) ds = true
  num : n = (rp.map (·.2.length)).sum

/- The same for one list of parts: from `RowW`, where the list's members are members of σ. -/
theorem row_where (pr : List (Nat × Nat × List Fmt.DeclaredRound)) (σ : Side S Cl V W Y Pb)
    (On : OnT V W Y Pb) :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (ds : List Fmt.Drawn) (n : Nat) (kp kq : List (Addr × Option (State W Y → Y)))
      (dp dq : List Fmt.Drawn) (rp rq : List (Fmt.DeclaredRound × List Oracle)),
    RowW keys dsAll m₀ v rsAll σ row j rs ds n kp kq dp dq rp rq →
    (∀ u ∈ membersOf row j rs, u ∈ σ.members) →
    ∀ C, Item.cell C ∈ rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb On pr row j rs n ds
        →
    PartCell (F := F) st ch ft tree φ pb keys dsAll m₀ v rsAll pr σ On C
  | [], _, _, _, _, _, _, _, _, _, _, _, _, C, hC => by cases hC
  | q :: row, j, rs, ds, n, kp, kq, dp, dq, rp, rq, h, hmem, C, hC => by
    obtain ⟨hk, hd, hr, hlen, hlenr, hfp, hfq, hsum, hds, hne, hstop, hfit, hnum⟩ := h
    simp only [List.map_cons, List.sum_cons] at hsum
    have hq0 : q.1.moves.length ≠ 0 := hne q (List.mem_cons.2 (Or.inl rfl))
    have hle : q.1.moves.length ≤ rs.length := by omega
    have htk : (rs.take q.1.moves.length).length = q.1.moves.length := by
      rw [List.length_take]
      omega
    have hdk : (ds.take q.1.moves.length).length = q.1.moves.length := by
      rw [List.length_take]
      omega
    have hkl : (((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
        ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)).length = q.1.moves.length := by
      rw [List.length_map, List.length_zip, htk, Nat.min_self]
    have hk2 : keys = kp ++ ((rs.take q.1.moves.length).zip q.1.moves).map
        (fun z => ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)) ++
        (rowKeys σ.block.place (row.map (·.1)) (j + 1) (rs.drop q.1.moves.length) ++ kq) := by
      rw [hk]
      show kp ++ rowKeys σ.block.place (q.1 :: row.map (·.1)) j rs ++ kq = _
      rw [rowKeys]
      simp only [List.append_assoc]
    have hd2 : dsAll = dp ++ ds.take q.1.moves.length ++ (ds.drop q.1.moves.length ++ dq) := by
      conv_lhs => rw [hd, ← List.take_append_drop q.1.moves.length ds]
      simp only [List.append_assoc]
    have hr2 : rsAll = rp ++ rs.take q.1.moves.length ++ (rs.drop q.1.moves.length ++ rq) := by
      conv_lhs => rw [hr, ← List.take_append_drop q.1.moves.length rs]
      simp only [List.append_assoc]
    have hstop' : (q.1.stopAt v (m₀.loc ++ dp) (ds.take q.1.moves.length)).or
        (rowStopAt v (row.map (·.1)) (m₀.loc ++ dp ++ ds.take q.1.moves.length)
          (ds.drop q.1.moves.length)) = none := hstop
    obtain ⟨st1, st2⟩ := none_of_or hstop'
    obtain ⟨f1, f2⟩ := drawsFit_cut q.1.moves.length _ _ hfit
    rw [← List.map_take] at f1
    rw [← List.map_drop] at f2
    have hu : (⟨j, rs.take q.1.moves.length, q.1, q.2⟩ : Member V W Y Pb) ∈
        membersOf (q :: row) j rs := List.mem_cons.2 (Or.inl rfl)
    have hC' : Item.cell C = partItem (F := F) x st R ch ft φ σ keys dsAll m₀ pb On pr
        ⟨j, rs.take q.1.moves.length, q.1, q.2⟩ (ds.take q.1.moves.length)
        (asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n) ∨
        Item.cell C ∈ rowItems (F := F) x st R ch ft tree φ σ keys dsAll m₀ pb On pr row (j + 1)
          (rs.drop q.1.moves.length) (n + ((rs.take q.1.moves.length).map (·.2.length)).sum)
          (ds.drop q.1.moves.length) := List.mem_cons.1 hC
    rcases hC' with e | e
    · -- the part's own cell
      unfold partItem at e
      split at e
      · rename_i hf
        have eC := Item.cell.inj e
        have hrs0 : rs ≠ [] := by
          intro e'
          rw [e'] at hle
          exact hq0 (Nat.le_zero.1 hle)
        obtain ⟨h0, rest, hkeys⟩ := rowKeys_head σ.block.place q.1 (row.map (·.1)) j rs hq0 hrs0
        have hk' : keys = kp ++ ((⟨σ.block.place, j⟩ : Addr), h0) :: (rest ++ kq) := by
          rw [hk]
          show kp ++ rowKeys σ.block.place (q.1 :: row.map (·.1)) j rs ++ kq = _
          rw [hkeys, List.append_assoc]
          rfl
        have hfp' : ∀ z ∈ kp, z.1 ≠ (⟨σ.block.place, j⟩ : Addr) := fun z hz e' => by
          rcases hfp z hz with h | h
          · exact h (by rw [e'])
          · rw [e'] at h
            exact Nat.lt_irrefl _ h
        have hdry := dryAt_split (a := ⟨σ.block.place, j⟩) (h := h0) (rest := rest ++ kq)
          (dsAll := dsAll) (dp := dp) (dr := ds ++ dq) m₀ hk' hfp'
          (by rw [hd, List.append_assoc]) hlen
        refine ⟨⟨j, rs.take q.1.moves.length, q.1, q.2⟩, ds.take q.1.moves.length, kp, _, dp, _,
          rp, _, hf, hmem _ hu, ?_, hk2, hd2, hr2, hlen, hlenr, by rw [hdk, htk], htk, hq0, hfp',
          ?_, hdry, st1, f1⟩
        · rw [eC, hnum]
        · intro z hz e'
          rcases List.mem_append.1 hz with hz | hz
          · have := (rowKeys_mem σ.block.place _ _ _ z hz).2
            rw [e'] at this
            exact Nat.lt_irrefl _ this
          · exact hfq z hz (by rw [e'])
      · cases e
    · -- the parts after it
      refine row_where pr σ On row (j + 1) (rs.drop q.1.moves.length) (ds.drop q.1.moves.length)
        (n + ((rs.take q.1.moves.length).map (·.2.length)).sum)
        (kp ++ ((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
          ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)) kq (dp ++ ds.take q.1.moves.length) dq
        (rp ++ rs.take q.1.moves.length) rq ?_
        (fun u hu' => hmem u (List.mem_cons_of_mem _ hu')) C e
      exact
        { keys := by rw [hk2]; simp only [List.append_assoc]
          all := by rw [hd2]; simp only [List.append_assoc]
          rounds := by rw [hr2]; simp only [List.append_assoc]
          len := by rw [List.length_append, List.length_append, hlen, hdk, hkl]
          lenr := by rw [List.length_append, List.length_append, hlenr, htk, hkl]
          freshp := fun z hz => by
            rcases List.mem_append.1 hz with hz | hz
            · rcases hfp z hz with h | h
              · exact Or.inl h
              · exact Or.inr (by omega)
            · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
              exact Or.inr (Nat.lt_succ_self j)
          freshq := hfq
          sum := by rw [List.length_drop]; omega
          dlen := by rw [List.length_drop, List.length_drop, hds]
          pos := fun z hz => hne z (List.mem_cons_of_mem _ hz)
          stop := by rw [← List.append_assoc]; exact st2
          fit := f2
          num := by rw [List.map_append, List.sum_append, ← hnum] }

/-! ## 4 A chain -/

/-- A structure of hypotheses, without a coin, on what comes before the sub-protocols bs of a chain;
`chain_where` takes it and carries it along the chain. -/
structure ChainW (bs : List (Block S Cl)) (ds : List Fmt.Drawn) (n : Nat)
    (kp : List (Addr × Option (State W Y → Y))) (dp : List Fmt.Drawn)
    (rp : List (Fmt.DeclaredRound × List Oracle)) : Prop where
  keys : keys = kp ++ chainKeys bs hs
  all : dsAll = dp ++ ds
  rounds : rsAll = rp ++ bs.flatMap fun b => b.rounds.zip b.oracles
  len : dp.length = kp.length
  lenr : rp.length = kp.length
  fresh : ∀ q ∈ kp, q.1.place ∉ bs.map (·.place)
  stop : chainStopAt v bs hs (m₀.loc ++ dp) ds = none
  fit : drawsFit (bs.flatMap (·.rounds)) ds = true
  num : n = (rp.map (·.2.length)).sum

/- Each cell among a chain's items is as `PartCell` says, at the side that `seat` gives at one of
the sub-protocols, at `preOf` (Honest/Rule.lean) of `earlier` and `bsAll` at that side's place.
Seven hypotheses: `ChainW`; no two sub-protocols at one place; as many lists of
oracle messages as rounds; `chainKeys [b] hs` is as long as b's rounds; no part of a cut has 0
rounds; `SeatOk`; the list's moves add up to the sub-protocol's rounds. -/
theorem chain_where : ∀ (bs : List (Block S Cl)) (ds : List Fmt.Drawn) (n : Nat)
    (kp : List (Addr × Option (State W Y → Y))) (dp : List Fmt.Drawn)
    (rp : List (Fmt.DeclaredRound × List Oracle)),
    ChainW hs keys dsAll m₀ v rsAll bs ds n kp dp rp → (bs.map (·.place)).Nodup →
    (∀ b ∈ bs, b.oracles.length = b.rounds.length) →
    (∀ b ∈ bs, (chainKeys [b] hs).length = b.rounds.length) →
    (∀ b ∈ bs, ∀ cs, Bk.cuts.lookup b.place = some cs → ∀ n ∈ cs, n ≠ 0) →
    (∀ b ∈ bs, SeatOk (Bk := Bk) R ch ft tl has φ pb hs keys dsAll m₀ seat earlier bsAll b) →
    (∀ b ∈ bs, ∀ p, seat b = some p →
      (p.1.row.map (·.1.moves.length)).sum = (b.rounds.zip b.oracles).length) →
    ∀ C, Item.cell C ∈ chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier
        bsAll bs n ds →
    ∃ b ∈ bs, ∃ p, seat b = some p ∧
      PartCell (F := F) st ch ft tree φ pb keys dsAll m₀ v rsAll (preOf ch ft earlier bsAll
          p.1.block.place) p.1 p.2 C
  | [], _, _, _, _, _, _, _, _, _, _, _, _, C, hC => by cases hC
  | b :: bs, ds, n, kp, dp, rp, h, hnd, ho, hkl, hpos, hok, hsum, C, hC => by
    obtain ⟨hk, hd, hr, hlen, hlenr, hfr, hstop, hfit, hnum⟩ := h
    have hb : b ∈ b :: bs := List.mem_cons.2 (Or.inl rfl)
    have hzl : (b.rounds.zip b.oracles).length = b.rounds.length := by
      rw [List.length_zip, ho b hb, Nat.min_self]
    have hzm : (b.rounds.zip b.oracles).map (·.1) = b.rounds :=
      List.map_fst_zip (by rw [ho b hb])
    have hfit' : drawsFit (b.rounds ++ bs.flatMap (·.rounds)) ds = true := hfit
    have hdl := drawsFit_length _ _ hfit'
    rw [List.length_append] at hdl
    obtain ⟨f1, f2⟩ := drawsFit_cut b.rounds.length _ _ hfit'
    rw [List.take_left' rfl] at f1
    rw [List.drop_left' rfl] at f2
    have hdk : (ds.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    have hds : ds = ds.take b.rounds.length ++ ds.drop b.rounds.length :=
      (List.take_append_drop _ _).symm
    have hstop' : ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt v g.parts (m₀.loc ++ dp) (ds.take b.rounds.length)).or
        (chainStopAt v bs hs (m₀.loc ++ dp ++ ds.take b.rounds.length)
          (ds.drop b.rounds.length)) = none := hstop
    obtain ⟨st1, st2⟩ := none_of_or hstop'
    have hC' : Item.cell C ∈ memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier
        bsAll b n
        (ds.take b.rounds.length) ++
        Item.det (Act.stage x st R (Ve.J b (ds.take b.rounds.length))) (fun _ => []) ::
          chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll bs
            (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum) (ds.drop b.rounds.length) := hC
    rcases List.mem_append.1 hC' with e | e
    · -- the sub-protocol's own items
      cases hseat : seat b with
      | none =>
        rw [memberItems_none x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _
          hseat] at e
        have e' := List.mem_singleton.1 e
        cases e'
      | some p =>
        obtain ⟨hpb, ⟨g, hg, hparts⟩, -, hcut, -, -⟩ := (hok b hb).some p hseat
        cases hrow : p.1.row.isEmpty with
        | true =>
          rw [memberItems_bare x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow] at e
          have e' := List.mem_singleton.1 e
          cases e'
        | false =>
          rw [memberItems_row x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow] at e
          subst hpb
          have hkeys : chainKeys [p.1.block] hs = rowKeys p.1.block.place (p.1.row.map (·.1)) 0
              (p.1.block.rounds.zip p.1.block.oracles) := by
            unfold chainKeys
            rw [List.flatMap_cons, hg, List.flatMap_nil, List.append_nil]
            show rowKeys p.1.block.place g.parts 0 _ = _
            rw [hparts]
          rw [hg] at st1
          have st1' : rowStopAt v g.parts (m₀.loc ++ dp) (ds.take p.1.block.rounds.length) = none :=
            st1
          rw [hparts] at st1'
          refine ⟨p.1.block, hb, p, hseat, row_where x st R ch ft tree φ pb keys dsAll m₀ v rsAll
            (preOf ch ft earlier bsAll p.1.block.place) p.1 p.2 p.1.row 0 _ _ n kp (chainKeys bs hs)
                dp (ds.drop p.1.block.rounds.length) rp
            (bs.flatMap fun b => b.rounds.zip b.oracles) ?_ (fun u hu => hu) C e⟩
          exact
            { keys := by rw [hk, chainKeys_cons p.1.block bs hs, hkeys, List.append_assoc]
              all := by rw [hd, List.append_assoc, ← hds]
              rounds := by
                rw [hr, List.flatMap_cons, List.append_assoc]
              len := hlen
              lenr := hlenr
              freshp := fun q hq => Or.inl fun e' =>
                hfr q hq (by rw [e']; exact List.mem_cons.2 (Or.inl rfl))
              freshq := fun q hq e' => by
                have := chainKeys_mem hs bs q hq
                rw [e'] at this
                exact (List.nodup_cons.1 hnd).1 this
              sum := hsum _ hb p hseat
              dlen := by rw [hdk, hzl]
              pos := fun q hq => hpos _ hb _ hcut _ (List.mem_map.2 ⟨q, hq, rfl⟩)
              stop := st1'
              fit := by rw [hzm]; exact f1
              num := hnum }
    · rcases List.mem_cons.1 e with e | e
      · cases e
      · obtain ⟨b', hb', p, hp, hP⟩ := chain_where bs (ds.drop b.rounds.length)
          (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum) (kp ++ chainKeys [b] hs)
          (dp ++ ds.take b.rounds.length) (rp ++ b.rounds.zip b.oracles)
          { keys := by rw [hk, chainKeys_cons b bs hs, List.append_assoc]
            all := by rw [hd, List.append_assoc, ← hds]
            rounds := by rw [hr, List.flatMap_cons, List.append_assoc]
            len := by rw [List.length_append, List.length_append, hlen, hdk, hkl b hb]
            lenr := by rw [List.length_append, List.length_append, hlenr, hzl, hkl b hb]
            fresh := by
              intro q hq
              have hnd' := List.nodup_cons.1 hnd
              rcases List.mem_append.1 hq with hq | hq
              · exact fun hmem => hfr q hq (List.mem_cons_of_mem _ hmem)
              · have := chainKeys_mem hs [b] q hq
                simp only [List.map_cons, List.map_nil, List.mem_singleton] at this
                rw [this]
                exact hnd'.1
            stop := by rw [← List.append_assoc]; exact st2
            fit := f2
            num := by rw [List.map_append, List.sum_append, ← hnum] }
          (List.nodup_cons.1 hnd).2 (fun b' hb' => ho b' (List.mem_cons_of_mem _ hb'))
          (fun b' hb' => hkl b' (List.mem_cons_of_mem _ hb'))
          (fun b' hb' => hpos b' (List.mem_cons_of_mem _ hb'))
          (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb'))
          (fun b' hb' => hsum b' (List.mem_cons_of_mem _ hb')) C e
        exact ⟨b', List.mem_cons_of_mem _ hb', p, hp, hP⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.drawsFit_cut
#print axioms ProofFile.Honest.none_of_or
#print axioms ProofFile.Honest.row_where
#print axioms ProofFile.Honest.chain_where
#print axioms ProofFile.Honest.PartCell
#print axioms ProofFile.Honest.RowW
#print axioms ProofFile.Honest.ChainW
