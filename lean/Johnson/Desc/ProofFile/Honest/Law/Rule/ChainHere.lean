-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/ChainHere.lean: one chain: its steps as items
(Honest/Law/Rule/Items.lean), whose stages are the steps' (Honest/Law/Rule/Real.lean); and `HereAll`
(Honest/Law/Rule/Here.lean) of them, from what holds before the chain at all coins (`ChainInv`,
Honest/Law/Rule/ChainStep.lean). The condition on `On` remains a hypothesis, as in
Honest/Law/Rule/RowHere.lean (`hOn` there). It is the sixth piece of the proof of `rowOk_of`
(Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `OnT`, `bareStretch`, `bareItem`, `memberItems`, `chainItems`   the items; the parameter
     `seat`: which side, with which parameter `On`, is at a sub-protocol
  2  `memberItems_none`, `memberItems_bare`, `memberItems_row`, `SeatOk`, `memberItems_stage`,
     `chainItems_stage`   their stages
  3  `chain_here`   the main lemma

Limits.
  * `ChainInv` asks `TieAt` and `FaithOwn` (Honest/Law/Rule/OpenedStep.lean) and `bsAll = passed ++
    bs`: hypotheses of `chain_here`; `file_inv` (Honest/Law/Rule/FileInv.lean) pays them.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi S Cl V W Y Pb : Type}

/-- The type of the parameter `On` of a list of parts. -/
abbrev OnT (V W Y Pb : Type) : Type :=
  (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (ch ft : Nat) (tree : Nat → List Nat) (tl : Addr → Option Teller)
  (has : Place → Bool) (φ : Face V W Pb) (pb : Pb) (hs : List (Placed V W Y))
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)
  (Ve : VerAt F S Cl x st ch ft) (v : Option V)
  (seat : Block S Cl → Option (Side S Cl V W Y Pb × OnT V W Y Pb)) (Bq : List Read)
  (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) (bsAll : List (Block S Cl))

/-! ## 1 The items -/

/-- The stretch of a sub-protocol at which there is no list with a part. -/
def bareStretch (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn) : Stretch :=
  ⟨ch, ⟨b.place, 0⟩, b.rounds.zip b.oracles, own,
    asksFrom tree ((b.rounds.zip b.oracles).map (·.2.length)) n, none⟩

/- That stretch as an item that draws nothing. Its stage is the step's (`Act.stage`). The function
that it shows: `Stretch.bare` where the verifier has not rejected in the chain, `Stretch.sub`, the
fixed substitutes, where it has. -/
noncomputable def bareItem (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn) :
    Item Bk (Stand F) (List (Shown × Fmt.Drawn)) :=
  .det (Act.stage x st R (.lay (bareStretch ch tree b n own) : Act F)) fun Z =>
    if Z.live ch then (bareStretch ch tree b n own).bare else (bareStretch ch tree b n own).sub

/- The items of one sub-protocol's rounds. Where `seat` gives a side whose list has a part: that
list's items (`rowItems`, Honest/Law/Rule/RowHere.lean), cut over the rounds of `b`. Where `seat`
gives none, or a side whose list is empty: the one item `bareItem`. Nothing here ties the side's own
sub-protocol to `b`: `SeatOk.some` does. `earlier`, `bsAll`: the earlier chains' declared rounds and
the chain's whole list: the parts at `b` are handed the columns for the reads of `preOf`
(Honest/Rule.lean) of them at the place of `b`. -/
noncomputable def memberItems (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn) :
    List (Item Bk (Stand F) (List (Shown × Fmt.Drawn))) :=
  match seat b with
  | some p =>
    if p.1.row.isEmpty then [bareItem x st R ch tree b n own]
    else rowItems x st R ch ft tree φ p.1 keys dsAll m₀ pb p.2 (preOf ch ft earlier bsAll b.place)
      p.1.row 0 (b.rounds.zip b.oracles) n own
  | none => [bareItem x st R ch tree b n own]

/- The items of a chain: for each sub-protocol its `memberItems`, then the verifier's step on it
(`Ve.J`) as an item that draws nothing and shows nothing: the `[]` is the empty list of rounds. The
arguments after the list: how many trees the chain has sent before, and the challenges from there
on. `bsAll`: the chain's whole list, the same at every step. -/
noncomputable def chainItems : List (Block S Cl) → Nat → List Fmt.Drawn →
    List (Item Bk (Stand F) (List (Shown × Fmt.Drawn)))
  | [], _, _ => []
  | b :: bs, n, ds =>
    memberItems x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n (ds.take
        b.rounds.length) ++
      .det (Act.stage x st R (Ve.J b (ds.take b.rounds.length))) (fun _ => []) ::
        chainItems bs (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum)
          (ds.drop b.rounds.length)

/-! ## 2 Their stages -/

theorem memberItems_none (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn) (h : seat b = none) :
    memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n own =
      [bareItem x st R ch tree b n own] := by
  unfold memberItems
  rw [h]

theorem memberItems_bare (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn)
    {p : Side S Cl V W Y Pb × OnT V W Y Pb} (h : seat b = some p)
    (hr : p.1.row.isEmpty = true) :
    memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n own =
      [bareItem x st R ch tree b n own] := by
  unfold memberItems
  rw [h]
  show (if p.1.row.isEmpty = true then _ else _) = _
  rw [if_pos hr]

theorem memberItems_row (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn)
    {p : Side S Cl V W Y Pb × OnT V W Y Pb} (h : seat b = some p)
    (hr : p.1.row.isEmpty = false) :
    memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n own =
      rowItems x st R ch ft tree φ p.1 keys dsAll m₀ pb p.2 (preOf ch ft earlier bsAll b.place)
        p.1.row 0 (b.rounds.zip b.oracles) n own := by
  unfold memberItems
  rw [h]
  show (if p.1.row.isEmpty = true then _ else _) = _
  have hn : ¬ (p.1.row.isEmpty = true) := by
    rw [hr]
    exact Bool.false_ne_true
  rw [if_neg hn]

/-- **What ties `seat` to a session's look-ups and to the prover's sides, at one sub-protocol.**
`none`: where `seat` gives nothing the session has no list at the place. `some`: the side is at `b`;
its parts are those of the prover's side there; the book's cut at the place is the list's; `R` and
`tl` at each part's address are the part's `partShows`, at `preOf` (Honest/Rule.lean) of `earlier`
and `bsAll` at the side's place, and its simulator. -/
structure SeatOk (b : Block S Cl) : Prop where
  none : seat b = none → has b.place = false
  some : ∀ p, seat b = some p → p.1.block = b ∧
    (∃ g, (hs.find? fun g => g.place == b.place) = some g ∧ g.parts = p.1.row.map (·.1)) ∧
    has b.place = !p.1.row.isEmpty ∧
    Bk.cuts.lookup b.place = some (p.1.row.map (·.1.moves.length)) ∧
    (∀ u ∈ p.1.members, R ch ⟨p.1.block.place, u.number⟩ =
      partShows φ p.1 u Bk ch (preOf ch ft earlier bsAll p.1.block.place)
        (dryAt keys dsAll m₀ ⟨p.1.block.place, u.number⟩)) ∧
    ∀ u ∈ p.1.members, tl ⟨p.1.block.place, u.number⟩ = some ⟨u.sim.takes, u.sim.tell pb⟩

theorem memberItems_stage (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn)
    (hok : SeatOk (Bk := Bk) R ch ft tl has φ pb hs keys dsAll m₀ seat earlier bsAll b) :
    (memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n own).map
        Item.stage =
      (stretchesOf (Bk := Bk) ch tree tl has b n own).map fun s =>
        Act.stage x st R (.lay s : Act F) := by
  unfold stretchesOf
  cases hseat : seat b with
  | none =>
    rw [memberItems_none x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n own hseat,
        hok.none hseat]
    rfl
  | some p =>
    obtain ⟨hb, -, hhas, hcut, hR, htl⟩ := hok.some p hseat
    rw [hhas]
    cases hrow : p.1.row.isEmpty with
    | true =>
      rw [memberItems_bare x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n own hseat
          hrow]
      rfl
    | false =>
      rw [memberItems_row x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n own hseat
          hrow]
      subst hb
      show _ = (cutRow ch tree tl p.1.block.place 0 ((Bk.cuts.lookup p.1.block.place).getD [])
          (p.1.block.rounds.zip p.1.block.oracles) n own).map fun s =>
            Act.stage x st R (.lay s : Act F)
      rw [hcut]
      exact rowItems_stage x st R ch ft tree φ p.1 keys dsAll m₀ pb p.2 _ tl p.1.row 0 _ n own hR
          htl

theorem chainItems_stage : ∀ (bs : List (Block S Cl)) (n : Nat) (ds : List Fmt.Drawn),
    (∀ b ∈ bs, SeatOk (Bk := Bk) R ch ft tl has φ pb hs keys dsAll m₀ seat earlier bsAll b) →
    (chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll bs n ds).map
        Item.stage =
      (chainActs F Bk ch tree tl has Ve.J bs n ds).map (Act.stage x st R)
  | [], _, _, _ => rfl
  | b :: bs, n, ds, hok => by
    have ih := chainItems_stage bs (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum)
      (ds.drop b.rounds.length) fun b' hb' => hok b' (List.mem_cons_of_mem _ hb')
    show (memberItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n
        (ds.take b.rounds.length) ++ _ :: _).map Item.stage =
      ((stretchesOf (Bk := Bk) ch tree tl has b n (ds.take b.rounds.length)).map Act.lay ++
        Ve.J b (ds.take b.rounds.length) :: chainActs F Bk ch tree tl has Ve.J bs
          (n + ((b.rounds.zip b.oracles).map fun z : Fmt.DeclaredRound × List Oracle =>
            z.2.length).sum) (ds.drop b.rounds.length)).map (Act.stage x st R)
    rw [List.map_append, List.map_append, List.map_map, List.map_cons, List.map_cons,
      memberItems_stage x st R ch ft tree tl has φ pb hs keys dsAll m₀ seat earlier bsAll b n _
        (hok b (List.mem_cons.2 (Or.inl rfl))), ih]
    rfl

/-! ## 3 The main lemma -/

/-- **One chain.** `pre`: the stages before the sub-protocols bs. `L`, `Zb`, `c'`: at all coins, the
walk's look-ups, what has been produced before the chain, and the walk's end. `passed`: the chain's
sub-protocols before bs. `LookOk` and `SeatOk` are asked at `preOf` (Honest/Rule.lean) of each
sub-protocol's place. The hypothesis on `On` may use `OpenedAt` (Honest/Law/Rule/OpenedAt.lean) at
the part's state. -/
theorem chain_here (Z₀ : Stand F) (L : Coins Bk → Lay) (Zb : Coins Bk → Laid)
    (c' : Coins Bk → Core S W Y) :
    ∀ (bs : List (Block S Cl)) (n : Nat) (ds : List Fmt.Drawn)
      (pre : List (Kit.Stage (Coins Bk) (Stand F) (List (Shown × Fmt.Drawn))))
      (passed : List (Block S Cl)),
    (bs.map (·.place)).Nodup →
    (∀ b ∈ bs, ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots) →
    (∀ b ∈ bs, ∀ cs, Bk.cuts.lookup b.place = some cs → ∀ n ∈ cs, n ≠ 0) →
    (∀ b ∈ bs, LookOk R ch tl has φ pb hs keys dsAll m₀ (preOf ch ft earlier bsAll b.place) b) →
    (∀ b ∈ bs, SeatOk (Bk := Bk) R ch ft tl has φ pb hs keys dsAll m₀ seat earlier bsAll b) →
    (∀ b ∈ bs, ∀ p, seat b = some p → ∀ (k : Coins Bk) (u : Member V W Y Pb)
      (ds : List Fmt.Drawn) (Z : Stand F) (c : u.part.Coins) (m : Mid W Y)
      (y₁ : List Played × Mid W Y) (lp la : List Played)
      (kp ku kq : List (Addr × Option (State W Y → Y))),
      u ∈ p.1.members → Z.live ch = true → Z.laid = (Zb k).add ch (pairsBy tree lp 0) →
      (c' k).laid = lp ++ y₁.1 ++ la → y₁.1 ≠ [] → SegAt keys ⟨p.1.block.place, u.number⟩ kp ku kq →
      lp.length = kp.length →
      (∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (u.rounds.map (·.1)) ds, q ∈ Bq) →
      lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.1.block.place, u.number⟩ u.part = .ok c →
      play (u.part.steps p.1.block.name ⟨p.1.block.place, u.number⟩ u.rounds v c) ds [] m =
        .ok y₁ →
      (dryAt keys dsAll m₀ ⟨p.1.block.place, u.number⟩).st = m.st →
      (dryAt keys dsAll m₀ ⟨p.1.block.place, u.number⟩).loc = m.loc →
      m.seen = (Z.laid.front ch st).seen →
      OpenedAt (preOf ch ft earlier bsAll p.1.block.place) m (Z.laid.front ch st) →
      p.2 u c.2.2 m (Z.laid.front ch st) ∧
        (Z.laid.front ch st).holds ch ft (u.rounds.map (·.1)) ds = true) →
    (∀ k, ∃ ss c kp dp, ChainInv x st ch ft tree φ hs keys dsAll m₀ Ve v Bq earlier bsAll k (L k)
      (Zb k) bs ss ds n c (c' k) (Kit.real pre k Z₀) kp dp passed) →
    HereAll Z₀ pre (chainItems (F := F) x st R ch ft tree φ pb keys dsAll m₀ Ve seat earlier bsAll
        bs n ds)
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | b :: bs, n, ds, pre, passed, hnd, hsh, hpos, hlook, hok, hOn, hinv => by
    have hb : b ∈ b :: bs := List.mem_cons.2 (Or.inl rfl)
    have hstage := memberItems_stage (F := F) x st R ch ft tree tl has φ pb hs keys dsAll m₀ seat
        earlier bsAll b
      n (ds.take b.rounds.length) (hok b hb)
    refine HereAll.append _ _ _ ?_ (HereAll.cons (fun C e => by cases e) ?_)
    · -- the sub-protocol's own items
      cases hseat : seat b with
      | none =>
        rw [memberItems_none x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat]
        exact HereAll.det _ _ fun i hi C e => by
          have hi' := List.mem_singleton.1 hi
          rw [hi'] at e
          cases e
      | some p =>
        obtain ⟨hpb, ⟨g, hg, hparts⟩, -, -, hR, -⟩ := (hok b hb).some p hseat
        cases hrow : p.1.row.isEmpty with
        | true =>
          rw [memberItems_bare x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow]
          exact HereAll.det _ _ fun i hi C e => by
            have hi' := List.mem_singleton.1 hi
            rw [hi'] at e
            cases e
        | false =>
          rw [memberItems_row x st R ch ft tree φ pb keys dsAll m₀ seat earlier bsAll b n _ hseat
              hrow]
          subst hpb
          refine row_here x st R ch ft tree φ p.1 v keys dsAll m₀ pb p.2 Bq (preOf ch ft earlier
              bsAll p.1.block.place) Z₀
            (fun k => (c' k).laid) Zb (hOn p.1.block hb p hseat) p.1.row 0 _ n _ pre
            (fun u hu => hu) hR fun k hlive => ?_
          obtain ⟨ss, c, kp, dp, hI⟩ := hinv k
          obtain ⟨m, cr, y, la, hRI⟩ := hI.row p.1 hnd (hsh _ hb) (hpos _ hb) hg hparts hlive
          exact ⟨m, cr, y, kp, _, dp, _, _, la, hRI⟩
    · -- the sub-protocols after it
      refine chain_here Z₀ L Zb c' bs _ _ _ (passed ++ [b]) (List.nodup_cons.1 hnd).2
        (fun b' hb' => hsh b' (List.mem_cons_of_mem _ hb'))
        (fun b' hb' => hpos b' (List.mem_cons_of_mem _ hb'))
        (fun b' hb' => hlook b' (List.mem_cons_of_mem _ hb'))
        (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb'))
        (fun b' hb' => hOn b' (List.mem_cons_of_mem _ hb')) fun k => ?_
      obtain ⟨ss, c, kp, dp, hI⟩ := hinv k
      obtain ⟨y, cols, l, hA, hI'⟩ := hI.step (R := R) (tl := tl) (has := has) (pb := pb) hnd
        (hsh _ hb) (hpos _ hb) (hlook _ hb)
      refine ⟨l, c.next (L k) b y cols, kp ++ chainKeys [b] hs, dp ++ ds.take b.rounds.length, ?_⟩
      rw [hstage, Kit.real_append, Kit.real_append, hA]
      exact hI' _

end

end ProofFile.Honest

#print axioms ProofFile.Honest.memberItems_none
#print axioms ProofFile.Honest.memberItems_bare
#print axioms ProofFile.Honest.memberItems_row
#print axioms ProofFile.Honest.memberItems_stage
#print axioms ProofFile.Honest.chainItems_stage
#print axioms ProofFile.Honest.chain_here
#print axioms ProofFile.Honest.OnT
#print axioms ProofFile.Honest.bareStretch
#print axioms ProofFile.Honest.bareItem
#print axioms ProofFile.Honest.memberItems
#print axioms ProofFile.Honest.chainItems
#print axioms ProofFile.Honest.SeatOk
