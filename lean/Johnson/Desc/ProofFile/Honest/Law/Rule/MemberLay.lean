-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/MemberLay.lean: one sub-protocol of a chain. The fold at
coins over the sub-protocol's stretches, as a session cuts them, produces exactly what is shown by
the rounds that the prover of Honest/Walk.lean has produced there (Honest/Law/Rule/WalkLaw.lean:
`lays`). This holds before and after a rejection, with a list of parts or without one
(`member_lay`). What the parts are handed of opened columns is tied to what has been produced by a
hypothesis (`hheld`), which `TieAt.member` (Honest/Law/Rule/OpenedStep.lean) pays in
Honest/Law/Rule/ChainModel.lean and Honest/Law/Rule/ChainStep.lean.

  1  `lays_draws`   as many challenges as `Step`s
  2  `bare_states`, `row_states`, `bare_moves`, `row_moves`   what a sub-protocol's `Step`s declare;
     which have a move
  3  `LookOk`   a definition: what ties a session's look-ups to the prover's sides, at one
     sub-protocol
  4  `stretchesOf`, `member_lay`   the sub-protocol's stretches; the main lemma

Limits.
  * `hheld` is a hypothesis: it is paid nowhere here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.RowModel
import Johnson.Desc.ProofFile.Honest.Law.Rule.Member

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 Lengths -/

theorem lays_draws : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (m : Option (Mid W Y))
    (y : List Played × Option (Mid W Y)), lays l ds m = .ok y → ds.length = l.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [lays] at h
  | _ :: _, [], _, _, h => by simp [lays] at h
  | s :: l, d :: ds, m, y, h => by
    rw [lays] at h
    obtain ⟨x, -, h⟩ := exBind_ok h
    obtain ⟨m', -, h⟩ := exBind_ok h
    obtain ⟨y', hy, -⟩ := exMap_ok h
    exact congrArg (· + 1) (lays_draws l ds m' y' hy)

/-! ## 2 What a sub-protocol's `Step`s declare -/

theorem bare_states (b : Block S Cl) :
    ((bareStepsR b : List (Step W Y)).map fun s => (s.decl, s.oracles)) =
      b.rounds.zip b.oracles := by
  unfold bareStepsR
  rw [List.map_map]
  exact (List.map_congr_left fun r _ => rfl).trans (List.map_id _)

theorem bare_moves (b : Block S Cl) :
    ∀ s ∈ (bareStepsR b : List (Step W Y)), s.move.isSome = false ∧ s.addr.part = 0 := by
  intro s hs
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
  exact ⟨rfl, rfl⟩

theorem row_states (g : Placed V W Y) (b : Block S Cl) (v : Option V) (c : RowCoins g.parts)
    (hr : g.rounds = b.rounds.length) (ho : b.oracles.length = b.rounds.length) :
    ((g.steps b v c).map fun s => (s.decl, s.oracles)) = b.rounds.zip b.oracles := by
  have e := congrArg (List.map fun t : Fmt.DeclaredRound × List Oracle × Place × Bool => (t.1, t.2.1))
    (Placed.steps_rows g b v c hr ho)
  rw [List.map_map, List.map_map] at e
  exact e.trans ((List.map_congr_left fun r _ => rfl).trans (List.map_id _))

theorem row_moves (g : Placed V W Y) (b : Block S Cl) (v : Option V) (c : RowCoins g.parts)
    (hr : g.rounds = b.rounds.length) (ho : b.oracles.length = b.rounds.length) :
    ∀ s ∈ g.steps b v c, s.move.isSome = true := by
  intro s hs
  have h1 : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      (g.steps b v c).map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hs, rfl⟩
  rw [Placed.steps_rows g b v c hr ho] at h1
  obtain ⟨z, -, e⟩ := List.mem_map.1 h1
  exact (congrArg (·.2.2.2) e).symm

/-! ## 3 The look-ups -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (k : Coins Bk) (ch : Nat) (tree : Nat → List Nat) (tl : Addr → Option Teller)
  (has : Place → Bool) (φ : Face V W Pb) (pb : Pb) (hs : List (Placed V W Y))
  (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn) (m₀ : Mid W Y)

/-- **What ties a session's look-ups to the prover's sides, at one sub-protocol**: a place has
simulators exactly where it has a prover's side with a part; there the prover's side's parts are
those of a side's list, at this very sub-protocol; the honest side at a part's address is that
part's; and the simulator that is found there is the part's own, at the public value `pb`. `pr`: the
declared rounds whose reads the parts at this place are handed. -/
def LookOk (pr : List (Nat × Nat × List Fmt.DeclaredRound)) (b : Block S Cl) : Prop :=
  ((hs.find? fun g => g.place == b.place) = none → has b.place = false) ∧
    ∀ g, (hs.find? fun g => g.place == b.place) = some g →
      ∃ σ : Side S Cl V W Y Pb, σ.block = b ∧ g.parts = σ.row.map (·.1) ∧
        has b.place = !σ.row.isEmpty ∧
        (∀ u ∈ σ.members, R ch ⟨b.place, u.number⟩ =
          partShows φ σ u Bk ch pr (dryAt keys dsAll m₀ ⟨b.place, u.number⟩)) ∧
        ∀ u ∈ σ.members, tl ⟨b.place, u.number⟩ = some ⟨u.sim.takes, u.sim.tell pb⟩

/-! ## 4 The sub-protocol -/

/-- A sub-protocol's stretches, as `chainActs` (Honest/Law/Rule/Session.lean) cuts them. -/
def stretchesOf (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn) : List Stretch :=
  if has b.place then
    cutRow ch tree tl b.place 0 ((Bk.cuts.lookup b.place).getD []) (b.rounds.zip b.oracles) n own
  else [(⟨ch, ⟨b.place, 0⟩, b.rounds.zip b.oracles, own,
    asksFrom tree ((b.rounds.zip b.oracles).map (·.2.length)) n, none⟩ : Stretch)]

/-- **One sub-protocol.** `sb`: its `Step`s. `own`: its challenges. `mid`: the state of the prover's
run before it, or `none` after a rejection. `kp`, `dp`: the chain's keys and challenges before it.
`hheld`: the state's field is `some` of the columns that what has been produced holds for the reads
of `pr` (`HeldAt`, Honest/Law/Rule/OpenedAt.lean), and that holds a challenge for each round of
`pr`. -/
theorem member_lay {pr : List (Nat × Nat × List Fmt.DeclaredRound)} (v : Option V) (b : Block S Cl)
    (sb : List (Step W Y)) (own : List Fmt.Drawn)
    (n : Nat) (mid : Option (Mid W Y)) (y : List Played × Option (Mid W Y)) (Z : Stand F)
    (kp kq : List (Addr × Option (State W Y → Y))) (dp dq : List Fmt.Drawn)
    (ho : b.oracles.length = b.rounds.length)
    (hcase : ((hs.find? fun g => g.place == b.place) = none ∧ sb = bareStepsR b) ∨
      ∃ g c, (hs.find? fun g => g.place == b.place) = some g ∧ g.rounds = b.rounds.length ∧
        Bk.cuts.lookup b.place = some (g.parts.map (·.moves.length)) ∧
        lendRow Bk (Bk.rowsOf ch) (k.look ch) b.place g.parts 0 = .ok c ∧ sb = g.steps b v c)
    (hy : lays sb own mid = .ok y) (hlive : Z.live ch = mid.isSome)
    (hm : ∀ m, mid = some m → v = φ.sees m.st.input ∧ m.seen = (Z.laid.front ch st).seen ∧
      m.st = dryFold (kp.map (·.2)) dp m₀.st ∧ m.loc = m₀.loc ++ dp)
    (hheld : ∀ m, mid = some m → ∃ cs : List OpenedColumn, m.opened = some cs ∧
      HeldAt pr (Z.laid.front ch st) cs ∧
      ∀ x ∈ pr, x.2.2.length ≤ ((Z.laid.front ch st).drawnOf x.1).length)
    (hk : keys = kp ++ chainKeys [b] hs ++ kq) (hd : dsAll = dp ++ own ++ dq)
    (hlen : dp.length = kp.length) (hfr : ∀ q ∈ kp, q.1.place ≠ b.place)
    (hsh : ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots)
    (hpos : ∀ cs, Bk.cuts.lookup b.place = some cs → ∀ n ∈ cs, n ≠ 0)
    (hlook : LookOk R ch tl has φ pb hs keys dsAll m₀ pr b) :
    Kit.real ((stretchesOf (Bk := Bk) ch tree tl has b n own).map fun s =>
        Act.stage x st R (.lay s : Act F)) k Z =
      { Z with laid := Z.laid.add ch (pairsBy tree y.1 n) } := by
  have hown := lays_draws _ _ _ _ hy
  have hzl : (b.rounds.zip b.oracles).length = b.rounds.length := by
    rw [List.length_zip, ho, Nat.min_self]
  rcases hcase with ⟨hnone, rfl⟩ | ⟨g, c, hg, hr, hcut, hlend, rfl⟩
  · -- no list of parts
    have hhas := hlook.1 hnone
    have hst : stretchesOf (Bk := Bk) ch tree tl has b n own =
        [(⟨ch, ⟨b.place, 0⟩, b.rounds.zip b.oracles, own,
          asksFrom tree ((b.rounds.zip b.oracles).map (·.2.length)) n, none⟩ : Stretch)] := by
      unfold stretchesOf
      rw [hhas]
      rfl
    rw [hst]
    show ({ Z with laid := Z.laid.add ch ((Act.stage x st R (.lay ⟨ch, ⟨b.place, 0⟩,
      b.rounds.zip b.oracles, own, asksFrom tree ((b.rounds.zip b.oracles).map (·.2.length)) n,
      none⟩ : Act F)).shows k Z) } : Stand F) = _
    cases mid with
    | none =>
      have e := lays_sub _ _ _ hy
      subst e
      have hs' := sub_model x st R k ch tree Z hlive ⟨b.place, 0⟩ (bareStepsR b : List (Step W Y))
        own n none
      rw [bare_states] at hs'
      rw [hs']
      rfl
    | some m =>
      obtain ⟨m', -, hp⟩ := lays_live _ _ m y (fun s hs' _ => (bare_moves b s hs').2) hy
      have hb := bare_pairs tree _ _ m (y.1, m') n hp (fun s hs' => (bare_moves b s hs').1)
        (fun s hs' => by
          have h1 : (s.decl, s.oracles) ∈
              (bareStepsR b : List (Step W Y)).map fun s => (s.decl, s.oracles) :=
            List.mem_map.2 ⟨s, hs', rfl⟩
          rw [bare_states] at h1
          exact hsh _ h1)
      have e : ((bareStepsR b : List (Step W Y)).map fun s =>
          (⟨[], List.replicate s.oracles.length []⟩ : Shown)) =
          (b.rounds.zip b.oracles).map fun z => (⟨[], List.replicate z.2.length []⟩ : Shown) := by
        rw [← bare_states (W := W) (Y := Y) b, List.map_map]
        rfl
      rw [e] at hb
      show ({ Z with laid := Z.laid.add ch (if Z.live ch = true then
          (if (none : Option Teller).isSome = true then _ else
            ((b.rounds.zip b.oracles).map fun z =>
              (⟨[], List.replicate z.2.length []⟩ : Shown)).zip own) else _) } : Stand F) = _
      have hlive' : Z.live ch = true := hlive
      have hnone : ¬ ((none : Option Teller).isSome = true) := by simp
      rw [if_pos hlive', if_neg hnone, ← hb]
  · -- a list of parts
    obtain ⟨σ, rfl, hparts, hhas, hR, htl⟩ := hlook.2 g hg
    obtain ⟨gp, gparts⟩ := g
    have hparts' : gparts = σ.row.map (·.1) := hparts
    subst hparts'
    have hne : ∀ q ∈ σ.row, q.1.moves.length ≠ 0 := fun q hq =>
      hpos _ hcut _ (List.mem_map.2 ⟨q.1, List.mem_map.2 ⟨q, hq, rfl⟩, rfl⟩)
    have hsum : (σ.row.map (·.1.moves.length)).sum =
        (σ.block.rounds.zip σ.block.oracles).length := by
      have h0 : (⟨gp, σ.row.map (·.1)⟩ : Placed V W Y).rounds = σ.block.rounds.length := hr
      unfold Placed.rounds at h0
      rw [foldl_moves, Nat.zero_add, List.map_map] at h0
      rw [hzl]
      exact h0
    have hsl : ((⟨gp, σ.row.map (·.1)⟩ : Placed V W Y).steps σ.block v c).length =
        σ.block.rounds.length := by
      have e := congrArg List.length (row_states _ σ.block v c hr ho)
      rw [List.length_map, hzl] at e
      exact e
    by_cases hrow : σ.row = []
    · -- a list without a part: the sub-protocol has no round
      have hz0 : σ.block.rounds.length = 0 := by
        rw [hrow] at hsum
        rw [← hzl, ← hsum]
        rfl
      have hs0 : (⟨gp, σ.row.map (·.1)⟩ : Placed V W Y).steps σ.block v c = [] :=
        List.eq_nil_of_length_eq_zero (hsl.trans hz0)
      rw [hs0] at hy hown
      have ho0 : own = [] := List.eq_nil_of_length_eq_zero hown
      subst ho0
      rw [lays] at hy
      cases hy
      have hst0 : stretchesOf (Bk := Bk) ch tree tl has σ.block n [] =
          [(⟨ch, ⟨σ.block.place, 0⟩, σ.block.rounds.zip σ.block.oracles, [],
            asksFrom tree ((σ.block.rounds.zip σ.block.oracles).map (·.2.length)) n, none⟩ :
              Stretch)] := by
        unfold stretchesOf
        rw [hhas, hrow]
        rfl
      rw [hst0]
      show ({ Z with laid := Z.laid.add ch ((Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, 0⟩,
        σ.block.rounds.zip σ.block.oracles, [],
        asksFrom tree ((σ.block.rounds.zip σ.block.oracles).map (·.2.length)) n,
        none⟩ : Act F)).shows k Z) } : Stand F) = { Z with laid := Z.laid.add ch [] }
      have hsh0 : (Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, 0⟩,
          σ.block.rounds.zip σ.block.oracles, [],
          asksFrom tree ((σ.block.rounds.zip σ.block.oracles).map (·.2.length)) n,
          none⟩ : Act F)).shows k Z = [] := by
        simp [Act.stage, Act.shows, Stretch.real, Stretch.bare, Stretch.sub]
      rw [hsh0]
    have hst : stretchesOf (Bk := Bk) ch tree tl has σ.block n own =
        cutRow ch tree tl σ.block.place 0 (σ.row.map (·.1.moves.length))
          (σ.block.rounds.zip σ.block.oracles) n own := by
      have hne' : (!σ.row.isEmpty) = true := by
        cases hr' : σ.row with
        | nil => exact absurd hr' hrow
        | cons _ _ => rfl
      unfold stretchesOf
      rw [hhas, hne', hcut, List.map_map]
      rfl
    rw [hst]
    cases mid with
    | none =>
      have e := lays_sub _ _ _ hy
      subst e
      have hrs := row_sub x st R k ch tree tl σ.block.place (σ.row.map (·.1.moves.length)) 0
        ((⟨gp, σ.row.map (·.1)⟩ : Placed V W Y).steps σ.block v c) own n Z hlive
        (by rw [hsum, hzl, hsl]) hown
      rw [row_states _ σ.block v c hr ho] at hrs
      exact hrs
    | some m =>
      obtain ⟨h1, h2, h3, h4⟩ := hm m rfl
      obtain ⟨cs, hW, hF, hL⟩ := hheld m rfl
      obtain ⟨m', -, hp⟩ := lays_live _ _ m y (fun s hs' hf => by
        rw [row_moves _ σ.block v c hr ho s hs'] at hf
        cases hf) hy
      have hkeys : chainKeys [σ.block] hs =
          rowKeys σ.block.place (σ.row.map (·.1)) 0 (σ.block.rounds.zip σ.block.oracles) := by
        unfold chainKeys
        rw [List.flatMap_cons, hg, List.flatMap_nil, List.append_nil]
      exact row_model x st R k ch tree tl φ σ v keys dsAll m₀ σ.row 0
        (σ.block.rounds.zip σ.block.oracles) own n m Z c (y.1, m') kp kq dp dq hp hlend hsum
        (by rw [hown, hsl, hzl]) hne hsh h1 hlive h2 hW hF hL (by rw [hk, hkeys]) hd hlen
        (fun q hq => Or.inl (hfr q hq)) h3 h4 hR (fun u hu => by rw [htl u hu]; rfl)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.lays_draws
#print axioms ProofFile.Honest.bare_states
#print axioms ProofFile.Honest.bare_moves
#print axioms ProofFile.Honest.row_states
#print axioms ProofFile.Honest.row_moves
#print axioms ProofFile.Honest.member_lay
#print axioms ProofFile.Honest.LookOk
#print axioms ProofFile.Honest.stretchesOf
