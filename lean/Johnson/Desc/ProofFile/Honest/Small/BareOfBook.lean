-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/BareOfBook.lean: CONDITIONAL. Statements with their proofs; no
definition but one private shorthand. NO KIND IS NAMED. By the writers of the feed-forward layers'
own rounds (sub-protocol K4). It stands over Honest/BookRowKit.lean and what that file imports.

What is here. IN THE WHOLE BOOK OF COINS (`bookWhole`, Honest/BookWhole.lean) A SUB-PROTOCOL OF THE
FIRST CHAIN THAT HOLDS NO ROUND "SEND seed" AND NO ROUND "FOLD epsilon" HAS NO COIN OF ITS OWN AND
CARRIES NONE: at each of its parts' addresses the first table's count is 0 (no row there, or a row
of the count 0), and the book has no carried entry. The book's maker reads the plan's rounds: every
row of the first table stands at the part that holds a round "SEND seed" (`rowsIn`,
Honest/BookRows.lean; `switchRows`, Honest/BookSwitch.lean); every carried entry is given to the
part that holds a "FOLD epsilon" or to the part that holds the first "SEND seed" after it, in the
chain whose list the maker hands to `behindFold` (Honest/BookCarry.lean). An address's place is the
place of the sub-protocol that holds the round (`addrIn_holds`, Honest/BookRowKit.lean, and its
like for `addrOfRound` here); under the library's test on places (`FileDescription.placesOk`,
Johnson/Desc/Block.lean) no two sub-protocols stand at one place. It is the twin, for what is
carried and owned, of `pick_whole` (Honest/BookRowStretch.lean), which speaks of what is spent; its
proof goes the same way.

  `bookWhole_bare_at`   **THE STATEMENT.**
  `addrOfRound_holds`, `seedRounds_name`, `seed_holds`, `behindFold_holds`   which sub-protocol
      holds the round at which an address stands.
  `rowsIn_holds`, `switchesDue_rounds`, `switchRows_holds`   the rows of a chain's table.
  `segmentCarries_spender`, `carryPair_spender`, `groupCarries_spender`, `ownFreshIn_behind`   who
      is given a carried entry.
  `spendingBook_first`, `bookRaw_first`   the first table, cut in its two pieces.

Not shown here. THAT `bookWhole` RETURNS AT ANY FILES; that the description passes its test on
places. THAT ANY SUB-PROTOCOL OF THE PROTOCOL HOLDS NO SUCH ROUND: hS and hF are premises. The
first chain alone; the first table alone. Nothing on what such a sub-protocol spends. Nothing on
soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

variable {Xi S Cl : Type}

/-! ## 1 Which sub-protocol holds a round -/

/-- `addrIn_holds` (Honest/BookRowKit.lean) for `addrOfRound`. -/
theorem addrOfRound_holds : ∀ (bs : List (Block S Cl)) (i : Nat) (a : Addr) (d : Fmt.DeclaredRound),
    addrOfRound bs i = some a → (bs.flatMap (·.rounds))[i]? = some d →
      ∃ x ∈ bs, x.place = a.place ∧ d ∈ x.rounds
  | [], _, _, _, h, _ => by
    unfold addrOfRound at h
    cases h
  | b :: bs, i, a, d, h, hd => by
    unfold addrOfRound at h
    rw [List.flatMap_cons] at hd
    split at h
    · rename_i hi
      have e := Option.some.inj h
      rw [List.getElem?_append_left hi] at hd
      exact ⟨b, List.Mem.head _, by rw [← e], List.mem_of_getElem? hd⟩
    · rename_i hi
      rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hd
      obtain ⟨x, hx, h1, h2⟩ := addrOfRound_holds bs _ a d h hd
      exact ⟨x, List.Mem.tail _ hx, h1, h2⟩

theorem seedRounds_name {bs : List (Block S Cl)} {i : Nat} (h : i ∈ seedRounds bs) :
    ∃ d, (bs.flatMap (·.rounds))[i]? = some d ∧ d.entry.name = "SEND seed" := by
  unfold seedRounds at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hx
  exact ⟨x.1, List.mem_zipIdx_iff_getElem?.1 h1, by simpa using h2⟩

/-- The part that holds a round "SEND seed" stands at a sub-protocol that holds such a round. -/
theorem seed_holds {bs : List (Block S Cl)} {i : Nat} {a : Addr} (h : i ∈ seedRounds bs)
    (ha : addrOfRound bs i = some a) :
    ∃ x ∈ bs, x.place = a.place ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed" := by
  obtain ⟨d, hd, hn⟩ := seedRounds_name h
  obtain ⟨x, hx, h1, h2⟩ := addrOfRound_holds bs i a d ha hd
  exact ⟨x, hx, h1, d, h2, hn⟩

/-- Of `behindFold`'s two parts the first stands at a sub-protocol that holds a "FOLD epsilon", the
second at one that holds a "SEND seed". -/
theorem behindFold_holds {l : List PlanB} {i : Nat} {p q : Addr}
    (h : behindFold l i = some (p, q)) :
    (∃ x ∈ l, x.place = p.place ∧ ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon") ∧
      ∃ x ∈ l, x.place = q.place ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed" := by
  unfold behindFold at h
  obtain ⟨⟨e, r, k⟩, hf, h⟩ := opt_bind h
  dsimp only at h
  obtain ⟨q', hq1, h⟩ := opt_bind h
  obtain ⟨p', hp', h⟩ := opt_map h
  obtain ⟨s, hs, hq2⟩ := opt_bind hq1
  obtain ⟨e1, e2⟩ := Prod.mk.inj h
  subst e1
  subst e2
  obtain ⟨d, hd, hn⟩ := foldBehind_name hf
  obtain ⟨x, hx, h1, h2⟩ := addrIn_holds _ _ _ _ hp' hd
  have hg := List.mem_zipIdx_iff_getElem?.1 (List.mem_of_mem_drop (List.mem_of_find?_eq_some hs))
  have hn2 : s.1.entry.name = "SEND seed" := by simpa using List.find?_some hs
  obtain ⟨y, hy, g1, g2⟩ := addrIn_holds _ _ _ _ hq2 hg
  exact ⟨⟨x, hx, h1, d, h2, hn⟩, y, hy, g1, s.1, g2, hn2⟩

/-! ## 2 The rows of a chain's table -/

theorem rowsIn_holds {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {r : List (Addr × Due)} (h : rowsIn bs c later = .ok r) :
    ∀ y ∈ r, ∃ x ∈ bs, x.place = y.1.place ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed" := by
  unfold rowsIn at h
  split at h
  · cases h
  · refine mapM_all _ r ?_ h
    intro v hv y hy
    have hz : (v.1, v.2) ∈ (seedRounds bs).zip c.sends := (List.mem_filter.1 hv).1
    have hs : v.1 ∈ seedRounds bs := (List.of_mem_zip hz).1
    try dsimp only at hy
    split at hy
    · cases hy
    · split at hy
      · rename_i a d ha hd
        have e := Except.ok.inj hy
        rw [← e]
        exact seed_holds hs ha
      · cases hy
      · cases hy

/-- A switch's round is one of the rounds that were handed in. -/
theorem switchesDue_rounds (codes : OnBytes.Codes) (rounds : List Fmt.DeclaredRound)
    (first : String → Option (OnBytes.Code × OnBytes.Code)) :
    ∀ (xs : List (Nat × Johnson.G.Sending)) (prev : Option (String × OnBytes.Code × OnBytes.Code))
      (l : List (String × Nat × Nat × Due)), switchesDue codes rounds first xs prev = .ok l →
      ∀ y ∈ l, y.2.1 ∈ xs.map (·.1)
  | [], _, l, h, y, hy => by
    unfold switchesDue at h
    have e := Except.ok.inj h
    rw [← e] at hy
    cases hy
  | x :: xs, prev, l, h, y, hy => by
    unfold switchesDue at h
    dsimp only at h
    repeat' split at h
    all_goals first
      | cases h
      | (obtain ⟨l', hl', e⟩ := ex_mapE h
         rw [← e] at hy
         cases hy with
         | head => exact List.Mem.head _
         | tail _ h2 =>
           exact List.Mem.tail _ (switchesDue_rounds codes rounds first xs _ l' hl' y h2))

theorem switchRows_holds {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {first : String → Option (OnBytes.Code × OnBytes.Code)} {r : List (Addr × Due)}
    (h : switchRows bs c first = .ok r) :
    ∀ y ∈ r, ∃ x ∈ bs, x.place = y.1.place ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed" := by
  unfold switchRows at h
  split at h
  · cases h
  · obtain ⟨l, hl, h⟩ := ex_bindE h
    obtain ⟨rows, hrows, e⟩ := ex_mapE h
    intro y hy
    rw [← e] at hy
    unfold mergeRows at hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (List.mem_eraseDups.1 ha)
    show ∃ x ∈ bs, x.place = z.1.place ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed"
    refine mapM_all (P := fun z : Addr × Due => ∃ x ∈ bs, x.place = z.1.place ∧
      ∃ d ∈ x.rounds, d.entry.name = "SEND seed") l rows ?_ hrows z hz
    intro w hw z' hz'
    have hs : w.2.1 ∈ seedRounds bs := by
      obtain ⟨v, hv, ev⟩ := List.mem_map.1 (switchesDue_rounds _ _ _ _ _ l hl w hw)
      have hz2 : (v.1, v.2) ∈ (seedRounds bs).zip c.sends := (List.mem_filter.1 hv).1
      rw [← ev]
      exact (List.of_mem_zip hz2).1
    try dsimp only at hz'
    split at hz'
    · rename_i a' ha'
      have e2 := Except.ok.inj hz'
      rw [← e2]
      exact seed_holds hs ha'
    · cases hz'

/-! ## 3 Who is given a carried entry -/

theorem carryPair_spender {p q : Addr} {reach : List SentMsg} {own : Option SentMsg} :
    ∀ e ∈ carryPair p q reach own, e.spender = p ∨ e.spender = q := by
  intro e he
  unfold carryPair at he
  rcases List.mem_append.1 he with h | h
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
    exact Or.inl rfl
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
    exact Or.inr rfl

theorem groupCarries_spender {l : List PlanB} {i : Nat} {g : List SentMsg} {own : Option SentMsg}
    {r : List Ahead} (h : groupCarries l i g own = .ok r) :
    ∀ e ∈ r, ∃ x ∈ l, x.place = e.spender.place := by
  unfold groupCarries at h
  split at h
  · rename_i p q hbf
    have e := Except.ok.inj h
    obtain ⟨⟨x, hx, hx1, -⟩, y, hy, hy1, -⟩ := behindFold_holds hbf
    rw [← e]
    intro a ha
    rcases carryPair_spender a ha with h1 | h1
    · exact ⟨x, hx, by rw [h1]; exact hx1⟩
    · exact ⟨y, hy, by rw [h1]; exact hy1⟩
  · cases h

theorem segmentCarries_spender {here : List PlanB} {ms : List SentMsg} {l : List Ahead}
    (h : segmentCarries here ms = .ok l) :
    ∀ e ∈ l, ∃ x ∈ here, x.place = e.spender.place ∧
      ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon" ∨ d.entry.name = "SEND seed" := by
  unfold segmentCarries at h
  obtain ⟨ll, hll, e⟩ := ex_map h
  intro a ha
  rw [← e] at ha
  obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
  refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, ∃ x ∈ here, x.place = a.spender.place ∧
    ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon" ∨ d.entry.name = "SEND seed") ?_ hll
    inner hin a ha
  intro f _ r hr
  try dsimp only at hr
  split at hr
  · rename_i p q l' hbf hl'
    have e2 := Except.ok.inj hr
    obtain ⟨⟨x, hx, hx1, d, hd, hn⟩, y, hy, hy1, d', hd', hn'⟩ := behindFold_holds hbf
    rw [← e2]
    intro a ha
    rcases List.mem_append.1 ha with h1 | h1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h1
      exact ⟨x, hx, hx1, d, hd, Or.inl hn⟩
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h1
      exact ⟨y, hy, hy1, d', hd', Or.inr hn'⟩
  · cases hr

theorem ownFreshIn_behind {bs : List (Block S Cl)} :
    ∀ o ∈ ownFreshIn bs, ∃ x ∈ planOf bs, x.place = o.behind.place := by
  intro o ho
  unfold ownFreshIn at ho
  dsimp only at ho
  obtain ⟨r, -, h⟩ := List.mem_filterMap.1 ho
  split at h
  · cases h
  · obtain ⟨pq, hpq, h⟩ := opt_bind h
    obtain ⟨f, -, h⟩ := opt_map h
    obtain ⟨p, q⟩ := pq
    obtain ⟨-, y, hy, hy1, -⟩ := behindFold_holds hpq
    rw [← h]
    exact ⟨y, hy, hy1⟩

/-! ## 4 The first table, cut in its two pieces -/

theorem spendingBook_first {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) :
    rowsIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok B₀.first := by
  unfold spendingBook at h
  obtain ⟨r0, hr0, h⟩ := ex_bind h
  obtain ⟨r1, -, h⟩ := ex_bind h
  obtain ⟨r2, -, h⟩ := ex_bind h
  rcases hidx : ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
      "link 0, moment 0" isIndexMaskMsg with _ | idx
  · rw [hidx] at h
    obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  rw [hidx] at h
  obtain ⟨idx', -, h⟩ := ex_bind h
  obtain ⟨a, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨f0, -, h⟩ := ex_bind h
  obtain ⟨f1, -, h⟩ := ex_bind h
  obtain ⟨f2, -, h⟩ := ex_bind h
  have e := Except.ok.inj h
  subst e
  exact hr0

theorem bookRaw_first {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {W : ProverCoinCounts}
    (h : bookRaw F p0 p1 p2 M = .ok W) :
    ∃ (B₀ : ProverCoinCounts) (r0 : List (Addr × Due)), spendingBook F p0 p1 p2 M = .ok B₀ ∧
      switchRows F.first.blocksInOrder p0 (firstCodes p0 p1) = .ok r0 ∧ W.first = B₀.first ++ r0 := by
  unfold bookRaw at h
  obtain ⟨B₀, hB, h⟩ := ex_bind h
  obtain ⟨m0, -, h⟩ := ex_bind h
  obtain ⟨m1, -, h⟩ := ex_bind h
  obtain ⟨r0, hr0, h⟩ := ex_bind h
  obtain ⟨r1, -, h⟩ := ex_bind h
  obtain ⟨r2, -, h⟩ := ex_bind h
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨seg, -, h⟩ := ex_bind h
  obtain ⟨iF, -, h⟩ := ex_bind h
  obtain ⟨cF, -, h⟩ := ex_bind h
  obtain ⟨iO, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨cO, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨pq, -, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨tail, -, h⟩ := ex_bind h
  have e := Except.ok.inj h
  exact ⟨B₀, r0, hB, hr0, by subst e; rfl⟩

/-! ## 5 The statement -/

/-- Of a list of entries those by which an address carries coins: `carryE`'s text at a list. -/
private abbrev cpick (a : Addr) (l : List Ahead) : List Ahead :=
  (l.filter fun e => e.spender == a).filter fun e => !e.once

private theorem cpick_append (a : Addr) (l l' : List Ahead) :
    cpick a (l ++ l') = cpick a l ++ cpick a l' := by
  simp only [cpick, List.filter_append]

private theorem cpick_spent {a : Addr} {l : List Ahead} (h : ∀ e ∈ l, e.once = true) :
    cpick a l = [] :=
  List.filter_eq_nil_iff.2 fun e he => by
    have h1 := h e (List.mem_filter.1 he).1
    simp [h1]

private theorem cpick_other {a : Addr} {l : List Ahead} (h : ∀ e ∈ l, e.spender ≠ a) :
    cpick a l = [] := by
  have h0 : l.filter (fun e => e.spender == a) = [] :=
    List.filter_eq_nil_iff.2 fun e he => by
      have hne := h e he
      simp [hne]
  show (l.filter fun e => e.spender == a).filter (fun e => !e.once) = []
  rw [h0]
  rfl

private theorem due_some {α : Type} {what : String} {x : Option α} {a : α}
    (h : due? what x = .ok a) : x = some a := by
  cases x with
  | none => cases h
  | some b => exact congrArg some (Except.ok.inj h)

/-- CONDITIONAL on h, hp, hb, hS and hF. **A SUB-PROTOCOL OF THE FIRST CHAIN THAT HOLDS NO
"SEND seed" AND NO "FOLD epsilon" HAS, IN THE WHOLE BOOK, NO COIN OF ITS OWN IN THE FIRST TABLE AND
NO CARRIED ENTRY**, at any part's address. -/
theorem bookWhole_bare_at {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder)
    (hS : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed")
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") :
    ∀ i, dueAt (B.rowsOf 0) ⟨b.place, i⟩ = ⟨0, 0⟩ ∧ carryE B ⟨b.place, i⟩ = [] := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, hm1, hseg, hiF, hcF, hiO, hcO, hpq,
    htail, eW⟩ := bookRaw_ahead hW
  obtain ⟨ws, f0, f1, f2, -, hf0, hf1, hf2, eB⟩ := spendingBook_ahead hB
  obtain ⟨B₁, r0, hB1, hr0, eF⟩ := bookRaw_first hW
  have eBB : B₁ = B₀ := Except.ok.inj (hB1.symm.trans hB)
  rw [eBB] at eF
  have hrows := spendingBook_first hB
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  have c1 : b.place.chain = 1 := chain_first hp _ (List.mem_map.2 ⟨b, hb, rfl⟩)
  have free1 : ∀ x ∈ planOf F.first.blocksInOrder, x.place = b.place → ∀ d ∈ x.rounds,
      d.entry.name ≠ "FOLD epsilon" ∧ d.entry.name ≠ "SEND seed" := by
    intro x hx hpl
    unfold planOf at hx
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hx
    have e : b' = b := List.inj_on_of_nodup_map hn hb' hb hpl
    rw [e]
    exact fun d hd => ⟨hF d hd, hS d hd⟩
  have not2 : ∀ x ∈ planOf F.shared.blocksInOrder, x.place ≠ b.place := by
    intro x hx hpl
    have h2 := chain_shared hp x.place (by
      rw [← planOf_places]
      exact List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [hpl] at h2
    omega
  have not3 : ∀ x ∈ planOf F.second.blocksInOrder, x.place ≠ b.place := by
    intro x hx hpl
    have h2 := chain_second hp x.place (by
      rw [← planOf_places]
      exact List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [hpl] at h2
    omega
  intro i
  constructor
  · show dueAt _ (⟨b.place, i⟩ : Addr) = ⟨0, 0⟩
    have eR : ProverCoinCounts.rowsOf _ 0 = B₀.first ++ r0 := eF
    rw [eR]
    refine dueAt_none _ _ (List.any_eq_false.2 ?_)
    intro y hy hh
    have ey : y.1 = ⟨b.place, i⟩ := beq_iff_eq.1 hh
    have hold : ∃ x ∈ F.first.blocksInOrder, x.place = y.1.place ∧
        ∃ d ∈ x.rounds, d.entry.name = "SEND seed" := by
      rcases List.mem_append.1 hy with h1 | h1
      · exact rowsIn_holds hrows y h1
      · exact switchRows_holds hr0 y h1
    obtain ⟨x, hx, hx1, d, hd, hn0⟩ := hold
    rw [ey] at hx1
    have e : x = b := List.inj_on_of_nodup_map hn hx hb hx1
    rw [e] at hd
    exact hS d hd hn0
  · show cpick ⟨b.place, i⟩ _ = []
    have y0 : cpick ⟨b.place, i⟩ (ws.map (·.entry)) = [] := cpick_spent (by
      intro e he
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 he
      rfl)
    have z0 : cpick ⟨b.place, i⟩ f0 = [] := cpick_other (by
      intro e he h0
      obtain ⟨x, hx, hx1, d, hd, hn0⟩ := foldEntries_spender hf0 e he
      rw [h0] at hx1
      rcases List.mem_append.1 hx with h1 | h1
      · exact (free1 x h1 hx1 d hd).1 hn0
      · exact not3 x h1 hx1)
    have z1 : cpick ⟨b.place, i⟩ f1 = [] := cpick_other (by
      intro e he h0
      obtain ⟨x, hx, hx1, -⟩ := foldEntries_spender hf1 e he
      rw [h0] at hx1
      rcases List.mem_append.1 hx with h1 | h1
      · exact not2 x h1 hx1
      · cases h1)
    have z2 : cpick ⟨b.place, i⟩ f2 = [] := cpick_other (by
      intro e he h0
      obtain ⟨x, hx, hx1, -⟩ := foldEntries_spender hf2 e he
      rw [h0] at hx1
      rcases List.mem_append.1 hx with h1 | h1
      · exact not3 x h1 hx1
      · cases h1)
    have z3 : cpick ⟨b.place, i⟩ (splitEntry F.shared.blocksInOrder p1).toList = [] := cpick_other (by
               intro e he h0
               have hs : splitEntry F.shared.blocksInOrder p1 = some e := by
                 cases hsp : splitEntry F.shared.blocksInOrder p1 with
                 | none =>
                   rw [hsp] at he
                   cases he
                 | some e' =>
                   rw [hsp] at he
                   rw [mem_one he]
               have h2 := chain_shared hp _ (splitEntry_spender hs)
               rw [h0] at h2
               have h3 : b.place.chain = 2 := h2
               omega)
    have z4 : cpick ⟨b.place, i⟩ seg = [] := cpick_other (by
      intro e he h0
      obtain ⟨x, hx, hx1, d, hd, hn0⟩ := segmentCarries_spender hseg e he
      rw [h0] at hx1
      rcases hn0 with hn0 | hn0
      · exact (free1 x hx hx1 d hd).1 hn0
      · exact (free1 x hx hx1 d hd).2 hn0)
    have z5 : cpick ⟨b.place, i⟩ cF = [] := cpick_other (by
      intro e he h0
      obtain ⟨x, hx, hx1⟩ := groupCarries_spender hcF e he
      rw [h0] at hx1
      exact not2 x hx hx1)
    have z6 : cpick ⟨b.place, i⟩ cO = [] := cpick_other (by
      intro e he h0
      obtain ⟨x, hx, hx1⟩ := groupCarries_spender hcO e he
      rw [h0] at hx1
      exact not2 x hx hx1)
    have z7 : cpick ⟨b.place, i⟩ (carryPair pq.1 pq.2
        (m0.filter (·.masks) ++ (under m0 "W").filter (!·.fresh) ++
          (under m1 "Omega").filter (!·.masks))
        ((under m0 "W").find? (·.fresh))) = [] := cpick_other (by
      intro e he h0
      have hbf : behindFold (planOf F.second.blocksInOrder) 0 = some (pq.1, pq.2) := due_some hpq
      obtain ⟨⟨x, hx, hx1, -⟩, y, hy, hy1, -⟩ := behindFold_holds hbf
      rcases carryPair_spender e he with h1 | h1
      · rw [← h1, h0] at hx1
        exact not3 x hx hx1
      · rw [← h1, h0] at hy1
        exact not3 y hy hy1)
    have z8 : cpick ⟨b.place, i⟩ ((ownFreshIn F.shared.blocksInOrder).map (·.carry tail)) = [] :=
      cpick_other (by
        intro e he h0
        obtain ⟨o, ho, rfl⟩ := List.mem_map.1 he
        obtain ⟨x, hx, hx1⟩ := ownFreshIn_behind o ho
        have h1 : o.behind = ⟨b.place, i⟩ := h0
        rw [h1] at hx1
        exact not2 x hx hx1)
    rw [eW, eB]
    simp only [cpick_append]
    rw [y0, z0, z1, z2, z3, z4, z5, z6, z7, z8]
    rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.addrOfRound_holds
#print axioms ProofFile.Honest.seedRounds_name
#print axioms ProofFile.Honest.seed_holds
#print axioms ProofFile.Honest.behindFold_holds
#print axioms ProofFile.Honest.rowsIn_holds
#print axioms ProofFile.Honest.switchesDue_rounds
#print axioms ProofFile.Honest.switchRows_holds
#print axioms ProofFile.Honest.carryPair_spender
#print axioms ProofFile.Honest.groupCarries_spender
#print axioms ProofFile.Honest.segmentCarries_spender
#print axioms ProofFile.Honest.ownFreshIn_behind
#print axioms ProofFile.Honest.spendingBook_first
#print axioms ProofFile.Honest.bookRaw_first
#print axioms ProofFile.Honest.bookWhole_bare_at
