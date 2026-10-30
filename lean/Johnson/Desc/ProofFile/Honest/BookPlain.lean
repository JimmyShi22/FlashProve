-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookPlain.lean: by the authors of the attention sub-protocol's (K5's)
honest side; it names no kind, and so it stands beside the book's kit. CONDITIONAL: AT A
SUB-PROTOCOL OF THE FIRST CHAIN WITH PLAIN NAMES THE WHOLE BOOK HAS NO ROW, AND EVERY ENTRY THAT IS
HANDED TO ONE OF ITS PARTS IS A SPENT ONE.

Why. A kind whose parts own nothing and carry nothing must find the book so at its places: no row of
its own, and no run that is carried to it. The book's maker names no kind: it reads the
sub-protocols' rounds by their names. So the two facts hold at every sub-protocol none of whose
rounds bears one of two names. What the parts there do spend is `pick_whole`'s
(BookRowStretch.lean), not this file's.

Main names (namespace `ProofFile.Honest`), each under hB: `bookWhole F p0 p1 p2 M = .ok B`, hp:
`F.placesOk = true`, hb: b stands in the first chain's list:
  `plain_no_row`: none of b's rounds is named "SEND seed": `dueAt B.first ⟨b.place, i⟩ = ⟨0, 0⟩` at
    every i.
  `plain_all_spent`: nor is one named "FOLD epsilon": every entry of `B.ahead` whose spender stands
    at b's place has `once = true`.
  `plain_no_carry`: the same in the other wording: no entry with `once = false` has its spender
    there.

The eighteen helpers (namespace `ProofFile.Honest.BookPlain`):
  `addrOfRound_holds`: the part that holds round i of a chain stands at the sub-protocol that holds
    it (the like for a plan is the kit's `BookRow.addrIn_holds`).
  `named_of_filter`, `seed_named`, `round_not_here`: a number of `seedRounds` is that of a round
    named "SEND seed"; the part that holds a round of a name stands at no sub-protocol without one.
  `rowsIn_seed`, `switchesDue_rounds`, `switchRows_seed`: every row's address is `addrOfRound` at a
    round named "SEND seed".
  `spendingBook_first`, `bookRaw_first`: the two makers, opened at the first chain's table. Near
    kin, of other authors, named here on the word of the book's keeper alone (the authors of this
    file have not seen that file): `spendingBook_rows`, `bookRaw_rows`
    (Johnson/Desc/ProofFile/Honest/BookRawRows.lean): all four fields at once.
  `lookup_none_addr`, `due_some`: a table without a row at an address; a value that must be there.
  `behindFold_named`, `carryPair_spender`, `fold_ends`, `pair_ends`, `groupCarries_ends`,
    `segmentCarries_ends`: a carried run ends at a sub-protocol of the plan over which it was made,
    and there at one that holds a round of one of the two names.
  `ownFresh_behind`: the run of a fold's own table ends at a place of the chain over which it was
    made; of names it says nothing.

Limits. Implications: that the book's maker returns is a hypothesis, proved at no files; so is the
test on the places. On the first chain's sub-protocols alone. Nothing is said of which entries are
handed to a part, of their names, owners or counts. A fold that sends a table of its own needs no
clause: its row goes into the shared chain's table alone, and the maker refuses where the first
chain has such a fold. The proofs lean on membership in the makers' lists alone, not on their order.
They open a maker by `unfold` or `split` only where the kit's files have done so; elsewhere by
`delta`, by a restated body (`switchesDue_rounds`) and by cases on what a match reads: so that Lean
makes no public name of its own under a maker's name here (seven names that bear this module's own
path, and so can meet no other module's, at `groupCarries` and `segmentCarries`). On public data
alone: names of rounds, places, counts.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.BookPlain
open VerifiableInference.Desc (Block FileDescription Place)
open OnBytes (Codes Code OracleNotice)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

variable {Xi S Cl : Type}

/-! ## 1 The part that holds a round stands at the sub-protocol that holds it -/

/-- **The part that holds round i of a chain stands at the sub-protocol that holds it.** -/
theorem addrOfRound_holds : ∀ (bs : List (Block S Cl)) (i : Nat) (a : Addr),
    addrOfRound bs i = some a →
      ∃ b ∈ bs, b.place = a.place ∧ ∃ r ∈ b.rounds, (bs.flatMap (·.rounds))[i]? = some r
  | [], _, _, h => by
    unfold addrOfRound at h
    cases h
  | b :: bs, i, a, h => by
    unfold addrOfRound at h
    split at h
    · rename_i hi
      have e := Option.some.inj h
      refine ⟨b, List.Mem.head _, by rw [← e], b.rounds[i], List.getElem_mem hi, ?_⟩
      rw [List.flatMap_cons, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
    · rename_i hi
      obtain ⟨b', hb', ep, r, hr, er⟩ := addrOfRound_holds bs _ a h
      refine ⟨b', List.Mem.tail _ hb', ep, r, hr, ?_⟩
      rw [List.flatMap_cons, List.getElem?_append_right (by omega)]
      exact er

/-- A numbered round that passes the test on its name. -/
theorem named_of_filter {L : List Fmt.DeclaredRound} {nm : String} {x : Fmt.DeclaredRound × Nat}
    (h : x ∈ L.zipIdx.filter fun r => r.1.entry.name == nm) :
    L[x.2]? = some x.1 ∧ x.1.entry.name = nm := by
  obtain ⟨hm, hn⟩ := List.mem_filter.1 h
  obtain ⟨r, j⟩ := x
  exact ⟨List.mk_mem_zipIdx_iff_getElem?.1 hm, beq_iff_eq.1 hn⟩

/-- A number of `seedRounds` is the number of a round named "SEND seed". -/
theorem seed_named {bs : List (Block S Cl)} {i : Nat} (h : i ∈ seedRounds bs) :
    ∃ r, (bs.flatMap (·.rounds))[i]? = some r ∧ r.entry.name = "SEND seed" := by
  have h' : i ∈ ((bs.flatMap (·.rounds)).zipIdx.filter fun r =>
      r.1.entry.name == "SEND seed").map (·.2) := h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h'
  exact ⟨x.1, (named_of_filter hx).1, (named_of_filter hx).2⟩

/-- The part that holds a round of a name stands at no sub-protocol without a round of that name.
-/
theorem round_not_here {bs : List (Block S Cl)} (hn : (bs.map (·.place)).Nodup) {b : Block S Cl}
    (hb : b ∈ bs) {nm : String} (hno : ∀ r ∈ b.rounds, r.entry.name ≠ nm) {i : Nat} {a : Addr}
    {r : Fmt.DeclaredRound} (ha : addrOfRound bs i = some a)
    (hr : (bs.flatMap (·.rounds))[i]? = some r) (hnm : r.entry.name = nm) :
    a.place ≠ b.place := by
  intro e
  obtain ⟨b', hb', ep, r', hr', er⟩ := addrOfRound_holds bs i a ha
  obtain rfl : b' = b := List.inj_on_of_nodup_map hn hb' hb (ep.trans e)
  obtain rfl : r' = r := Option.some.inj (er.symm.trans hr)
  exact hno _ hr' hnm

/-! ## 2 The rows -/

/-- Each row of `rowsIn` stands at the part that holds a round named "SEND seed". -/
theorem rowsIn_seed {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {l : List (Addr × Due)} (h : rowsIn bs c later = .ok l) :
    ∀ y ∈ l, ∃ i ∈ seedRounds bs, addrOfRound bs i = some y.1 := by
  delta rowsIn at h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · cases h
  refine mapM_all _ l ?_ h
  intro x hx y hy
  have hx1 : x.1 ∈ seedRounds bs := (List.of_mem_zip (a := x.1) (b := x.2)
    (List.mem_filter.1 hx).1).1
  dsimp only at hy
  rcases ex_ite hy with ⟨-, hy⟩ | ⟨-, hy⟩
  · cases hy
  cases ha : addrOfRound bs x.1 with
  | none =>
    rw [ha] at hy
    cases hy
  | some a =>
    rw [ha] at hy
    cases hd : sendDue c.codes ((foldK ((bs.flatMap (·.rounds) ++ later).drop (x.1 + 1))).getD 0)
        x.2.sent with
    | none =>
      rw [hd] at hy
      cases hy
    | some d =>
      rw [hd] at hy
      have e := Except.ok.inj hy
      exact ⟨x.1, hx1, by rw [← e]; exact ha⟩

/-- Each of the switches' rows bears the number of a round that was handed in. -/
theorem switchesDue_rounds (codes : Codes) (rounds : List Fmt.DeclaredRound)
    (first : String → Option (Code × Code)) :
    ∀ (xs : List (Nat × Johnson.G.Sending)) (prev : Option (String × Code × Code))
      (l : List (String × Nat × Nat × Due)),
      switchesDue codes rounds first xs prev = .ok l → ∀ y ∈ l, y.2.1 ∈ xs.map (·.1)
  | [], _, l, h => by
    have e : ([] : List (String × Nat × Nat × Due)) = l := Except.ok.inj h
    intro y hy
    rw [← e] at hy
    cases hy
  | x :: xs, prev, l, h => by
    have step : switchesDue codes rounds first (x :: xs) prev =
        (match (match prev with
            | some p => if p.1 == testOf x.2.label then some p.2 else first (testOf x.2.label)
            | none => first (testOf x.2.label)), x.2.sent.head? with
        | some o, some g =>
          match roomOf codes o g,
            switchDue codes ((foldK (rounds.drop (x.1 + 1))).getD 0) o x.2.sent,
            groupCodes codes [g] with
          | some room, some d, some now_ =>
            (switchesDue codes rounds first xs (some (testOf x.2.label, now_))).map
              fun l => (x.2.label, x.1, room, d) :: l
          | _, _, _ =>
            .error (x.2.label ++ ": a message names a code that the chain does not have")
        | none, _ => .error (x.2.label ++ ": the codes of the test's first stage are not laid")
        | _, none => .error (x.2.label ++ ": the sending holds no message")) := rfl
    rw [step] at h
    split at h
    · split at h
      · obtain ⟨l', hl', e⟩ := ex_mapE h
        intro y hy
        rw [← e] at hy
        cases hy with
        | head => exact List.Mem.head _
        | tail _ hy =>
          exact List.Mem.tail _ (switchesDue_rounds codes rounds first xs _ l' hl' y hy)
      · cases h
    · cases h
    · cases h

/-- Each row of `switchRows` stands at the part that holds a round named "SEND seed". -/
theorem switchRows_seed {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {first : String → Option (Code × Code)} {l : List (Addr × Due)}
    (h : switchRows bs c first = .ok l) :
    ∀ y ∈ l, ∃ i ∈ seedRounds bs, addrOfRound bs i = some y.1 := by
  delta switchRows at h
  rcases ex_ite h with ⟨-, h⟩ | ⟨-, h⟩
  · cases h
  obtain ⟨sd, hsd, h⟩ := ex_bindE h
  obtain ⟨rows, hrows, e⟩ := ex_mapE h
  have hr : ∀ y ∈ rows, ∃ i ∈ seedRounds bs, addrOfRound bs i = some y.1 := by
    refine mapM_all _ rows ?_ hrows
    intro x hx y hy
    have h1 := switchesDue_rounds _ _ _ _ _ sd hsd x hx
    obtain ⟨z, hz, ez⟩ := List.mem_map.1 h1
    have hz1 : z.1 ∈ seedRounds bs := (List.of_mem_zip (a := z.1) (b := z.2)
      (List.mem_filter.1 hz).1).1
    cases ha : addrOfRound bs x.2.1 with
    | none =>
      rw [ha] at hy
      cases hy
    | some a =>
      rw [ha] at hy
      have e2 := Except.ok.inj hy
      exact ⟨x.2.1, ez ▸ hz1, by rw [← e2]; exact ha⟩
  intro y hy
  rw [← e] at hy
  have hy' : y ∈ (rows.map (·.1)).eraseDups.map fun a =>
      (a, (rows.filter fun r => r.1 == a).foldl (fun n r => n.plus r.2) (⟨0, 0⟩ : Due)) := hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy'
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (List.mem_eraseDups.1 ha)
  exact hr z hz

/-! ## 3 The makers, opened at the first chain's table -/

/-- `spendingBook`'s table for the first chain is what `rowsIn` returns. -/
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

/-- `bookRaw`'s table for the first chain is `spendingBook`'s, with `switchRows`' rows behind it. -/
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

/-- A table in which no row bears an address answers nothing there. -/
theorem lookup_none_addr {l : List (Addr × Due)} {a : Addr} (h : ∀ x ∈ l, x.1 ≠ a) :
    l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨k, v⟩ := x
    have hk : (a == k) = false := beq_eq_false_iff_ne.2 fun e => h (k, v) (List.Mem.head _) e.symm
    rw [List.lookup_cons, hk]
    exact ih fun y hy => h y (List.Mem.tail _ hy)

/-! ## 4 Where a carried run ends -/

/-- **The two addresses of a fold**: the first stands at a sub-protocol that holds a round "FOLD
epsilon", the second at one that holds a round "SEND seed". -/
theorem behindFold_named {l : List PlanB} {i : Nat} {p q : Addr}
    (h : behindFold l i = some (p, q)) :
    (∃ x ∈ l, x.place = p.place ∧ ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon") ∧
      ∃ x ∈ l, x.place = q.place ∧ ∃ d ∈ x.rounds, d.entry.name = "SEND seed" := by
  have h' : ((foldBehind l i).bind fun f =>
      ((((l.flatMap (·.rounds)).zipIdx.drop (f.1 + 1)).find? fun r =>
        r.1.entry.name == "SEND seed").bind fun s => addrIn l s.2).bind fun q =>
          (addrIn l f.1).map fun p => (p, q)) = some (p, q) := h
  obtain ⟨f, hf, h1⟩ := opt_bind h'
  obtain ⟨q', hq, h2⟩ := opt_bind h1
  obtain ⟨s, hs, hq'⟩ := opt_bind hq
  obtain ⟨p', hp, e⟩ := opt_map h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨f1, f2, f3⟩ := f
  obtain ⟨d, hd, hn⟩ := foldBehind_name hf
  obtain ⟨x, hx, ex, hdx⟩ := addrIn_holds _ _ _ _ hp hd
  have hsb : (s.1.entry.name == "SEND seed") = true :=
    List.find?_some (p := fun r : Fmt.DeclaredRound × Nat => r.1.entry.name == "SEND seed") hs
  have hsn : s.1.entry.name = "SEND seed" := beq_iff_eq.1 hsb
  have hsg : (l.flatMap (·.rounds))[s.2]? = some s.1 :=
    List.mem_zipIdx_iff_getElem?.1 (List.mem_of_mem_drop (List.mem_of_find?_eq_some hs))
  obtain ⟨y, hy, ey, hdy⟩ := addrIn_holds _ _ _ _ hq' hsg
  exact ⟨⟨x, hx, ex, d, hdx, hn⟩, y, hy, ey, s.1, hdy, hsn⟩

/-- A run that a pair carries ends at one of the pair's two addresses. -/
theorem carryPair_spender {p q : Addr} {reach : List SentMsg} {own : Option SentMsg} :
    ∀ e ∈ carryPair p q reach own, e.spender = p ∨ e.spender = q := by
  intro e he
  unfold carryPair at he
  rcases List.mem_append.1 he with h | h
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
    exact Or.inl rfl
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
    exact Or.inr rfl

/-- An entry whose spender is one of a fold's two addresses ends at a sub-protocol of the plan that
holds a round of one of the two names. -/
theorem fold_ends {l : List PlanB} {i : Nat} {p q : Addr} (h : behindFold l i = some (p, q))
    {e : Ahead} (he : e.spender = p ∨ e.spender = q) :
    ∃ x ∈ l, x.place = e.spender.place ∧
      ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon" ∨ d.entry.name = "SEND seed" := by
  obtain ⟨⟨x, hx, ex, d, hd, hn⟩, y, hy, ey, d', hd', hn'⟩ := behindFold_named h
  rcases he with e1 | e1
  · exact ⟨x, hx, by rw [e1]; exact ex, d, hd, Or.inl hn⟩
  · exact ⟨y, hy, by rw [e1]; exact ey, d', hd', Or.inr hn'⟩

/-- A run that a fold's pair carries ends at a sub-protocol of the plan that holds a round of one of
the two names. -/
theorem pair_ends {l : List PlanB} {i : Nat} {p q : Addr} (h : behindFold l i = some (p, q))
    {reach : List SentMsg} {own : Option SentMsg} :
    ∀ e ∈ carryPair p q reach own, ∃ x ∈ l, x.place = e.spender.place ∧
      ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon" ∨ d.entry.name = "SEND seed" :=
  fun e he => fold_ends h (carryPair_spender e he)

/-- The like of `pair_ends` for `groupCarries`. -/
theorem groupCarries_ends {l : List PlanB} {i : Nat} {g : List SentMsg} {own : Option SentMsg}
    {r : List Ahead} (h : groupCarries l i g own = .ok r) :
    ∀ e ∈ r, ∃ x ∈ l, x.place = e.spender.place ∧
      ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon" ∨ d.entry.name = "SEND seed" := by
  unfold groupCarries at h
  split at h
  · rename_i p q hb
    have e := Except.ok.inj h
    rw [← e]
    exact pair_ends hb
  · cases h

/-- The like of `pair_ends` for `segmentCarries`; by membership alone. The one step that reads the
arm's value reads it as two lists of carried runs, one to each of the fold's two addresses: a
`carryPair` is such a value by unfolding. -/
theorem segmentCarries_ends {here : List PlanB} {ms : List SentMsg} {l : List Ahead}
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
  · rename_i p q k hb hk
    have e2 := Except.ok.inj hr
    rw [← e2]
    intro a ha
    refine fold_ends hb ?_
    rcases List.mem_append.1 ha with h1 | h1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h1
      exact Or.inl rfl
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h1
      exact Or.inr rfl
  · cases hr

/-- The part behind a fold that sends its own table stands at a sub-protocol of the chain. -/
theorem ownFresh_behind {bs : List (Block S Cl)} {o : OwnFresh} (h : o ∈ ownFreshIn bs) :
    o.behind.place ∈ bs.map (·.place) := by
  have h' : o ∈ (((planOf bs).flatMap (·.rounds)).zipIdx.filter fun r =>
      r.1.entry.name == "FOLD epsilon" && r.1.entry.roots != 0).filterMap fun r =>
      if r.2 == 0 then none else
      (behindFold (planOf bs) (r.2 - 1)).bind fun pq =>
        (foldBehind (planOf bs) (r.2 - 1)).map fun f =>
          (⟨pq.1, pq.2, f.2.2, (maskWordsByRound bs).getD r.2 0 / 3⟩ : OwnFresh) := h
  obtain ⟨r, -, hr⟩ := List.mem_filterMap.1 h'
  by_cases h0 : (r.2 == 0) = true
  · rw [if_pos h0] at hr
    cases hr
  · rw [if_neg h0] at hr
    obtain ⟨pq, hpq, h1⟩ := opt_bind hr
    obtain ⟨f, -, rfl⟩ := opt_map h1
    obtain ⟨p, q⟩ := pq
    obtain ⟨-, y, hy, ey, -⟩ := behindFold_named hpq
    show q.place ∈ bs.map (·.place)
    rw [← ey, ← planOf_places]
    exact List.mem_map_of_mem hy

/-- A value that must be there, and is. -/
theorem due_some {α : Type} {what : String} {x : Option α} {a : α} (h : due? what x = .ok a) :
    x = some a := by
  cases x with
  | none =>
    have h' : (Except.error (what ++ " is not found") : Except String α) = .ok a := h
    cases h'
  | some b => exact congrArg some (Except.ok.inj h)

end ProofFile.Honest.BookPlain

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow ProofFile.Honest.BookPlain

variable {Xi : Type}

/-- **(i) AT A SUB-PROTOCOL OF THE FIRST CHAIN NONE OF WHOSE ROUNDS IS NAMED "SEND seed" THE WHOLE
BOOK's TABLE FOR THAT CHAIN HAS NO ROW.** Conditional: hB: the book's maker returns B; hp: the
description's test on its places accepts; hb; hs. -/
theorem plain_no_row {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true) {b : Block F.S₁ F.Cl}
    (hb : b ∈ F.first.blocksInOrder) (hs : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed") :
    ∀ i, dueAt B.first ⟨b.place, i⟩ = ⟨0, 0⟩ := by
  intro i
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨B₀, r0, hB₀, hr0, eF⟩ := bookRaw_first hW
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  have key : ∀ y ∈ W.first, y.1 ≠ ⟨b.place, i⟩ := by
    intro y hy e
    rw [eF] at hy
    have hy' : ∃ j ∈ seedRounds F.first.blocksInOrder, addrOfRound F.first.blocksInOrder j = some y.1 := by
      rcases List.mem_append.1 hy with h1 | h1
      · exact rowsIn_seed (spendingBook_first hB₀) y h1
      · exact switchRows_seed hr0 y h1
    obtain ⟨j, hj, ha⟩ := hy'
    obtain ⟨r, hr, hnm⟩ := seed_named hj
    exact round_not_here hn hb hs ha hr hnm (by rw [e])
  show ((W.first.lookup ⟨b.place, i⟩).getD ⟨0, 0⟩ : Due) = ⟨0, 0⟩
  rw [lookup_none_addr key]
  rfl

/-- **(ii) AT A SUB-PROTOCOL OF THE FIRST CHAIN NONE OF WHOSE ROUNDS IS NAMED "SEND seed" OR "FOLD
epsilon" EVERY ENTRY OF THE WHOLE BOOK THAT IS HANDED TO ONE OF ITS PARTS IS A SPENT ONE.**
Conditional: hB; hp; hb; hs; hf. -/
theorem plain_all_spent {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true) {b : Block F.S₁ F.Cl}
    (hb : b ∈ F.first.blocksInOrder) (hs : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed")
    (hf : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") :
    ∀ e ∈ B.ahead, e.spender.place = b.place → e.once = true := by
  intro e he hpl
  unfold bookWhole at hB
  obtain ⟨W, hW, hc⟩ := ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB₀, -, -, hseg, -, hcF, -, hcO, hpq, -, eW⟩ :=
    bookRaw_ahead hW
  obtain ⟨ws, f0, f1, f2, -, hf0, hf1, hf2, eB⟩ := spendingBook_ahead hB₀
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  have c1 : b.place.chain = 1 := chain_first hp _ (List.mem_map_of_mem hb)
  -- no sub-protocol of the first chain's plan at b's place holds a round of one of the two names
  have no1 : ∀ x ∈ planOf F.first.blocksInOrder, x.place = e.spender.place →
      ∀ d ∈ x.rounds, ¬ (d.entry.name = "FOLD epsilon" ∨ d.entry.name = "SEND seed") := by
    intro x hx ex d hd hnm
    have hx' : x ∈ F.first.blocksInOrder.map fun b => (⟨b.place, partsCut b, b.rounds⟩ : PlanB) := hx
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hx'
    obtain rfl : b' = b := List.inj_on_of_nodup_map hn hb' hb (ex.trans hpl)
    rcases hnm with h1 | h1
    · exact hf d hd h1
    · exact hs d hd h1
  -- no place of the shared or of the second chain is b's
  have no2 : e.spender.place ∉ F.shared.blocksInOrder.map (·.place) := fun h2 => by
    have := chain_shared hp _ h2
    rw [hpl, c1] at this
    cases this
  have no3 : e.spender.place ∉ F.second.blocksInOrder.map (·.place) := fun h3 => by
    have := chain_second hp _ h3
    rw [hpl, c1] at this
    cases this
  have in2 : ∀ x ∈ planOf F.shared.blocksInOrder, x.place ≠ e.spender.place := fun x hx ex =>
    no2 (by rw [← ex, ← planOf_places]; exact List.mem_map_of_mem hx)
  have in3 : ∀ x ∈ planOf F.second.blocksInOrder, x.place ≠ e.spender.place := fun x hx ex =>
    no3 (by rw [← ex, ← planOf_places]; exact List.mem_map_of_mem hx)
  rw [eW, eB] at he
  simp only [List.mem_append] at he
  rcases he with ((((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1) | h1
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 h1
    rfl
  · obtain ⟨x, hx, ex, d, hd, hnm⟩ := foldEntries_spender hf0 e h1
    rcases List.mem_append.1 hx with hx | hx
    · exact absurd (Or.inl hnm) (no1 x hx ex d hd)
    · exact absurd ex (in3 x hx)
  · obtain ⟨x, hx, ex, -⟩ := foldEntries_spender hf1 e h1
    rw [List.append_nil] at hx
    exact absurd ex (in2 x hx)
  · obtain ⟨x, hx, ex, -⟩ := foldEntries_spender hf2 e h1
    rw [List.append_nil] at hx
    exact absurd ex (in3 x hx)
  · exact absurd (splitEntry_spender (Option.mem_toList.1 h1)) no2
  · obtain ⟨x, hx, ex, d, hd, hnm⟩ := segmentCarries_ends hseg e h1
    exact absurd hnm (no1 x hx ex d hd)
  · obtain ⟨x, hx, ex, -⟩ := groupCarries_ends hcF e h1
    exact absurd ex (in2 x hx)
  · obtain ⟨x, hx, ex, -⟩ := groupCarries_ends hcO e h1
    exact absurd ex (in2 x hx)
  · obtain ⟨x, hx, ex, -⟩ := pair_ends (p := pq.1) (q := pq.2) (due_some hpq) e h1
    exact absurd ex (in3 x hx)
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h1
    exact absurd (ownFresh_behind ho) no2

/-- **(ii) in the other wording: NO CARRIED RUN ENDS THERE.** Conditional: as (ii). -/
theorem plain_no_carry {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (hB : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true) {b : Block F.S₁ F.Cl}
    (hb : b ∈ F.first.blocksInOrder) (hs : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed")
    (hf : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") :
    ∀ e ∈ B.ahead, e.once = false → e.spender.place ≠ b.place := by
  intro e he ho hpl
  rw [plain_all_spent hB hp hb hs hf e he hpl] at ho
  cases ho

end ProofFile.Honest

#print axioms ProofFile.Honest.BookPlain.addrOfRound_holds
#print axioms ProofFile.Honest.BookPlain.named_of_filter
#print axioms ProofFile.Honest.BookPlain.seed_named
#print axioms ProofFile.Honest.BookPlain.round_not_here
#print axioms ProofFile.Honest.BookPlain.rowsIn_seed
#print axioms ProofFile.Honest.BookPlain.switchesDue_rounds
#print axioms ProofFile.Honest.BookPlain.switchRows_seed
#print axioms ProofFile.Honest.BookPlain.spendingBook_first
#print axioms ProofFile.Honest.BookPlain.bookRaw_first
#print axioms ProofFile.Honest.BookPlain.lookup_none_addr
#print axioms ProofFile.Honest.BookPlain.behindFold_named
#print axioms ProofFile.Honest.BookPlain.carryPair_spender
#print axioms ProofFile.Honest.BookPlain.fold_ends
#print axioms ProofFile.Honest.BookPlain.pair_ends
#print axioms ProofFile.Honest.BookPlain.groupCarries_ends
#print axioms ProofFile.Honest.BookPlain.segmentCarries_ends
#print axioms ProofFile.Honest.BookPlain.ownFresh_behind
#print axioms ProofFile.Honest.BookPlain.due_some
#print axioms ProofFile.Honest.plain_no_row
#print axioms ProofFile.Honest.plain_all_spent
#print axioms ProofFile.Honest.plain_no_carry
