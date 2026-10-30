-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/RowModel.lean: one list of parts, while the verifier has not
rejected (`Stand.live`). Where `play` has played the list's rounds (Honest/Frame.lean: `rowSteps`),
the fold at coins (Honest/Law/Rule/Stages.lean: `Kit.real`) over the list's stretches, as a session
cuts them (Honest/Law/Rule/Session.lean: `cutRow`), produces exactly what these rounds show
(`row_model`). What the parts are handed of opened columns is tied to what has been produced by
hypotheses (Honest/Law/Rule/OpenedAt.lean): `OpenedAt` at a part, which `row_model` makes from its
own three: the field's value, `HeldAt`, and a challenge for each declared round. These three are
paid nowhere here: `member_lay` (Honest/Law/Rule/MemberLay.lean) carries them, and `TieAt.member`
(Honest/Law/Rule/OpenedStep.lean) reads them off `TieAt` in Honest/Law/Rule/ChainModel.lean and
Honest/Law/Rule/ChainStep.lean.

  1  `mapError_ok`, `lendRow_cons_ok`   the coins that a list of parts is given, part by part
  2  `steps_orc`, `steps_shape`, `steps_len`   a part's `Step`s: what they declare; how many they
     are
  3  `rowKeys_head`, `dryAt_split`   the state and the challenges before a part
     (Honest/Law/Rule/Real.lean: `dryAt`), where the chain's keys are cut at the part's first round
  4  `pairs_rounds`, `part_model`   one part
  5  `row_model`   the list of parts

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Real
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartLaw
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.Keys
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 The coins that a list of parts is given -/

theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {e : Except ε α} {y : α}
    (h : e.mapError f = .ok y) : e = .ok y := by
  cases e with
  | error s => cases h
  | ok a =>
    have h' : (Except.ok a : Except ε' α) = .ok y := h
    exact congrArg Except.ok (Except.ok.inj h')

theorem lendRow_cons_ok {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : Place} {p : Part V W Y} {ps : List (Part V W Y)} {j : Nat} {c : RowCoins (p :: ps)}
    (h : lendRow B rows look a (p :: ps) j = .ok c) :
    lendPart B rows look ⟨a, j⟩ p = .ok c.1 ∧ lendRow B rows look a ps (j + 1) = .ok c.2 := by
  rw [lendRow] at h
  obtain ⟨c₁, h1, h⟩ := exBind_ok h
  obtain ⟨c₂, h2, h⟩ := exMap_ok h
  subst h
  exact ⟨mapError_ok h1, h2⟩

/-! ## 2 A part's `Step`s -/

section
variable (p : Part V W Y) (name : String) (a : Addr) (rs : List (Fmt.DeclaredRound × List Oracle))
  (v : Option V) (c : p.Coins)

theorem steps_orc (h : rs.length ≤ p.moves.length) :
    (p.steps name a rs v c).map (·.oracles.length) = rs.map (·.2.length) := by
  have e := congrArg (List.map fun t : Fmt.DeclaredRound × List Oracle × Place × Bool => t.2.1.length)
    (Part.steps_rows p name a rs v c h)
  rw [List.map_map, List.map_map] at e
  exact e

theorem steps_shape (h : rs.length ≤ p.moves.length)
    (hs : ∀ z ∈ rs, z.2.length = z.1.entry.roots) :
    ∀ s ∈ p.steps name a rs v c, s.oracles.length = s.decl.entry.roots := by
  intro s hs'
  have h1 : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      (p.steps name a rs v c).map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hs', rfl⟩
  rw [Part.steps_rows p name a rs v c h] at h1
  obtain ⟨z, hz, e⟩ := List.mem_map.1 h1
  have e1 : z.1 = s.decl := congrArg (·.1) e
  have e2 : z.2 = s.oracles := congrArg (·.2.1) e
  rw [← e1, ← e2]
  exact hs z hz

theorem steps_len (h : rs.length ≤ p.moves.length) :
    (p.steps name a rs v c).length = rs.length := by
  have e := congrArg List.length (steps_orc p name a rs v c h)
  rw [List.length_map, List.length_map] at e
  exact e

end

/-! ## 3 Before a part -/

/-- A list of parts whose first part has a round, at a non-empty list of rounds: its keys begin at
that part's address. -/
theorem rowKeys_head (a : Place) (p : Part V W Y) (ps : List (Part V W Y)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (h0 : p.moves.length ≠ 0) (h1 : rs ≠ []) :
    ∃ h rest, rowKeys a (p :: ps) j rs = ((⟨a, j⟩ : Addr), h) :: rest := by
  rw [rowKeys]
  cases hm : p.moves with
  | nil => simp [hm] at h0
  | cons mv ms =>
    cases rs with
    | nil => exact absurd rfl h1
    | cons r rs' => exact ⟨some mv.hand, _, rfl⟩

theorem dryAt_split {keys kp rest : List (Addr × Option (State W Y → Y))} {a : Addr}
    {h : Option (State W Y → Y)} {dsAll dp dr : List Fmt.Drawn} (m₀ : Mid W Y)
    (hk : keys = kp ++ (a, h) :: rest) (hf : ∀ q ∈ kp, q.1 ≠ a) (hd : dsAll = dp ++ dr)
    (hl : dp.length = kp.length) :
    dryAt keys dsAll m₀ a = ⟨dryFold (kp.map (·.2)) dp m₀.st, m₀.loc ++ dp, [], none⟩ := by
  unfold dryAt
  rw [hk, takeWhile_split a h rest kp hf, List.take_left' rfl, hd, List.take_left' hl]

/-! ## 4 One part -/

theorem pairs_rounds (tree : Nat → List Nat) : ∀ (l : List Played) (n : Nat),
    ((pairsBy tree l n).map fun z => (⟨z.1.vals, z.2⟩ : Fmt.RoundView)) = roundsOf l
  | [], _ => rfl
  | p :: l, n =>
    congrArg ((⟨p.vals, p.drawn⟩ : Fmt.RoundView) :: ·) (pairs_rounds tree l (n + p.tables.length))

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} (x : Xi) (st : List (Nat × Nat × List UInt64))
  (R : RealAt Bk) (k : Coins Bk) (ch : Nat) (tree : Nat → List Nat)

/-- **One part, while the verifier has not rejected**: its stage shows what the rounds of `play`
show. `hopen`: the columns that the part is handed are those that what has been produced holds for
the reads of `pre`. -/
theorem part_model {pre : List (Nat × Nat × List Fmt.DeclaredRound)} (φ : Face V W Pb)
    (σ : Side S Cl V W Y Pb) (u : Member V W Y Pb) (n : Nat)
    (ds : List Fmt.Drawn) (m : Mid W Y) (Z : Stand F) (c : u.part.Coins)
    (y : List Played × Mid W Y)
    (hplay : play (u.part.steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds
      (φ.sees m.st.input) c) ds [] m = .ok y)
    (hlend : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨σ.block.place, u.number⟩ u.part = .ok c)
    (hlen : u.rounds.length ≤ u.part.moves.length)
    (hshape : ∀ z ∈ u.rounds, z.2.length = z.1.entry.roots) (hlive : Z.live ch = true)
    (hseen : m.seen = (Z.laid.front ch st).seen) (hopen : OpenedAt pre m (Z.laid.front ch st))
    (dry : Mid W Y) (hst : m.st = dry.st) (hloc : m.loc = dry.loc)
    (hR : R ch ⟨σ.block.place, u.number⟩ = partShows φ σ u Bk ch pre dry) (t : Teller) :
    (Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds,
      asksFrom tree (u.rounds.map (·.2.length)) n, some t⟩ : Act F)).shows k Z =
      pairsBy tree y.1 n := by
  obtain ⟨s1, s2⟩ := play_shape _ _ _ _ _ hplay
    (steps_shape u.part σ.block.name ⟨σ.block.place, u.number⟩ u.rounds _ c hlen hshape)
  rw [steps_orc u.part σ.block.name ⟨σ.block.place, u.number⟩ u.rounds _ c hlen] at s1
  have hM : (⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
      (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩ : Mid W Y) = m := by
    unfold OpenedAt at hopen
    rw [← hst, ← hloc, ← hseen, ← hopen]
  have hs : partShows φ σ u Bk ch pre dry k (Z.laid.front ch st) ds
      (asksFrom tree (u.rounds.map (·.2.length)) n) =
      some (shownOf y.1 (asksFrom tree (u.rounds.map (·.2.length)) n)) := by
    unfold partShows
    rw [hlend, hM]
    show σ.shows φ u c m ds _ = _
    unfold Side.shows
    rw [hplay]
    rfl
  show (if Z.live ch = true then
      (if (some t).isSome = true then
        ((R ch ⟨σ.block.place, u.number⟩ k (Z.laid.front ch st) ds
          (asksFrom tree (u.rounds.map (·.2.length)) n)).bind (zipLen ds)).getD []
      else _) else _) = _
  have hsome : (some t).isSome = true := rfl
  rw [if_pos hlive, if_pos hsome, hR, hs]
  have hl' : (shownOf y.1 (asksFrom tree (u.rounds.map (·.2.length)) n)).length = ds.length := by
    rw [← s2]
    unfold shownOf
    simp
  show (zipLen ds (shownOf y.1 (asksFrom tree (u.rounds.map (·.2.length)) n))).getD [] = _
  unfold zipLen
  rw [if_pos (by rw [hl']; exact beq_self_eq_true _)]
  exact shows_pairs tree y.1 n _ ds s1 s2

/-! ## 5 The list of parts -/

/-- **One list of parts, while the verifier has not rejected.** `keys`, `dsAll`, `m₀`: the chain's
keys, challenges and start. `kp`, `dp`: the keys and the challenges before the list's part number j.
`pre`, `cs`: the declared rounds whose reads the list's parts are handed, and the columns: the
state's field is `some cs`; what has been produced holds `cs` for these reads (`HeldAt`) and a
challenge for each of these rounds. -/
theorem row_model {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {cs : List OpenedColumn}
    (tl : Addr → Option Teller) (φ : Face V W Pb) (σ : Side S Cl V W Y Pb)
    (v : Option V) (keys : List (Addr × Option (State W Y → Y))) (dsAll : List Fmt.Drawn)
    (m₀ : Mid W Y) :
    ∀ (row : List (Part V W Y × Sim Pb)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (ds : List Fmt.Drawn) (n : Nat) (m : Mid W Y) (Z : Stand F)
      (c : RowCoins (row.map (·.1))) (y : List Played × Mid W Y)
      (kp kq : List (Addr × Option (State W Y → Y))) (dp dq : List Fmt.Drawn),
    play (rowSteps σ.block.name σ.block.place v (row.map (·.1)) j rs c) ds [] m = .ok y →
    lendRow Bk (Bk.rowsOf ch) (k.look ch) σ.block.place (row.map (·.1)) j = .ok c →
    (row.map (·.1.moves.length)).sum = rs.length → ds.length = rs.length →
    (∀ q ∈ row, q.1.moves.length ≠ 0) → (∀ z ∈ rs, z.2.length = z.1.entry.roots) →
    v = φ.sees m.st.input → Z.live ch = true → m.seen = (Z.laid.front ch st).seen →
    m.opened = some cs → HeldAt pre (Z.laid.front ch st) cs →
    (∀ x ∈ pre, x.2.2.length ≤ ((Z.laid.front ch st).drawnOf x.1).length) →
    keys = kp ++ rowKeys σ.block.place (row.map (·.1)) j rs ++ kq → dsAll = dp ++ ds ++ dq →
    dp.length = kp.length → (∀ q ∈ kp, q.1.place ≠ σ.block.place ∨ q.1.part < j) →
    m.st = dryFold (kp.map (·.2)) dp m₀.st → m.loc = m₀.loc ++ dp →
    (∀ u ∈ membersOf row j rs, R ch ⟨σ.block.place, u.number⟩ =
      partShows φ σ u Bk ch pre (dryAt keys dsAll m₀ ⟨σ.block.place, u.number⟩)) →
    (∀ u ∈ membersOf row j rs, (tl ⟨σ.block.place, u.number⟩).isSome = true) →
    Kit.real ((cutRow ch tree tl σ.block.place j (row.map (·.1.moves.length)) rs n ds).map
        fun s => Act.stage x st R (.lay s : Act F)) k Z =
      { Z with laid := Z.laid.add ch (pairsBy tree y.1 n) }
  | [], j, rs, ds, n, m, Z, c, y, kp, kq, dp, dq, hp, _, hsum, hds, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _ => by
    have hrs : rs = [] := List.eq_nil_of_length_eq_zero (by simpa using hsum.symm)
    subst hrs
    have hd0 : ds = [] := List.eq_nil_of_length_eq_zero (by simpa using hds)
    subst hd0
    have hp' : play ([] : List (Step W Y)) [] [] m = .ok y := hp
    simp only [play] at hp'
    cases hp'
    show Z = { Z with laid := Z.laid.add ch [] }
    rw [Laid.add_nil]
  | q :: row, j, rs, ds, n, m, Z, c, y, kp, kq, dp, dq, hp, hl, hsum, hds, hne, hsh, hv, hlive,
      hseen, hW, hF, hL, hk, hd, hlen, hfr, hst, hloc, hR, htl => by
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
    -- the play, cut after the first part
    have hp' : play (q.1.steps σ.block.name ⟨σ.block.place, j⟩ (rs.take q.1.moves.length) v c.1 ++
        rowSteps σ.block.name σ.block.place v (row.map (·.1)) (j + 1)
          (rs.drop q.1.moves.length) c.2)
        (ds.take q.1.moves.length ++ ds.drop q.1.moves.length) [] m = .ok y := by
      rw [List.take_append_drop]
      exact hp
    rw [play_append _ _ _ _ _ _ (by rw [hdk, steps_len _ _ _ _ _ _ htk', htk])] at hp'
    obtain ⟨y₁, h1, hp'⟩ := exBind_ok hp'
    obtain ⟨y₂, h2, e⟩ := exMap_ok hp'
    subst e
    have h2' : play (rowSteps σ.block.name σ.block.place v (row.map (·.1)) (j + 1)
        (rs.drop q.1.moves.length) c.2) (ds.drop q.1.moves.length) [] y₁.2 = .ok y₂ := by
      simpa using h2
    obtain ⟨i1, i2, i3⟩ := play_mid _ _ _ _ _ h1
    obtain ⟨d1, d2⟩ := play_dry _ _ _ _ _ h1
    obtain ⟨s1, -⟩ := play_shape _ _ _ _ _ h1 (steps_shape q.1 σ.block.name ⟨σ.block.place, j⟩
      (rs.take q.1.moves.length) v c.1 htk' fun z hz => hsh z (List.mem_of_mem_take hz))
    rw [steps_orc q.1 σ.block.name ⟨σ.block.place, j⟩ (rs.take q.1.moves.length) v c.1 htk'] at s1
    -- the first part's `Member`, teller and dry state
    have hu : (⟨j, rs.take q.1.moves.length, q.1, q.2⟩ : Member V W Y Pb) ∈
        membersOf (q :: row) j rs := List.mem_cons.2 (Or.inl rfl)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (htl _ hu)
    have ht' : tl ⟨σ.block.place, j⟩ = some t := ht
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
      (by rw [hdry]; exact hst) (by rw [hdry]; exact hloc) (hR _ hu) t
    have hshow' : (Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, j⟩, rs.take q.1.moves.length,
        ds.take q.1.moves.length,
        asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n, some t⟩ : Act F)).shows k Z =
        pairsBy tree y₁.1 n := hshow
    -- the rest of the list
    have hkp : (q.1.steps σ.block.name ⟨σ.block.place, j⟩ (rs.take q.1.moves.length) v c.1).map
        Step.hand = (((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
          ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)).map (·.2) := by
      rw [← Part.steps_keys q.1 σ.block.name ⟨σ.block.place, j⟩ (rs.take q.1.moves.length) v c.1,
        List.map_map]
      rfl
    have hkl : (((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
        ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)).length = q.1.moves.length := by
      rw [List.length_map, List.length_zip, htk, Nat.min_self]
    have ih := row_model tl φ σ v keys dsAll m₀ row (j + 1) (rs.drop q.1.moves.length)
      (ds.drop q.1.moves.length) (n + ((rs.take q.1.moves.length).map (·.2.length)).sum) y₁.2
      { Z with laid := Z.laid.add ch (pairsBy tree y₁.1 n) } c.2 y₂
      (kp ++ ((rs.take q.1.moves.length).zip q.1.moves).map fun z =>
        ((⟨σ.block.place, j⟩ : Addr), some z.2.hand)) kq (dp ++ ds.take q.1.moves.length) dq
      h2' l2 (by rw [List.length_drop]; omega) (by rw [List.length_drop, List.length_drop, hds])
      (fun z hz => hne z (List.mem_cons_of_mem _ hz))
      (fun z hz => hsh z (List.mem_of_mem_drop hz)) (by rw [i1]; exact hv) hlive
      (by
        show y₁.2.seen = ((Z.laid.add ch (pairsBy tree y₁.1 n)).front ch st).seen
        rw [Laid.seen_add, pairs_rounds, i3, hseen])
      (by rw [play_opened _ _ _ _ _ h1]; exact hW)
      (by
        show HeldAt pre ((Z.laid.add ch (pairsBy tree y₁.1 n)).front ch st) cs
        rw [Laid.front_add]
        exact hF.more _ hL)
      (fun x hx => by
        show x.2.2.length ≤ (((Z.laid.add ch (pairsBy tree y₁.1 n)).front ch st).drawnOf x.1).length
        rw [Laid.front_add]
        exact Nat.le_trans (hL x hx) (Before.drawnOf_more _ _ _).length_le)
      (by
        rw [hk]
        show kp ++ rowKeys σ.block.place (q.1 :: row.map (·.1)) j rs ++ kq = _
        rw [rowKeys]
        simp only [List.append_assoc])
      (by
        conv_lhs => rw [hd, ← List.take_append_drop q.1.moves.length ds]
        simp only [List.append_assoc])
      (by rw [List.length_append, List.length_append, hlen, hdk, hkl])
      (fun z hz => by
        rcases List.mem_append.1 hz with hz | hz
        · rcases hfr z hz with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
          exact Or.inr (Nat.lt_succ_self j))
      (by rw [d1, hst, hkp, List.map_append, dryFold_append _ _ _ _ _ (by
            rw [List.length_map, hlen])])
      (by rw [d2, hloc, List.append_assoc])
      (fun u hu' => hR u (List.mem_cons_of_mem _ hu'))
      (fun u hu' => htl u (List.mem_cons_of_mem _ hu'))
    show Kit.real ((cutRow ch tree tl σ.block.place (j + 1) (row.map (·.1.moves.length))
        (rs.drop q.1.moves.length) (n + ((rs.take q.1.moves.length).map (·.2.length)).sum)
        (ds.drop q.1.moves.length)).map fun s => Act.stage x st R (.lay s : Act F)) k
      { Z with laid := (Z.laid.add ch
        ((Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, j⟩, rs.take q.1.moves.length,
          ds.take q.1.moves.length,
          asksFrom tree ((rs.take q.1.moves.length).map (·.2.length)) n,
          tl ⟨σ.block.place, j⟩⟩ : Act F)).shows k Z)) } = _
    rw [ht', hshow', ih]
    show ({ Z with laid := ((Z.laid.add ch (pairsBy tree y₁.1 n)).add ch
        (pairsBy tree y₂.1 (n + ((rs.take q.1.moves.length).map (·.2.length)).sum))) } : Stand F) =
      { Z with laid := Z.laid.add ch (pairsBy tree (y₁.1 ++ y₂.1) n) }
    rw [Laid.add_add, pairsBy_append, s1]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.mapError_ok
#print axioms ProofFile.Honest.lendRow_cons_ok
#print axioms ProofFile.Honest.steps_orc
#print axioms ProofFile.Honest.steps_shape
#print axioms ProofFile.Honest.steps_len
#print axioms ProofFile.Honest.rowKeys_head
#print axioms ProofFile.Honest.dryAt_split
#print axioms ProofFile.Honest.pairs_rounds
#print axioms ProofFile.Honest.part_model
#print axioms ProofFile.Honest.row_model
