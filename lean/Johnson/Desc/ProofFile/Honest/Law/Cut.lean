-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Cut.lean: the functions of Honest/Frame.lean, divided at a
sub-protocol. The lemmas are general in the description, the book and the prover.

  1  `chainSteps_append`, `drawsFit_append`, `readsOf_append`, `fillCols_append`, `decides_append`
     (`decides`: Honest/Law/Kept.lean), `yields_length`   each of the first five goes over two
     consecutive lists as over the first and then the second (`play_append`: Honest/Law/Play.lean);
     `play_cut`: a run of `play` over three consecutive lists, taken apart
  2  `fits_played`, `step_iff_decide`   one sub-protocol's book-keeping, in the very terms of
     `Good.acc` (Honest/Side.lean): if a prover's side's rounds have been played and the columns
     that the sub-protocol reads have been filled, the library's `Block.Fits` holds, and
     `Block.step` accepts if and only if `decide` does
  3  `envOf` and five lemmas   the available tables (`Env`, Honest/Side.lean) at a real run: after
     played rounds

Limits.
  * `step_iff_decide` is an equivalence: no acceptance is concluded.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Side
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W X : Type}

/-! ## 1 Two consecutive lists -/

theorem chainSteps_append {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} (hs : List (Placed V W X)) : ∀ (b₁ b₂ : List (Block S Cl)),
    chainSteps B rows look v (b₁ ++ b₂) hs =
      (chainSteps B rows look v b₁ hs).bind fun l₁ =>
        (chainSteps B rows look v b₂ hs).map fun l₂ => l₁ ++ l₂
  | [], b₂ => by
    cases h : chainSteps B rows look v b₂ hs <;> simp [chainSteps, Except.bind, Except.map, h]
  | b :: b₁, b₂ => by
    have ih := chainSteps_append (B := B) (rows := rows) (look := look) (v := v) hs b₁ b₂
    simp only [List.cons_append, chainSteps]
    split
    · rfl
    split
    · rw [ih]
      cases chainSteps B rows look v b₁ hs with
      | error e => rfl
      | ok l₁ =>
        cases chainSteps B rows look v b₂ hs with
        | error e => rfl
        | ok l₂ => simp [Except.bind, Except.map]
    · split
      · rfl
      split
      · rfl
      split
      · rfl
      split
      · rfl
      rw [ih]
      rename_i g _ _ _ _ _
      cases lendRow B rows look b.place g.parts 0 with
      | error e => rfl
      | ok c =>
        cases chainSteps B rows look v b₁ hs with
        | error e => rfl
        | ok l₁ =>
          cases chainSteps B rows look v b₂ hs with
          | error e => rfl
          | ok l₂ => simp [Except.mapError, Except.bind, Except.map]

/-- The test on a list of challenges, over two consecutive lists of rounds. -/
theorem drawsFit_append : ∀ (A B : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    drawsFit (A ++ B) Rs = (drawsFit A (Rs.take A.length) && drawsFit B (Rs.drop A.length))
  | [], B, Rs => by simp [drawsFit]
  | d :: A, B, [] => by simp [drawsFit]
  | d :: A, B, R :: Rs => by
    simp only [List.cons_append, drawsFit, List.length_cons, List.take_succ_cons,
      List.drop_succ_cons, drawsFit_append A B Rs, Bool.and_assoc]

theorem readsOf_append (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (ds es : List Fmt.DeclaredRound) (Rs Ss : List Fmt.Drawn), ds.length = Rs.length →
    readsOf chain ft stored tree (ds ++ es) (Rs ++ Ss) =
      readsOf chain ft stored tree ds Rs ++ readsOf chain ft stored tree es Ss
  | [], _, [], _, _ => by simp [readsOf]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | d :: ds, es, R :: Rs, Ss, h => by
    have ih := readsOf_append chain ft stored tree ds es Rs Ss (by simpa using h)
    simp only [List.cons_append, readsOf, ih, List.append_assoc]

theorem fillCols_append : ∀ (q₁ q₂ : List Read) (back : List OpenedColumn),
    fillCols (q₁ ++ q₂) back =
      (fillCols q₁ back).bind fun c₁ => (fillCols q₂ (back.drop q₁.length)).map fun c₂ => c₁ ++ c₂
  | [], q₂, back => by
    cases h : fillCols q₂ back <;> simp [fillCols, Except.bind, Except.map, h]
  | r :: q₁, q₂, back => by
    have hb : back.tail.drop q₁.length = back.drop (q₁.length + 1) := by cases back <;> simp
    have ih := fillCols_append q₁ q₂ back.tail
    rw [hb] at ih
    simp only [List.cons_append, fillCols, List.length_cons]
    split
    · split
      · rfl
      rw [ih]
      cases fillCols q₁ back.tail with
      | error e => rfl
      | ok c₁ =>
        cases fillCols q₂ (back.drop (q₁.length + 1)) with
        | error e => rfl
        | ok c₂ => simp [Except.bind, Except.map]
    · split
      · rfl
      split
      · rfl
      rw [ih]
      cases fillCols q₁ back.tail with
      | error e => rfl
      | ok c₁ =>
        cases fillCols q₂ (back.drop (q₁.length + 1)) with
        | error e => rfl
        | ok c₂ => simp [Except.bind, Except.map]
    · rfl

theorem decides_append (ft : Nat) (l₂ : List (Block S Cl)) : ∀ (l₁ : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    decides ft (l₁ ++ l₂) s rs cols =
      (decides ft l₁ s rs cols).bind fun s' =>
        decides ft l₂ s' (rs.drop (l₁.flatMap (·.rounds)).length)
          (cols.drop ((groupsOf ft (l₁.flatMap (·.rounds)) (rs.map (·.drawn))).flatMap id).length)
  | [], s, rs, cols => by simp [decides, Except.bind, groupsOf]
  | b :: l₁, s, rs, cols => by
    have hcut : ((groupsOf ft ((b :: l₁).flatMap (·.rounds)) (rs.map (·.drawn))).flatMap
        id).length = (b.want ft (rs.take b.rounds.length)).length +
          ((groupsOf ft (l₁.flatMap (·.rounds)) ((rs.drop b.rounds.length).map
            (·.drawn))).flatMap id).length := by
      rw [List.flatMap_cons, groupsOf_app, List.flatMap_append, List.length_append,
        ← List.map_take, ← List.map_drop]
      rfl
    rw [List.cons_append, decides_cons, decides_cons, hcut, List.flatMap_cons, List.length_append]
    cases b.decide s ((rs.take b.rounds.length).map noDigest)
        (b.shown ft (rs.take b.rounds.length) cols) with
    | error e => rfl
    | ok s' =>
      show decides ft (l₁ ++ l₂) s' _ _ = (decides ft l₁ s' _ _).bind _
      rw [decides_append ft l₂ l₁ s', List.drop_drop, List.drop_drop]

theorem yields_length : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (ps : List Played), Yields ss ds back ps → ps.length = ss.length := by
  intro ss
  induction ss with
  | nil =>
    intro ds back ps h
    cases ds <;> cases ps <;> first | rfl | simp [Yields] at h
  | cons s ss ih =>
    intro ds back ps h
    cases ds with
    | nil => simp [Yields] at h
    | cons d ds =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        simp only [Yields] at h
        rw [List.length_cons, List.length_cons, ih ds back.tail ps h.2]

theorem play_cut {l₁ l₂ l₃ : List (Step W X)} {ds : List Fmt.Drawn} {m : Mid W X}
    {y : List Played × Mid W X} (h : play (l₁ ++ l₂ ++ l₃) ds [] m = .ok y) :
    ∃ y₁ y₂ y₃, play l₁ (ds.take l₁.length) [] m = .ok y₁ ∧
      play l₂ ((ds.drop l₁.length).take l₂.length) [] y₁.2 = .ok y₂ ∧
      play l₃ (ds.drop (l₁.length + l₂.length)) [] y₂.2 = .ok y₃ ∧
      y = (y₁.1 ++ y₂.1 ++ y₃.1, y₃.2) := by
  have hlen : ds.length = (l₁ ++ l₂ ++ l₃).length := by
    have h1 := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ h)
    have h2 := yields_length _ _ _ _ (play_yields _ _ _ _ _ h)
    rw [← h1, List.length_map, roundsOf, List.length_map, h2]
  rw [List.length_append, List.length_append] at hlen
  have e1 : ds = ds.take l₁.length ++ ((ds.drop l₁.length).take l₂.length ++
      ds.drop (l₁.length + l₂.length)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  rw [List.append_assoc, e1, play_append _ _ _ _ _ _ (by rw [List.length_take]; omega)] at h
  obtain ⟨y₁, h1, h⟩ := exBind_ok h
  obtain ⟨z, hz, h⟩ := exMap_ok h
  rw [List.drop_nil, play_append _ _ _ _ _ _ (by
    rw [List.length_take, List.length_drop]; omega)] at hz
  obtain ⟨y₂, h2, hz⟩ := exBind_ok hz
  obtain ⟨y₃, h3, hz⟩ := exMap_ok hz
  rw [List.drop_nil] at h3
  refine ⟨y₁, y₂, y₃, h1, h2, h3, ?_⟩
  rw [← h, ← hz, List.append_assoc]

/-! ## 2 One sub-protocol's book-keeping -/

/-- **The two tests of `Block.step` on form** (`Block.Fits`, Johnson/Top/H0/StepLaws/StepLaws.lean)
hold at a prover's side's played rounds and the filled columns; these columns are exactly as many as
are wanted; and what `decide` is shown of them is all of them, in groups. -/
theorem fits_played {g : Placed V W X} {b : Block S Cl} {v : Option V} {c : RowCoins g.parts}
    {ds : List Fmt.Drawn} {m : Mid W X} {y : List Played × Mid W X} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {cols : List OpenedColumn}
    (hr : g.rounds = b.rounds.length) (ho : b.oracles.length = b.rounds.length)
    (hy : play (g.steps b v c) ds [] m = .ok y) (hd : drawsFit b.rounds ds = true)
    (hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols) :
    b.Fits ft (roundsOf y.1) cols ∧ (b.want ft (roundsOf y.1)).length = cols.length ∧
      b.shown ft (roundsOf y.1) cols =
        regroup ((groupsOf ft b.rounds ds).map (·.length)) cols := by
  have hq := Placed.steps_rows g b v c hr ho
  have hdecl : (g.steps b v c).map (·.decl) = b.rounds := by
    have h1 := congrArg (List.map (·.1)) hq
    rw [List.map_map, List.map_map] at h1
    exact h1.trans ((map_zip_fst (fun (d : Fmt.DeclaredRound) => d) b.rounds b.oracles
      (Nat.le_of_eq ho.symm)).trans (List.map_id' _))
  have hmv : ∀ t ∈ g.steps b v c, t.move.isSome = true := by
    intro t ht
    have h1 : (t.decl, t.oracles, t.addr.place, t.move.isSome) ∈ (g.steps b v c).map
        (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
      List.mem_map.2 ⟨t, ht, rfl⟩
    rw [hq] at h1
    obtain ⟨z, _, hz⟩ := List.mem_map.1 h1
    exact (congrArg (·.2.2.2) hz).symm
  have hi : itemsFall (g.steps b v c) [] = true := by
    rw [itemsFall_nil, List.all_eq_true]
    intro t ht
    rw [hmv t ht]
    rfl
  have hk := chain_kept hdecl hy (drawsFit_bare _ _ hd) hi hc
  obtain ⟨k1, k2⟩ := (kept_iff _ _ _ _).1 hk
  have hdr : (roundsOf y.1).map (·.drawn) = ds :=
    yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  rw [hdr] at k2
  have hlen : ((groupsOf ft b.rounds ds).flatMap id).length = cols.length := by
    rw [← k2, List.length_map]
  have hwant : b.want ft (roundsOf y.1) = (groupsOf ft b.rounds ds).flatMap id := by
    unfold Block.want
    rw [hdr]
  refine ⟨⟨k1, ?_⟩, ?_, ?_⟩
  · rw [hwant, hlen, List.take_length, k2]
    exact beq_self_eq_true _
  · rw [hwant, hlen]
  · unfold Block.shown
    rw [hwant, hdr, hlen, List.take_length]

/-- One sub-protocol's book-keeping, in the very terms of `Good.acc`: its hypotheses on `play`, on
`fillCols` and on the challenges, and two of the three clauses of `Side.fits`. -/
theorem step_iff_decide {g : Placed V W X} {b : Block S Cl} {v : Option V} {c : RowCoins g.parts}
    {ds : List Fmt.Drawn} {m : Mid W X} {y : List Played × Mid W X} {chain ft : Nat}
    {stored : Nat → Nat → Option (List UInt64)} {tree : Fmt.TreeSource → Option (Place × Table)}
    {cols : List OpenedColumn} (s s' : S)
    (hr : g.rounds = b.rounds.length) (ho : b.oracles.length = b.rounds.length)
    (hy : play (g.steps b v c) ds [] m = .ok y) (hd : drawsFit b.rounds ds = true)
    (hc : fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok cols) :
    b.step ft s (roundsOf y.1) cols = .ok (s', cols.length) ↔
      b.decide s ((roundsOf y.1).map noDigest)
        (regroup ((groupsOf ft b.rounds ds).map (·.length)) cols) = .ok s' := by
  obtain ⟨hf, hl, hsh⟩ := fits_played hr ho hy hd hc
  rw [step_iff, hsh]
  exact ⟨fun h => h.2.1, fun h => ⟨hf, h, hl.symm⟩⟩

/-! ## 3 The available tables, at a real run -/

/-- The available tables of Honest/Side.lean (`Env`), at a real run: after played rounds. `taken`:
the look-up of a tree that is taken over from an earlier chain. -/
def envOf (stored : Nat → Nat → Option (List UInt64)) (taken : Nat → Nat → Option (Place × Table))
    (ps : List Played) : Env :=
  ⟨stored, (fun s => match s with
      | .own n => ((tablesOf ps)[n]?).bind id
      | .taken ch k => taken ch k),
    (tablesOf ps).length⟩

theorem tablesOf_append (ps qs : List Played) :
    tablesOf (ps ++ qs) = tablesOf ps ++ tablesOf qs := by
  unfold tablesOf
  rw [List.flatMap_append]

theorem envOf_add (stored : Nat → Nat → Option (List UInt64))
    (taken : Nat → Nat → Option (Place × Table)) (ps qs : List Played) :
    (envOf stored taken ps).add qs = envOf stored taken (ps ++ qs) := by
  have ht : ((envOf stored taken ps).add qs).tree = (envOf stored taken (ps ++ qs)).tree := by
    funext s
    cases s with
    | own n =>
      show (if n < (tablesOf ps).length then ((tablesOf ps)[n]?).bind id
        else ((tablesOf qs)[n - (tablesOf ps).length]?).bind id) =
          ((tablesOf (ps ++ qs))[n]?).bind id
      rw [tablesOf_append]
      by_cases h : n < (tablesOf ps).length
      · rw [if_pos h, List.getElem?_append_left h]
      · rw [if_neg h, List.getElem?_append_right (Nat.le_of_not_lt h)]
    | taken ch k => rfl
  have hn : ((envOf stored taken ps).add qs).sent = (envOf stored taken (ps ++ qs)).sent := by
    show (tablesOf ps).length + (tablesOf qs).length = (tablesOf (ps ++ qs)).length
    rw [tablesOf_append, List.length_append]
  have hst : ((envOf stored taken ps).add qs).stored = (envOf stored taken (ps ++ qs)).stored := rfl
  cases h1 : (envOf stored taken ps).add qs
  cases h2 : envOf stored taken (ps ++ qs)
  rw [h1, h2] at ht hn hst
  simp only at ht hn hst
  rw [ht, hn, hst]

theorem envOf_prefix (stored : Nat → Nat → Option (List UInt64))
    (taken : Nat → Nat → Option (Place × Table)) (ps qs : List Played) (s : Fmt.TreeSource)
    (pt : Place × Table) (h : (envOf stored taken ps).tree s = some pt) :
    (envOf stored taken (ps ++ qs)).tree s = some pt := by
  cases s with
  | own n =>
    have h' : ((tablesOf ps)[n]?).bind id = some pt := h
    show ((tablesOf (ps ++ qs))[n]?).bind id = some pt
    rw [tablesOf_append]
    by_cases hn : n < (tablesOf ps).length
    · rw [List.getElem?_append_left hn]
      exact h'
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h'
      cases h'
  | taken ch k => exact h

theorem envOf_tree (stored : Nat → Nat → Option (List UInt64)) (l₁ l₂ l₃ : List Played) :
    (envOf stored (fun _ _ => none) l₁).tree = treeOwn l₁ ∧
    (envOf stored (fun ch k => if ch == 0 then ((tablesOf l₁)[k]?).bind id
      else if ch == 1 then ((tablesOf l₂)[k]?).bind id else none) l₃).tree =
      treeThird l₁ l₂ l₃ := by
  constructor
  · funext s
    cases s <;> rfl
  · funext s
    cases s <;> rfl

theorem fillCols_mono {chain ft : Nat} {stored : Nat → Nat → Option (List UInt64)}
    {tree tree' : Fmt.TreeSource → Option (Place × Table)}
    (h : ∀ s pt, tree s = some pt → tree' s = some pt) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (cols : List OpenedColumn),
    fillCols (readsOf chain ft stored tree ds Rs) [] = .ok cols →
    fillCols (readsOf chain ft stored tree' ds Rs) [] = .ok cols := by
  intro ds Rs cols hc
  have key : ∀ (q q' : List Read) (c : List OpenedColumn),
      List.Forall₂ (fun (a a' : Read) => a.key = a'.key ∧ a.pos = a'.pos ∧ a.width = a'.width ∧
        ∀ u, a.words = some u → a'.words = some u) q q' →
      fillCols q [] = .ok c → fillCols q' [] = .ok c := by
    intro q q' c hF
    induction hF generalizing c with
    | nil => exact id
    | @cons a a' q q' h1 _ ih =>
      intro hq
      obtain ⟨e1, e2, e3, e4⟩ := h1
      cases hw : a.words with
      | none => simp [fillCols, hw] at hq
      | some u =>
        simp only [fillCols, hw, List.tail_nil] at hq
        simp only [fillCols, e4 u hw, List.tail_nil, ← e1, ← e2, ← e3]
        split at hq
        · cases hq
        rename_i hl
        rw [if_neg hl]
        obtain ⟨l, hl1, hl2⟩ := exMap_ok hq
        rw [ih l hl1]
        exact congrArg Except.ok hl2
  refine key _ _ cols ?_ hc
  clear hc key
  induction ds generalizing Rs with
  | nil => simp [readsOf]
  | cons d ds ih =>
    cases Rs with
    | nil => simp [readsOf]
    | cons R Rs =>
      simp only [readsOf]
      refine List.rel_append (List.rel_append ?_ ?_) (ih Rs)
      · exact List.forall₂_same.2 fun a _ => ⟨rfl, rfl, rfl, fun u hu => hu⟩
      · induction d.opens with
        | nil => exact .nil
        | cons o os iho =>
          rw [List.flatMap_cons, List.flatMap_cons]
          refine List.rel_append ?_ iho
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          refine List.forall₂_same.2 fun x _ => ⟨rfl, rfl, rfl, fun u hu => ?_⟩
          obtain ⟨pt, hpt, hu'⟩ := Option.map_eq_some_iff.1 hu
          show (tree' o.2).map (·.2.col x) = some u
          rw [h _ _ hpt]
          exact congrArg some hu'

end ProofFile.Honest

#print axioms ProofFile.Honest.chainSteps_append
#print axioms ProofFile.Honest.drawsFit_append
#print axioms ProofFile.Honest.readsOf_append
#print axioms ProofFile.Honest.fillCols_append
#print axioms ProofFile.Honest.decides_append
#print axioms ProofFile.Honest.yields_length
#print axioms ProofFile.Honest.play_cut
#print axioms ProofFile.Honest.fits_played
#print axioms ProofFile.Honest.step_iff_decide
#print axioms ProofFile.Honest.tablesOf_append
#print axioms ProofFile.Honest.envOf_add
#print axioms ProofFile.Honest.envOf_prefix
#print axioms ProofFile.Honest.envOf_tree
#print axioms ProofFile.Honest.fillCols_mono
