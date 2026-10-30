-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TableOfRun.lean: THE TIE OF A
TREE's TEXT TO A RUN, over the whole of a half's play: where the frame lends the half's coins and
play of the half returns, the entry of tablesOf y.1 at tree τ, counted over every round, is testTbl's
pair: its place and its table.


  cntSome, depths_at, depthAt_seed, cnt_seed   by depths' text: at seedRound τ the depth is the next
                 stage's C.a, and τ tables (τ + 1 where the first fold sends its own) stand in front.
                 So ha of ScriptLotsTie.lean is a theorem, general in J
  flatTo, flatTo_len, flatTo_at   a round's tables in the list of all of them
  row_place, play_place_all, tablesOf_at   every round of a half's play stands at the half's place
                 (after KeyFreshTrial 8595bc8d, part_place, row_place, play_place)
  half_tables    y.1.map (·.tables) whole: msgAt's at every round, at that round's coins: no Agree
  lendRow_second, lendPart_cross, handedRest_of_row   the frame's lending to the second part, at the chain's V, is
                 handedRest's, at Empty: ScriptLots.lean:142–143 crossed
  first_le_seed, seed_lt   the sending round stands in the second part, and inside the rounds
  take_front, draws_agree, seed_text   h against what is heard
  table_in_run   THE TIE

This is a tie of a text to a run. Beside
it stand RowsOfHeard and tables_at_frontAt (TablesAtFront.lean).
THE BOOK's FACT DOES NOT ENTER THE LEAN HERE: hc is a premise that the frame
lends, not that fact. So this tie says nothing of that fact.

A YES WOULD NOT SHOW: hT (TreesOfThr.lean takes that step) · that the road by the tests' tables has
survived a test: a yes is in great part the kernel's stamp on had laws; what is new here is the count
over depths and the flatten · that hc and hplay are met at the key's book or at any run there: hplay
is met nowhere there; at TieAtSmall.lean's plan the evaluator plays ready's steps filtered by place
and evaluates lendPart at part 1, which is not lendRow = .ok c nor rowSteps at c in their forms, and
reads one round's first table: so the index over all rounds has no evaluator's control anywhere ·
anything at O behind the guard:
proverSideOfTestOnOmega's parts are guarded, so this law does not apply to them as it stands · any ok but the constant
yes: where ok says no and the run plays the tie would be false · a round's vals, widths, Sending.fits
· a message's or a pad's text · that runC's walk plays a block from such an m · anything over coins,
and nothing on hiding. It is a law on what play shows, pointwise.

Limits.
- What ScriptLots.lean's head says a law over coins has to mind holds here.
- Round 1 at J.fresh = none, own 7's, is not here (OwnTbl.lean): the term if J.fresh.isNone … in the
  index only moves the count over it.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TablesAtFront
import Johnson.Desc.ProofFile.Honest.K12.PlayedTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {V W X : Type}

/-! ## 1 The count over depths -/

/-- How many entries of a list are some. -/
def cntSome {α : Type} (l : List (Option α)) : ℕ := (l.filter (·.isSome)).length

theorem cntSome_append {α : Type} (a b : List (Option α)) :
    cntSome (a ++ b) = cntSome a + cntSome b := by
  unfold cntSome
  rw [List.filter_append, List.length_append]

theorem cntSome_replicate {α : Type} (k : ℕ) : cntSome (List.replicate k (none : Option α)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show cntSome (none :: List.replicate k (none : Option α)) = 0
    exact ih

theorem cntSome_head {α : Type} (own : Bool) (x : α) (k : ℕ) :
    cntSome ((if own then some x else none) :: List.replicate k none) = if own then 1 else 0 := by
  cases own
  · show cntSome (List.replicate k (none : Option α)) = 0
    exact cntSome_replicate k
  · show cntSome (List.replicate k (none : Option α)) + 1 = 1
    rw [cntSome_replicate]

/-- A list's front with its length and more. -/
theorem take_pre {α : Type} (l₁ l₂ : List α) (i : ℕ) :
    (l₁ ++ l₂).take (l₁.length + i) = l₁ ++ l₂.take i := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    have e : (a :: t).length + i = (t.length + i) + 1 := by
      rw [List.length_cons]
      omega
    rw [e, List.cons_append, List.take_succ_cons, ih, List.cons_append]

/-- The position in depths of the sending round of tree τ. -/
def posOf (st : List Fmt.M1.Stage) (τ : ℕ) : ℕ :=
  ((st.take τ).map (·.k + 3)).sum + 1 + (st.getD τ default).k

theorem seedRound_eq (st : List Fmt.M1.Stage) (τ : ℕ) : seedRound st τ = posOf st τ + 1 := by
  unfold seedRound roundOf posOf
  omega

theorem posOf_zero (s : Fmt.M1.Stage) (t : List Fmt.M1.Stage) : posOf (s :: t) 0 = 1 + s.k := rfl

theorem posOf_succ (s : Fmt.M1.Stage) (t : List Fmt.M1.Stage) (τ : ℕ) :
    posOf (s :: t) (τ + 1) = s.k + 3 + posOf t τ := by
  simp only [posOf, List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ]
  omega

theorem depths_cons (own : Bool) (s n : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    depths own (s :: n :: rest) =
      ((if own then some s.Z.a else none) :: List.replicate s.k none) ++ [some n.C.a, none] ++
        depths false (n :: rest) := rfl

/-- **At the position of tree τ's sending round depths names the next stage's tree, and τ tables
stand in front of it, one more where the first fold sends its own.** -/
theorem depths_at (τ : ℕ) : ∀ (st : List Fmt.M1.Stage) (own : Bool), τ + 1 < st.length →
    (depths own st)[posOf st τ]? = some (some (st.getD (τ + 1) default).C.a) ∧
      cntSome ((depths own st).take (posOf st τ)) = τ + (if own then 1 else 0) := by
  induction τ with
  | zero =>
    intro st own h
    cases st with
    | nil =>
      have e : ([] : List Fmt.M1.Stage).length = 0 := rfl
      omega
    | cons s t =>
      cases t with
      | nil =>
        have e : ([s] : List Fmt.M1.Stage).length = 1 := rfl
        omega
      | cons n rest =>
        have el : ((if own then some s.Z.a else none) :: List.replicate s.k none).length =
            1 + s.k := by
          rw [List.length_cons, List.length_replicate]
          omega
        rw [posOf_zero, ← el, depths_cons, List.append_assoc]
        refine ⟨?_, ?_⟩
        · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        · rw [List.take_left' rfl, cntSome_head, Nat.zero_add]
  | succ τ ih =>
    intro st own h
    cases st with
    | nil =>
      have e : ([] : List Fmt.M1.Stage).length = 0 := rfl
      omega
    | cons s t =>
      cases t with
      | nil =>
        have e : ([s] : List Fmt.M1.Stage).length = 1 := rfl
        omega
      | cons n rest =>
        have h' : τ + 1 < (n :: rest).length := by
          have e : (s :: n :: rest).length = (n :: rest).length + 1 := rfl
          omega
        obtain ⟨i1, i2⟩ := ih (n :: rest) false h'
        have i2' : cntSome ((depths false (n :: rest)).take (posOf (n :: rest) τ)) = τ := by
          simpa using i2
        have el : (((if own then some s.Z.a else none) :: List.replicate s.k none) ++
            [some n.C.a, none]).length = s.k + 3 := by
          rw [List.length_append, List.length_cons, List.length_replicate]
          rfl
        rw [posOf_succ, ← el, depths_cons]
        refine ⟨?_, ?_⟩
        · rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, i1]
          rfl
        · rw [take_pre, cntSome_append, cntSome_append, cntSome_head, i2']
          have e : cntSome ([some n.C.a, none] : List (Option ℕ)) = 1 := rfl
          rw [e]
          omega

/-- **ha, general in J**: depthAt at a switch's sending round is the next stage's first depth. -/
theorem depthAt_seed (J : TestJob W X) {τ : ℕ} (hτ : τ + 1 < J.p.nums.stages.length) :
    depthAt J (seedRound J.p.nums.stages τ) =
      some (J.p.nums.stages.getD (τ + 1) default).C.a := by
  have h := (depths_at τ J.p.nums.stages J.fresh.isNone hτ).1
  unfold depthAt
  rw [seedRound_eq, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, h]
  try rfl

theorem cnt_seed (own : Bool) (st : List Fmt.M1.Stage) {τ : ℕ} (hτ : τ + 1 < st.length) :
    cntSome ((none :: depths own st).take (seedRound st τ)) = τ + (if own then 1 else 0) := by
  rw [seedRound_eq, List.take_succ_cons]
  exact (depths_at τ st own hτ).2

/-! ## 2 A round's tables among all of them -/

/-- The lists of the rounds below r, one after another. -/
def flatTo {β : Type} (B : ℕ → List β) (r : ℕ) : List β := ((List.range r).map B).flatten

theorem flatTo_succ {β : Type} (B : ℕ → List β) (r : ℕ) :
    flatTo B (r + 1) = flatTo B r ++ B r := by
  simp [flatTo, List.range_succ]

theorem flatTo_len {α β : Type} (B : ℕ → List β) (P : List (Option α))
    (hB : ∀ i, (B i).length = (P.getD i none).toList.length) (r : ℕ) :
    (flatTo B r).length = cntSome (P.take r) := by
  induction r with
  | zero => simp [flatTo, cntSome]
  | succ r ih =>
    rw [flatTo_succ, List.length_append, ih, hB, List.take_add_one, cntSome_append,
      List.getD_eq_getElem?_getD]
    cases P[r]? with
    | none => rfl
    | some x => cases x <;> rfl

theorem flatTo_at {β : Type} (B : ℕ → List β) {r : ℕ} {x : β} (hx : B r = [x]) (d : ℕ) :
    (flatTo B (r + 1 + d))[(flatTo B r).length]? = some x := by
  induction d with
  | zero =>
    rw [Nat.add_zero, flatTo_succ, hx, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  | succ d ih =>
    have hlt : (flatTo B r).length < (flatTo B (r + 1 + d)).length := by
      rcases Nat.lt_or_ge (flatTo B r).length (flatTo B (r + 1 + d)).length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at ih
        cases ih
    rw [show r + 1 + (d + 1) = (r + 1 + d) + 1 from rfl, flatTo_succ,
      List.getElem?_append_left hlt]
    exact ih

/-! ## 3 The place -/

theorem part_place (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)) (v : Option V) (c : p.Coins) :
    ∀ s ∈ p.steps name a rs v c, s.addr = a := by
  intro s hs
  unfold Part.steps at hs
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs
  rfl

theorem row_place (name : String) (a : VerifiableInference.Desc.Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : ℕ) (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)) (c : RowCoins ps),
      ∀ s ∈ rowSteps name a v ps j rs c, s.addr.place = a
  | [], _, _, _ => fun _ hs => by cases hs
  | p :: ps, j, rs, c => fun s hs => by
    rcases List.mem_append.1 hs with h | h
    · rw [part_place p name ⟨a, j⟩ _ v c.1 s h]
    · exact row_place name a v ps (j + 1) _ c.2 s h

/-- Every round played stands at the place of the steps, where all the steps stand at one. -/
theorem play_place_all (a : VerifiableInference.Desc.Place) : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X),
    (∀ s ∈ ss, s.addr.place = a) → play ss ds back m = .ok y → ∀ p ∈ y.1, p.place = a
  | [], [], _, m, y, _, h => by
    simp only [play] at h
    cases h
    intro p hp
    cases hp
  | [], _ :: _, _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, _, h => by simp [play] at h
  | s :: ss, d :: ds, back, m, y, hs, h => by
    obtain ⟨x, m', z, -, -, hz, rfl⟩ := play_cons_ok h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hs s List.mem_cons_self
    · exact play_place_all a ss ds back.tail m' z
        (fun t ht => hs t (List.mem_cons_of_mem _ ht)) hz p hp

/-- Where every round stands at one place, the run's tables are the rounds' tables at that place. -/
theorem tablesOf_at (a : VerifiableInference.Desc.Place) : ∀ ps : List Played, (∀ p ∈ ps, p.place = a) →
    tablesOf ps = ((ps.map (·.tables)).flatten).map (Option.map fun x => (a, x))
  | [], _ => rfl
  | p :: ps, h => by
    have ih := tablesOf_at a ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    unfold tablesOf at ih ⊢
    rw [List.flatMap_cons, ih, hp, List.map_cons, List.flatten_cons, List.map_append]
    try rfl

/-! ## 4 The half's play, whole -/

theorem tables_length (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ) : (msgAt J w fr C D i).tables.length = (depthAt J i).toList.length := by
  unfold msgAt
  simp only [List.length_map]

/-- **What the play makes of the half, whole**: at every round that round's message, at that round's
coins, at the front at which the play began. No Agree. -/
theorem half_tables (J : TestJob W X) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (name : String) (v : Option V)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle))
    (hrs : rs.length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X)
    (hplay : play (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 rs c) ds
      back m = .ok y) :
    y.1.map (·.tables) = (List.range rs.length).map (fun i =>
        (msgAt J m.st.input (frontOf m) (coinsAtRound J c i) (byNo ds) i).tables.map some) ∧
      y.2.st = { m.st with heard := m.st.heard ++ ds } := by
  obtain ⟨hl, hm⟩ := half_steps J s t rest hst name v rs hrs c
  obtain ⟨p1, p2, -, -⟩ := play_test J (coinsAtRound J c) (byNo ds) _ 0 ds back m y
    (fun i h => by rw [Nat.zero_add]; exact hm i h) hplay
    ⟨Nat.zero_le _, Nat.zero_le _, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
    (fun n h => by
      rw [Nat.zero_add]
      unfold byNo
      rw [List.getD_eq_getElem _ _ h])
  rw [hl, frontBy_zero] at p1
  refine ⟨?_, p2⟩
  have e : y.1.map (·.tables) = (y.1.map shownOf).map fun x => x.2.1 := by
    rw [List.map_map]
    rfl
  rw [e, p1, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show (msgAt J m.st.input (frontOf m) (coinsAtRound J c (0 + i)) (byNo ds) (0 + i)).tables.map
    some = _
  rw [Nat.zero_add]

/-! ## 5 The lending -/

/-- Of a row of two parts the second's coins are lendPart's at number 1. -/
theorem lendRow_second {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {a : VerifiableInference.Desc.Place} {p q : Part V W X} {c : RowCoins [p, q]}
    (h : lendRow B rows look a [p, q] 0 = .ok c) : lendPart B rows look ⟨a, 1⟩ q = .ok c.2.1 := by
  simp only [lendRow, Nat.zero_add] at h
  cases h0 : lendPart B rows look ⟨a, 0⟩ p with
  | error e =>
    rw [h0] at h
    cases h
  | ok c₁ =>
    rw [h0] at h
    cases h1 : lendPart B rows look ⟨a, 1⟩ q with
    | error e =>
      rw [h1] at h
      cases h
    | ok c₂ =>
      rw [h1] at h
      have e : c = (c₁, c₂, ()) := (Except.ok.inj h).symm
      subst e
      rfl

/-- lendPart reads no stop and no move: at two parts of one count it is one, whatever V. After
FieldGuardLift.lean's lendPart_guarded. -/
theorem lendPart_cross {V' : Type} (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Addr) (p : Part V W X) (q : Part V' W X)
    (ht : p.takes = q.takes) (hs : p.spends = q.spends) (hc : p.carries = q.carries) :
    HEq (lendPart B rows look a p) (lendPart B rows look a q) := by
  cases p with
  | mk t s c b h o1 o2 m =>
    cases q with
    | mk t' s' c' b' h' o1' o2' m' =>
      obtain rfl : t = t' := ht
      obtain rfl : s = s' := hs
      obtain rfl : c = c' := hc
      dsimp only [lendPart]
      by_cases hd : (t != dueAt rows a) = true
      · simp only [if_pos hd]
        exact HEq.rfl
      · simp only [if_neg hd]
        cases (look a).2.cut ⟨0, 0⟩ t with
        | none => exact HEq.rfl
        | some own => exact HEq.rfl

/-- **The frame's lending to the second part, at the chain's V, is handedRest's, at Empty.** -/
theorem handedRest_of_row {Bk : ProverCoinCounts} (ch : ℕ) (J : TestJob W X) (k : Coins Bk)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (hc : lendRow Bk (Bk.rowsOf ch) (k.look ch) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c) :
    handedRest ch J k = some c.2.1 := by
  have e := lendRow_second hc
  have e2 : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨J.p.place, 1⟩ (restPart (V := Empty) J) =
      lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨J.p.place, 1⟩ (restPart (V := V) J) :=
    eq_of_heq (lendPart_cross _ _ _ _ _ _ rfl rfl rfl)
  unfold handedRest
  rw [e2, e]
  rfl

/-! ## 6 Counts -/

theorem first_le_seed (st : List Fmt.M1.Stage) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : st = s :: t :: rest) (τ : ℕ) : firstLen st ≤ seedRound st τ := by
  subst hst
  have e : firstLen (s :: t :: rest) = 2 + s.k := rfl
  rw [e, seedRound_eq]
  cases τ with
  | zero =>
    rw [posOf_zero]
    omega
  | succ τ =>
    rw [posOf_succ]
    omega

theorem roundOf_le (st : List Fmt.M1.Stage) (τ : ℕ) :
    ∀ d, τ + d < st.length → roundOf st τ ≤ roundOf st (τ + d) := by
  intro d
  induction d with
  | zero => intro _; exact Nat.le_refl _
  | succ d ih =>
    intro h
    have e := roundOf_succ st (τ + d) (by omega)
    have i := ih (by omega)
    rw [show τ + (d + 1) = τ + d + 1 from rfl, e]
    omega

theorem seed_lt (st : List Fmt.M1.Stage) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : st = s :: t :: rest) {τ : ℕ} (hτ : τ + 1 < st.length) :
    seedRound st τ < firstLen st + restLen st := by
  have e0 : seedRound st τ = roundOf st τ + 1 + (st.getD τ default).k := rfl
  have e1 := roundOf_succ st τ (by omega)
  have e2 := roundOf_le st (τ + 1) (st.length - 1 - (τ + 1)) (by omega)
  rw [show τ + 1 + (st.length - 1 - (τ + 1)) = st.length - 1 by omega] at e2
  have e3 := first_le_seed st s t rest hst τ
  show _ < firstLen st + (roundOf st (st.length - 1) + 2 - firstLen st)
  omega

/-! ## 7 The tie -/

theorem take_front {α : Type} {l₁ l₂ h : List α} {n₀ r : ℕ} (hn : l₁.length = n₀)
    (hh : h.take (n₀ + r) = (l₁ ++ l₂).take (n₀ + r)) : h.take n₀ = l₁ := by
  have e := congrArg (List.take n₀) hh
  rw [List.take_take, List.take_take] at e
  have h1 : min n₀ (n₀ + r) = n₀ := by omega
  rw [h1] at e
  rw [e]
  exact List.take_left' hn

theorem draws_agree {l₁ l₂ h : List Fmt.Drawn} {n₀ r : ℕ} (hn : l₁.length = n₀)
    (hh : h.take (n₀ + r) = (l₁ ++ l₂).take (n₀ + r)) {i : ℕ} (hi : i < r) :
    byNo l₂ i = testDrawsAt n₀ h i := by
  have a : n₀ + i < n₀ + r := by omega
  have e : (h.take (n₀ + r))[n₀ + i]? = ((l₁ ++ l₂).take (n₀ + r))[n₀ + i]? := by rw [hh]
  rw [List.getElem?_take, List.getElem?_take, if_pos a, if_pos a, ← hn,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at e
  unfold byNo testDrawsAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← hn, e]

/-- **The message at the play's front holds the one table of the text.** -/
theorem seed_text {Bk : ProverCoinCounts} (J : TestJob W X) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k) (ch : ℕ) (k : Coins Bk)
    (c₂ : (restPart (V := Empty) J).Coins) (hc₂ : handedRest ch J k = some c₂)
    (ds : List Fmt.Drawn) (m : Mid W X) (own₀ : X) (n₀ : ℕ) (hn : m.st.heard.length = n₀)
    {τ : ℕ} (hτ : τ + 1 < J.p.nums.stages.length) (h : List Fmt.Drawn)
    (hh : h.take (n₀ + seedRound J.p.nums.stages τ) =
      (m.st.heard ++ ds).take (n₀ + seedRound J.p.nums.stages τ)) :
    ∃ T : ProofFile.Honest.Table,
      (msgAt J m.st.input (frontOf m) (restCoins J c₂) (byNo ds)
        (seedRound J.p.nums.stages τ)).tables = [T] ∧
      testTbl ch J own₀ n₀ (fun _ _ _ => true) τ k m.st.input h = (J.p.place, T) := by
  have hfr : (frontOf m).heard = h.take n₀ := (take_front hn hh).symm
  obtain ⟨T, -, h1, h2⟩ := tables_at_frontAt J hR hk m.st.input own₀ n₀ h (frontOf m) hfr
    (restCoins J c₂) (byNo ds) hτ (depthAt_seed J hτ)
  have h3 : msgAt J m.st.input (frontAt own₀ n₀ h) (restCoins J c₂) (testDrawsAt n₀ h)
      (seedRound J.p.nums.stages τ) = msgAt J m.st.input (frontAt own₀ n₀ h) (restCoins J c₂)
      (byNo ds) (seedRound J.p.nums.stages τ) :=
    msgAt_causal J _ _ _ _ _ _ fun i hi => (draws_agree hn hh hi).symm
  refine ⟨T, h1, ?_⟩
  unfold testTbl
  simp only [hc₂, ↓reduceIte]
  rw [h3, h2]
  rfl

/-- **THE TIE.** Where the frame lends the half's coins and play of the half returns, the entry of
tablesOf y.1 at tree τ, counted over every round, is testTbl's pair. At every m whose heard has
length n₀, at every h that agrees with what is heard up to the sending round.
NOT IN FRONT OF A LAW OVER COINS: it ties a table to a run's coins. -/
theorem table_in_run {Bk : ProverCoinCounts} (J : TestJob W X) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (name : String) (v : Option V) (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle))
    (hrs : rs.length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (ch : ℕ) (k : Coins Bk) (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (hc : lendRow Bk (Bk.rowsOf ch) (k.look ch) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c)
    (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X)
    (hplay : play (rowSteps name J.p.place v [(firstPart J : Part V W X), restPart J] 0 rs c)
      ds back m = .ok y)
    (own₀ : X) (n₀ : ℕ) (hn : m.st.heard.length = n₀)
    {τ : ℕ} (hτ : τ + 1 < J.p.nums.stages.length) (h : List Fmt.Drawn)
    (hh : h.take (n₀ + seedRound J.p.nums.stages τ) =
      (m.st.heard ++ ds).take (n₀ + seedRound J.p.nums.stages τ)) :
    (tablesOf y.1)[τ + (if J.fresh.isNone then 1 else 0)]? =
      some (some (testTbl ch J own₀ n₀ (fun _ _ _ => true) τ k m.st.input h)) := by
  have hlt := seed_lt _ s t rest hst hτ
  have hge := first_le_seed _ s t rest hst τ
  obtain ⟨hT, -⟩ := half_tables J s t rest hst name v rs hrs c ds back m y hplay
  have hpl : ∀ p ∈ y.1, p.place = J.p.place :=
    play_place_all J.p.place _ ds back m y (row_place name J.p.place v _ 0 rs c) hplay
  obtain ⟨T, hTab, hText⟩ := seed_text J hR hk ch k c.2.1 (handedRest_of_row ch J k c hc) ds m own₀
    n₀ hn hτ h hh
  let B : ℕ → List (Option ProofFile.Honest.Table) := fun i =>
    (msgAt J m.st.input (frontOf m) (coinsAtRound J c i) (byNo ds) i).tables.map some
  have hlen : ∀ i, (B i).length =
      ((none :: depths J.fresh.isNone J.p.nums.stages).getD i none).toList.length := by
    intro i
    show ((msgAt J m.st.input (frontOf m) (coinsAtRound J c i) (byNo ds) i).tables.map some).length
      = _
    rw [List.length_map, tables_length]
    rfl
  have hco : coinsAtRound J c (seedRound J.p.nums.stages τ) = restCoins J c.2.1 := by
    unfold coinsAtRound
    rw [if_neg (by omega)]
  have hBr : B (seedRound J.p.nums.stages τ) = [some T] := by
    show (msgAt J m.st.input (frontOf m) (coinsAtRound J c (seedRound J.p.nums.stages τ)) (byNo ds)
      (seedRound J.p.nums.stages τ)).tables.map some = _
    rw [hco, hTab]
    rfl
  have hcnt : (flatTo B (seedRound J.p.nums.stages τ)).length =
      τ + (if J.fresh.isNone then 1 else 0) := by
    rw [flatTo_len B _ hlen, cnt_seed _ _ hτ]
  have hat := flatTo_at B hBr (rs.length - (seedRound J.p.nums.stages τ + 1))
  rw [show seedRound J.p.nums.stages τ + 1 + (rs.length - (seedRound J.p.nums.stages τ + 1)) =
    rs.length by omega, hcnt] at hat
  have htab : tablesOf y.1 = (flatTo B rs.length).map (Option.map fun x => (J.p.place, x)) := by
    rw [tablesOf_at _ _ hpl, hT]
    rfl
  rw [htab, List.getElem?_map, hat, hText]
  rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.cntSome
#print axioms ProofFile.Honest.K12.cntSome_append
#print axioms ProofFile.Honest.K12.cntSome_replicate
#print axioms ProofFile.Honest.K12.cntSome_head
#print axioms ProofFile.Honest.K12.take_pre
#print axioms ProofFile.Honest.K12.posOf
#print axioms ProofFile.Honest.K12.seedRound_eq
#print axioms ProofFile.Honest.K12.posOf_zero
#print axioms ProofFile.Honest.K12.posOf_succ
#print axioms ProofFile.Honest.K12.depths_cons
#print axioms ProofFile.Honest.K12.depths_at
#print axioms ProofFile.Honest.K12.depthAt_seed
#print axioms ProofFile.Honest.K12.cnt_seed
#print axioms ProofFile.Honest.K12.flatTo
#print axioms ProofFile.Honest.K12.flatTo_succ
#print axioms ProofFile.Honest.K12.flatTo_len
#print axioms ProofFile.Honest.K12.flatTo_at
#print axioms ProofFile.Honest.K12.part_place
#print axioms ProofFile.Honest.K12.row_place
#print axioms ProofFile.Honest.K12.play_place_all
#print axioms ProofFile.Honest.K12.tablesOf_at
#print axioms ProofFile.Honest.K12.tables_length
#print axioms ProofFile.Honest.K12.half_tables
#print axioms ProofFile.Honest.K12.lendRow_second
#print axioms ProofFile.Honest.K12.lendPart_cross
#print axioms ProofFile.Honest.K12.handedRest_of_row
#print axioms ProofFile.Honest.K12.first_le_seed
#print axioms ProofFile.Honest.K12.roundOf_le
#print axioms ProofFile.Honest.K12.seed_lt
#print axioms ProofFile.Honest.K12.take_front
#print axioms ProofFile.Honest.K12.draws_agree
#print axioms ProofFile.Honest.K12.seed_text
#print axioms ProofFile.Honest.K12.table_in_run
