-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.First.K8.LawBefore
import Johnson.Desc.K12.Law.MasksFixed
import Johnson.G.RoundsOfPlan
/-
Johnson/Desc/K12/Law/BeforeK12.lean: THE TREES THAT A PROXIMITY TEST's FIRST SWITCH OPENS WERE SENT IN TIME: K12's own corollary of the law of beforeAt (beforeAt_at, Johnson/Desc/First/K8/LawBefore.lean). It reads no JoinP5. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  sendRound_count: the round i that sendRound finds for the message number n: the rounds in front of it send at most n roots, those up to it more than n: so n is below the chain's count of roots.
  bat_draws: the first declared round of a proximity test draws: so it is the block's first drawing round. bat_roots: it sends no root.
  first_sent: ON THE PLAN ALONE: MasksFixed p · a yes of beforeAt at a list of blocks that holds, behind pre, a block b with K12's «before» and declared rounds · the place's chain is that list's · the chain's declared round at b's first index is b's first: THEN each tree of nums.first is (i) an own tree below free, SENT IN A ROUND STRICTLY IN FRONT OF "BAT"'s, or (ii) another source «taken c' n», sent in the chain c' + 1 ≤ the block's (strictly in front of "BAT"'s round if it is the block's own chain), or (iii) the first fold's own mask's tree itself.
  own_sent: the step for a message of the block's own chain. rootsOf_take_le: a tool.
  taken_below: the pin n3 off the plan: what «before» names of an earlier chain is below that chain's count of roots; what it names OF THE BLOCK's OWN CHAIN is below the count of the roots that the chain's rounds in front of the block send.
  sendRound_of_lt: the converse of sendRound_count. SentBy D c at' lim o: the tree that the opening o names is sent: an own tree in a round of the block's chain in front of the chain's round number lim; another source's in its chain, the block's or an earlier one (if the block's: in front of the block).
  fixed_sent: from «Fixed … start o» (FixedLaw.lean: fixedOk's yes gives it at every switch and at the base case) to SentBy at the chain's round number ‹the block's first› + start.
  opened_sent (IT IS NOT THE ROW masks_fixed_word): ON THE PLAN: fixedOk p · beforeAt's yes · the chain's declared rounds are preR ++ (rds ++ postR) with b at preR's end · free = rootsOf preR: EVERY TREE THAT A SWITCH OR THE BASE CASE OPENS is SentBy in front of the round behind that stage's first round (a switch: its fold's first round, whose message stands in front of its draw) | in front of the base case's first round.
  No literal of ours has a source «taken c' n» with c' the test's own chain: arm (ii)'s last clause is for the form's sake. O stands in beforeAt's yes alone: the clause on sampled tenants is not spent.
Limits: b is ANY block with these two fields: that a description's seated block has them is the seat's (Block.inside keeps both: not shown here). «Sent in front» is of rounds of the declared plan; that a file's bytes come in that order is the reading's. Nothing on the later stages: their trees are the test's own (MasksFixed.made). The clause of beforeAt on sampled messages is not drawn out.

-/
set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.G.OfPlan (rootsOf)

theorem sendRound_count : ∀ (ds : List Fmt.DeclaredRound) (n i : ℕ), sendRound ds n = some i →
    rootsOf (ds.take i) ≤ n ∧ n < rootsOf (ds.take (i + 1)) ∧ n < rootsOf ds
  | [], _, _, h => by simp [sendRound] at h
  | r :: l, n, i, h => by
    unfold sendRound at h
    by_cases hn : n < r.entry.roots
    · rw [if_pos hn] at h
      obtain rfl : 0 = i := by simpa using h
      simp only [rootsOf, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        List.take_succ_cons, List.map_cons, List.sum_cons]
      omega
    · rw [if_neg hn] at h
      cases hs : sendRound l (n - r.entry.roots) with
      | none => simp [hs] at h
      | some j =>
        rw [hs] at h
        obtain rfl : j + 1 = i := by simpa using h
        obtain ⟨h1, h2, h3⟩ := sendRound_count l _ j hs
        simp only [rootsOf, List.take_succ_cons, List.map_cons, List.sum_cons] at h1 h2 h3 ⊢
        omega

theorem bat_draws (rows : ℕ) :
    drawsAny ⟨{ Fmt.M1.rBat.entry with rows := rows }, [], []⟩ = true := rfl

theorem bat_roots (rows : ℕ) :
    ({ Fmt.M1.rBat.entry with rows := rows } : Fmt.Entry).roots = 0 := rfl

theorem rootsOf_take_le (ds : List Fmt.DeclaredRound) (a k : ℕ) (h : a ≤ k) :
    rootsOf (ds.take a) ≤ rootsOf (ds.take k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add]
  simp only [rootsOf, List.map_append, List.sum_append]
  omega

/-- A message of the block's own chain that «before» names is sent strictly in front of "BAT"'s
round. -/
theorem own_sent {S Cl : Type} (N : H2U.TestNums) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums N = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hrd : b.rounds = rds)
    (h : beforeAt D O c from' (pre ++ b :: post) = true)
    (hD : (chainOf D (c + 1))[from' + roundsIn pre]? = rds.head?) (n : ℕ)
    (hn : (c + 1, n) ∈ b.before) :
    ∃ i, sendRound (chainOf D (c + 1)) n = some i ∧ i < from' + roundsIn pre := by
  obtain ⟨_, _, _, R, _, _, rfl⟩ := rounds_top N rds hr
  have hidx : b.rounds.findIdx drawsAny = 0 := by
    rw [hrd, List.findIdx_cons, bat_draws]
    rfl
  obtain ⟨i, h1, _, _, h4⟩ := beforeAt_at D O c pre from' b post h (c + 1, n) hn
  simp only [beq_self_eq_true, if_true, hidx, Nat.add_zero] at h4
  refine ⟨i, h1, Nat.lt_of_le_of_ne h4 ?_⟩
  rintro rfl
  obtain ⟨r, g1, g2⟩ := sendRound_roots _ _ _ h1
  rw [hD, List.head?_cons] at g1
  obtain rfl := Option.some.inj g1
  exact absurd g2 (by rw [bat_roots]; exact Nat.lt_irrefl 0)

/-- **Each tree of nums.first was sent in time.** -/
theorem first_sent {S Cl : Type} (p : P12) (M : MasksFixed p) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (hc : p.place.chain = c + 1)
    (h : beforeAt D O c from' (pre ++ b :: post) = true)
    (hD : (chainOf D (c + 1))[from' + roundsIn pre]? = rds.head?) :
    ∀ o ∈ p.nums.first,
      (∃ n, o.2 = .own n ∧ n < p.nums.free ∧
        ∃ i, sendRound (chainOf D (c + 1)) n = some i ∧ i < from' + roundsIn pre) ∨
      (∃ c' n, o.2 = .taken c' n ∧ c' ≤ c ∧ ∃ i, sendRound (chainOf D (c' + 1)) n = some i ∧
        (c' = c → i < from' + roundsIn pre)) ∨
      (p.nums.ownMask = true ∧ o.2 = .own p.nums.free) := by
  have hown := own_sent p.nums rds hr D O c from' pre b post hrd h hD
  intro o ho
  rcases M.front o ho with hf | hf
  · cases hs : o.2 with
    | own n =>
      rw [hs] at hf
      obtain ⟨f1, f2⟩ := hf
      rw [hc, ← hbef] at f2
      exact .inl ⟨n, rfl, f1, hown n f2⟩
    | taken c' n =>
      rw [hs] at hf
      have f2 : (c' + 1, n) ∈ b.before := by
        rw [hbef]
        exact hf
      obtain ⟨i, h1, _, h3, _⟩ := beforeAt_at D O c pre from' b post h (c' + 1, n) f2
      refine .inr (.inl ⟨c', n, rfl, Nat.le_of_succ_le_succ h3, i, h1, ?_⟩)
      rintro rfl
      obtain ⟨i', g1, g2⟩ := hown n f2
      obtain rfl := Option.some.inj (h1.symm.trans g1)
      exact g2
  · exact .inr (.inr hf)

/-- **The pin n3, off the plan**: what «before» names of an earlier chain is below that chain's count
of roots; what it names of the block's own chain is below the count of the roots that the chain's
rounds IN FRONT OF THE BLOCK send. -/
theorem taken_below {S Cl : Type} (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (h : beforeAt D O c from' (pre ++ b :: post) = true)
    (hD : (chainOf D (c + 1))[from' + roundsIn pre]? = rds.head?) (c' n : ℕ)
    (hm : (c' + 1, n) ∈ p.before) :
    c' ≤ c ∧ n < rootsOf (chainOf D (c' + 1)) ∧
      (c' = c → n < rootsOf ((chainOf D (c + 1)).take (from' + roundsIn pre))) := by
  have hm' : (c' + 1, n) ∈ b.before := hbef ▸ hm
  obtain ⟨i, h1, _, h3, _⟩ := beforeAt_at D O c pre from' b post h (c' + 1, n) hm'
  refine ⟨Nat.le_of_succ_le_succ h3, (sendRound_count _ _ _ h1).2.2, ?_⟩
  rintro rfl
  obtain ⟨i', g1, g2⟩ := own_sent p.nums rds hr D O c' from' pre b post hrd h hD n hm'
  exact Nat.lt_of_lt_of_le (sendRound_count _ _ _ g1).2.1 (rootsOf_take_le _ _ _ g2)

theorem sendRound_of_lt : ∀ (ds : List Fmt.DeclaredRound) (n k : ℕ), n < rootsOf (ds.take k) →
    ∃ i, sendRound ds n = some i ∧ i < k
  | [], n, k, h => by simp [rootsOf] at h
  | _ :: _, n, 0, h => by simp [rootsOf] at h
  | r :: l, n, k + 1, h => by
    unfold sendRound
    by_cases hn : n < r.entry.roots
    · exact ⟨0, by rw [if_pos hn], Nat.succ_pos k⟩
    · have h' : n - r.entry.roots < rootsOf (l.take k) := by
        simp only [rootsOf, List.take_succ_cons, List.map_cons, List.sum_cons] at h ⊢
        omega
      obtain ⟨i, h1, h2⟩ := sendRound_of_lt l _ k h'
      exact ⟨i + 1, by rw [if_neg hn, h1]; rfl, Nat.succ_lt_succ h2⟩

/-- The tree that an opening names is sent: an own tree in a round of the block's chain in front of
the chain's round number `lim`; a tree of another source in its chain, which is the block's or an
earlier one, and, if the block's, in front of the block. -/
def SentBy (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (c at' lim : ℕ)
    (o : Fmt.Shape × Fmt.TreeSource) : Prop :=
  match o.2 with
  | .own n => ∃ i, sendRound (chainOf D (c + 1)) n = some i ∧ i < lim
  | .taken c' n => c' ≤ c ∧ ∃ i, sendRound (chainOf D (c' + 1)) n = some i ∧ (c' = c → i < at')

/-- **From «fixed in front of the block's round number start» (FixedLaw.lean) to «sent, in the
chain's declared rounds, in front of that round».** -/
theorem fixed_sent {S Cl : Type} (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (hc : p.place.chain = c + 1)
    (h : beforeAt D O c from' (pre ++ b :: post) = true) (preR postR : List Fmt.DeclaredRound)
    (hDs : chainOf D (c + 1) = preR ++ (rds ++ postR)) (hlen : preR.length = from' + roundsIn pre)
    (hfree : p.nums.free = rootsOf preR) (start : ℕ) (o : Fmt.Shape × Fmt.TreeSource)
    (hF : H2K.FixedBefore.Fixed p.place.chain p.before p.nums rds start o) :
    SentBy D c (from' + roundsIn pre) (from' + roundsIn pre + start) o := by
  have hD : (chainOf D (c + 1))[from' + roundsIn pre]? = rds.head? := by
    obtain ⟨_, _, _, R, _, _, rfl⟩ := rounds_top p.nums rds hr
    rw [hDs, ← hlen]
    simp
  have hown := own_sent p.nums rds hr D O c from' pre b post hrd h hD
  unfold H2K.FixedBefore.Fixed at hF
  unfold SentBy
  cases hs : o.2 with
  | own n =>
    simp only [hs] at hF ⊢
    rcases hF with ⟨_, f2⟩ | ⟨_, f2⟩
    · rw [hc, ← hbef] at f2
      obtain ⟨i, g1, g2⟩ := hown n f2
      exact ⟨i, g1, Nat.lt_of_lt_of_le g2 (Nat.le_add_right _ _)⟩
    · refine sendRound_of_lt _ n _ ?_
      rw [hDs, ← hlen, List.take_length_add_append]
      have e : rootsOf (rds.take start) ≤ rootsOf ((rds ++ postR).take start) := by
        rw [List.take_append]
        simp only [rootsOf, List.map_append, List.sum_append]
        omega
      simp only [H2K.FixedBefore.sentIn, hfree, rootsOf] at f2
      simp only [rootsOf, List.map_append, List.sum_append] at e ⊢
      omega
  | taken c' n =>
    simp only [hs] at hF ⊢
    have f2 : (c' + 1, n) ∈ b.before := hbef ▸ hF
    obtain ⟨i, h1, _, h3, _⟩ := beforeAt_at D O c pre from' b post h (c' + 1, n) f2
    refine ⟨Nat.le_of_succ_le_succ h3, i, h1, ?_⟩
    rintro rfl
    obtain ⟨i', g1, g2⟩ := hown n f2
    obtain rfl := Option.some.inj (h1.symm.trans g1)
    exact g2

/-- **On the plan: every tree that a switch or the base case of a proximity test
opens is sent, in the declared rounds of its chain, in front of the round behind that stage's first
(whose message stands in front of its draw); a tree of another chain in that chain, an earlier
one.** -/
theorem opened_sent {S Cl : Type} (p : P12) (hfx : H2K.FixedBefore.fixedOk p = true)
    (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c from' : ℕ) (pre : List (Block S Cl))
    (b : Block S Cl) (post : List (Block S Cl)) (hbef : b.before = p.before)
    (hrd : b.rounds = rds) (hc : p.place.chain = c + 1)
    (h : beforeAt D O c from' (pre ++ b :: post) = true) (preR postR : List Fmt.DeclaredRound)
    (hDs : chainOf D (c + 1) = preR ++ (rds ++ postR)) (hlen : preR.length = from' + roundsIn pre)
    (hfree : p.nums.free = rootsOf preR) :
    (∀ (j : ℕ) (s : Fmt.M1.Stage), j + 1 < p.nums.stages.length → p.nums.stages[j]? = some s →
      ∀ r ∈ (rds.drop (H2K.FixedBefore.foldStart 1 p.nums.stages j + 1 + s.k)).take 2,
      ∀ o ∈ r.opens, SentBy D c (from' + roundsIn pre)
        (from' + roundsIn pre + (H2K.FixedBefore.foldStart 1 p.nums.stages j + 1)) o) ∧
    (∀ r ∈ (rds.drop
        (H2K.FixedBefore.foldStart 1 p.nums.stages (p.nums.stages.length - 1))).take 2,
      ∀ o ∈ r.opens, SentBy D c (from' + roundsIn pre)
        (from' + roundsIn pre +
          H2K.FixedBefore.foldStart 1 p.nums.stages (p.nums.stages.length - 1)) o) :=
  ⟨fun j s hj hs r hr' o ho => fixed_sent p rds hr D O c from' pre b post hbef hrd hc h preR postR
      hDs hlen hfree _ o (H2K.FixedBefore.fixed_switch p hfx rds hr j s hj hs r hr' o ho),
    fun r hr' o ho => fixed_sent p rds hr D O c from' pre b post hbef hrd hc h preR postR hDs hlen
      hfree _ o (H2K.FixedBefore.fixed_base p hfx rds hr r hr' o ho)⟩

end H2K.Made

#print axioms H2K.Made.sendRound_count
#print axioms H2K.Made.first_sent
#print axioms H2K.Made.own_sent
#print axioms H2K.Made.taken_below
#print axioms H2K.Made.fixed_sent
#print axioms H2K.Made.opened_sent
