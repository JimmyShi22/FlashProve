-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineSayOfThreads.lean: FROM A FAMILY OF INVARIANTS (`ThreadsP`, Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean) AND A RUN THAT HAS
RETURNED TO THE ONE CLAUSE OF TRUTH AT THE RUN (`SayAtRun`, E2E/OfflineSayAtRun.lean), general in the description, the book,
the prover and the job: one law a chain, at a plain half and at a half behind the guard on the field.

  `cut_index`            a list cut at a member whose image stands once: the cut's length is the member's number
  `pairSide`, `secondMember`, `stands_second`   where the rounds of the second of a half's two parts stand in the chain's
                       steps (`StandsAt`), from what the prover's list holds at the place: no simulator is asked
  `inside_called_first`, `inside_called_shared`, `inside_called_second`   **`InsideOf` (Honest/Law/Inside.lean) AT A CALLED
                       SECOND PART**, out of the family at the returned run: the state that the walk has there is
                       reached by the frame's play over the first part's rounds from a state at which the family's
                       invariant in front of the sub-protocol holds. By `owed_part_first`, `_shared`, `_second`, at a
                       list whose condition is that very sentence
  `sayAtRun_first`, `sayAtRun_shared`, `sayAtRun_second`   **the law**, at the half `proverSideOfProximityTest J`
  `sayAtRun_first_guarded`, `sayAtRun_shared_guarded`, `sayAtRun_second_guarded`   at `(proverSideOfProximityTest J).needsField`, where the
                       invariant in front holds the field being some

Asked by the law. The run: `runC` and `ready` have returned, the plan's test, the challenges fit, no stop (and, in the last
chain, `PlanServes`). The place: sub-protocol number j of the chain is b; its rounds are the job's; the prover's list
holds the job's half there. The job's public part: `FirstPartPublic`, the count of rounds, a second part with a round.
hrows: the plain rows read of the coins all but the second part's own. hSay: WHEREVER THE FAMILY's INVARIANT NUMBER j HOLDS
at the run's coins and the row of the two parts is lent, the clause holds there.

Limits. The family and hSay are premises: no member of either is given here: the law moves the sentence and proves nothing
of it. The sentence reads the input and the carried coins: no later law may take it as a hypothesis on a run and then
speak of the coins as sampled anew. Nothing on any property.
-/
import E2E.OfflineSayOfInside
import Johnson.Desc.ProofFile.Honest.Law.OwedParts
import Johnson.Desc.ProofFile.Honest.Law.Rule.Stands
import Johnson.Desc.ProofFile.Honest.Law.Cuts
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactSide
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block FileDescription Place)

/-- A list cut at a member whose image stands once in the list of images. -/
theorem cut_index {α β : Type} (f : α → β) {a : α} {t : List α} :
    ∀ (pre l : List α) (j : ℕ), (l.map f).Nodup → l = pre ++ a :: t → l[j]? = some a →
      pre.length = j
  | [], l, j, hn, hcut, hj => by
    subst hcut
    cases j with
    | zero => rfl
    | succ j =>
      have hm : a ∈ t := List.mem_of_getElem? (by simpa using hj)
      rw [List.nil_append, List.map_cons, List.nodup_cons] at hn
      exact absurd (List.mem_map_of_mem (f := f) hm) hn.1
  | p :: pre, l, j, hn, hcut, hj => by
    subst hcut
    rw [List.cons_append, List.map_cons, List.nodup_cons] at hn
    cases j with
    | zero =>
      have e : p = a := by simpa using hj
      subst e
      exact absurd (List.mem_map_of_mem (f := f) (List.mem_append_right _ List.mem_cons_self)) hn.1
    | succ j =>
      have e := cut_index f pre _ j hn.2 rfl (by simpa using hj)
      rw [List.length_cons, e]

section Stands
variable {S Cl V W Y Pb : Type}

/-- A simulator's form that tells nothing: it fills a type. -/
def silentSim (Pb : Type) (a : Addr) : Sim Pb := ⟨a, ⟨0, 0⟩, fun _ _ _ _ _ => none⟩

/-- A sub-protocol with two parts, each beside a form that tells nothing. -/
def pairSide (Pb : Type) (b : Block S Cl) (p₀ p₁ : Part V W Y) : Side S Cl V W Y Pb :=
  ⟨b, [(p₀, silentSim Pb ⟨b.place, 0⟩), (p₁, silentSim Pb ⟨b.place, 1⟩)], fun _ _ => none⟩

/-- Its second member. -/
def secondMember (Pb : Type) (b : Block S Cl) (p₀ p₁ : Part V W Y) : Member V W Y Pb :=
  ⟨1, ((b.rounds.zip b.oracles).drop p₀.moves.length).take p₁.moves.length, p₁,
    silentSim Pb ⟨b.place, 1⟩⟩

/-- **Where the second part's rounds stand in the chain's steps.** -/
theorem stands_second {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W Y)} {bs : List (Block S Cl)} {ss : List (Step W Y)}
    (hss : chainSteps B rows look v bs hs = .ok ss) (hnd : (bs.map (·.place)).Nodup)
    (b : Block S Cl) (hb : b ∈ bs) {g : Placed V W Y}
    (hg : (hs.find? fun g => g.place == b.place) = some g) (p₀ p₁ : Part V W Y)
    (hparts : g.parts = [p₀, p₁]) (hsum : p₀.moves.length + p₁.moves.length = b.rounds.length)
    (hor : b.oracles.length = b.rounds.length) (hpos : p₁.moves.length ≠ 0) :
    ∃ pre t, StandsAt bs ss (pairSide Pb b p₀ p₁) (secondMember Pb b p₀ p₁) pre t
      p₀.moves.length := by
  have hu : secondMember Pb b p₀ p₁ ∈ (pairSide Pb b p₀ p₁).members :=
    List.Mem.tail _ (List.Mem.head _)
  have hs' : ((pairSide Pb b p₀ p₁).row.map (·.1.moves.length)).sum =
      ((pairSide Pb b p₀ p₁).block.rounds.zip (pairSide Pb b p₀ p₁).block.oracles).length := by
    show p₀.moves.length + (p₁.moves.length + 0) = (b.rounds.zip b.oracles).length
    rw [List.length_zip, hor, Nat.min_self]
    omega
  obtain ⟨pre, t, n, hcut, hle, hp0, hstr, hown, hn⟩ :=
    steps_stand hss hnd (pairSide Pb b p₀ p₁) hb hg hparts hs' (secondMember Pb b p₀ p₁) hu hpos
  have hn' : n = p₀.moves.length := hn.trans (Nat.add_zero _)
  subst hn'
  refine ⟨pre, t, hcut, hle, hp0, ?_, hstr, hown⟩
  have e := congrArg List.length hown
  rw [List.length_map, List.length_take, List.length_drop] at e
  omega

end Stands

/-! ## InsideOf at a called second part -/

section Called
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}

/-- **At a called second part of the first chain.** -/
theorem inside_called_first (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (T : ThreadsP F Bk H w₀ rc x k R)
    (b : Block F.S₁ F.Cl) (hb : b ∈ F.first.blocksInOrder)
    {g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X}
    (hg : (H.first.find? fun g => g.place == b.place) = some g)
    (p₀ p₁ : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) (hparts : g.parts = [p₀, p₁])
    (hsum : p₀.moves.length + p₁.moves.length = b.rounds.length) (hpos : p₁.moves.length ≠ 0)
    (hl : ∃ ca, carriedAt Bk k 0 ⟨b.place, 1⟩ p₁ = .ok ca)
    (hc : r.called ⟨b.place, 1⟩ = true) :
    ∃ pre t m E, F.first.blocksInOrder = pre ++ b :: t ∧
      orRefused (midAtW F Bk H w₀ rc x k ρ ⟨b.place, 1⟩) = .ok m ∧
      InsideOf .own Bk 0 H.first b (T.I₁ pre.length) p₀.moves.length k m E := by
  obtain ⟨-, tr, -, -, -, s1, -, -⟩ := ready_ok hR
  obtain ⟨n1, -, -⟩ := places_nodup ((F.planOk_ok).1 hpl).places
  have hor : b.oracles.length = b.rounds.length := by
    have e := ((planOk_all hpl).1 b hb).2
    unfold Block.shaped at e
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    exact e.1
  obtain ⟨pre, t, S⟩ := stands_second (Pb := Xi) s1 n1 b hb hg p₀ p₁ hparts hsum hor hpos
  obtain ⟨_, m, _, hm, hin⟩ := (owed_part_first h hR hpl hρ hsil T
    (L := ⟨b.place, (pairSide Xi b p₀ p₁).row, fun _ _ _ _ => True, fun _ _ _ _ => True,
      fun _ _ m _ => InsideOf .own Bk 0 H.first b (T.I₁ pre.length) p₀.moves.length k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.1.take ((pre.flatMap (·.rounds)).length + p₀.moves.length))),
      fun _ _ _ => True⟩) rfl S rfl hl trivial fun _ _ hin _ _ => hin).2 hc
  exact ⟨pre, t, m, _, S.cut, hm, hin⟩

/-- **At a called second part of the shared chain.** -/
theorem inside_called_shared (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (T : ThreadsP F Bk H w₀ rc x k R)
    (b : Block F.S₂ F.Cl) (hb : b ∈ F.shared.blocksInOrder) {g : Placed Empty (Common W₀ Rc Ky) X₀}
    (hg : (H.shared.find? fun g => g.place == b.place) = some g)
    (p₀ p₁ : Part Empty (Common W₀ Rc Ky) X₀) (hparts : g.parts = [p₀, p₁])
    (hsum : p₀.moves.length + p₁.moves.length = b.rounds.length) (hpos : p₁.moves.length ≠ 0)
    (hl : ∃ ca, carriedAt Bk k 1 ⟨b.place, 1⟩ p₁ = .ok ca)
    (hc : r.called ⟨b.place, 1⟩ = true) :
    ∃ pre t m E, F.shared.blocksInOrder = pre ++ b :: t ∧
      orRefused (midSharedAtW F Bk H w₀ rc x k ρ ⟨b.place, 1⟩) = .ok m ∧
      InsideOf .shared Bk 1 H.shared b (T.I₂ pre.length) p₀.moves.length k m E := by
  obtain ⟨-, tr, -, -, -, -, s2, -⟩ := ready_ok hR
  obtain ⟨-, n2, -⟩ := places_nodup ((F.planOk_ok).1 hpl).places
  have hor : b.oracles.length = b.rounds.length := by
    have e := ((planOk_all hpl).2.1 b hb).2
    unfold Block.shaped at e
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    exact e.1
  obtain ⟨pre, t, S⟩ := stands_second (Pb := Ky) s2 n2 b hb hg p₀ p₁ hparts hsum hor hpos
  obtain ⟨_, m, _, hm, hin⟩ := (owed_part_shared h hR hpl hρ hsil T
    (L := ⟨b.place, (pairSide Ky b p₀ p₁).row, fun _ _ _ _ => True, fun _ _ _ _ => True,
      fun _ _ m _ => InsideOf .shared Bk 1 H.shared b (T.I₂ pre.length) p₀.moves.length k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + p₀.moves.length))),
      fun _ _ _ => True⟩) rfl S rfl hl trivial fun _ _ hin _ _ => hin).2 hc
  exact ⟨pre, t, m, _, S.cut, hm, hin⟩

/-- **At a called second part of the last chain.** -/
theorem inside_called_second (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (hP : PlanServes H w₀ rc R)
    (T : ThreadsP F Bk H w₀ rc x k R) (b : Block F.S₃ F.Cl) (hb : b ∈ F.second.blocksInOrder)
    {g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X}
    (hg : (H.second.find? fun g => g.place == b.place) = some g)
    (p₀ p₁ : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) (hparts : g.parts = [p₀, p₁])
    (hsum : p₀.moves.length + p₁.moves.length = b.rounds.length) (hpos : p₁.moves.length ≠ 0)
    (hl : ∃ ca, carriedAt Bk k 2 ⟨b.place, 1⟩ p₁ = .ok ca)
    (hc : r.called ⟨b.place, 1⟩ = true) :
    ∃ pre t m E, F.second.blocksInOrder = pre ++ b :: t ∧
      orRefused (midAtW F Bk H w₀ rc x k ρ ⟨b.place, 1⟩) = .ok m ∧
      InsideOf .own Bk 2 H.second b (T.I₃ pre.length) p₀.moves.length k m E := by
  obtain ⟨-, tr, -, -, -, -, -, s3⟩ := ready_ok hR
  obtain ⟨-, -, n3⟩ := places_nodup ((F.planOk_ok).1 hpl).places
  have hor : b.oracles.length = b.rounds.length := by
    have e := ((planOk_all hpl).2.2 b hb).2
    unfold Block.shaped at e
    simp only [Bool.and_eq_true, beq_iff_eq] at e
    exact e.1
  obtain ⟨pre, t, S⟩ := stands_second (Pb := Xi) s3 n3 b hb hg p₀ p₁ hparts hsum hor hpos
  obtain ⟨_, m, _, hm, hin⟩ := (owed_part_second h hR hpl hρ hsil hP T
    (L := ⟨b.place, (pairSide Xi b p₀ p₁).row, fun _ _ _ _ => True, fun _ _ _ _ => True,
      fun _ _ m _ => InsideOf .own Bk 2 H.second b (T.I₃ pre.length) p₀.moves.length k m
        (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
          (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + p₀.moves.length))),
      fun _ _ _ => True⟩) rfl S rfl hl trivial fun _ _ hin _ _ => hin).2 hc
  exact ⟨pre, t, m, _, S.cut, hm, hin⟩

end Called

/-! ## The job's two parts -/

section Job
variable {S Cl V W X : Type}

/-- What is asked of the place: the sub-protocol's rounds are the job's, and the job's two parts have as many
moves; the second has one. -/
structure TestAtBlock (J : TestJob W X) (b : Block S Cl) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) : Prop where
  pub : FirstPartPublic J s next rest
  laid : b.rounds.zip b.oracles = J.laid
  lists : b.oracles.length = b.rounds.length
  count : (H2K.JointK.laidOf J.p).length =
    firstLen J.p.nums.stages + restLen J.p.nums.stages
  second : restLen J.p.nums.stages ≠ 0

theorem rest_moves_length (J : TestJob W X) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) :
    (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
  exact (congrArg List.length (rest_moves J s next rest hst)).trans (len_movesFrom J _ _ _)

theorem TestAtBlock.sum {J : TestJob W X} {b : Block S Cl} {s next : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} (Q : TestAtBlock J b s next rest) :
    (firstPart J : Part V W X).moves.length + (restPart J : Part V W X).moves.length =
      b.rounds.length := by
  have e : (b.rounds.zip b.oracles).length = (H2K.JointK.laidOf J.p).length :=
    congrArg List.length Q.laid
  rw [List.length_zip, Q.lists, Nat.min_self, Q.count] at e
  rw [Light.first_moves_len, rest_moves_length J s next rest Q.pub.stages, e]

/-- The carried blocks do not see the guard on the field. -/
theorem carriedAt_behind (Bk : ProverCoinCounts) (k : Coins Bk) (chain : ℕ) (a : Addr) (p : Part V W X) :
    carriedAt Bk k chain a p.needsField = carriedAt Bk k chain a p := by
  cases p with
  | mk t s c b h o1 o2 m =>
    unfold carriedAt
    dsimp only [Part.needsField, lendPart]
    by_cases hd : (t != dueAt (Bk.rowsOf chain) a) = true
    · simp only [if_pos hd]
    · simp only [if_neg hd]
      cases (k.look chain a).2.cut ⟨0, 0⟩ t <;> rfl

end Job

/-! ## The law -/

section Law
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}

/-- **The clause at the run, in the first chain.** -/
theorem sayAtRun_first (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (T : ThreadsP F Bk H w₀ rc x k R)
    (J : TestJob (Local W₀ Rc Xi Tr) X)
    (rows : Local W₀ Rc Xi Tr → Front X → TestCoins → PlainRows)
    (hrows : ∀ w fr (c : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).Coins),
      rows w fr (restCoins J c) = rows w fr (carriedCoins J (stretches _ c.2.2)))
    (j : ℕ) (b : Block F.S₁ F.Cl) (hb : F.first.blocksInOrder[j]? = some b) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (Q : TestAtBlock J b s next rest)
    (hhalf : (H.first.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J))
    (hSay : ∀ st m₀ E₀ (c : RowCoins [(firstPart J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J]), T.I₁ j k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf 0) (k.look 0) b.place [(firstPart J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J] 0 = .ok c →
      SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1))) :
    SayAtRun (Local W₀ Rc Xi Tr) J rows k 0 b.place r.called (midAtW F Bk H w₀ rc x k ρ) := by
  intro hc m ca hm hca
  obtain ⟨pre, t, m', E, hcut, hm', hin⟩ := inside_called_first h hR hpl hρ hsil T b
    (List.mem_of_getElem? hb) hhalf (firstPart J) (restPart J) rfl Q.sum
    (by rw [rest_moves_length J s next rest Q.pub.stages]; exact Q.second) ⟨ca, hca⟩ hc
  obtain rfl : m = m' := by
    rw [hm] at hm'
    exact Except.ok.inj hm'
  rw [cut_index (·.place) pre _ j (places_nodup ((F.planOk_ok).1 hpl).places).1 hcut hb,
    Light.first_moves_len] at hin
  exact says_of_inside J rows hrows s next rest Q.pub Q.laid Q.lists hhalf hin hSay ca hca

/-- **The clause at the run, in the shared chain.** -/
theorem sayAtRun_shared (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (T : ThreadsP F Bk H w₀ rc x k R)
    (J : TestJob (Common W₀ Rc Ky) X₀)
    (rows : Common W₀ Rc Ky → Front X₀ → TestCoins → PlainRows)
    (hrows : ∀ w fr (c : (restPart J : Part Empty (Common W₀ Rc Ky) X₀).Coins),
      rows w fr (restCoins J c) = rows w fr (carriedCoins J (stretches _ c.2.2)))
    (j : ℕ) (b : Block F.S₂ F.Cl) (hb : F.shared.blocksInOrder[j]? = some b) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (Q : TestAtBlock J b s next rest)
    (hhalf : (H.shared.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J))
    (hSay : ∀ st m₀ E₀ (c : RowCoins [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀),
        restPart J]), T.I₂ j k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf 1) (k.look 1) b.place [(firstPart J :
        Part Empty (Common W₀ Rc Ky) X₀), restPart J] 0 = .ok c →
      SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1))) :
    SayAtRun Empty J rows k 1 b.place r.called (midSharedAtW F Bk H w₀ rc x k ρ) := by
  intro hc m ca hm hca
  obtain ⟨pre, t, m', E, hcut, hm', hin⟩ := inside_called_shared h hR hpl hρ hsil T b
    (List.mem_of_getElem? hb) hhalf (firstPart J) (restPart J) rfl Q.sum
    (by rw [rest_moves_length J s next rest Q.pub.stages]; exact Q.second) ⟨ca, hca⟩ hc
  obtain rfl : m = m' := by
    rw [hm] at hm'
    exact Except.ok.inj hm'
  rw [cut_index (·.place) pre _ j (places_nodup ((F.planOk_ok).1 hpl).places).2.1 hcut hb,
    Light.first_moves_len] at hin
  exact says_of_inside J rows hrows s next rest Q.pub Q.laid Q.lists hhalf hin hSay ca hca

/-- **The clause at the run, in the last chain.** -/
theorem sayAtRun_second (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (hP : PlanServes H w₀ rc R)
    (T : ThreadsP F Bk H w₀ rc x k R) (J : TestJob (Local W₀ Rc Xi Tr) X)
    (rows : Local W₀ Rc Xi Tr → Front X → TestCoins → PlainRows)
    (hrows : ∀ w fr (c : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).Coins),
      rows w fr (restCoins J c) = rows w fr (carriedCoins J (stretches _ c.2.2)))
    (j : ℕ) (b : Block F.S₃ F.Cl) (hb : F.second.blocksInOrder[j]? = some b) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (Q : TestAtBlock J b s next rest)
    (hhalf : (H.second.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J))
    (hSay : ∀ st m₀ E₀ (c : RowCoins [(firstPart J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J]), T.I₃ j k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf 2) (k.look 2) b.place [(firstPart J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J] 0 = .ok c →
      SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1))) :
    SayAtRun (Local W₀ Rc Xi Tr) J rows k 2 b.place r.called (midAtW F Bk H w₀ rc x k ρ) := by
  intro hc m ca hm hca
  obtain ⟨pre, t, m', E, hcut, hm', hin⟩ := inside_called_second h hR hpl hρ hsil hP T b
    (List.mem_of_getElem? hb) hhalf (firstPart J) (restPart J) rfl Q.sum
    (by rw [rest_moves_length J s next rest Q.pub.stages]; exact Q.second) ⟨ca, hca⟩ hc
  obtain rfl : m = m' := by
    rw [hm] at hm'
    exact Except.ok.inj hm'
  rw [cut_index (·.place) pre _ j (places_nodup ((F.planOk_ok).1 hpl).places).2.2 hcut hb,
    Light.first_moves_len] at hin
  exact says_of_inside J rows hrows s next rest Q.pub Q.laid Q.lists hhalf hin hSay ca hca

/-- **In the first chain, behind the guard on the field.** -/
theorem sayAtRun_first_guarded (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (T : ThreadsP F Bk H w₀ rc x k R)
    (J : TestJob (Local W₀ Rc Xi Tr) X)
    (rows : Local W₀ Rc Xi Tr → Front X → TestCoins → PlainRows)
    (hrows : ∀ w fr (c : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).Coins),
      rows w fr (restCoins J c) = rows w fr (carriedCoins J (stretches _ c.2.2)))
    (j : ℕ) (b : Block F.S₁ F.Cl) (hb : F.first.blocksInOrder[j]? = some b) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (Q : TestAtBlock J b s next rest)
    (hhalf : (H.first.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J).needsField)
    (hopen : ∀ k s m E, T.I₁ j k s m E → m.opened.isSome = true)
    (hSay : ∀ st m₀ E₀ (c : RowCoins [(firstPart J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J]), T.I₁ j k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf 0) (k.look 0) b.place [(firstPart J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J] 0 = .ok c →
      SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1))) :
    SayAtRun (Local W₀ Rc Xi Tr) J rows k 0 b.place r.called (midAtW F Bk H w₀ rc x k ρ) := by
  intro hc m ca hm hca
  obtain ⟨pre, t, m', E, hcut, hm', hin⟩ := inside_called_first h hR hpl hρ hsil T b
    (List.mem_of_getElem? hb) hhalf (firstPart J).needsField (restPart J).needsField rfl
    (by rw [needsField_length, needsField_length]; exact Q.sum)
    (by rw [needsField_length, rest_moves_length J s next rest Q.pub.stages]; exact Q.second)
    ⟨ca, (carriedAt_behind Bk k 0 _ _).trans hca⟩ hc
  obtain rfl : m = m' := by
    rw [hm] at hm'
    exact Except.ok.inj hm'
  rw [cut_index (·.place) pre _ j (places_nodup ((F.planOk_ok).1 hpl).places).1 hcut hb,
    needsField_length, Light.first_moves_len] at hin
  exact says_of_inside_guarded J rows hrows s next rest Q.pub Q.laid Q.lists hhalf hopen hin hSay ca
    hca

/-- **In the shared chain, behind the guard on the field.** -/
theorem sayAtRun_shared_guarded (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (T : ThreadsP F Bk H w₀ rc x k R)
    (J : TestJob (Common W₀ Rc Ky) X₀)
    (rows : Common W₀ Rc Ky → Front X₀ → TestCoins → PlainRows)
    (hrows : ∀ w fr (c : (restPart J : Part Empty (Common W₀ Rc Ky) X₀).Coins),
      rows w fr (restCoins J c) = rows w fr (carriedCoins J (stretches _ c.2.2)))
    (j : ℕ) (b : Block F.S₂ F.Cl) (hb : F.shared.blocksInOrder[j]? = some b) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (Q : TestAtBlock J b s next rest)
    (hhalf : (H.shared.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J).needsField)
    (hopen : ∀ k s m E, T.I₂ j k s m E → m.opened.isSome = true)
    (hSay : ∀ st m₀ E₀ (c : RowCoins [(firstPart J : Part Empty (Common W₀ Rc Ky) X₀),
        restPart J]), T.I₂ j k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf 1) (k.look 1) b.place [(firstPart J :
        Part Empty (Common W₀ Rc Ky) X₀), restPart J] 0 = .ok c →
      SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1))) :
    SayAtRun Empty J rows k 1 b.place r.called (midSharedAtW F Bk H w₀ rc x k ρ) := by
  intro hc m ca hm hca
  obtain ⟨pre, t, m', E, hcut, hm', hin⟩ := inside_called_shared h hR hpl hρ hsil T b
    (List.mem_of_getElem? hb) hhalf (firstPart J).needsField (restPart J).needsField rfl
    (by rw [needsField_length, needsField_length]; exact Q.sum)
    (by rw [needsField_length, rest_moves_length J s next rest Q.pub.stages]; exact Q.second)
    ⟨ca, (carriedAt_behind Bk k 1 _ _).trans hca⟩ hc
  obtain rfl : m = m' := by
    rw [hm] at hm'
    exact Except.ok.inj hm'
  rw [cut_index (·.place) pre _ j (places_nodup ((F.planOk_ok).1 hpl).places).2.1 hcut hb,
    needsField_length, Light.first_moves_len] at hin
  exact says_of_inside_guarded J rows hrows s next rest Q.pub Q.laid Q.lists hhalf hopen hin hSay ca
    hca

/-- **In the last chain, behind the guard on the field.** -/
theorem sayAtRun_second_guarded (h : runC F Bk H w₀ rc x k ρ = .ok r)
    (hR : ready F Bk H w₀ rc x k = .ok R) (hpl : F.planOk = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (hP : PlanServes H w₀ rc R)
    (T : ThreadsP F Bk H w₀ rc x k R) (J : TestJob (Local W₀ Rc Xi Tr) X)
    (rows : Local W₀ Rc Xi Tr → Front X → TestCoins → PlainRows)
    (hrows : ∀ w fr (c : (restPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).Coins),
      rows w fr (restCoins J c) = rows w fr (carriedCoins J (stretches _ c.2.2)))
    (j : ℕ) (b : Block F.S₃ F.Cl) (hb : F.second.blocksInOrder[j]? = some b) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (Q : TestAtBlock J b s next rest)
    (hhalf : (H.second.find? fun g => g.place == b.place) = some (proverSideOfProximityTest J).needsField)
    (hopen : ∀ k s m E, T.I₃ j k s m E → m.opened.isSome = true)
    (hSay : ∀ st m₀ E₀ (c : RowCoins [(firstPart J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J]), T.I₃ j k st m₀ E₀ →
      lendRow Bk (Bk.rowsOf 2) (k.look 2) b.place [(firstPart J :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J] 0 = .ok c →
      SaysInFront J m₀.st.input (frontOf m₀) (rows m₀.st.input (frontOf m₀) (restCoins J c.2.1))) :
    SayAtRun (Local W₀ Rc Xi Tr) J rows k 2 b.place r.called (midAtW F Bk H w₀ rc x k ρ) := by
  intro hc m ca hm hca
  obtain ⟨pre, t, m', E, hcut, hm', hin⟩ := inside_called_second h hR hpl hρ hsil hP T b
    (List.mem_of_getElem? hb) hhalf (firstPart J).needsField (restPart J).needsField rfl
    (by rw [needsField_length, needsField_length]; exact Q.sum)
    (by rw [needsField_length, rest_moves_length J s next rest Q.pub.stages]; exact Q.second)
    ⟨ca, (carriedAt_behind Bk k 2 _ _).trans hca⟩ hc
  obtain rfl : m = m' := by
    rw [hm] at hm'
    exact Except.ok.inj hm'
  rw [cut_index (·.place) pre _ j (places_nodup ((F.planOk_ok).1 hpl).places).2.2 hcut hb,
    needsField_length, Light.first_moves_len] at hin
  exact says_of_inside_guarded J rows hrows s next rest Q.pub Q.laid Q.lists hhalf hopen hin hSay ca
    hca

end Law

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.cut_index
#print axioms AtPublicFiles.OfflineRows.stands_second
#print axioms AtPublicFiles.OfflineRows.inside_called_first
#print axioms AtPublicFiles.OfflineRows.inside_called_shared
#print axioms AtPublicFiles.OfflineRows.inside_called_second
#print axioms AtPublicFiles.OfflineRows.TestAtBlock
#print axioms AtPublicFiles.OfflineRows.rest_moves_length
#print axioms AtPublicFiles.OfflineRows.carriedAt_behind
#print axioms AtPublicFiles.OfflineRows.sayAtRun_first
#print axioms AtPublicFiles.OfflineRows.sayAtRun_shared
#print axioms AtPublicFiles.OfflineRows.sayAtRun_second
#print axioms AtPublicFiles.OfflineRows.sayAtRun_first_guarded
#print axioms AtPublicFiles.OfflineRows.sayAtRun_shared_guarded
#print axioms AtPublicFiles.OfflineRows.sayAtRun_second_guarded
