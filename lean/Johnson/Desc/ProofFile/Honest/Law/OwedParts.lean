-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean: what one part of a list is owed at one run
(`Lettered.owedAt`, Honest/Rule.lean), from the invariants and the side's two hypotheses. At a run
of `runC` (Honest/Walk.lean) that has returned, at a part whose rounds are one section of its
chain's, i rounds inside its sub-protocol: `bud` holds at the run's own challenges and positions
there, where it holds at their closed form; and where the part was called: the book's carried blocks
are available, `midAtW` or `midSharedAtW` (Honest/MidW.lean: the walk's own state) returns a state,
and On holds at what the run shows before the part, where On follows from the invariant's condition
at the state before it.

What this is. Conditional lemmas on this folder's own functions, pointwise. Their conclusion is a
clause of a definition of this folder (meant as a hypothesis). None of the library's goals.

  1  `ThreadsP`   hypotheses of `runC_returns`, as one structure
  2  `StandsAt`, `stretch_back`   where a part's rounds are
  3  `owed_part_first`, `owed_part_shared`, `owed_part_second`   the three lemmas

Limits.
  * Where a part's rounds are (`StandsAt`) and that the book gives it its carried blocks are
    hypotheses here.
  * The side's two hypotheses are taken at this one part, run and coins.
  * `hon` knows of the state's field `opened` what the invariant says of it, and no more: an On that
    reads the field wants invariants that pin it.
  * `ThreadsP` asks the invariants at the starts at the states as `ChainProgress.start` (Honest/Walk.lean)
    lays them: the field `opened` is `some []` at the first and the shared chain, and at the second
    chain, where the two ends' fields hold columns, these joined.
  * `PlaysOn` is asked at every state that the invariant allows, at every value of the field
    `opened` too: at a prover with a part that reads the columns and errs at `none` (its duty:
    Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant that lets `none` through before
    that part's sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits).
  * Nothing is said of `midAt` and `midSharedAt` (Honest/Frame.lean), which play the rounds by
    `play` and hand no columns.
  * Among the hypotheses that the prose above does not name: `Draws.due` (the challenges are such as
    the description's rounds can draw; the first chain's last challenge is the empty one):
    `owed_part_first`, `owed_part_shared`, `owed_part_second`; `FileDescription.planOk` (the library's
    executable test): `owed_part_first`, `owed_part_shared`, `owed_part_second`; `ready … = .ok`
    (`ready` returns at these coins): `owed_part_first`, `owed_part_shared`, `owed_part_second`;
    `silentAt … = none` (the honest side does not stop at these challenges, or the request has no
    trace): `owed_part_first`, `owed_part_shared`, `owed_part_second`; `PlanServes`
    (Honest/Law/RunsFile.lean): `owed_part_second`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.InsideFile
import Johnson.Desc.ProofFile.Honest.Law.RunBefore
import Johnson.Desc.ProofFile.Honest.Law.StratRun
import Johnson.Desc.ProofFile.Honest.Law.Rule.OnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X S Cl V W Y Pb : Type}

/-! ## 1 The invariants -/

/-- **Hypotheses of `runC_returns` (Honest/Law/RunsFile.lean)**, at one input, one run's coins and
what `ready` has prepared: the three families of invariants, `PlaysOn` at every sub-protocol, the
invariants at the first and the shared chain's starts, and at the second chain's from the two ends,
each at the state as `ChainProgress.start` lays it. It is a structure of hypotheses. Nothing is claimed of
it, and it is none of the library's goals. -/
structure ThreadsP (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀)
    (rc : Rc) (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) where
  I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop
  I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop
  I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop
  h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1))
  h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b → PlaysOn .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1))
  h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
    PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1))
  a₁ : I₁ 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
    (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])
  a₂ : I₂ 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
    (envOf (H.storedWords w₀ rc) (fun _ _ => none) [])
  a₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
    I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
    m₁.opened = some o₁ → m₂.opened = some o₂ →
    I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂)

/-! ## 2 Where a part's rounds are -/

/-- **Where the rounds of the part u of the side σ are in its chain's**. `bs`: the chain's flat
list; `ss`: its `Step`s; `pre`, `t`: the sub-protocols before σ's and after it; `i`: the rounds of
the list's parts before u. A definition, meant as a hypothesis. -/
structure StandsAt (bs : List (Block S Cl)) (ss : List (Step W Y)) (σ : Side S Cl V W Y Pb)
    (u : Member V W Y Pb) (pre t : List (Block S Cl)) (i : Nat) : Prop where
  cut : bs = pre ++ σ.block :: t
  le : i + u.rounds.length ≤ σ.block.rounds.length
  pos : 0 < u.rounds.length
  fits : (pre.flatMap (·.rounds)).length + i + u.rounds.length ≤ ss.length
  str : InStretch ss ⟨σ.block.place, u.number⟩ ((pre.flatMap (·.rounds)).length + i)
    u.rounds.length
  own : ((ss.drop ((pre.flatMap (·.rounds)).length + i)).take u.rounds.length).map
    (fun s => (s.decl, s.oracles)) = u.rounds

/-- A section, in the form in which the lemmas on a run at an address take it. -/
theorem stretch_back {ss : List (Step W Y)} {a : Addr} {n len : Nat} (h : InStretch ss a n len)
    (hl : 0 < len) (hf : n + len ≤ ss.length) :
    ss.any (·.addr == a) = true ∧ (ss.takeWhile fun s => s.addr != a).length = n ∧
      (ss.filter fun s => s.addr == a).length = len ∧
      (ss.drop (ss.takeWhile fun s => s.addr != a).length).take
        (ss.filter fun s => s.addr == a).length = ss.filter fun s => s.addr == a := by
  have e1 : ss.filter (fun s => s.addr == a) = (ss.drop n).take len :=
    filter_stretch (fun s : Step W Y => s.addr == a) ss n len h.front h.own h.behind
  have e2 : (ss.filter fun s => s.addr == a).length = len := by
    rw [e1, List.length_take, List.length_drop]
    omega
  have e3 : ss.takeWhile (fun s => s.addr != a) = ss.take n := by
    refine takeWhile_stretch (fun s : Step W Y => s.addr == a) ss n h.front fun x hx => ?_
    refine h.own x ?_
    cases hd : ss.drop n with
    | nil =>
      rw [hd] at hx
      cases hx
    | cons y l =>
      rw [hd] at hx
      cases hx
      obtain ⟨j, rfl⟩ : ∃ j, len = j + 1 := ⟨len - 1, by omega⟩
      exact List.mem_cons_self
  have e4 : (ss.takeWhile fun s => s.addr != a).length = n := by
    rw [e3, List.length_take]
    omega
  refine ⟨?_, e4, e2, by rw [e4, e2, e1]⟩
  have hne : 0 < (ss.filter fun s => s.addr == a).length := by rw [e2]; exact hl
  obtain ⟨y, hy⟩ := List.exists_mem_of_length_pos hne
  exact List.any_eq_true.2 ⟨y, (List.mem_filter.1 hy).1, (List.mem_filter.1 hy).2⟩

/-! ## 3 One part of a list -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
  (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
  (hpl : F.planOk = true) (hρ : ρ.due F = true) (hsil : silentAt F H w₀ rc x ρ = none)
  (hP : PlanServes H w₀ rc R) (T : ThreadsP F Bk H w₀ rc x k R)
include h hR hpl hρ hsil hP

omit hP in
/-- **What one part of a list of the first chain is owed, at one run.** `S`: where its rounds are;
`n`: how many of the chain's rounds come before. `hl`: the book gives it its carried blocks. `hbud`,
`hon`: the side's two hypotheses, at this part. -/
theorem owed_part_first
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {σ : Side F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {pre t : List (Block F.S₁ F.Cl)} {i n : Nat} (hpl' : σ.block.place = L.place)
    (S : StandsAt F.first.blocksInOrder R.first σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hl : ∃ ca, carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca)
    (hbud : L.bud u.number ((ρ.first.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 0) (u.rounds.map (·.2.length))
        (((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length)).sum))
    (hon : ∀ m ca, InsideOf .own Bk 0 H.first σ.block (T.I₁ pre.length) i k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.1.take n)) →
      m.seen = roundsOf (r.run.played.1.take n) →
      carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
      L.On u ca m ((laidOf F ρ (r.run.played.1.take n) [] []).front 0
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))) :
    L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩) ∧
      (r.called ⟨L.place, u.number⟩ = true → ∃ ca m,
        carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca ∧
        orRefused (midAtW F Bk H w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m ∧
        L.On u ca m (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
          ⟨L.place, u.number⟩)) := by
  have P := (F.planOk_ok).1 hpl
  have hp := P.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  have hstr := S.str
  have hown := S.own
  have hfit := S.fits
  rw [hpl', ← hn] at hstr
  rw [← hn] at hown hfit
  obtain ⟨ha, htw, hfl, hseg⟩ := stretch_back hstr S.pos hfit
  have hA := at_first h hR o₁ o₂ o₃ hp ha
  have hRO := (runOk_of h).1
  refine ⟨?_, fun hc => ?_⟩
  · rw [drawnAt_of hA hstr,
      askedAt_of hA hstr (treeAsks F ρ 0) (runC_asks h hR o₁ o₂ o₃ 0)]
    have e1 : ((R.first.drop n).take u.rounds.length).map (·.oracles.length) =
        u.rounds.map (·.2.length) := by
      have g := congrArg (List.map (·.2.length)) hown
      rw [List.map_map] at g
      exact g
    have e2 : (R.first.take n).map (·.oracles.length) =
        ((rowsOfChain F.first.blocksInOrder).take n).map (·.2.length) := by
      rw [← steps_pairs s1, ← List.map_take, List.map_map]
      rfl
    rw [e1, e2]
    exact hbud
  · obtain ⟨ca, hca⟩ := hl
    obtain ⟨m, hm, hin, hseen⟩ := thread_in_first h hR hpl hρ hsil T.I₁ T.h₁ T.a₁
      S.cut
      (Nat.lt_of_lt_of_le S.pos (Nat.le_trans (Nat.le_add_left _ _) S.le)) i
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right S.pos) S.le) ha hseg (htw.trans hn) hc
    rw [← hn] at hin hseen
    refine ⟨ca, m, hca, orRefused_some hm, ?_⟩
    have hb := before_first h hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 0)
      (shown_is hRO 0 (by decide)) (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
    rw [htw] at hb
    rw [hb, asked_is r.run hRO]
    exact hon m ca hin hseen hca

omit hP in
/-- **What one part of a list of the shared chain is owed, at one run.** `S`: where its rounds are;
`n`: how many of the chain's rounds come before. `hl`: the book gives it its carried blocks. `hbud`,
`hon`: the side's two hypotheses, at this part. -/
theorem owed_part_shared
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {σ : Side F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    {u : Member Empty (Common W₀ Rc Ky) X₀ Ky}
    {pre t : List (Block F.S₂ F.Cl)} {i n : Nat} (hpl' : σ.block.place = L.place)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hl : ∃ ca, carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca)
    (hbud : L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
        (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum))
    (hon : ∀ m ca, InsideOf .shared Bk 1 H.shared σ.block (T.I₂ pre.length) i k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.2.1.take n)) →
      m.seen = roundsOf (r.run.played.2.1.take n) →
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      L.On u ca m ((laidOf F ρ [] (r.run.played.2.1.take n) []).front 1
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))) :
    L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩) ∧
      (r.called ⟨L.place, u.number⟩ = true → ∃ ca m,
        carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca ∧
        orRefused (midSharedAtW F Bk H w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m ∧
        L.On u ca m (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
          ⟨L.place, u.number⟩)) := by
  have P := (F.planOk_ok).1 hpl
  have hp := P.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  have hstr := S.str
  have hown := S.own
  have hfit := S.fits
  rw [hpl', ← hn] at hstr
  rw [← hn] at hown hfit
  obtain ⟨ha, htw, hfl, hseg⟩ := stretch_back hstr S.pos hfit
  have hA := at_shared h hR o₁ o₂ o₃ hp ha
  have hRO := (runOk_of h).1
  refine ⟨?_, fun hc => ?_⟩
  · rw [drawnAt_of hA hstr,
      askedAt_of hA hstr (treeAsks F ρ 1) (runC_asks h hR o₁ o₂ o₃ 1)]
    have e1 : ((R.shared.drop n).take u.rounds.length).map (·.oracles.length) =
        u.rounds.map (·.2.length) := by
      have g := congrArg (List.map (·.2.length)) hown
      rw [List.map_map] at g
      exact g
    have e2 : (R.shared.take n).map (·.oracles.length) =
        ((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length) := by
      rw [← steps_pairs s2, ← List.map_take, List.map_map]
      rfl
    rw [e1, e2]
    exact hbud
  · obtain ⟨ca, hca⟩ := hl
    obtain ⟨m, hm, hin, hseen⟩ := thread_in_shared h hR hpl hρ hsil T.I₂ T.h₂ T.a₂
      S.cut
      (Nat.lt_of_lt_of_le S.pos (Nat.le_trans (Nat.le_add_left _ _) S.le)) i
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right S.pos) S.le) ha hseg (htw.trans hn) hc
    rw [← hn] at hin hseen
    refine ⟨ca, m, hca, orRefused_some hm, ?_⟩
    have hb := before_shared h hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 1)
      (shown_is hRO 1 (by decide)) (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
    rw [htw] at hb
    rw [hb, asked_is r.run hRO]
    exact hon m ca hin hseen hca

/-- **What one part of a list of the second chain is owed, at one run.** `S`: where its rounds are;
`n`: how many of the chain's rounds come before. `hl`: the book gives it its carried blocks. `hbud`,
`hon`: the side's two hypotheses, at this part. -/
theorem owed_part_second
    {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {σ : Side F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {pre t : List (Block F.S₃ F.Cl)} {i n : Nat} (hpl' : σ.block.place = L.place)
    (S : StandsAt F.second.blocksInOrder R.second σ u pre t i)
    (hn : n = (pre.flatMap (·.rounds)).length + i)
    (hl : ∃ ca, carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca)
    (hbud : L.bud u.number ((ρ.second.drop n).take u.rounds.length)
      (asksFrom (treeAsks F ρ 2) (u.rounds.map (·.2.length))
        (((rowsOfChain F.second.blocksInOrder).take n).map (·.2.length)).sum))
    (hon : ∀ m ca, InsideOf .own Bk 2 H.second σ.block (T.I₃ pre.length) i k m
        (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
          (r.run.played.2.2.take n)) →
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take n) →
      carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca →
      L.On u ca m ((laidOf F ρ r.run.played.1 r.run.played.2.1
        (r.run.played.2.2.take n)).front 2
        (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)))) :
    L.bud u.number (r.run.drawnAt ⟨L.place, u.number⟩) (r.run.askedAt ⟨L.place, u.number⟩) ∧
      (r.called ⟨L.place, u.number⟩ = true → ∃ ca m,
        carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca ∧
        orRefused (midAtW F Bk H w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m ∧
        L.On u ca m (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
          ⟨L.place, u.number⟩)) := by
  have P := (F.planOk_ok).1 hpl
  have hp := P.places
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  have hstr := S.str
  have hown := S.own
  have hfit := S.fits
  rw [hpl', ← hn] at hstr
  rw [← hn] at hown hfit
  obtain ⟨ha, htw, hfl, hseg⟩ := stretch_back hstr S.pos hfit
  have hA := at_second h hR o₁ o₂ o₃ hp ha
  have hRO := (runOk_of h).1
  refine ⟨?_, fun hc => ?_⟩
  · rw [drawnAt_of hA hstr,
      askedAt_of hA hstr (treeAsks F ρ 2) (runC_asks h hR o₁ o₂ o₃ 2)]
    have e1 : ((R.second.drop n).take u.rounds.length).map (·.oracles.length) =
        u.rounds.map (·.2.length) := by
      have g := congrArg (List.map (·.2.length)) hown
      rw [List.map_map] at g
      exact g
    have e2 : (R.second.take n).map (·.oracles.length) =
        ((rowsOfChain F.second.blocksInOrder).take n).map (·.2.length) := by
      rw [← steps_pairs s3, ← List.map_take, List.map_map]
      rfl
    rw [e1, e2]
    exact hbud
  · obtain ⟨ca, hca⟩ := hl
    obtain ⟨m, hm, hin, hseen⟩ := thread_in_second h hR hpl hρ hsil hP T.I₁ T.I₂ T.I₃ T.h₁ T.h₂ T.h₃
      T.a₁ T.a₂ T.a₃ S.cut
      (Nat.lt_of_lt_of_le S.pos (Nat.le_trans (Nat.le_add_left _ _) S.le)) i
      (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right S.pos) S.le) ha hseg (htw.trans hn) hc
    rw [← hn] at hin hseen
    refine ⟨ca, m, hca, orRefused_some hm, ?_⟩
    have hb := before_second h hR o₁ o₂ o₃ hp ha hseg (treeAsks F ρ 0) (treeAsks F ρ 1)
      (treeAsks F ρ 2) (shown_is hRO 0 (by decide)) (shown_is hRO 1 (by decide))
      (shown_is hRO 2 (by decide)) (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
    rw [htw] at hb
    rw [hb, asked_is r.run hRO]
    exact hon m ca hin hseen hca

end

end ProofFile.Honest

#print axioms ProofFile.Honest.stretch_back
#print axioms ProofFile.Honest.owed_part_first
#print axioms ProofFile.Honest.owed_part_shared
#print axioms ProofFile.Honest.owed_part_second
#print axioms ProofFile.Honest.ThreadsP
#print axioms ProofFile.Honest.StandsAt
