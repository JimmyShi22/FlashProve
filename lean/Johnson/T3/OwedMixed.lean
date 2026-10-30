-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OwedMixed.lean: each list's On in the form OnAtRun₁₋₃ (Honest/Law/OwedAtRun.lean), from one of two others that a list may owe: from the
thread and what is said, at every front true to the stand (OnFromS); or at a run that has returned, at the run's own front (RunOn₁₋₃).

1.  RunOn₁, RunOn₂, RunOn₃: On at a run, at the list, at every input of Rel.
2.  debt₁, debt₂, debt₃: one list's clause of OnDebts from OnFromS: the three branches of onDebts_of_onFromS, at one list.
3.  ready_of_same: ready returns at a prover with the same halves, range and trace: its key and stored columns may differ.
4.  partsStand_of_hand, ThreadDebts, onAtRun₁₋₃_of_fromS, onAtRun₁₋₃_of_runOn.
5.  Conditional lemmas on this library's definitions. They restate what is asked of a list; none of it is shown here.
-/
import Johnson.T3.OwedAtTheDoor
import Johnson.Desc.ProofFile.Honest.Law.OwedAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-! ## 1 On at runs, one list at a time -/

section Run
variable (F : FileDescription Xi) (Rel : W₀ → Rc → Xi → Prop) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X)

/-- **On at the runs, at one list of the first chain**: OnAtRun's clause on₁ at the list L, at every input of Rel. -/
def RunOn₁ (L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop :=
  ∀ w₀ rc x, Rel w₀ rc x → ∀ k ρ r, ρ.due F = true → silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
    ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, r.called ⟨L.place, u.number⟩ = true →
    ∀ ca m, carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
    orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    L.On u ca m (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
      ⟨L.place, u.number⟩)

/-- The same at one list of the shared chain. -/
def RunOn₂ (L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky) : Prop :=
  ∀ w₀ rc x, Rel w₀ rc x → ∀ k ρ r, ρ.due F = true → silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
    ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, r.called ⟨L.place, u.number⟩ = true →
    ∀ ca m, carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
    orRefused (midSharedAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    L.On u ca m (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
      ⟨L.place, u.number⟩)

/-- The same at one list of the second chain. -/
def RunOn₃ (L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop :=
  ∀ w₀ rc x, Rel w₀ rc x → ∀ k ρ r, ρ.due F = true → silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F Bk (G.prover H) w₀ rc x k ρ = .ok r →
    ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, r.called ⟨L.place, u.number⟩ = true →
    ∀ ca m, carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca →
    orRefused (midAtW F Bk (G.prover H) w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
    L.On u ca m (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
      ⟨L.place, u.number⟩)

end Run

/-! ## 2 One list's clause of OnDebts from OnFromS -/

section Debt
variable {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {w₀ : W₀} {rc : Rc} {k : Coins Bk} {len : Nat → Nat → Nat}

theorem debt₁ (hS : Sits F (G.prover H) T₁ T₂ T₃) (htrue : TrueLaid F (H.storedWords w₀ rc) len)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (on₁ : ∀ b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place → OnFromS T₁ S₁ L b len) :
    ∀ σ, L.side F.first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.first.blocksInOrder = pre ++ σ.block :: t → ∀ ρ p m ca, ρ.due F = true →
    InsideOf .own Bk 0 (G.prover H).first σ.block (ThrS T₁ S₁ pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) p) →
    m.seen = roundsOf p →
    carriedAt Bk k 0 ⟨L.place, u.number⟩ u.part = .ok ca →
    L.On u ca m ((laidOf F ρ p [] []).front 0
      (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))) := by
  obtain ⟨⟨p1, c1, f1, b1, h1⟩, -, -, -, -, -⟩ := id hS
  intro σ hσ u hu pre t hcut ρ p m ca hρ hin hseen hca
  have hb : F.first.blocksInOrder[pre.length]? = some σ.block := by
    rw [hcut]
    simp
  refine on₁ pre.length σ.block hb (side_place hσ) σ (by rw [b1]; exact hσ) u hu k m _ ca _
    (insideS_of_insideOf T₁ S₁ (by rw [b1]; exact hb)
      (by rw [p1, c1, h1]; exact hin)) (by rw [c1]; exact hca) ?_
  rw [c1, hseen]
  exact htrue.one ρ p hρ

theorem debt₂ (hS : Sits F (G.prover H) T₁ T₂ T₃) (htrue : TrueLaid F (H.storedWords w₀ rc) len)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    (on₂ : ∀ b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place → OnFromS T₂ S₂ L b len) :
    ∀ σ, L.side F.shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.shared.blocksInOrder = pre ++ σ.block :: t → ∀ ρ p m ca, ρ.due F = true →
    InsideOf .shared Bk 1 (G.prover H).shared σ.block (ThrS T₂ S₂ pre.length) (σ.roundsTo u.number)
      k m (envOf (H.storedWords w₀ rc) (fun _ _ => none) p) →
    m.seen = roundsOf p →
    carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
    L.On u ca m ((laidOf F ρ [] p []).front 1
      (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))) := by
  obtain ⟨-, ⟨p2, c2, f2, b2, h2⟩, -, -, -, -⟩ := id hS
  intro σ hσ u hu pre t hcut ρ p m ca hρ hin hseen hca
  have hb : F.shared.blocksInOrder[pre.length]? = some σ.block := by
    rw [hcut]
    simp
  refine on₂ pre.length σ.block hb (side_place hσ) σ (by rw [b2]; exact hσ) u hu k m _ ca _
    (insideS_of_insideOf T₂ S₂ (by rw [b2]; exact hb)
      (by rw [p2, c2, h2]; exact hin)) (by rw [c2]; exact hca) ?_
  rw [c2, hseen]
  exact htrue.two ρ p hρ

theorem debt₃ (hS : Sits F (G.prover H) T₁ T₂ T₃) (htrue : TrueLaid F (H.storedWords w₀ rc) len)
    {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (on₃ : ∀ b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place → OnFromS T₃ S₃ L b len) :
    ∀ σ, L.side F.second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t,
    F.second.blocksInOrder = pre ++ σ.block :: t → ∀ ρ p₀ p₁ p m ca, ρ.due F = true →
    InsideOf .own Bk 2 (G.prover H).second σ.block (ThrS T₃ S₃ pre.length) (σ.roundsTo u.number) k m
      (envOf (H.storedWords w₀ rc) (taken₃ p₀ p₁) p) →
    m.seen = roundsOf p₀ ++ roundsOf p₁ ++ roundsOf p →
    carriedAt Bk k 2 ⟨L.place, u.number⟩ u.part = .ok ca →
    L.On u ca m ((laidOf F ρ p₀ p₁ p).front 2
      (storedShown (H.storedWords w₀ rc) (storedAsks F ρ))) := by
  obtain ⟨-, -, ⟨p3, c3, f3, b3, h3⟩, -, -, -⟩ := id hS
  intro σ hσ u hu pre t hcut ρ p₀ p₁ p m ca hρ hin hseen hca
  have hb : F.second.blocksInOrder[pre.length]? = some σ.block := by
    rw [hcut]
    simp
  refine on₃ pre.length σ.block hb (side_place hσ) σ (by rw [b3]; exact hσ) u hu k m _ ca _
    (insideS_of_insideOf T₃ S₃ (by rw [b3]; exact hb)
      (by rw [p3, c3, h3]; exact hin)) (by rw [c3]; exact hca) ?_
  rw [c3, hseen]
  exact htrue.three ρ p₀ p₁ p hρ

end Debt

/-! ## 3 ready at a prover with the same halves -/

/-- **ready returns at a prover with the same halves, range, named member and trace.** Its key and stored columns may differ: the shared
chain's rounds do not read the key. -/
theorem ready_of_same {F : FileDescription Xi} {B : ProverCoinCounts} {H H' : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (e₁ : H'.first = H.first) (e₂ : H'.shared = H.shared) (e₃ : H'.second = H.second)
    (e₄ : H'.inRange = H.inRange) (e₅ : H'.dummy = H.dummy) (e₆ : H'.trace = H.trace)
    (h : ready F B H w₀ rc x c = .ok R) : ∃ R', ready F B H' w₀ rc x c = .ok R' := by
  obtain ⟨hT, tr, htr, hown, -, s1, s2, s3⟩ := ready_ok h
  rw [hown] at s1 s3
  have hT' : readyTests F B H' w₀ = .ok () := by
    unfold readyTests at hT ⊢
    rw [e₁, e₂, e₃, e₄, e₅]
    exact hT
  have htr' : H'.trace w₀ x = some tr := by rw [e₆]; exact htr
  have g₂ : sharedSteps F B H' ⟨w₀, rc, H'.key x⟩ c.shared = .ok R.shared := by
    unfold sharedSteps
    have g : chainSteps B (B.rowsOf 1) (sharedLook B c.shared)
        (Face.shared.sees (⟨w₀, rc, H'.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder H'.shared =
        .ok R.shared := by
      rw [e₂]
      exact s2
    rw [g]
    rfl
  refine ⟨⟨⟨w₀, rc, x, tr⟩, ⟨w₀, rc, H'.key x⟩, R.first, R.shared, R.second⟩, ?_⟩
  unfold ready
  rw [hT', htr']
  show ((unfit (chainSteps B (B.rowsOf 0) (c.look 0)
    (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder H'.first)).bind
    fun m₁ => (sharedSteps F B H' ⟨w₀, rc, H'.key x⟩ c.shared).bind fun m₂ =>
      (unfit (chainSteps B (B.rowsOf 2) (c.look 2)
        (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H'.second)).map
        fun m₃ => (⟨⟨w₀, rc, x, tr⟩, ⟨w₀, rc, H'.key x⟩, m₁, m₂, m₃⟩ :
          Ready W₀ Rc Xi Ky Tr X₀ X)) = _
  rw [e₁, e₃, s1, g₂, s3]
  rfl

/-! ## 4 Threads, and each list's On in the form of OnAtRun -/

section Carry
variable {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
  {Rel : W₀ → Rc → Xi → Prop}

/-- **Where the parts' rounds are**, from each side's Good at any A and B. -/
theorem partsStand_of_hand (plan : F.planOk = true) (book : Bk.word F = none)
    (seats : G.seated = true)
    (hand₁ : ∀ L ∈ G.first, ∀ σ, L.side F.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf F 0) F.first.blocksInOrder L.place) .own σ Bk (orderOf F) 0 0 A' B'
        L.On L.bud)
    (hand₂ : ∀ L ∈ G.shared, ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ Bk (orderOf F) 1 0
        A' B' L.On L.bud)
    (hand₃ : ∀ L ∈ G.second, ∀ σ, L.side F.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 F.lastChainFirstTreeNumber (earlierOf F 2) F.second.blocksInOrder L.place) .own σ Bk
        (orderOf F) 2 F.lastChainFirstTreeNumber A' B' L.On L.bud)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) : PartsStand G k R := by
  have goodM : (∀ L ∈ G.mute.first,
        L.goodAt (earlierOf F 0) .own F.first.blocksInOrder (orderOf F) 0 0 G.mute.falls₁) ∧
      (∀ L ∈ G.mute.shared,
        L.goodAt (earlierOf F 1) .shared F.shared.blocksInOrder (orderOf F) 1 0 G.mute.falls₂) ∧
      ∀ L ∈ G.mute.second,
        L.goodAt (earlierOf F 2) .own F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.mute.falls₃ := by
    refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_⟩
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact goodAt_mute_plain (hand₁ L₀ h₀)
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact goodAt_mute_plain (hand₂ L₀ h₀)
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact goodAt_mute_plain (hand₃ L₀ h₀)
  have hR' : ready F Bk (G.mute.prover H) w₀ rc x k = .ok R := by rw [prover_mute]; exact hR
  have P : PartsStand G.mute k R := parts_stand plan book ((seated_mute G).trans seats) goodM hR'
  exact ⟨fun L hL => P.at₁ L.mute (List.mem_map_of_mem hL),
    fun L hL => P.at₂ L.mute (List.mem_map_of_mem hL),
    fun L hL => P.at₃ L.mute (List.mem_map_of_mem hL)⟩

/-- **What the rule asks of the threads**, as one record. -/
structure ThreadDebts (F : FileDescription Xi) (Bk : ProverCoinCounts) (P : Prover W₀ Rc Xi Ky Tr X₀ X)
    (Rel : W₀ → Rc → Xi → Prop)
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) : Prop where
  plan : F.planOk = true
  sits : ∀ w w', Sits F P (T₁ w) (T₂ w') (T₃ w)
  o₁ : ∀ w, OwesS (T₁ w) (S₁ w)
  o₂ : ∀ w, OwesS (T₂ w) (S₂ w)
  o₃ : ∀ w, OwesS (T₃ w) (S₃ w)
  n₁ : ∀ w b, SaidNext (T₁ w) (S₁ w) b
  n₂ : ∀ w b, SaidNext (T₂ w) (S₂ w) b
  n₃ : ∀ w b, SaidNext (T₃ w) (S₃ w) b
  a₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk P w₀ rc x k = .ok R →
    Enters₁ F P (T₁ R.own) w₀ rc x k R
  a₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk P w₀ rc x k = .ok R →
    Enters₂ F P (T₂ R.common) w₀ rc x k R
  d₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk P w₀ rc x k = .ok R →
    DoorBehindS F P (T₁ R.own) (T₂ R.common) (T₃ R.own) (S₁ R.own) (S₂ R.common) (S₃ R.own) x k R
  e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk P w₀ rc x k = .ok R →
    S₁ R.own 0 k { R.start₁ P with opened := some [] }
  e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready F Bk P w₀ rc x k = .ok R →
    S₂ R.common 0 k { R.start₂ P with opened := some [] }

variable {T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}

/-- The invariants that these debts give, at one run's coins. -/
def ThreadDebts.threads {P : Prover W₀ Rc Xi Ky Tr X₀ X}
    (d : ThreadDebts F Bk P Rel T₁ T₂ T₃ S₁ S₂ S₃) (w₀ : W₀) (rc : Rc) (x : Xi)
    (h : Rel w₀ rc x) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X)
    (hR : ready F Bk P w₀ rc x k = .ok R) : ThreadsP F Bk P w₀ rc x k R :=
  threadsD (T₁ R.own) (T₂ R.common) (T₃ R.own) (S₁ R.own) (S₂ R.common) (S₃ R.own) (d.sits _ _) d.plan
    (d.o₁ _) (d.o₂ _) (d.o₃ _) (d.n₁ _) (d.n₂ _) (d.n₃ _) (d.a₁ w₀ rc x h k R hR)
    (d.a₂ w₀ rc x h k R hR) (d.d₃ w₀ rc x h k R hR) (d.e₁ w₀ rc x h k R hR) (d.e₂ w₀ rc x h k R hR)

theorem trueLaid_depth (stored : Nat → Nat → Option (List UInt64)) :
    TrueLaid F stored (depthAt F) :=
  ⟨fun ρ p _ => trueTo_one F _ ρ p, fun ρ p _ => trueTo_two F _ ρ p,
    fun ρ p₀ p₁ p _ => trueTo_three F _ ρ p₀ p₁ p⟩

/-- **An On from the thread, in the form of OnAtRun₁.** -/
theorem onAtRun₁_of_fromS (d : ThreadDebts F Bk (G.prover H) Rel T₁ T₂ T₃ S₁ S₂ S₃) {w₀ : W₀} {rc : Rc}
    {x : Xi} (h : Rel w₀ rc x) {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) {ρ : Draws} (hρ : ρ.due F = true) (r : RunC F)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hF : ∀ w b blk, F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₁ w) (S₁ w) L b (depthAt F)) :
    OnAtRun₁ (G := G) (H := H) (d.threads w₀ rc x h k R hR) ρ r L :=
  fun σ hσ u hu pre t hc m ca hin hs hca _ _ _ =>
    debt₁ (d.sits R.own R.common) (trueLaid_depth (H.storedWords w₀ rc)) (hF R.own) σ hσ u hu pre t hc ρ
      _ m ca hρ hin hs hca

/-- The same at a list of the shared chain. -/
theorem onAtRun₂_of_fromS (d : ThreadDebts F Bk (G.prover H) Rel T₁ T₂ T₃ S₁ S₂ S₃) {w₀ : W₀} {rc : Rc}
    {x : Xi} (h : Rel w₀ rc x) {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) {ρ : Draws} (hρ : ρ.due F = true) (r : RunC F)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    (hF : ∀ w b blk, F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₂ w) (S₂ w) L b (depthAt F)) :
    OnAtRun₂ (G := G) (H := H) (d.threads w₀ rc x h k R hR) ρ r L :=
  fun σ hσ u hu pre t hc m ca hin hs hca _ _ _ =>
    debt₂ (d.sits R.own R.common) (trueLaid_depth (H.storedWords w₀ rc)) (hF R.common) σ hσ u hu pre t
      hc ρ _ m ca hρ hin hs hca

/-- The same at a list of the second chain. -/
theorem onAtRun₃_of_fromS (d : ThreadDebts F Bk (G.prover H) Rel T₁ T₂ T₃ S₁ S₂ S₃) {w₀ : W₀} {rc : Rc}
    {x : Xi} (h : Rel w₀ rc x) {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R) {ρ : Draws} (hρ : ρ.due F = true) (r : RunC F)
    {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hF : ∀ w b blk, F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
      OnFromS (T₃ w) (S₃ w) L b (depthAt F)) :
    OnAtRun₃ (G := G) (H := H) (d.threads w₀ rc x h k R hR) ρ r L :=
  fun σ hσ u hu pre t hc m ca hin hs hca _ _ _ =>
    debt₃ (d.sits R.own R.common) (trueLaid_depth (H.storedWords w₀ rc)) (hF R.own) σ hσ u hu pre t hc
      ρ _ _ _ m ca hρ hin hs hca

/-- **An On given at the run's own front, in the form of OnAtRun₁**, at any invariants. -/
theorem onAtRun₁_of_runOn {w₀ : W₀} {rc : Rc} {x : Xi} (h : Rel w₀ rc x) {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) {ρ : Draws}
    (hρ : ρ.due F = true) (hs : silentAt F (G.prover H) w₀ rc x ρ = none) {r : RunC F}
    (hr : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hN : RunOn₁ F Rel H G L) : OnAtRun₁ (G := G) (H := H) T ρ r L :=
  fun σ hσ u hu _ _ _ m ca _ _ hca hc hm hf => by
    rw [hf]
    exact hN w₀ rc x h k ρ r hρ hs hr σ hσ u hu hc ca m hca hm

/-- The same at a list of the shared chain. -/
theorem onAtRun₂_of_runOn {w₀ : W₀} {rc : Rc} {x : Xi} (h : Rel w₀ rc x) {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) {ρ : Draws}
    (hρ : ρ.due F = true) (hs : silentAt F (G.prover H) w₀ rc x ρ = none) {r : RunC F}
    (hr : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
    (hN : RunOn₂ F Rel H G L) : OnAtRun₂ (G := G) (H := H) T ρ r L :=
  fun σ hσ u hu _ _ _ m ca _ _ hca hc hm hf => by
    rw [hf]
    exact hN w₀ rc x h k ρ r hρ hs hr σ hσ u hu hc ca m hca hm

/-- The same at a list of the second chain. -/
theorem onAtRun₃_of_runOn {w₀ : W₀} {rc : Rc} {x : Xi} (h : Rel w₀ rc x) {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (T : ThreadsP F Bk (G.prover H) w₀ rc x k R) {ρ : Draws}
    (hρ : ρ.due F = true) (hs : silentAt F (G.prover H) w₀ rc x ρ = none) {r : RunC F}
    (hr : runC F Bk (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hN : RunOn₃ F Rel H G L) : OnAtRun₃ (G := G) (H := H) T ρ r L :=
  fun σ hσ u hu _ _ _ m ca _ _ hca hc hm hf => by
    rw [hf]
    exact hN w₀ rc x h k ρ r hρ hs hr σ hσ u hu hc ca m hca hm

end Carry

end ProofFile.Honest

#print axioms ProofFile.Honest.RunOn₁
#print axioms ProofFile.Honest.debt₁
#print axioms ProofFile.Honest.debt₂
#print axioms ProofFile.Honest.debt₃
#print axioms ProofFile.Honest.ready_of_same
#print axioms ProofFile.Honest.partsStand_of_hand
#print axioms ProofFile.Honest.ThreadDebts
#print axioms ProofFile.Honest.onAtRun₁_of_fromS
#print axioms ProofFile.Honest.onAtRun₂_of_fromS
#print axioms ProofFile.Honest.onAtRun₃_of_fromS
#print axioms ProofFile.Honest.onAtRun₁_of_runOn
#print axioms ProofFile.Honest.onAtRun₂_of_runOn
#print axioms ProofFile.Honest.onAtRun₃_of_runOn
