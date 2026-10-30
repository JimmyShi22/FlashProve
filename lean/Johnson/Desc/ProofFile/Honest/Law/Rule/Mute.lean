-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Mute.lean: `rule_views` (Honest/Law/Rule/Row.lean) and
`one_exact_at` (Honest/Law/Rule/OneAt.lean) from a form of their hypothesis `Owed`
(Honest/Owed.lean) in which two fields of `Good` (Honest/Side.lean) ask nothing. `Owed` asks `Good`
of every list of parts, at the list's own parameters `A` and `B`. Two fields of `Good`, `plays` and
`acc`, have `A` as a hypothesis. Here a list is muted: its `A` and `B` are set to "never". `Owed`
asks `Good` with what the field `opened` holds beside `A` and `B` (`Lettered.withField`,
Honest/Owed.lean): beside "never" that is still never.

At a muted list `plays` and `acc` hold vacuously. They are made vacuous on purpose. Whoever wants
these two fields takes the lists `G`, not `G.mute`. What is proved is that the two theorems do not
need them: their conclusions, stated at `G`, follow from `Owed` at `G.mute`. The conclusions name
`G` through `G.prover H`, `G.sims` and `G.owns`, which do not see the muting.

  1  `Lettered.mute`, `Sides.mute`   the two definitions
  2  `side_mute`, `owedAt_mute`, `addrsOf_mute`, `prover_mute`, `sims_mute`, `owns_mute`,
     `seated_mute`   what does not see the muting
  3  `goodAt_mute`   `goodAt` at a muted list, in the form in which `Owed.good` asks it
     (`Lettered.withField`), from `Good` at any `A` and `B`
  4  `Owed.mute`   `Owed` at `G` gives `Owed` at `G.mute`
  5  `rule_views_mute`, `one_exact_at_mute`   the two theorems' conclusions at `G`, from `Owed` at
     `G.mute`

Limits.
  * The other seven fields of `Owed` are asked as before, `runs` and `owed` among them. Nothing here
    proves them.
  * The statements of `rule_views_mute` and `one_exact_at_mute` are those of `rule_views` and
    `one_exact_at`, with `G.mute` for `G` in the hypothesis `hO` alone. All limits of these two
    theorems' files hold here.
  * What is proved is that the content of `plays` and `acc` is not needed for the two conclusions.
    By `Owed.mute` the two muted forms are strengthenings: `rule_views` and `one_exact_at` follow
    from them.
  * Only these two conclusions are freed. `Owed` at `G` still asks `acc` at the lists' own
    parameters, with what the field holds beside `A`.
  * Hypotheses that the prose above does not name: `Draws.due` (the challenges are such as the
    description's rounds can draw; the first chain's last challenge is the empty one):
    `rule_views_mute`, `one_exact_at_mute`; `silentAt … = none` (the honest side does not stop at
    these challenges, or the request has no trace): `rule_views_mute`; `DataFits`
    (Honest/Law/StratWords.lean): `one_exact_at_mute`; `Rel`: `rule_views_mute`; `TiedAt`:
    `one_exact_at_mute`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Row
import Johnson.Desc.ProofFile.Honest.Law.Rule.OneAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (FileDescription Block Place OpenedColumn)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK SgX)

/-! ## 1 The two definitions -/

section Row
variable {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type}

/-- The list of parts with its two parameters `A` and `B` set to "never". `A` and `B` are the
conditions before and after the list's place in `Good.plays` and `Good.acc` (Honest/Side.lean), and
`A` is a hypothesis of both: so at a muted list these two fields hold vacuously. Place, parts,
simulators, `On` and `bud` are unchanged. -/
def Lettered.mute (L : Lettered Bk S Cl V W Y Pb) : Lettered Bk S Cl V W Y Pb :=
  { L with A := fun _ _ _ _ => False, B := fun _ _ _ _ => False }

/-- A muted list's side is the list's. -/
theorem side_mute (L : Lettered Bk S Cl V W Y Pb) (bs : List (Block S Cl)) (fs : List (Fall S)) :
    L.mute.side bs fs = L.side bs fs := rfl

/-- What has to be proved of a list at one run's values (`owedAt`) does not see the muting. -/
theorem owedAt_mute (L : Lettered Bk S Cl V W Y Pb) (bs : List (Block S Cl)) (k : Coins Bk)
    (chain : Nat) (mid : Addr → Except Refusal (Mid W Y)) (r : Run)
    (st : List (Nat × Nat × List UInt64)) (called : Addr → Bool) :
    L.mute.owedAt bs k chain mid r st called ↔ L.owedAt bs k chain mid r st called := Iff.rfl

/-- `goodAt` at a muted list with what the field holds beside its `A` and `B`, from `Good` at any
`A` and `B`: `fits`, `exact` and `fresh` are taken; `plays` and `acc` hold vacuously. The form
without the field: `goodAt_mute_plain`, Honest/Thread/FileOwedMute.lean. -/
theorem goodAt_mute {L : Lettered Bk S Cl V W Y Pb} {φ : Face V W Pb} {bs : List (Block S Cl)}
    {ord : List Place} {chain ft skip : Nat} {fs : List (Fall S)} {base : List OpenedColumn}
    {earlier : List (Nat × Nat × List Fmt.DeclaredRound)}
    (h : ∀ σ, L.side bs fs = some σ →
      ∃ A' B', Good (preOf chain ft earlier bs L.place) φ σ Bk ord chain ft A' B' L.On L.bud) :
    (L.mute.withField chain ft bs base skip).goodAt earlier φ bs ord chain ft fs := by
  intro σ hσ
  obtain ⟨A', B', g⟩ := h σ hσ
  exact
    { fits := g.fits
      plays := fun _ _ _ _ _ hA => hA.1.elim
      acc := fun _ _ _ _ _ hA => hA.1.elim
      exact := g.exact
      fresh := g.fresh }

/-- The addresses of muted lists are the lists'. -/
theorem addrsOf_mute : ∀ l : List (Lettered Bk S Cl V W Y Pb),
    addrsOf (l.map Lettered.mute) = addrsOf l
  | [] => rfl
  | L :: l => by
    have ih := addrsOf_mute l
    unfold addrsOf at ih ⊢
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih]
    rfl

end Row

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- The lists of parts of a description's three chains, each muted. The falls are unchanged. -/
def Sides.mute {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X) :
    Sides F Bk W₀ Rc Ky Tr X₀ X :=
  { G with first := G.first.map Lettered.mute, shared := G.shared.map Lettered.mute,
           second := G.second.map Lettered.mute }

/-! ## 2 What does not see the muting -/

section File
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop}

/-- The prover whose sides are the muted lists is the prover whose sides are the lists. -/
theorem prover_mute (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) :
    G.mute.prover H = G.prover H := by
  unfold Sides.prover Sides.mute
  simp only [List.map_map]
  rfl

/-- The simulators of the muted lists are the lists'. -/
theorem sims_mute (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : G.mute.sims = G.sims := by
  unfold Sides.sims Sides.mute
  simp only [List.flatMap_map]
  rfl

/-- The test `owns` does not see the muting. -/
theorem owns_mute (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : G.mute.owns = G.owns := by
  unfold Sides.owns Sides.mute
  simp only [addrsOf_mute]

/-- The test `seated` does not see the muting. -/
theorem seated_mute (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : G.mute.seated = G.seated := by
  unfold Sides.seated Sides.mute
  simp only [List.all_map]
  rfl

/-! ## 3 `Owed` at the muted lists -/

/-- `Owed` at the lists gives `Owed` at the muted lists. -/
theorem Owed.mute (hO : Owed F Bk H G Rel) : Owed F Bk H G.mute Rel where
  plan := hO.plan
  book := hO.book
  places := hO.places
  seats := (seated_mute G).trans hO.seats
  good :=
    ⟨fun L hL => by
        obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
        exact goodAt_mute fun σ hσ => ⟨_, _, hO.good.1 L₀ h₀ σ hσ⟩,
      fun L hL => by
        obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
        exact goodAt_mute fun σ hσ => ⟨_, _, hO.good.2.1 L₀ h₀ σ hσ⟩,
      fun L hL base skip => by
        obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
        exact goodAt_mute fun σ hσ => ⟨_, _, hO.good.2.2 L₀ h₀ base skip σ hσ⟩⟩
  input := hO.input
  runs := by
    rw [prover_mute]
    exact hO.runs
  owed := by
    rw [prover_mute]
    intro w₀ rc x hrel k ρ r hρ hsil hrun
    obtain ⟨a, b, c⟩ := hO.owed w₀ rc x hrel k ρ r hρ hsil hrun
    refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_⟩
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact a L₀ h₀
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact b L₀ h₀
    · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
      exact c L₀ h₀

/-! ## 4 The two theorems -/

/-- The conclusion of `rule_views` at `G`, from `Owed` at `G.mute`. -/
theorem rule_views_mute (hO : Owed F Bk H G.mute Rel) (hE : G.owns = true) :
    ∀ w₀ rc x, Rel w₀ rc x → ∀ ρ : Draws, ρ.due F = true →
      silentAt F (G.prover H) w₀ rc x ρ = none →
      (unif (Coins Bk)).map (fun k => outcomeC F Bk (G.prover H) w₀ rc x k ρ) =
        session F Bk G.sims H.key x ρ (storedShown (H.storedWords w₀ rc) (storedAsks F ρ)) := by
  have h := rule_views hO ((owns_mute G).trans hE)
  rw [prover_mute, sims_mute] at h
  exact h

end File

section Join
variable {I X RI Seed Ans Xi Ky Tr X₀ Xh TF TJ T3 R2 R3 : Type} {ans : I → RI → Seed → Ans}
  {Ryes : I → X → Prop} {wr : X × (Seed × Ans) → Xi} {Cm : Committer I RI Seed X Xi Ky}
  {kp : Seed × Ans → Ky} {n : ℕ} {C : CK} {D : WholeD} {tF : TF} {tJ : TJ} {t3 : T3}
  {F : FileDescription Xi} {silent : Xi → TF → TJ → T3 → Bool} {Bk : ProverCoinCounts} {sh : Ky → F.S₂}
  {front : ℕ → R2 → R3 → I → RI → Seed → Xi → TF} {join : R2 → I → RI → Seed → TJ}
  {seam : R2 → R3 → I → RI → Seed → Xi → T3} {pubJ : ℕ → R2 → R3 → Xi → TF × TJ × T3}
  [Fintype R2] [Nonempty R2] [Fintype R3] [Inhabited R3] {H : Prover I RI Xi Ky Tr X₀ Xh}
  {G : Sides F Bk I RI Ky Tr X₀ Xh}

/-- The conclusion of `one_exact_at` at `G`, from `Owed` at `G.mute`. -/
theorem one_exact_at_mute (h : TiedAt ans wr Cm kp n D F sh front join seam pubJ)
    (hO : Owed F Bk (Cm.prover H) G.mute (relAt ans Ryes wr)) (hE : G.owns = true)
    (hD : DataFits F D)
    (w : I × RI × Seed)
    (a : X × (Seed × Ans)) (ha : a.2 = (w.2.2, ans w.1 w.2.1 w.2.2) ∧ Ryes w.1 a.1)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hρ : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Hid w (wr
          a)) :
    (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.output w
          (wr a) ρ =
      simOne C D tF tJ t3 F silent Bk G.sims (Cm.prover H).key (pubJ n)
        (honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover (Cm.prover H))
      (fun r2 r3 => Cm.seam (front n r2 r3) (join r2) (seam r2 r3)) sh (Cm.ext D.a)).one.Bad (wr a)
          ρ
        ((batchOf C D tF tJ t3 F silent).loc.extAns (wr a) ρ (Cm.ext D.a w)) := by
  have h' := one_exact_at h hO ((owns_mute G).trans hE) hD w a ha ρ hdue (by
    rw [prover_mute]
    exact hρ)
  rw [prover_mute, sims_mute] at h'
  exact h'

end Join

end ProofFile.Honest

#print axioms ProofFile.Honest.side_mute
#print axioms ProofFile.Honest.owedAt_mute
#print axioms ProofFile.Honest.goodAt_mute
#print axioms ProofFile.Honest.addrsOf_mute
#print axioms ProofFile.Honest.prover_mute
#print axioms ProofFile.Honest.sims_mute
#print axioms ProofFile.Honest.owns_mute
#print axioms ProofFile.Honest.seated_mute
#print axioms ProofFile.Honest.Owed.mute
#print axioms ProofFile.Honest.rule_views_mute
#print axioms ProofFile.Honest.one_exact_at_mute
#print axioms ProofFile.Honest.Lettered.mute
#print axioms ProofFile.Honest.Sides.mute
