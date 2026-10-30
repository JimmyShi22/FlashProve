-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: on₁ of the kind K12 at the sides of the return, at the named first thread.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/K12OnAtTheG.lean: onAtRun_at_letters (LeftAtLetters.lean) at every list of the
kind K12 in the first chain of theGOfReturn: the form of on₁ in k12_share_at_theGOfReturn
(AtFullSide/K12/ShareK12.lean).

  onAtRun₁_of_bare    On at a run reads of a list what its bare row holds
  k12_on_of_rows      general in the sides, at any description equal to the head's
  k12_on₁_at_the_g    at theGOfReturn, for a family Th whose first invariant is the named one

By: k12_rows_theG (AtFullSide/M1/KindRowsTheG.lean): the list's bare row is a row of the value;
mem_rowsOfLot: it is the row of a job; theGOfReturn_prover: the prover is the maker's.

Premises. made, hd: the return and the head. h₄: K holds the kind's lot. hI: each member of the family has the
named first invariant: T's field I₁, in HEq across the two descriptions, as threadsAtRelation_I gives
it. The rest as on₁ has them; silentAt = none is not read.

Limits. That a list of the kind stands in G is not said here. That Th meets hI is its caller's.

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). They call
onAtRun_at_letters, which bears the label; that file's ground stands here: first kind T, hI, hR, hrun;
hρ public; second kind: hR. Of neither kind: made, hd, K, h₄. The label bars a premise, never a
theorem. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.LeftAtLetters
import AtFullSide.M1.KindRowsTheG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription KindName)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (baseMaker baseFilling matrixInput)
open AtFullSide.Honest AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.TheG (ThreadParts theGOfReturn theGOfReturn_prover)
open AtPublicFiles.TheSides (KindRows)

/-- **On at a run reads of a list what its bare row holds.** -/
theorem onAtRun₁_of_bare {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {G : Sides F Bk W₀ Rc Ky Tr X₀ X} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X} (T : ThreadsP F Bk (G.prover H) w₀ rc x k R)
    {ρ : Draws} {r : RunC F}
    {L L' : Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (e : L.bare = L'.bare) (h : OnAtRun₁ T ρ r L') : OnAtRun₁ T ρ r L := by
  obtain ⟨p, row, A₁, B₁, On, bud⟩ := L
  obtain ⟨p', row', A₂, B₂, On', bud'⟩ := L'
  simp only [Lettered.bare, Unlettered.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  exact h

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

/-- **On at every list of the kind, from where those lists come.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem k12_on_of_rows {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    {F : FileDescription ProofFile.Inst} (e : F = hd.description)
    {G : Sides F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit} (hP : G.prover A.H = A.H)
    (rows : ∀ L ∈ G.first, L.place.kind = KindName.K12 →
      L.bare ∈ rowsOfLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref A.Z A.G)
    {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B} {ρ : Draws}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit} {r : RunC F}
    (T : ThreadsP F A.B (G.prover A.H) w₀ rc x k R)
    (hI : HEq T.I₁ (fun b => ThrS (thread₁ hd R) (said₁ hd R) b))
    (hρ : ρ.due F = true)
    (hR : ready F A.B (G.prover A.H) w₀ rc x k = .ok R)
    (hrun : runC F A.B (G.prover A.H) w₀ rc x k ρ = .ok r) :
    ∀ L ∈ G.first, L.place.kind = KindName.K12 → OnAtRun₁ T ρ r L := by
  subst e
  have hI' := eq_of_heq hI
  intro L hL hk
  obtain ⟨pl, hfin, -, eL⟩ := mem_rowsOfLot matrixInput OnBytes.HonestTrace.Sz.ref A.Z A.G _
    (rows L hL hk)
  obtain ⟨Bs, base, O⟩ := hd.head.laid.opened
  obtain ⟨-, hG, -⟩ := atPure_ok made
  have eG : Bs.G₀ = A.G := Option.some.inj (O.blank.symm.trans hG)
  have hf : finishWritten = some pl := by
    rw [← finish_at_head hd.head.toAtMg O, eG]
    exact hfin
  have hH : (G.prover A.H).first = A.H.first := by rw [hP]
  exact onAtRun₁_of_bare T (L' := (rowOfJob A.Z (jobOfLot matrixInput OnBytes.HonestTrace.Sz.ref A.Z
    A.G pl)).lay (fun _ => thread₁ hd R) (fun _ => said₁ hd R) []) eL
    (onAtRun_at_letters hd made hf T (fun k s m E a => by rw [hI'] at a; exact a) hρ hR hrun hH _ _ _)

/-- **on₁ of the kind K12 at the sides of the return.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem k12_on₁_at_the_g {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}
    (made : baseMaker files = .ok A) (hd : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G)
    (h₄ : simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots)
    {Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop}
    (Th : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready A.F A.B ((theGOfReturn made hd T K).prover A.H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B ((theGOfReturn made hd T K).prover A.H) w₀ rc x k R)
    (hI : ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready A.F A.B ((theGOfReturn made hd T K).prover A.H) w₀ rc x k = .ok R),
      HEq (Th w₀ rc x hrel k R hR).I₁ (fun b => ThrS (thread₁ hd R) (said₁ hd R) b)) :
    ∀ w₀ rc x (hrel : Rel w₀ rc x) k R
      (hR : ready A.F A.B ((theGOfReturn made hd T K).prover A.H) w₀ rc x k = .ok R) ρ r,
      ρ.due A.F = true → silentAt A.F ((theGOfReturn made hd T K).prover A.H) w₀ rc x ρ = none →
      runC A.F A.B ((theGOfReturn made hd T K).prover A.H) w₀ rc x k ρ = .ok r →
      ∀ L ∈ (theGOfReturn made hd T K).first, L.place.kind = KindName.K12 →
        OnAtRun₁ (G := theGOfReturn made hd T K) (H := A.H) (Th w₀ rc x hrel k R hR) ρ r L :=
  fun w₀ rc x hrel k R hR _ _ hρ _ hrun =>
    k12_on_of_rows made hd (atPure_at_laid hd.head.laid made).2
      (theGOfReturn_prover made hd T K) (AtFullSide.M1.k12_rows_theG hd T K made h₄)
      (Th w₀ rc x hrel k R hR) (hI w₀ rc x hrel k R hR) hρ hR hrun

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onAtRun₁_of_bare
#print axioms ProofFile.Honest.K12.Sim2.k12_on_of_rows
#print axioms ProofFile.Honest.K12.Sim2.k12_on₁_at_the_g
