-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ValsBool.lean: WHAT "RETURNS" ASKS BESIDE THE STEP ON THE SHAPE, AS ONE Bool OF
THE STATE IN FRONT, at fifty members without a round of the proof file's own first chain: "behind
the batching" (25) and K9's "the one equation" (25). So that these seats can be laid in the form in
which the rule for acceptance asks a member's named tests (one Bool of the state, its rounds and its
columns). Definitions with code, and the laws that they pay the seats' premises; nothing is
evaluated.

Why a Bool must run a text. Some of the seats' premises speak at a state INSIDE the member (behind
its first run). That state is a function of the state in front: the Bool runs the same text.

  **`behindV w nU`**: vTw w at the state in front; and, where the smallness test's first run behind
    the batching returns, valsS nU at the state behind it.
  **`behindV₃ w hp nU`**: the like at a layers' link: behind that first run freeVH hp; and, where
    the free slot's run returns, valsS nU behind it.
  **`oneV`**: a Bool whose yes gives the named structure OneRest (DoorChain.lean; one way alone):
    the slots in use are told; four tests on sizes that the shape does not hold yet (termsB, madeB,
    seatsB, maskB); three tests on values (outsideV, termsV, slotsV); and, where the equation and
    its row are made, the fourth (padB: no coefficient on a pad).
  `behindV_pays`, `behindV₃_pays`, `oneV_pays`: a yes of the Bool gives the premises.
  **`behind_bool`**, **`layers_bool`**, **`equation_bool`**: the seats' "returns" at the one Bool.

Limits. oneV IS NOT A TEST ON VALUES ALONE: four of its clauses are tests on sizes that the shape
does not hold yet. WHERE AN INNER RUN REFUSES, OR THE LINK OR THE LEDGER IS MISSING, THE CLAUSE THAT
WOULD ASK THE INNER TEST IS true: a yes does not say that the inner test was asked. That a Bool
accepts in any run is not shown. UNDER THE HEAD: that it has a member is shown in scope, where the
reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three
hold together, at two named sets of public files, in a side library. At the earlier hash. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.AtFull.Shape.EquationStepAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere usedOf equation asRow St)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T fullLinks)

/-! ## 1 "Behind the batching" -/

def behindV (w : SegSort × Nat × TWhere) (nU : Array Nat) (s : S) : Bool :=
  vTw w s &&
    match bareRun k8LsTail.2 s with
    | .ok s₁ => valsS nU s₁
    | .error _ => true

theorem behindV_pays {w : SegSort × Nat × TWhere} {nU : Array Nat} {s : S}
    (h : behindV w nU s = true) :
    vTw w s = true ∧ ∀ s₁, bareRun k8LsTail.2 s = .ok s₁ → valsS nU s₁ = true := by
  unfold behindV at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, fun s₁ h₁ => ?_⟩
  have h2 := h.2
  rw [h₁] at h2
  exact h2

def behindV₃ (w : SegSort × Nat × TWhere) (hp : Layer.HPlan2) (nU : Array Nat) (s : S) : Bool :=
  vTw w s &&
    match bareRun k8LsTail.2 s with
    | .ok s₁ =>
      freeVH hp s₁ &&
        match freeRunH hp s₁ with
        | .ok s₂ => valsS nU s₂
        | .error _ => true
    | .error _ => true

theorem behindV₃_pays {w : SegSort × Nat × TWhere} {hp : Layer.HPlan2} {nU : Array Nat} {s : S}
    (h : behindV₃ w hp nU s = true) :
    vTw w s = true ∧ (∀ s₁, bareRun k8LsTail.2 s = .ok s₁ → freeVH hp s₁ = true) ∧
      ∀ s₁ s₂, bareRun k8LsTail.2 s = .ok s₁ → freeRunH hp s₁ = .ok s₂ →
        valsS nU s₂ = true := by
  unfold behindV₃ at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, fun s₁ h₁ => ?_, fun s₁ s₂ h₁ h₂ => ?_⟩
  · have h2 := h.2
    rw [h₁] at h2
    exact (Bool.and_eq_true _ _ ▸ h2).1
  · have h2 := h.2
    rw [h₁] at h2
    have h3 := (Bool.and_eq_true _ _ ▸ h2).2
    rw [h₂] at h3
    exact h3

/-! ## 2 "The one equation" -/

/-- A Bool whose yes gives OneRest (oneV_pays). Where the link or the ledger is missing it answers
by (usedOf s).isSome alone. -/
def oneV (s : S) : Bool :=
  (usedOf s).isSome &&
    match s.link?, s.fork? with
    | some L, some F =>
      let F' : Fork := { F with doorShutF := true }
      termsB L F' && madeB L F' s.st &&
        (match s.st.groups[L.check.group]? with
         | some G => seatsB L F' s.st G && maskB L.check.frame s.st G F.ns
         | none => false) &&
        outsideV L F && termsV L F' && slotsV F' &&
        (match equation L F with
         | .ok q =>
           match asRow L.check.rows L.check.frame q.1
             ({ st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } :
               St Unit) with
           | .ok y => padB y.2.st L.check.group y.1
           | .error _ => true
         | .error _ => true)
    | _, _ => true

theorem oneV_pays {s : S} (h : oneV s = true) : OneRest s := by
  unfold oneV at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  refine ⟨h0, fun L F hL hF => ?_, fun L F hL hF => ?_, fun L F q F' y hL hF hq hy => ?_⟩
  · rw [hL, hF] at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, -⟩, -⟩, -⟩, -⟩ := h1
    refine ⟨a1, a2, ?_⟩
    cases hG : s.st.groups[L.check.group]? with
    | none => rw [hG] at a3; exact nomatch a3
    | some G =>
      rw [hG] at a3
      have a3' : (seatsB L { F with doorShutF := true } s.st G &&
        maskB L.check.frame s.st G F.ns) = true := a3
      rw [Bool.and_eq_true] at a3'
      exact ⟨G, rfl, a3'.1, a3'.2⟩
  · rw [hL, hF] at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨⟨⟨-, b1⟩, b2⟩, b3⟩, -⟩ := h1
    exact ⟨b1, b2, b3⟩
  · rw [hL, hF] at h1
    simp only [Bool.and_eq_true] at h1
    have c := h1.2
    rw [hq] at c
    dsimp only at c
    rw [hy] at c
    exact c

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 3 The seats' "returns" at the one Bool -/

theorem behind_bool (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : Nat) (hm : m < 25)
    (hs : subAt m ≠ .layers) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (w : SegSort × Nat × TWhere) (L : Link S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧ Bs.G₀.built[m]? = some Xl ∧
      testsWhere Zp.p.X m 0 = some w ∧ cF.links[m]? = some L ∧
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps m + 1]? =
        some L.behindB ∧
      ∀ (s : S) (t : ChainSh),
        behindG (gTw w) (ProofFile.k8ParW Zp Bs.G₀ Xl m).nU (chainSh s) = .ok t →
        behindV w (ProofFile.k8ParW Zp Bs.G₀ Xl m).nU s = true → ∃ s', L.runBehind s = .ok s' := by
  obtain ⟨Bs, Xl, w, L, a1, a2, a3, a4, a5, -, hr⟩ := behind_named h m hm hs
  refine ⟨Bs, Xl, w, L, a1, a2, a3, a4, a5, fun s t hg hv => ?_⟩
  obtain ⟨v1, v2⟩ := behindV_pays hv
  exact hr s t hg v1 v2

theorem layers_bool (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH) (hp : Layer.HPlan2) (w : SegSort × Nat × TWhere)
        (L : Link S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[2 * g]? = some Xl ∧ Bs.G₀.W.G[g]? = some hp ∧
      testsWhere Zp.p.X (2 * g) 0 = some w ∧ cF.links[2 * g]? = some L ∧
      (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[batchAt fullLinks P5J.At.ps (2 * g) + 1]? =
        some L.behindB ∧
      ∀ (s : S) (t : ChainSh),
        behindG₃ (gTw w) freeG (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)).nU (chainSh s) = .ok t →
        behindV₃ w hp (ProofFile.k8ParW Zp Bs.G₀ Xl (2 * g)).nU s = true →
        ∃ s', L.runBehind s = .ok s' := by
  obtain ⟨Bs, Xl, hp, w, L, a1, a2, a3, a4, a5, a6, -, hr⟩ := layers_named h g hg
  refine ⟨Bs, Xl, hp, w, L, a1, a2, a3, a4, a5, a6, fun s t hgg hv => ?_⟩
  obtain ⟨v1, v2, v3⟩ := behindV₃_pays hv
  exact hr s t hgg v1 v2 v3

theorem equation_bool (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (L : Link S ProofFile.Cl) (b : Block S ProofFile.Cl), cF.links[l]? = some L ∧
      cF.blocksInOrder[14 * l + L.hear.length + 4 + 0]? = some b ∧
      ∀ s rs gs u, oneGS (chainSh s) = .ok u → oneV s = true →
        ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨L, b, a1, a2, -, hr⟩ := equation_step_at h l hl
  exact ⟨L, b, a1, a2, fun s rs gs u hg hv => hr s rs gs u hg (oneV_pays hv)⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.behindV_pays
#print axioms Johnson.AtFull.Shape.behindV₃_pays
#print axioms Johnson.AtFull.Shape.oneV_pays
#print axioms Johnson.AtFull.Shape.behind_bool
#print axioms Johnson.AtFull.Shape.layers_bool
#print axioms Johnson.AtFull.Shape.equation_bool
#print axioms Johnson.AtFull.Shape.behindV
#print axioms Johnson.AtFull.Shape.behindV₃
#print axioms Johnson.AtFull.Shape.oneV
