-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/Sim/AtPure.lean: K14's SIX ROWS AT THE BOOK OF THE FRAME's MAKER `onlineProverFromPublicFiles`: under the library's head,
where `onlineProverFromPublicFiles` yields A at the head's files, AT ANY FILLING: A's description is the head's, the premise OwnClear holds of A's book,
and at A's book and A's order of places each of the six rows has a side and `Good`. No test on the book is left as a premise.

  `six_at_atPure`  **the statement**
  `kind_clause_at_return`   the shared clause of `KindPays` there, at any readers, with one premise on the sides

So at any term that is made from a return of `onlineProverFromPublicFiles` (such as the seat of the honest prover's filling, whose field `made` is such a
return) the book and the order are that return's. By `atPure_book_same` (Honest/AtPureBook.lean) the book does not hang on the
filling.

Limits. THAT `onlineProverFromPublicFiles` YIELDS IS A PREMISE, and so is the head. This file does not say that the filling's shared field is these rows'
halves: the filling's own text does that. `Good` at A := False: plays and acc are met for nothing. No property of the protocol is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sim.Book
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.BookAtUPure
import Johnson.Desc.ProofFile.Honest.K14.BookAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place Chain)
open Desc.K14 (St)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}
  {V₀ Vc Tr Y₀ Y : Type}

/-- **At the book of `onlineProverFromPublicFiles`, at any filling: OwnClear, and at each of the six rows a side and `Good`, at A := False.** -/
theorem six_at_atPure (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) {P : OnlineProverParts V₀ Vc Tr Y₀ Y}
    {A : OnlineProverWithDescription V₀ Vc Tr Y₀ Y} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.Z = Zp ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ OwnClear A.B ∧
      ∀ (W₀ Rc Ky X : Type) (weights : W₀ → Weights) (rand : Rc → TableRand) (fs : List (Fall St))
        (r : Unlettered Empty (Common W₀ Rc Ky) X Ky) (pre : List (Nat × Nat × List Fmt.DeclaredRound)),
        r ∈ simRows (simData Zp Np) (simPub Zp Np) weights rand →
        ∃ σ, Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs = some σ ∧
          Good pre .shared σ A.B (orderOf A.F) 1 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False)
            r.On r.bud := by
  obtain ⟨eZ, eF, -, -, -, -, okU⟩ := maskAtBook_at_atPure h.scope h.laid 0 hA
  obtain ⟨-, -, -, okO⟩ := spOwner_ok_at_atPure h.scope h.laid 0 hA
  have hb := atPure_book_at_head h hA
  rw [VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (P5J.pins_of_laid h.scope h.laid).1] at hb
  have hc := ownClear_of_whole h hb
  exact ⟨eZ, eF, hc, fun W₀ Rc Ky X weights rand fs r pre hr =>
    six_good h weights rand fs A.B _ hc okU okO r hr pre⟩

/-- **THE SHARED CLAUSE OF `KindPays` AT ANY RETURN OF THE MAKER**, at any filling, at any readers: at a kind of whose rows in the sides `rows` says that each has the letters of one
of the six: K14's four, K1's two at the shared chain. `rows` is the one premise on the sides. -/
theorem kind_clause_at_return (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {P : OnlineProverParts V₀ Vc Tr Y₀ Y} {A : OnlineProverWithDescription V₀ Vc Tr Y₀ Y}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {W₀ Rc Ky Tr' X₀ X : Type}
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (G : Sides A.F A.B W₀ Rc Ky Tr' X₀ X) (κ : VerifiableInference.Desc.KindName)
    (rows : ∀ L ∈ G.shared, L.place.kind = κ →
      ∃ r ∈ (simRows (simData Zp Np) (simPub Zp Np) weights rand :
          List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)),
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    ∀ L ∈ G.shared, L.place.kind = κ → ∀ σ, L.side A.F.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf A.F 1) A.F.shared.blocksInOrder L.place) .shared σ
        A.B (orderOf A.F) 1 0 A' B' L.On L.bud := by
  obtain ⟨-, eF, -, hall⟩ := six_at_atPure h hA
  have key : ∀ (F : VerifiableInference.Desc.FileDescription ProofFile.Inst),
      F = P5J.F0T OnBytes.secondHashFunction Zp Np cF → orderOf F = orderOf A.F →
      ∀ (G : Sides F A.B W₀ Rc Ky Tr' X₀ X),
      (∀ L ∈ G.shared, L.place.kind = κ →
        ∃ r ∈ (simRows (simData Zp Np) (simPub Zp Np) weights rand :
            List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)),
          L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) →
      ∀ L ∈ G.shared, L.place.kind = κ → ∀ σ, L.side F.shared.blocksInOrder G.falls₂ = some σ →
        ∃ A' B', Good (preOf 1 0 (earlierOf F 1) F.shared.blocksInOrder L.place) .shared σ
          A.B (orderOf F) 1 0 A' B' L.On L.bud := by
    intro F e eo G rows L hL hk σ hσ
    subst e
    obtain ⟨r, hr, c1, c2, c3, c4⟩ := rows L hL hk
    obtain ⟨σ', h1, h2⟩ := hall W₀ Rc Ky X₀ weights rand G.falls₂ r
      (preOf 1 0 (earlierOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 1)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder L.place) hr
    have e : σ' = σ := by
      unfold Lettered.side at hσ
      rw [c1, c2] at hσ
      exact Option.some.inj (h1.symm.trans hσ)
    subst e
    rw [c3, c4, eo]
    exact ⟨_, _, h2⟩
  exact key _ eF rfl G rows

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.kind_clause_at_return
#print axioms ProofFile.Honest.K14.six_at_atPure
