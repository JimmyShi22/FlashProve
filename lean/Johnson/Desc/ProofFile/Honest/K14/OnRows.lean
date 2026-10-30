-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OnRows.lean: kind K14: THE CLAUSES OF THE FRAME's DEBT on₂ (a
field of OnDebts, Honest/Law/OwedRule.lean: a row's sentence at entry follows from the frame's
sentence at the stand in front of the part) AT THE ROWS OF BOTH SENDINGS OF THE SHARED CHAIN
(sendingRows, Honest/K14/ExactRows.lean), AT THE PROOF FILE's IOP AS WRITTEN IN LEAN, UNDER THE
LIBRARY's HEAD (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). Statements with their proofs: calls. No
definition.

  onFromS_rows    **OnFromS (Honest/Thread/OnSaid.lean) at a row that has the place, the parts and
                  the sentence at entry of a row of sendingRows at the plan qAt Zp Np with "LIN
                  point" as round number 0**: at every frame's sentence T₂ whose list is the
                  description's shared list, every letter S₂, every member at the row's place,
                  every len: THE CLAUSE THAT THE PREMISE on₂ OF THE FRAME's onDebts_of_onFromS
                  (Honest/Thread/FileOwed.lean) ASKS AT SUCH A ROW. By onFrom_rows
                  (Honest/K14/OnSending.lean) and the frame's onFromS_of_onFrom; that the library
                  makes its eight sub-protocols there: plan2_at_head (Honest/K14/PlanAtHead.lean);
                  the list's form: shared_flat_at (Honest/K14/OmegaAtShared.lean) and flatOf_carried
                  (Johnson/Desc/K14/Honest/FlatForm.lean)
  on₂_row         **THE BODY OF THE FIELD on₂ AT ONE SUCH ROW**: the field's text behind "∀ L ∈
                  G.shared", typed by hand, with ThrS T₂ S₂ where the field has the letter T.I₂
                  (what the frame's threadsS lays there). Of T₂ it asks the five equations of the
                  field two of the frame's Sits (Honest/Thread/File.lean). That the front which
                  rounds as laid yield is true to these rounds is no premise: the frame's laws
                  trueTo_one, trueTo_two and trueTo_three (Honest/Law/Rule/TrueLaid.lean) are
                  called, and the term of the frame's structure TrueLaid
                  (Honest/Thread/FileOwed.lean) is written out of them where it is spent. The steps
                  are those of onDebts_of_onFromS's own proof at the field on₂
  onDebts_with_rows   CONDITIONAL. **the frame's record OnDebts at threadsS, A THREAD BUILT FROM
                  LETTERS, at any filling**: each row of the shared chain is of one of these two
                  sorts, or its own clause OnFromS is a premise; so are the clauses of the rows of
                  the two other chains: the frame's onDebts_of_onFromS with the clauses at these two
                  sorts of rows, AND AT NO OTHER, paid. The field on₂ is laid by on₂_row at these
                  rows: SO LEAN HOLDS BOTH onFromS_rows AND on₂_row AGAINST THE FIELD's OWN TYPE

WHAT IS LEFT AS THE FRAME's OWN LETTERS. In onFromS_rows and on₂_row: T₂, under the equations named;
S₂ is free; of the five equations the third (ft = 0) is idle. In onDebts_with_rows: the three
sentences T₁, T₂, T₃ with Sits; OwesS and SaidNext at each; Enters₁, Enters₂, DoorBehind; the three
starts of S₁, S₂, S₃ (each at the frame's start with the field opened laid as the frame lays it:
"some []" at the first two chains; at the last chain the two earlier chains' columns, one behind the
other, asked only at ends of these two at which the field is "some ..."); OnFromS at every row of
another sort: all as premises, as onDebts_of_onFromS has them. These letters only build the term
threadsS that stands in the conclusion's type. The test on the plan is the head's. WHETHER THE
FRAME's LETTERS CAN BE MET TOGETHER AT ANY FILLING IS NOT KNOWN. (At a filling whose only rows were
of these two sorts the prover would play nothing but the two sendings: there is ground to doubt that
they could be met there.)

What is not claimed. The field on₂ without premises: it runs over ALL rows of a filling's shared
chain, and at every row of another sort its clause is a premise here. That a frame's sentence can be
entered or holds along a run. That any filling has such rows. In on₂_row the row L is not asked to
lie in the filling G. The bound on positions. The full size alone. Nothing on what is or is not
hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OnSending
import Johnson.Desc.ProofFile.Honest.K14.PlanAtHead
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtShared
import Johnson.Desc.ProofFile.Honest.K14.AskedAtShared
import Johnson.Desc.ProofFile.Honest.Thread.FileOwed
import Johnson.Desc.ProofFile.Honest.Law.Rule.TrueLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open P5J (F0T TS)
open Desc.K14 (St)
open Desc.K14.Honest (flatOf_carried)

variable {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
  {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **OnFromS at a row that has the place, the parts and the sentence at entry of a row of
sendingRows**, under the library's head: the clause that the premise on₂ of the frame's
onDebts_of_onFromS asks at such a row. -/
theorem onFromS_rows (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    (T₂ : Thread Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hbs : T₂.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (r : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)
    (hr : r ∈ sendingRows ⟨qAt Zp Np, 0⟩ weights rand)
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky) (hplace : L.place = r.place)
    (hrow : L.row = r.row) (hOn : L.On = r.On) (b : Nat) (blk : Block St ProofFile.Cl)
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[b]? = some blk) (hp : blk.place = L.place)
    (len : Nat → Nat → Nat) : OnFromS T₂ S₂ L b len := by
  obtain ⟨sentU, layO, hP⟩ := plan2_at_head h
  obtain ⟨B⟩ := hP.eight
  refine onFromS_of_onFrom T₂ S₂ (onFrom_rows T₂ (c := Zp.p.chains) (P := qAt Zp Np) ?_ B.made
    weights rand r hr L hplace hrow hOn b blk (by rw [hbs]; exact hx) hp len)
  rw [hbs, shared_flat_at]
  exact flatOf_carried Zp.p.chains (qAt Zp Np) B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 (tests Np)
    last B.made

/-- **on₂'s BODY AT ONE ROW OF A FILLING**: at every row L with letters that has the place, the
parts and the sentence at entry of a row of sendingRows: the text of the field on₂ behind "∀ L ∈
G.shared", with ThrS T₂ S₂ for the letter T.I₂. Under the library's head; T₂ under the five
equations of hT. -/
theorem on₂_row (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    {G : Sides (F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X}
    (T₂ : Thread Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hT : T₂.φ = .shared ∧ T₂.chain = 1 ∧ T₂.ft = 0 ∧
      T₂.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder ∧ T₂.hs = (G.prover H).shared)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop) (w₀ : W₀) (rc : Rc) (k : Coins Bk)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (r : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)
    (hr : r ∈ sendingRows ⟨qAt Zp Np, 0⟩ weights rand)
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky) (hplace : L.place = r.place)
    (hrow : L.row = r.row) (hOn : L.On = r.On) :
    ∀ σ, L.side (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      ∀ (pre t : List (Block St ProofFile.Cl)),
      (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t → ∀ ρ p m ca,
      ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true →
      InsideOf .shared Bk 1 (G.prover H).shared σ.block (ThrS T₂ S₂ pre.length)
        (σ.roundsTo u.number) k m (envOf (H.storedWords w₀ rc) (fun _ _ => none) p) →
      m.seen = roundsOf p →
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      L.On u ca m ((laidOf (F0T OnBytes.secondHashFunction Zp Np cF) ρ [] p []).front 1
        (storedShown (H.storedWords w₀ rc) (storedAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ))) := by
  obtain ⟨p2, c2, -, b2, h2⟩ := hT
  intro σ hσ u hu pre t hcut ρ p m ca hρ hin hseen hca
  have hb0 : (pre ++ σ.block :: t)[pre.length]? = some σ.block := by simp
  have hb : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[pre.length]? = some σ.block := by
    rw [hcut]
    exact hb0
  refine onFromS_rows h T₂ b2 S₂ weights rand r hr L hplace hrow hOn pre.length σ.block hb
    (side_place hσ) (depthAt (F0T OnBytes.secondHashFunction Zp Np cF)) σ (by rw [b2]; exact hσ) u hu k m _ ca
    _ (insideS_of_insideOf T₂ S₂ (by rw [b2]; exact hb) (by rw [p2, c2, h2]; exact hin))
    (by rw [c2]; exact hca) ?_
  rw [c2, hseen]
  exact trueTo_two (F0T OnBytes.secondHashFunction Zp Np cF) (H.storedWords w₀ rc) ρ p

/-- CONDITIONAL. **THE FRAME's RECORD OnDebts AT A THREAD BUILT FROM LETTERS (threadsS), AT ANY
FILLING**: each row of the shared chain has the place, the parts and the sentence at entry of a row
of sendingRows, or its own clause OnFromS is a premise; the clauses of the rows of the two other
chains are premises. The frame's onDebts_of_onFromS, with the clauses at these two sorts of rows,
and at no other, paid by onFromS_rows; the field on₂ is laid by on₂_row at these rows. Under the
library's head, and under the frame's own letters as premises: this file's head names them; whether
they can be met together is not known. -/
theorem onDebts_with_rows (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    {G : Sides (F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X}
    (T₁ : Thread Bk (F0T OnBytes.secondHashFunction Zp Np cF).S₁ (F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (T₂ : Thread Bk (F0T OnBytes.secondHashFunction Zp Np cF).S₂ (F0T OnBytes.secondHashFunction Zp Np cF).Cl
      Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Thread Bk (F0T OnBytes.secondHashFunction Zp Np cF).S₃ (F0T OnBytes.secondHashFunction Zp Np cF).Cl
      (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    (hS : Sits (F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) T₁ T₂ T₃)
    (o₁ : OwesS T₁ S₁) (o₂ : OwesS T₂ S₂) (o₃ : OwesS T₃ S₃)
    (n₁ : ∀ b, SaidNext T₁ S₁ b) (n₂ : ∀ b, SaidNext T₂ S₂ b) (n₃ : ∀ b, SaidNext T₃ S₃ b)
    (a₁ : Enters₁ (F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) T₁ w₀ rc x k R)
    (a₂ : Enters₂ (F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) T₂ w₀ rc x k R)
    (a₃ : DoorBehind (F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) T₁ T₂ T₃ x k R)
    (e₁ : S₁ 0 k { R.start₁ (G.prover H) with opened := some [] })
    (e₂ : S₂ 0 k { R.start₂ (G.prover H) with opened := some [] })
    (e₃ : ∀ m₁ m₂ o₁ o₂, S₁ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length k m₁ →
      S₂ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k m₂ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      S₃ 0 k { R.start₃ (G.prover H) m₁ m₂ with opened := some (o₁ ++ o₂) })
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (on₁ : ∀ L ∈ G.first, ∀ b blk, (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS T₁ S₁ L b (depthAt (F0T OnBytes.secondHashFunction Zp Np cF)))
    (on₂ : ∀ L ∈ G.shared,
      (∃ r ∈ (sendingRows ⟨qAt Zp Np, 0⟩ weights rand :
        List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)),
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On) ∨
      ∀ b blk, (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[b]? = some blk →
        blk.place = L.place → OnFromS T₂ S₂ L b (depthAt (F0T OnBytes.secondHashFunction Zp Np cF)))
    (on₃ : ∀ L ∈ G.second, ∀ b blk, (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder[b]? = some blk →
      blk.place = L.place → OnFromS T₃ S₃ L b (depthAt (F0T OnBytes.secondHashFunction Zp Np cF))) :
    OnDebts (G := G) (H := H)
      (threadsS T₁ T₂ T₃ S₁ S₂ S₃ hS h.laid.planOk o₁ o₂ o₃ n₁ n₂ n₃ a₁ a₂ a₃ e₁ e₂ e₃) := by
  have A := onDebts_of_onFromS (G := G) (H := H) T₁ T₂ T₃ S₁ S₂ S₃ hS h.laid.planOk o₁ o₂ o₃ n₁ n₂
    n₃ a₁ a₂ a₃ e₁ e₂ e₃
    -- the term of TrueLaid, written out: the frame's three laws trueTo_one, _two, _three
    ⟨fun ρ p _ => trueTo_one (F0T OnBytes.secondHashFunction Zp Np cF) (H.storedWords w₀ rc) ρ p,
      fun ρ p _ => trueTo_two (F0T OnBytes.secondHashFunction Zp Np cF) (H.storedWords w₀ rc) ρ p,
      fun ρ p₀ p₁ p _ =>
        trueTo_three (F0T OnBytes.secondHashFunction Zp Np cF) (H.storedWords w₀ rc) ρ p₀ p₁ p⟩
    on₁
    (fun L hL b blk hx hp => by
      rcases on₂ L hL with ⟨r, hr, c1, c2, c3⟩ | q
      · exact onFromS_rows h T₂ hS.two.2.2.2.1 S₂ weights rand r hr L c1 c2 c3 b blk hx hp _
      · exact q b blk hx hp) on₃
  refine ⟨A.on₁, fun L hL => ?_, A.on₃⟩
  rcases on₂ L hL with ⟨r, hr, c1, c2, c3⟩ | -
  · exact on₂_row (H := H) (G := G) h T₂ hS.two S₂ w₀ rc k weights rand r hr L c1 c2 c3
  · exact A.on₂ L hL

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.onFromS_rows
#print axioms ProofFile.Honest.K14.on₂_row
#print axioms ProofFile.Honest.K14.onDebts_with_rows
