-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/RowMoves.lean
(kind K9's soundness lemma): THEOREM: KIND K9's LEMMA IN THE FORM THAT THE RULE OF
COMPOSITION TAKES, AT A DESCRIPTION THAT ADDS THE CLAIMS STEP BY STEP: two pieces in a row:
  a block that is K9's draw with moves behind it (Law/Moves.lean: DrawMoves; Law/MovesBlock.lean
  pays it at K9.drawAlone joined with steps of adding and quiet blocks) · the one equation
  (K9.oneEquation X pw);
FROM  "every coefficient of the moves' terms is 0 at the data that the witness's tables hold, and
      every open row of the segment's group holds on these tables"
TO    "every open row of the segment's group holds on the witness's tables".
No block "behind the batching" stands between the two: what the claims' values read must have been
laid behind the last move (hend).
  relM          the relations at the three boundaries.
  k9_row_moves  EachGoodIn on (relM ..) j [pb, pe].
It glues Law/LawF.lean (goodInF_real), Law/Moves.lean (valueF_moves) and Law/DoorFacts.lean
(equation_goodIn'). The blocks' own type of claims is free.
Fx IS A LETTER OF THE STATEMENT: "the state goes on from the fixed part" (Law/Moves.lean).
THE HYPOTHESES, BY NAME: HF: the lens and the other kinds' letters at the draw and at the adding ·
hms: MoveOk of each move (AddOk | QuietOk: the runs' kinds'; Law/Gather.lean takes AddOk down to
each run) · hbm: the block is a draw with these moves · hend · hok: the exponents differ and are at
most d · **hpin under ctx, as in Law/Row3.lean: THE ONE THAT WEIGHS MOST** · hcb, hce · hdb, hgb:
the data and "every open row holds" are carried past the first piece · htab · lens · hN · inside ·
hlog · hback · hinj (paid: Law/Member.lean) · herr. None is shown at a segment of the protocol.

-/
import Johnson.Desc.First.Batch.Law.Row3
import Johnson.Desc.First.Batch.Law.Moves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens Where)
open VerifiableInference.Desc.Sound
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err)

variable {T P K W Cl : Type} [Field K] [Fintype K] [DecidableEq K] {F : Frame}

/-- The relations at the boundaries j, j + 1 and behind. -/
def relM (ρ : Reading K) (X : Lens T) (O : Others T P K) (ms : List (Termed T P K)) (N : Nat)
    (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K) (ctx : T × F.E.Str → W → Prop)
    (j : ℕ) : ℕ → T × F.E.Str → W → Prop := fun i a w =>
  if i = j then
    (∃ y, boundAt X tabOf ctx a w y ∧ ∀ x ∈ termsOf (O.fixed a.1) y ms 0, x.2 = 0) ∧
      GroupHoldsAt X ρ N a.1 (tabOf a w)
  else if i = j + 1 then
    (oneK X ρ a.1 a.1 (dataAt X a.1 (tabOf a w)) = 0 ∧ GroupHoldsAt X ρ N a.1 (tabOf a w)) ∧
      ctx a w
  else GroupHoldsAt X ρ N a.1 (tabOf a w) ∧ ctx a w

/-- **Kind K9's two pieces in a row, at a draw with moves behind it.** -/
theorem k9_row_moves (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)
    (p pw : Where) (ms : List (Termed T P K)) (d N j : ℕ) (HF : FitsM X O Fx p)
    (hms : ∀ m ∈ ms, MoveOk ρ X O Fx m) (b : Block T Cl)
    (hbm : DrawMoves X p (ms.map (·.move)) b)
    (hend : ∀ s s' cls, O.good s → MovesYes X (ms.map (·.move)) s s' cls →
      O.behind s' ∧ O.full s')
    (hok : ∀ s y, O.ready s → Desc.TermsOk K (termsOf (O.fixed s) y ms 0) d)
    (pb pe : Piece (ckP .two) F T Cl W)
    (hpb : pb.b = below b) (hpe : pe.b = below (K9.oneEquation X pw))
    (hextb : ∀ a τ w, pb.ext a τ w = w) (hexte : ∀ a τ w, pe.ext a τ w = w)
    (on : ℕ → T × F.E.Str → Prop)
    (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K) (ctx : T × F.E.Str → W → Prop)
    (hready : ∀ a, on j a → O.ready a.1)
    (hhb : ∀ a τ b', on j a → pb.ior.red.out a τ = some b' → on (j + 1) b')
    (hhe : ∀ a τ b', on (j + 1) a → pe.ior.red.out a τ = some b' → on (j + 2) b')
    (hpin : ∀ a w w', on j a → ctx a w → ctx a w' → tabOf a w = tabOf a w')
    (hcb : ∀ a τ b' w, on j a → pb.ior.red.out a τ = some b' → ctx b' w → ctx a w)
    (hce : ∀ a τ b' w, on (j + 1) a → pe.ior.red.out a τ = some b' → ctx b' w → ctx a w)
    (hdb : ∀ a τ b' w, on j a → pb.ior.red.out a τ = some b' →
      dataAt X b'.1 (tabOf b' w) = dataAt X a.1 (tabOf a w))
    (hgb : ∀ a τ b' w, on j a → pb.ior.red.out a τ = some b' →
      GroupHoldsAt X ρ N b'.1 (tabOf b' w) → GroupHoldsAt X ρ N a.1 (tabOf a w))
    (htab : ∀ a τ b' w, on (j + 1) a → pe.ior.red.out a τ = some b' → tabOf b' w = tabOf a w)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (hN : ∀ s, on (j + 1) s → ∀ a, X.get? s.1 = some a → a.d.st.oracles.size ≤ N)
    (inside : ∀ s, on (j + 1) s → ∀ a, X.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl)
    (hlog : ∀ r ∈ pb.ds, r.entry.logN ≤ 64) (hback : ∀ r ∈ pb.back, r.drawn.elems = [])
    (hinj : Function.Injective fun a : EV .two => ρ.val (E.ofTriple (toU3 a)))
    (herr : Err.le (allErr (fun _ _ => d) 0 pb.ds) pb.err) :
    EachGoodIn on (relM ρ X O ms N tabOf ctx j) j [pb, pe] := by
  have r0 : relM ρ X O ms N tabOf ctx j j = fun a w =>
      (∃ y, boundAt X tabOf ctx a w y ∧ ∀ x ∈ termsOf (O.fixed a.1) y ms 0, x.2 = 0) ∧
        GroupHoldsAt X ρ N a.1 (tabOf a w) := by
    funext a w
    simp [relM]
  have r1 : relM ρ X O ms N tabOf ctx j (j + 1) = fun a w =>
      (oneK X ρ a.1 a.1 (dataAt X a.1 (tabOf a w)) = 0 ∧ GroupHoldsAt X ρ N a.1 (tabOf a w)) ∧
        ctx a w := by
    funext a w
    simp [relM]
  have r2 : relM ρ X O ms N tabOf ctx j (j + 1 + 1) = fun a w =>
      GroupHoldsAt X ρ N a.1 (tabOf a w) ∧ ctx a w := by
    funext a w
    unfold relM
    rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨?_, ?_, trivial⟩
  · rw [r0, r1]
    refine goodIn_conseq pb (goodIn_and pb
      (goodInF_real (semOf ρ X O) b (fun q y => termsOf q y ms 0) d hok
        (valueF_moves ρ X O Fx p HF ms hms b hbm hend F.ft) pb hpb hextb (on j) (on (j + 1))
        (boundAt X tabOf ctx) hready hhb
        (fun a w w' y y' ha h1 h2 => by rw [h1.2, h2.2, hpin a w w' ha h1.1 h2.1])
        (fun a τ b' w y ha hout hB => ⟨hcb a τ b' w ha hout hB.1, by
          rw [hB.2]
          exact hdb a τ b' w ha hout⟩)
        hlog hback hinj herr)
      (fun a τ b' w ha hout hq => by
        rw [hextb]
        exact hgb a τ b' w ha hout hq))
      (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)
      (fun b' w _ h => ⟨⟨_, ⟨h.2, rfl⟩, h.1.1⟩, h.1.2⟩)
  · rw [r1, r2]
    exact goodIn_and pe (equation_goodIn' X ρ pw N pe hpe hexte (on (j + 1)) (on (j + 1 + 1))
      tabOf hhe htab lens hN inside) (fun a τ b' w ha hout hq => by
        rw [hexte]
        exact hce a τ b' w ha hout hq)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k9_row_moves
