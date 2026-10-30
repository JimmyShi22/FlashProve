-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/RowSteps.lean
(kind K9's soundness lemma): THEOREM: KIND K9's TWO PIECES IN A ROW, AT THE REAL RECORD, AT THE CAP
(Law/RowAtS.lean: k9_row_atS), WITH ITS FOUR HYPOTHESES ON THE MOVES PAID DOWN TO ONE DUTY A RUN
(Law/Steps.lean): the form into which the kinds' payers go as they stand.
THE FIRST PIECE's BLOCK IS WRITTEN OUT: K9's draw joined (andThen) with one K9.addsStep a step.
  k9_row_steps  EachGoodIn .. [pb, pe], FROM, ON THE MOVES:
     hrun   RunOk of every run (Law/Gather.lean)            hquiet  QuietOk of every quiet move
     hrund  every run keeps the door (Law/MovesDoor.lean)   hquietd every quiet move does
     hdisc  at every ready state: the discipline on the exponents of the runs in a row
            (Law/ExpsOk.lean), the runs' claims at most the plan's number, plan + ties - 1 at most d
  and hend (behind the last move the state is good and full) and all that k9_row_atS asks of
  whoever makes the two pieces, of the witness's tables and of the context, unturned.
PAID SO FAR, EACH UNDER HYPOTHESES ON THE SHARED LETTERS: for the smallness test's run and its quiet
move: Law/K8Run.lean (but for its first four claims), Law/K8Step.lean, Law/K8Disc.lean.

-/
import Johnson.Desc.First.Batch.Law.RowAtS
import Johnson.Desc.First.Batch.Law.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where addsStep drawAlone)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err)

variable {α W Cl : Type} {F : Frame}

/-- A step at the real record, with its block's dress: its numbers, its name, its counts in front.
-/
abbrev Step9 (α : Type) : Type :=
  Step S (α × Option Pub9) Cb.Gl.E × Where × String × List (String × (S → Bool))

/-- The first piece's block: the draw joined with the steps' blocks. -/
def placeOf (p : Where) (name : String) (l : List (Step9 α)) : Block S Cl :=
  (l.map fun s => addsStep (Cl := Cl) atS s.2.1 s.2.2.1 s.2.2.2 s.1.ws s.1.cut
    (s.1.runs.map (·.run)) s.1.behind).foldl (fun acc x => acc.andThen name x) (drawAlone atS p)

/-- **Kind K9's two pieces in a row, from one duty a run.** -/
theorem k9_row_steps (φ : S → α) (hφ : ∀ s a, φ (atS.set s a) = φ s)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where) (name : String)
    (l : List (Step9 α)) (d N j : ℕ) (hd : d ≤ 2 ^ 60)
    (hrun : ∀ r ∈ runsOf (l.map (·.1)),
      RunOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) r.run.2 r.tm r.len)
    (hquiet : ∀ s ∈ l.map (·.1), QuietOk atS (O9 (K := Cb.Gl.E) φ Ok Fu) (Fx9 φ Ok) s.behind)
    (hrund : ∀ r ∈ runsOf (l.map (·.1)), ∀ n e c e₁, r.run.2 n e = .ok (c, e₁) →
      KeepsDoor atS e e₁)
    (hquietd : ∀ s ∈ l.map (·.1), ∀ e e₁, s.behind e = .ok e₁ → KeepsDoor atS e e₁)
    (hdisc : ∀ s y, k9OnA s = true ∧ Ok (fixed9 φ s) →
      ∃ (plan : ℕ) (ties : List (TermedRun S (α × Option Pub9) Cb.Gl.E × ℕ)),
        ties.map (·.1) = runsOf (l.map (·.1)) ∧
        DiscFrom (fixed9 φ s) y plan (ties.map fun r => (asMove r.1, r.2)) 0 0 ∧
        lenAll (fixed9 φ s) (ties.map fun r => (asMove r.1, r.2)) ≤ plan ∧
        plan + tieAll (ties.map fun r => (asMove r.1, r.2)) - 1 ≤ d)
    (hend : ∀ s s' cls, good9 s →
      MovesYes atS ((movesOf (l.map (·.1))).map (·.move)) s s' cls → good9 s' ∧ Fu s')
    (pb pe : Piece (ckP .two) F S Cl W)
    (hpb : pb.b = below (placeOf p name l)) (hpe : pe.b = below (K9.oneEquation atS pw))
    (hextb : ∀ a τ w, pb.ext a τ w = w) (hexte : ∀ a τ w, pe.ext a τ w = w)
    (hds : pb.ds = [k9Round p]) (hbk : pb.back = [])
    (hcap : pb.err = Err.cap 128 (uLT (ckP .two) pb.ds))
    (on0 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → Nat → OnBytes.Part → Nat → Cb.Gl.E)
    (ctx : S × F.E.Str → W → Prop)
    (hready : ∀ a, on0 a → k9OnA a.1 = true ∧ Ok (fixed9 φ a.1))
    (hpin : ∀ a w w', on0 a → ctx a w → ctx a w' → tabOf a w = tabOf a w')
    (hcb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → ctx b' w → ctx a w)
    (hce : ∀ a τ b' w, pe.ior.red.out a τ = some b' → ctx b' w → ctx a w)
    (htabb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → tabOf b' w = tabOf a w)
    (htab : ∀ a τ b' w, pe.ior.red.out a τ = some b' → tabOf b' w = tabOf a w)
    (hN : ∀ s, on0 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N)
    (inside : ∀ s, on0 s → ∀ a, atS.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl) :
    EachGoodIn (onPost on0 pb j)
      (relM Reading.gl atS (O9 φ Ok Fu) (movesOf (l.map (·.1))) N tabOf ctx j) j [pb, pe] :=
  k9_row_atS φ hφ Ok Fu p pw (movesOf (l.map (·.1))) d N j hd
    (steps_moveOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p (fitsM_atS φ hφ Ok Fu p) _ hrun hquiet)
    (steps_door atS _ hrund hquietd) (placeOf p name l) (steps_drawMoves atS p name l) hend
    (fun s y hs => by
      obtain ⟨plan, ties, e, h1, h2, h3⟩ := hdisc s y hs
      obtain ⟨t1, t2⟩ := steps_termsOk (fixed9 φ s) y plan (l.map (·.1)) ties e h1 h2
      exact ⟨t1, fun x hx => Nat.le_trans (t2 x hx) h3⟩)
    pb pe hpb hpe hextb hexte hds hbk hcap on0 tabOf ctx hready hpin hcb hce htabb htab hN inside

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k9_row_steps
