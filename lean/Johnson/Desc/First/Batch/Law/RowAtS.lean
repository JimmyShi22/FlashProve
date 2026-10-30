-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/RowAtS.lean
(kind K9's soundness lemma): THEOREM: KIND K9's TWO PIECES IN A ROW AT
THE REAL RECORD, AT THE CAP: k9_row_moves_post (Law/MovesDoor.lean) with all that K9's files have
paid laid in:
  the state is S, the record that the proof file's first chain carries; the lens is atS;
  the field and the reading are the library's; the reading is one to one (Law/Member.lean);
  the lens's laws (Law/AtSLens.lean: atS_reads);
  the letters are O9 φ Ok Fu and Fx9 φ Ok (what lies under a filled slot stays; a run may fill a
  free one), and FitsM holds at them (Law/FitsAtS.lean);
  where the first piece's one round is K9's own and its errors are the cap (hds, hcap: ASKED, see
  below), K9's own count is at most these errors, for d ≤ 2^60 (Law/AtCap.lean).
  k9_row_atS   EachGoodIn (onPost on0 pb j) (relM ..) j [pb, pe].
WHAT IS LEFT AS HYPOTHESES, BY NAME, AND WHOSE EACH IS:
  hφ      the reader φ does not see K9's part: whoever chooses φ.
  hms     MoveOk of each move (AddOk | QuietOk; Law/Gather.lean takes AddOk down to RunOk of each
          run): THE KINDS' WHOSE RUNS LAY THE CLAIMS.   hkd   MoveDoor of each move: the same.
  hbm     the block is K9's draw with these moves behind it (Law/MovesBlock.lean pays it at
          drawAlone joined with steps of adding and quiet blocks): the seat's.
  hend    behind the last move the record is full: K8's files (the virtual rows' weights).
  hok     the exponents differ and are at most d; hd: d ≤ 2^60: the plan's numbers.
  hpin under ctx: THE ONE THAT WEIGHS MOST: at one statement all witnesses in the context hold the
          same tables: the row words_are_committed.   hcb, hce, htabb, htab: the context and the
          tables ride past the two pieces: whoever fills them.
  hready  the condition in front gives the promise k9OnA and the kinds' promise Ok on the fixed
          part.   hN, inside: two public facts in front.
  OF WHOEVER MAKES THE TWO PIECES: hpb, hpe: their blocks are these two; hextb, hexte: their
          extractors hand the witness on; hds: the first piece's data are just K9's own round
          (k9Round p); hbk: nothing stands behind it; hcap: ITS ERRORS ARE THE CAP (Err.cap 128).
THE SECOND PIECE IS closeOf's FIRST BLOCK (Batch/Place.lean), not a block of a flat list in which
K9.joint stands as one block.

-/
import Johnson.Desc.First.Batch.Law.Member
import Johnson.Desc.First.Batch.Law.MovesDoor
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Desc.First.Batch.Law.AtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open _root_.Run (ckP EV toU3)
open _root_.Iop (Err)

variable {α W Cl : Type} {F : Frame}

/-- **Kind K9's two pieces in a row, at the real record, at the cap.** -/
theorem k9_row_atS (φ : S → α) (hφ : ∀ s a, φ (atS.set s a) = φ s)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (p pw : Where) (ms : List (Termed S (α × Option Pub9) Cb.Gl.E)) (d N j : ℕ)
    (hd : d ≤ 2 ^ 60)
    (hms : ∀ m ∈ ms, MoveOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) m)
    (hkd : ∀ m ∈ ms, MoveDoor atS m.move)
    (b : Block S Cl) (hbm : DrawMoves atS p (ms.map (·.move)) b)
    (hend : ∀ s s' cls, good9 s → MovesYes atS (ms.map (·.move)) s s' cls → good9 s' ∧ Fu s')
    (hok : ∀ s y, k9OnA s = true ∧ Ok (fixed9 φ s) →
      Desc.TermsOk Cb.Gl.E (termsOf (fixed9 φ s) y ms 0) d)
    (pb pe : Piece (ckP .two) F S Cl W)
    (hpb : pb.b = below b) (hpe : pe.b = below (K9.oneEquation atS pw))
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
    EachGoodIn (onPost on0 pb j) (relM Reading.gl atS (O9 φ Ok Fu) ms N tabOf ctx j) j
      [pb, pe] := by
  have hlog : ∀ r ∈ pb.ds, r.entry.logN ≤ 64 := by
    intro r hr
    rw [hds, List.mem_singleton] at hr
    rw [hr]
    exact Nat.zero_le 64
  have hheld : AllHeldEx (fun _ _ => d) ((2 : ℝ≥0∞)⁻¹ ^ 128) 0 pb.ds := by
    rw [hds]
    exact (allHeldEx_one (fun _ _ => d) _ 0 (k9Round p) 0 (dsOf_k9Round p)).2
      (num_k9 d (k9Round p).entry.work hd)
  refine k9_row_moves_post Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) p pw ms d N j
    (fitsM_atS φ hφ Ok Fu p) hms hkd b hbm hend hok pb pe hpb hpe hextb hexte on0 tabOf ctx hready
    hpin hcb hce htabb htab
    (fun s a h => by
      obtain ⟨a', e0, _, e2, e3⟩ := atS_reads s a h
      exact ⟨a', e0, e2, e3⟩)
    hN inside hlog
    (fun r hr => by
      rw [hbk] at hr
      exact nomatch hr)
    reading_inj ?_
  rw [hcap]
  exact herr_cap d pb.ds hlog hheld

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k9_row_atS
