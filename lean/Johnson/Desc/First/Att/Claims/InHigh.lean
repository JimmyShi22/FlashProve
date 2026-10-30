-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/InHigh.lean: kind K5: the lawful heads of the four readers on the
table tO (RH, RHP, RH2, RHP2 of claim 5), drawn from the return of "first": the premise DivIs.fe of
Johnson/Desc/First/Att/Claims/PortParts.lean, paid.

Main names:
  `rc_pieces`: a condition that holds wherever one piece's reader returns holds where the loop over
    the pieces returns. `w1_mem`.
  `in_high`: firstRun (inOld h) K = some x → h.S.G = 2 ^ lgk → at every piece w of pwW or pwH and
    every head g: headFeat (atRh or atRhp) (g HA + w.a) dh = .ok …. `in_high_fe`: in the form of
    DivIs.fe, under PiecesAll.
Used: as Johnson/Desc/First/Att/Claims/InRunAll.lean, and PiecesAll, piece_at, Attention.atRh,
Attention.atRhp.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.InRunAll
import Johnson.Desc.First.Att.Claims.PortParts

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (tenOf w1Of W1)
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP)

variable {K : ℕ} (h : Attention.Heard)

/-- A condition that holds wherever one piece's reader returns holds where the loop over the pieces returns. -/
theorem rc_pieces {start : Aff} {pw : Array W1} {f : W1 → W Aff} {C : Prop} {w : W1}
    (hw : w ∈ pw.toList) (hf : RC K (f w) C) : RC K (P.Runs.lessPieces start pw f) C := by
  unfold P.Runs.lessPieces
  rw [← Array.foldlM_toList]
  exact RC.foldlM (a := w) (fun _ => RC.left hf) hw _

theorem w1_mem {pw : Array PW} {w : PW} (hw : w ∈ pw.toList) : w1 w ∈ (w1Of pw).toList := by
  unfold w1Of
  rw [Array.toList_map]
  exact List.mem_map.2 ⟨w, hw, rfl⟩

/-- **Where "first" returns, the heads of the four readers on the table tO are lawful.** -/
theorem in_high {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld h) K = some x)
    (hG : h.S.G = 2 ^ h.S.cf.lgk) (first : Bool) (pw : Array PW) (hp : pw = h.d.pwW ∨ pw = h.d.pwH)
    (w : PW) (hw : w ∈ pw.toList) (g : ℕ) (hg : g < 2 ^ h.S.cf.lgk) :
    headFeat (if first then Attention.atRh h.S else Attention.atRhp h.S) (g * h.S.HA + w.a) h.S.dh =
      .ok ((g * h.S.HA + w.a) * h.S.dh) := by
  have hg' : g < h.S.G := by rw [hG]; exact hg
  rcases hp with rfl | rfl
  · cases first with
    | true =>
      refine (first_rc5 h (fun j => ?_) h1 : InLongG h h.t.tO (Attention.atRh h.S) w.lam
        (fun g => g * h.S.HA + w.a) h.d.zcW).feat g hg'
      unfold P.Runs.claim5
      refine RC.right fun _ => RC.left (rc_pieces (w1_mem hw) ?_)
      exact rc_readHead h _ (Attention.atRh h.S) _ _ _ _
    | false =>
      refine (first_rc5 h (fun j => ?_) h1 : InLongG h h.t.tO (Attention.atRhp h.S) w.lam
        (fun g => g * h.S.HA + w.a) h.d.zcW).feat g hg'
      unfold P.Runs.claim5
      iterate 2 (refine RC.right fun _ => ?_)
      refine RC.left (rc_pieces (w1_mem hw) ?_)
      exact rc_readHead h _ (Attention.atRhp h.S) _ _ _ _
  · cases first with
    | true =>
      refine (first_rc5 h (fun j => ?_) h1 : InLongG h h.t.tO (Attention.atRh h.S) w.lam
        (fun g => g * h.S.HA + w.a) h.d.zcH).feat g hg'
      unfold P.Runs.claim5
      iterate 3 (refine RC.right fun _ => ?_)
      refine RC.left (rc_pieces (w1_mem hw) ?_)
      exact rc_readHead h _ (Attention.atRh h.S) _ _ _ _
    | false =>
      refine (first_rc5 h (fun j => ?_) h1 : InLongG h h.t.tO (Attention.atRhp h.S) w.lam
        (fun g => g * h.S.HA + w.a) h.d.zcH).feat g hg'
      unfold P.Runs.claim5
      iterate 4 (refine RC.right fun _ => ?_)
      refine RC.left (rc_pieces (w1_mem hw) ?_)
      exact rc_readHead h _ (Attention.atRhp h.S) _ _ _ _

/-- In the form of DivIs.fe (Johnson/Desc/First/Att/Claims/PortParts.lean). -/
theorem in_high_fe {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld h) K = some x)
    (hG : h.S.G = 2 ^ h.S.cf.lgk) (pW : PiecesAll h.S h.d.pwW) (pH : PiecesAll h.S h.d.pwH) :
    ∀ (first : Bool) (pw : Array PW), pw = h.d.pwW ∨ pw = h.d.pwH → ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk,
      headFeat (if first then Attention.atRh h.S else Attention.atRhp h.S)
        (g * h.S.HA + (pw.getD b default).a) h.S.dh = .ok ((g * h.S.HA + (pw.getD b default).a) * h.S.dh) := by
  intro first pw hp b hb g hg
  have hm : pw.getD b default ∈ pw.toList := by
    rcases hp with rfl | rfl
    · exact (piece_at pW hb).1
    · exact (piece_at pH hb).1
  exact in_high h h1 hG first pw hp _ hm g hg

end K5Law
