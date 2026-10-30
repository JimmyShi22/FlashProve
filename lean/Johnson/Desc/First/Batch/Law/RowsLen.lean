-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/RowsLen.lean (kind K9's soundness lemma; the law of a link on the road
of moves): THE PUBLIC SENTENCE OF THE SECOND LIST, AS ONE WRITTEN TERM; ITS PREMISE hR1 OF
inMoves_rows (Law/RowsNumber.lean), WHOLE; AND THE MONOTONY THAT LETS THE RUNS' PREMISES BE OWED
ONCE, AT THE BARE PROMISE. A definition; statements and proofs: calls.

  `rowsLen rows π len` := fun q => rowsFit rows π q ∧ lenFit len q. THE ONE NAME for the sentence
    C' of the second list (a written term, not a letter: a letter under "there is" could be laid at
    False). At a link: rowsLen p.rows π (fun q => lenRuns q (rlOf L tmOf lenOf)).
  `rowsLen_hR1`: **hR1 AT C' := rowsLen .., WHOLE**: from the first piece's yes and rowsAt behind
    it. THE ORDER INSIDE: rowsAt behind gives rowsFit in front (rows_hR1, Law/RowsRide.lean);
    rowsFit with the condition in front gives the bare promise (hready: THE FIELD Aready: rowsFit on
    its left, NOT C'); the bare promise with the yes gives lenFit
    (len_hR1_link, Law/LenOfYes.lean). No step wants lenFit.
  `fx9_and`, `fx9_bare`: "goes on from the fixed part" at the promise Ok₀ ∧ C and at the bare Ok₀.
  `runOk_and`: **RunOk at the bare promise gives RunOk at Ok₀ ∧ C**, for every C: the promise
    stands in the letters O9 in "ready" alone, and in Fx9 as one conjunct at the same fixed part on
    both sides of the arrow. So a list owes the runs' premises ONCE, at the bare promise:
    len_hR1_link takes them there, the joining takes them at Ok₀ ∧ C'.

Limits. hk (the gatherer keeps the map of weights), hruns, hready are premises. Nothing is turned
by this file. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.LenOfYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.JoinAtBlocks (runsIn)
open _root_.Run (ckP)

variable {α : Type}

/-- **THE PUBLIC SENTENCE OF THE SECOND LIST.** -/
def rowsLen (rows : ℕ) (π : α → Option HTailF2 × Option (Array HFun))
    (len : α × Option Pub9 → ℕ) : α × Option Pub9 → Prop :=
  fun q => rowsFit rows π q ∧ lenFit len q

theorem rowsLen_rows {rows : ℕ} {π : α → Option HTailF2 × Option (Array HFun)}
    {len : α × Option Pub9 → ℕ} {q : α × Option Pub9} (h : rowsLen rows π len q) :
    rowsFit rows π q := h.1

theorem rowsLen_len {rows : ℕ} {π : α → Option HTailF2 × Option (Array HFun)}
    {len : α × Option Pub9 → ℕ} {q : α × Option Pub9} (h : rowsLen rows π len q) :
    lenFit len q := h.2

section
variable {W : Type} {F : Frame}

/-- **hR1 AT THE SECOND LIST's SENTENCE, WHOLE.** -/
theorem rowsLen_hR1 (u : HTailF2) (φ : S → α) (hφ : ∀ s a, φ (atS.set s a) = φ s)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (Ok₀ : α × Option Pub9 → Prop)
    (Fu : S → Prop) (p : Where) (L : Link S Claim)
    (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E))
    (hrl : rl.map (·.run) = runsIn L.hear L.order)
    (hruns : ∀ r ∈ rl, RunOk Reading.gl atS (O9 φ Ok₀ Fu) (Fx9 φ Ok₀) r.run.2 r.tm r.len)
    (hk : KeepsKap atS (claimsInBy L.each L.hear L.order))
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (hms : ∀ m ∈ [Move.add (claimsInBy L.each L.hear L.order)], MoveNum u m)
    (pb : Piece (ckP .two) F S Claim W) (hpb : pb.b = below L.batchB)
    (on0 : S × F.E.Str → Prop) (hon : ∀ a, on0 a → k9OnA a.1 = true)
    (hready : ∀ a, on0 a → rowsFit p.rows π (fixed9 φ a.1) → Ok₀ (fixed9 φ a.1)) :
    ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → rowsAt p.rows u b'.1 →
      rowsLen p.rows π (fun q => lenRuns q rl) (fixed9 φ a.1) := by
  intro a τ b' h0 hout hRw
  have r := rows_hR1 u φ π hπ p _ L.batchB hb₁ hms pb hpb a b' τ hout hRw
  exact ⟨r, len_hR1_link φ Ok₀ Fu p (fitsM_atS φ hφ Ok₀ Fu p) L rl hrl hruns hk hb₁ pb hpb a b' τ
    hout ⟨hon a h0, hready a h0 r⟩⟩

end

/-- From the promise with C to the bare one. -/
theorem fx9_bare {φ : S → α} {Ok₀ C : α × Option Pub9 → Prop} {q : α × Option Pub9} {e : S}
    (h : Fx9 φ (fun q => Ok₀ q ∧ C q) q e) : Fx9 φ Ok₀ q e := ⟨h.1.1, h.2⟩

/-- And back, where C holds of the fixed part. -/
theorem fx9_and {φ : S → α} {Ok₀ C : α × Option Pub9 → Prop} {q : α × Option Pub9} {e : S}
    (h : Fx9 φ Ok₀ q e) (hC : C q) : Fx9 φ (fun q => Ok₀ q ∧ C q) q e := ⟨⟨h.1, hC⟩, h.2⟩

/-- **RunOk AT THE BARE PROMISE GIVES RunOk AT THE PROMISE WITH C.** -/
theorem runOk_and {φ : S → α} {Ok₀ : α × Option Pub9 → Prop} {Fu : S → Prop}
    (C : α × Option Pub9 → Prop) {r : ℕ → S → Except String (List Claim × S)}
    {tm : ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
    {len : α × Option Pub9 → ℕ}
    (H : RunOk Reading.gl atS (O9 φ Ok₀ Fu) (Fx9 φ Ok₀) r tm len) :
    RunOk Reading.gl atS (O9 φ (fun q => Ok₀ q ∧ C q) Fu) (Fx9 φ (fun q => Ok₀ q ∧ C q)) r tm
      len := by
  intro q front e a c e₁ hf hg ha hs hr
  obtain ⟨a₁, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H q front e a c e₁ (fx9_bare hf) hg ha hs hr
  exact ⟨a₁, h1, h2, h3, h4, h5, fx9_and h6 hf.1.2, h7, h8⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.rowsLen_hR1
#print axioms VerifiableInference.Desc.K9L.fx9_bare
#print axioms VerifiableInference.Desc.K9L.fx9_and
#print axioms VerifiableInference.Desc.K9L.runOk_and
