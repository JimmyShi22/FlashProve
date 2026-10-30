-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/SmallPassDigits.lean: The kind "lookup" (K3): THE READER THAT THE DESCRIPTION
LAYS INTO A LINK's FIRST HOLE (K9.smallReader, Johnson/Desc/First/Batch/SmallReader.lean:
the single equations of the approximate range proof as forms) ANSWERS THE SAME IN
FRONT OF AND BEHIND AN ACCEPT OF THE DIGITS' DECISION; so the public test formsInA at
"K8.equations" (the table's name "small") passes that accept with no premise on the hole left.
Statements and proofs.

OBJECT: K9.smallReader; TailClaims.rowsAff; K3.block's decide at K3.seatDigits.
Used by Johnson/Desc/Sound/MgAt/K3DigitsFormsSmall.lean.
LETTERS: claim, piece, laid, before, p, guests, s, s', rs, cols, F; H, l, sent, own, b free.
Compiled with the whole library.

Why it holds. smallReader s reads S.tl? and S.funs?, and of the approximate range proof's
parameters tl only what rowsAff reads: NM, shp, tau, cfF, cfFirst, ix, gtTree, mats, mz, off
(Johnson/Desc/First/TailClaims/SingleForms.lean; zzCol and tabAt: OnBytes/Model/Tail.lean). The
digits' accept turns foldDrawn, slotA, slotB, heard and the ledger (k3_digits_footprint).

Main names:
  rowsAff_put: the four turned fields are not read: by rfl.
  put_funs, put_tlIs: what the digits' put leaves of S.funs?, and lays as S.tl?.
  smallReader_late: the reader names no late slot.
  k3_digits_smallReader: THE READER's ANSWER IS THE SAME.
  k3_digits_small_pass: THE END, at any letters H whose first hole is smallReader.

Limits. OVER THE DECISION's OWN ACCEPT: the step without a round behind the digits' rounds is
crossed by smallReader_same (Johnson/Desc/First/Batch/ReadersAt.lean),
where that step leaves S.tl? and S.funs?.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsAheadPassK3
import Johnson.Top.H.Keep.K3PassOf
import Johnson.Desc.First.Batch.SmallReader

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (rowsAff)
open VerifiableInference.Desc.K3 (seatDigits)
open VerifiableInference.Desc.K9 (Read readersOfLink LinkHoles formsInA smallReader)

/-- The four fields that the digits' accept turns are not read. -/
theorem rowsAff_put (tl : HTailF2) (funs : Array HFun) (n a b : ℕ) (g : Option Forest.Heard) :
    rowsAff { tl with foldDrawn := n, slotA := a, slotB := b, heard := g } funs =
      rowsAff tl funs := rfl

theorem put_funs (s : S) (tl : HTailF2) (G : Fork) :
    ((s.putTl tl).putFork G).funs? = s.funs? := by
  cases hh : s.here with
  | between => simp [S.funs?, S.putTl, S.putFork, hh]
  | fin _ => simp [S.funs?, S.putTl, S.putFork, hh]
  | mem _ => simp [S.funs?, S.putTl, S.putFork, hh]
  | lay a => simp [S.funs?, S.putTl, S.putFork, hh]
  | att a => simp [S.funs?, S.putTl, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.funs?, S.putTl, S.putFork, hh, ho]
    | true => simp [S.funs?, S.putTl, S.putFork, hh, ho]

theorem put_tlIs {s : S} {tl0 : HTailF2} (h : s.tl? = some tl0) (tl : HTailF2) (G : Fork) :
    ((s.putTl tl).putFork G).tl? = some tl := by
  cases hh : s.here with
  | between => simp [S.tl?, hh] at h
  | fin _ => simp [S.tl?, hh] at h
  | mem _ => simp [S.tl?, hh] at h
  | lay a => simp [S.tl?, S.putTl, S.putFork, hh]
  | att a => simp [S.tl?, S.putTl, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.tl?, hh, ho] at h
    | true => simp [S.tl?, S.putTl, S.putFork, hh, ho]

/-- The reader names no late slot. -/
theorem smallReader_late {s : S} {R : Read} (h : smallReader s = some R) : R.late = [] := by
  unfold smallReader at h
  cases ht : s.tl? with
  | none => simp [ht] at h
  | some tl =>
    cases hf : s.funs? with
    | none => simp [ht, hf] at h
    | some funs =>
      simp only [ht, hf] at h
      rw [← Option.some.inj h]

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S)
  (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
  (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s')
include hd

/-- **THE READER's ANSWER IS THE SAME.** -/
theorem k3_digits_smallReader : smallReader s' = smallReader s := by
  obtain ⟨F, G, g, tl, _, htl, e, _⟩ :=
    k3_digits_footprint claim piece laid before p guests s s' rs cols hd
  unfold smallReader
  rw [e, put_tlIs htl, put_funs, htl]
  cases s.funs? with
  | none => rfl
  | some funs =>
    show some ({ forms := rowsAff _ funs, late := [] } : Read) =
      some { forms := rowsAff tl funs, late := [] }
    rw [rowsAff_put]

/-- **"small" PASSES AN ACCEPT OF THE DIGITS' DECISION.** -/
theorem k3_digits_small_pass {F : Fork} (hF : s.fork? = some F) (hS : Sized F) (H : LinkHoles)
    (hHs : H.small = smallReader) (l : Link S Claim) (sent : ℕ → List (ℕ × ℕ))
    (own : List (ℕ × ℕ)) (b : ℕ)
    (hin : formsInA (readersOfLink H l) sent own b "K8.equations" s = true) :
    formsInA (readersOfLink H l) sent own b "K8.equations" s' = true := by
  obtain ⟨G, P⟩ := k3_digits_pass claim piece laid before p guests s s' rs cols hd hF hS
  refine small_formsInA_pass P H l sent own b (fun R h => ?_) (fun R h x hx => ?_) hin
  · rw [hHs] at h ⊢
    rw [k3_digits_smallReader claim piece laid before p guests s s' rs cols hd]
    exact h
  · rw [hHs] at h
    rw [smallReader_late h] at hx
    exact absurd hx List.not_mem_nil

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.rowsAff_put
#print axioms VerifiableInference.OnPublicFiles.put_funs
#print axioms VerifiableInference.OnPublicFiles.put_tlIs
#print axioms VerifiableInference.OnPublicFiles.smallReader_late
#print axioms VerifiableInference.OnPublicFiles.k3_digits_smallReader
#print axioms VerifiableInference.OnPublicFiles.k3_digits_small_pass
