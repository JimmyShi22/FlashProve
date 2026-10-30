-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadSumP.lean: "the reply is the model's first choice", from statements on the matrices
of the output head's sub-proof.

Johnson/Road/HeadSum.lean starts from integer cells. Here the cells are those that are read, by the
verifier's own rule (cellsH in Johnson/Road/HeadPlace.lean), in integer matrices Mz: one for each
matrix of the sub-proof's list.

Main theorems: small_cellsH (if all entries are small, so are the cells); cast_cellsH; and
next_token_of_mats.

What is not claimed. As in Johnson/Road/HeadSum.lean: the statements on the calls' functions, on the
identities and on the entries are hypotheses, and so is what the layers must give. Nothing ties Mz
to a commitment. The program does not import this file.
-/
import Johnson.Road.HeadSum
import Johnson.Road.HeadPlace

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head

/-- If every entry of the matrices is below B in absolute value, so is every cell. -/
theorem small_cellsH {B : ℤ} (h : Model.Head.Shape) (L : Model.Head.HL) (b : Model.Head.Border)
    {Mz : Mats ℤ} (hM : ∀ a r c, |Mz a r c| < B) : Cm.Plain.Small B (cellsH h L b Mz) :=
  fun _ _ => ⟨fun _ _ => hM _ _ _, fun _ _ => hM _ _ _, fun _ _ => hM _ _ _, fun _ _ => hM _ _ _⟩

/-- The cells of integer matrices, read in a ring, are the cells of the matrices read in the
ring. -/
theorem cast_cellsH (K : Type) [CommRing K] (h : Model.Head.Shape) (L : Model.Head.HL)
    (b : Model.Head.Border) (Mz : Mats ℤ) :
    (cellsH h L b Mz).cast K = cellsH h L b fun a r c => ((Mz a r c : ℤ) : K) := rfl

/-- **From the matrices to the reply.** Mz: integer matrices, one for each matrix of the list of the
head's sub-proof; the cells are read in them by the verifier's rule. For a request for the next
token (r = 1,023, e = 1,024): if every entry is below 2^18 in absolute value, every value of each
call's function is a row of the call's table, every identity is 0, and the layers give what the
head borrows, then the library's relation holds under every policy. Mz is a function of three
numbers: the bound is asked at all of them, also where the list has no matrix, row or column; there
Mz is free and can be taken as 0. -/
theorem next_token_of_mats {R : Model.Head.Run} {kv : String → ℕ → ℕ → Cb.Gl.E} {T : ℕ → Lut}
    {c : Cb.Gl.E} (hc : c * 2 ^ 23 = 1) {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables}
    (hn : nf.OK) (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024)
    {Mz : Mats ℤ}
    (A : CallsFit R kv T c nf (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x))
    {w : ℕ → Array ℕ} {pad : ℕ → Cb.Gl.E} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J kv
      (pad q) (fn q))
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (keys : ∀ q j, j < (R.L.calls.getD q default).J → ∀ i, i < nT → InLut (T q) (fn q j i))
    (idns : ∀ i < nT, ∀ k < 17, Cm.Plain.idn nf
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) i k = 0)
    (hl : Top.LayersGive κ tbs i.val x.prompt (cellsH R.h R.L R.b Mz)) (pol : AcceptancePolicy) :
    RinfR ppref κ nf tbs pol i x :=
  next_token_of_calls hc hn i x hr he (tz := cellsH R.h R.L R.b Mz) A hw Kf
    (small_cellsH R.h R.L R.b small) keys idns hl pol

#print axioms small_cellsH
#print axioms next_token_of_mats

end OnBytes.Road.Hd
