-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadSum.lean: from the key vectors of the output head's lookup calls to "the reply is
the model's first choice".

The verifier in OnBytes/ places the keys of the output head in the columns of six lookup calls
(OnBytes/Model/HeadLayout.lean). Johnson/Road/HeadCols.lean and Johnson/Road/HeadFn.lean describe a
call's key vector as a function on the call's columns and the positions. This file starts from three
statements on such functions and on integer cells:
  every value of each call's function is a row of the call's table;
  each of the 17 identities of the final normalisation is 0 at each position;
  every cell is below 2^18 in absolute value.
It concludes the field relation of the library's plain head (Cm/TargetPHead.lean), and with what the
layers must give (Johnson/Road/HeadTop.lean) the library's relation of a request for the next token.

Main definitions: segName (the verifier's name of a family), keysOf (the families' keys under the
verifier's names, the third digit of a margin divided by 2^23), CallsFit (what is asked of the
layout: each family is a segment of a call, with at least the library's length, and its table).
Main theorems: plainRF_of_calls; next_token_of_calls.

What is not claimed. The three statements are hypotheses: no theorem here derives them
from a verifier's acceptance. They are what a lookup argument, a test at a random point and a
smallness test are meant to give. That CallsFit holds of the verifier's layout is not shown here.
The program does not import this file.
-/
import Johnson.Road.HeadFn
import Johnson.Road.HeadTop

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head

/-- The verifier's name of a family of the plain head. -/
def segName : Cm.Plain.Fam → String
  | .NF => "NF" | .NFH => "NFH" | .HD0 => "HD0" | .HD1 => "HD1" | .ROW => "ROW" | .HD2 => "HD2"
  | .CNF => "CNF"

/-- The table in which the verifier looks a family's keys up: the library's, but for the third digit
of a margin, which the verifier divides by 2^23 and looks up among the numbers below 2^16. -/
def lutOf : Cm.Plain.Fam → Lut
  | .HD0 => R16
  | f => Cm.Plain.TP.tableOf f

section Sum

variable {K : Type} [Field K]

/-- A family's keys as the verifier looks them up. c: the inverse of 2^23. -/
def keyOf (c : K) (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Req) :
    Cm.Plain.Fam → ℕ → ℕ → K
  | .HD0 => fun v i => c * Cm.Plain.TP.key np t H y .HD0 v i
  | f => Cm.Plain.TP.key np t H y f

/-- What is asked of the layout and of the keys kv under the verifier's names: each family of the
plain head is a segment g of some call q, with at least the library's number of entries (the
verifier's segment of the ledger's bytes has 120, of which the plain head reads 99); the keys under
the segment's name are the family's; and T q, the table of call q, is the family's. -/
def CallsFit (R : Model.Head.Run) (kv : String → ℕ → ℕ → K) (T : ℕ → Lut) (c : K) (np : NormPar)
    (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Req) : Prop :=
  ∀ f : Cm.Plain.Fam, ∃ q g, g ∈ (R.L.calls.getD q default).segs ∧ g.name = segName f ∧
    Cm.Plain.len f ≤ g.n ∧ T q = lutOf f ∧ kv (segName f) = keyOf c np t H y f

/-- From the calls' functions to the field relation of the plain head, over any field in which c is
the inverse of 2^23. fn q: the function of call q; w q: the marks of its columns. -/
theorem plainRF_of_calls {R : Model.Head.Run} {kv : String → ℕ → ℕ → K} {T : ℕ → Lut} {c : K}
    (hc : c * 2 ^ 23 = 1) {np : NormPar} {tz : Head.Cells ℤ} {H : ℕ → ℕ → K} {y : Req}
    (A : CallsFit R kv T c np (tz.cast K) H y) {w : ℕ → Array ℕ} {pad : ℕ → K}
    {fn : ℕ → ℕ → ℕ → K}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J kv
      (pad q) (fn q))
    (small : Cm.Plain.Small (2 ^ 18) tz)
    (keys : ∀ q j, j < (R.L.calls.getD q default).J → ∀ i, i < nT → InLut (T q) (fn q j i))
    (idns : ∀ i < nT, ∀ k < 17, Cm.Plain.idn np (tz.cast K) i k = 0) :
    Cm.Plain.TP.RF (F := K) np H y tz := by
  refine ⟨small, fun f a i ha hi => ?_, idns⟩
  obtain ⟨q, g, hg, hname, hn, hT, hkv⟩ := A f
  have h1 := keys_of_fn (hw q) (Kf q) (fun v => InLut (T q) v) nT (keys q) g hg a
    (Nat.lt_of_lt_of_le ha hn) i hi
  rw [hname, hkv, hT] at h1
  cases f
  case HD0 => exact (Down.hd0_plain hc np (tz.cast K) H y a i).2 h1
  all_goals exact h1

end Sum

/-- **From the calls' functions to the reply.** At the challenge field of the protocol, for a
request for the next token (r = 1,023, e = 1,024): if every value of each call's function is a row
of the call's table, every identity is 0, every cell is small, and the layers give what the head
borrows, then the library's relation holds under every policy: the integer program runs, and the
reply is the least token of largest logit at the last position. -/
theorem next_token_of_calls {R : Model.Head.Run} {kv : String → ℕ → ℕ → Cb.Gl.E} {T : ℕ → Lut}
    {c : Cb.Gl.E} (hc : c * 2 ^ 23 = 1) {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables}
    (hn : nf.OK) (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024)
    {tz : Head.Cells ℤ}
    (A : CallsFit R kv T c nf (tz.cast Cb.Gl.E) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
      (Cm.reqOf x))
    {w : ℕ → Array ℕ} {pad : ℕ → Cb.Gl.E} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J kv
      (pad q) (fn q))
    (small : Cm.Plain.Small (2 ^ 18) tz)
    (keys : ∀ q j, j < (R.L.calls.getD q default).J → ∀ i, i < nT → InLut (T q) (fn q j i))
    (idns : ∀ i < nT, ∀ k < 17, Cm.Plain.idn nf (tz.cast Cb.Gl.E) i k = 0)
    (hl : Top.LayersGive κ tbs i.val x.prompt tz) (pol : AcceptancePolicy) :
    RinfR ppref κ nf tbs pol i x :=
  haveI : Cm.TI.Big Cb.Gl.p := Down.big_gl
  Top.next_token_of_head (p := Cb.Gl.p) hn i x hr he hl
    (Down.plainRF_gl.1 (plainRF_of_calls hc A hw Kf small keys idns)) pol

#print axioms plainRF_of_calls
#print axioms next_token_of_calls

end OnBytes.Road.Hd
