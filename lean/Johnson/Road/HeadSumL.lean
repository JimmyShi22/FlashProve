-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadSumL.lean: from the key vectors of the output head's lookup calls and the four
clauses of the cost ledger to the relation of a request under its policy: every request.

Johnson/Road/HeadSum.lean starts from statements on the functions of the six lookup calls and
concludes the field relation of the library's plain head (seven families), and so the relation of a
request for the next token. This file is its twin for the head with the cost ledger
(Policy/Rel/LedgerHead.lean): nine families, with the two families of looked-up exponentials, and
the ledger's four clauses. It starts from five statements on integer cells:
  every value of each call's function is a row of the call's table;
  each of the 17 identities of the final normalisation is 0 at each position;
  the clauses B4 and Z of the ledger are 0 at each position;
  the clauses B2 and B3, two sums over the positions, are 0;
  every cell is small.
It concludes the field relation of the head with the ledger, and with what the layers must give
(Johnson/Road/HeadTop.lean) the library's relation RinfR of the request under the policy, for every
request of the right form, not only a request for the next token.

Main definitions: lutOfL, keyOfL (table and keys of a family as the verifier looks them up: the
third digit of a margin divided by 2^23); CallsFitL (what is asked of the layout and of the keys
under the verifier's names).
Main theorems: ledgerRF_of_calls; rinfR_of_calls; kvOf_keyOfL (the keys of
Johnson/Road/HeadCallLib.lean under the verifier's names are these keys); mem_of_segHas,
callsFitL_of_layout (CallsFitL holds of every layout that the verifier returns at the library's
sizes, for the keys kvOf, if each call's table is its families'); stFromCall_tests,
head3_of_call (the request's form, from the verifier's test on the request).

What is not claimed. The five statements are hypotheses: no theorem here derives them from a
verifier's acceptance. They are what a lookup argument, tests at random points, two claims that are
tested outright and a smallness test are meant to give. That the table of each call is its
families' is a hypothesis of callsFitL_of_layout. That all hypotheses of rinfR_of_calls can be met
together is not shown here; that its middle term, the field relation, can be met with what the
layers give is Top.ledger_next_hyps_met. The program does not import this file.
-/
import Johnson.Road.HeadFn
import Johnson.Road.HeadTop
import Johnson.Road.HeadCallLib
import Johnson.Road.HeadLaid

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head

/-- The table in which the verifier looks a family's keys up: the library's, but for the third digit
of a margin, which the verifier divides by 2^23 and looks up among the numbers below 2^16. -/
def lutOfL : Inst.Model.Head.Fam → Lut
  | .HD0 => R16
  | s => Policy.LedgerHead.tableOf s

section SumL

variable {K : Type} [Field K]

/-- A family's keys as the verifier looks them up. c: the inverse of 2^23. -/
def keyOfL (c : K) (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Req) :
    Inst.Model.Head.Fam → ℕ → ℕ → K
  | .HD0 => fun v i => c * Policy.LedgerHead.key np t H y .HD0 v i
  | s => Policy.LedgerHead.key np t H y s

/-- What is asked of the layout and of the keys kv under the verifier's names: each of the nine
families is a segment g of some call q, with at least the library's number of entries; the keys
under the segment's name are the family's; and T q, the table of call q, is the family's. -/
def CallsFitL (R : Model.Head.Run) (kv : String → ℕ → ℕ → K) (T : ℕ → Lut) (c : K) (np : NormPar)
    (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Req) : Prop :=
  ∀ s : Inst.Model.Head.Fam, ∃ q g, g ∈ (R.L.calls.getD q default).segs ∧ g.name = nameOf s ∧
    Inst.Model.Head.len s ≤ g.n ∧ T q = lutOfL s ∧ kv (nameOf s) = keyOfL c np t H y s

/-- **From the calls' functions and the ledger's clauses to the field relation of the head with the
ledger**, over any field in which c is the inverse of 2^23. fn q: the function of call q; w q: the
marks of its columns. -/
theorem ledgerRF_of_calls {R : Model.Head.Run} {kv : String → ℕ → ℕ → K} {T : ℕ → Lut} {c : K}
    (hc : c * 2 ^ 23 = 1) {np : NormPar} {tz : Head.Cells ℤ} {H : ℕ → ℕ → K} {y : Req}
    (A : CallsFitL R kv T c np (tz.cast K) H y) {w : ℕ → Array ℕ} {pad : ℕ → K}
    {fn : ℕ → ℕ → ℕ → K}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J kv
      (pad q) (fn q))
    (small : Head.Small tz)
    (keys : ∀ q j, j < (R.L.calls.getD q default).J → ∀ i, i < nT → InLut (T q) (fn q j i))
    (idns : ∀ i < nT, ∀ k < 17, N.idn np (tz.cast K) i k = 0)
    (jc : ∀ i < nT, dB4 (tz.cast K) y i = 0 ∧ dZ (tz.cast K) y i = 0)
    (sums : sB2 (tz.cast K) y = 0 ∧ sB3 (tz.cast K) y = 0) :
    Policy.LedgerHead.RF (F := K) np H y tz := by
  refine ⟨small, fun s a i ha hi => ?_, idns, jc, sums⟩
  obtain ⟨q, g, hg, hname, hn, hT, hkv⟩ := A s
  have h1 := keys_of_fn (hw q) (Kf q) (fun v => InLut (T q) v) nT (keys q) g hg a
    (Nat.lt_of_lt_of_le ha hn) i hi
  rw [hname, hkv, hT] at h1
  cases s
  case HD0 => exact (Down.hd0_ledger hc np (tz.cast K) H y a i).2 h1
  all_goals exact h1

/-- The keys of Johnson/Road/HeadCallLib.lean at the library's sizes, under the verifier's names,
are the keys as the verifier looks them up. -/
theorem kvOf_keyOfL (c : K) (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Req)
    (s : Inst.Model.Head.Fam) :
    kvOf c HeadSizes.ref np t H y (nameOf s) = keyOfL c np t H y s := by
  cases s
  case HD0 => exact kv_ref_HD0 c np t H y
  all_goals exact kv_ref c np t H y (fun e => by cases e)

end SumL

/-- **From the calls' functions and the ledger's clauses to the relation of a request under its
policy.** At the challenge field of the protocol, for every request of the right form and every
policy with AcceptancePolicy.OK: if every value of each call's function is a row of the call's table, every
identity and every clause of the ledger is 0, every cell is small, and the layers give what the
head borrows, then the library's relation holds: the integer program runs, and the request meets
the policy. -/
theorem rinfR_of_calls {R : Model.Head.Run} {kv : String → ℕ → ℕ → Cb.Gl.E} {T : ℕ → Lut}
    {c : Cb.Gl.E} (hc : c * 2 ^ 23 = 1) {κ : ℕ → LayerScale} {nf : NormPar} {tbs : ℕ → Tables}
    (hn : nf.OK) {pol : AcceptancePolicy} (hpol : pol.OK) (i : Index ppref) (x : Instance ppref)
    (h3 : Head3 x) {tz : Head.Cells ℤ}
    (A : CallsFitL R kv T c nf (tz.cast Cb.Gl.E) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
      (Req.of pol x))
    {w : ℕ → Array ℕ} {pad : ℕ → Cb.Gl.E} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J kv
      (pad q) (fn q))
    (small : Head.Small tz)
    (keys : ∀ q j, j < (R.L.calls.getD q default).J → ∀ i, i < nT → InLut (T q) (fn q j i))
    (idns : ∀ i < nT, ∀ k < 17, N.idn nf (tz.cast Cb.Gl.E) i k = 0)
    (jc : ∀ i < nT, dB4 (tz.cast Cb.Gl.E) (Req.of pol x) i = 0 ∧
      dZ (tz.cast Cb.Gl.E) (Req.of pol x) i = 0)
    (sums : sB2 (tz.cast Cb.Gl.E) (Req.of pol x) = 0 ∧ sB3 (tz.cast Cb.Gl.E) (Req.of pol x) = 0)
    (hl : Top.LayersGive κ tbs i.val x.prompt tz) :
    RinfR ppref κ nf tbs pol i x :=
  haveI : Cm.TI.Big Cb.Gl.p := Down.big_gl
  Top.rinfR_of_ledger (p := Cb.Gl.p) hn hpol i x h3 hl
    (Down.ledgerRF_gl.1 (ledgerRF_of_calls hc A hw Kf small keys idns jc sums))

/-! ## The record CallsFitL, of a layout that the verifier returns -/

/-- A segment that a name has: its call, that it is one of the call's segments, its name and its
length. -/
theorem mem_of_segHas {R : Model.Head.Run} {sn : String} {n : ℕ} (S : SegHas R sn n) :
    ∃ q g, Model.Head.callNo R.L sn = some q ∧ g ∈ (R.L.calls.getD q default).segs ∧
      g.name = sn ∧ g.n = n := by
  obtain ⟨q, g, hq, hg, hn, -⟩ := S
  exact ⟨q, g, hq, List.mem_of_find?_eq_some hg, by simpa using List.find?_some hg, hn⟩

/-- **The record holds of every layout that the verifier returns at the library's sizes**, with five
limbs, for the keys kvOf: if the table of the call of each family is the family's. -/
theorem callsFitL_of_layout {K : Type} [Field K] {h : Model.Head.Shape} {tauFC : Array F}
    {L : Model.Head.HL} (hy : Model.Head.layout h tauFC = .ok L) (h1 : h.lt = 10)
    (h2 : h.d = 5120) (h3 : h.V = 202048) (h5 : h.XL = 5) {R : Model.Head.Run} (e1 : R.h = h)
    (e2 : R.L = L) {T : ℕ → Lut}
    (hT : ∀ s q, Model.Head.callNo R.L (nameOf s) = some q → T q = lutOfL s) (c : K)
    (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y : Req) :
    CallsFitL R (kvOf c HeadSizes.ref np t H y) T c np t H y := by
  have Z := laid_ref hy h1 h2 h3 e1 e2
  have hJV : L.JV = 202048 := by rw [← e2]; exact Z.JV
  have hJa : L.JVa = 131072 := by rw [← e2]; exact Z.JVa
  have key : ∀ (s : Inst.Model.Head.Fam) (x : String × String × ℕ),
      x ∈ Model.Head.segments h L → x.1 = nameOf s → Inst.Model.Head.len s ≤ x.2.2 →
      ∃ q g, g ∈ (R.L.calls.getD q default).segs ∧ g.name = nameOf s ∧
        Inst.Model.Head.len s ≤ g.n ∧ T q = lutOfL s ∧
        kvOf c HeadSizes.ref np t H y (nameOf s) = keyOfL c np t H y s := by
    intro s x hx hn hl
    obtain ⟨q, g, hq, hg, hgn, hgl⟩ := mem_of_segHas (segHas_of_layout hy e1 e2 x hx)
    rw [hn] at hq hgn
    exact ⟨q, g, hg, hgn, by rw [hgl]; exact hl, hT s q hq, kvOf_keyOfL c np t H y s⟩
  have hR : Inst.Model.Head.len .ROW ≤ Model.ledNRH h.XL := by
    rw [h5]
    exact Nat.le_refl 120
  intro s
  cases s
  case NF => exact key .NF ("NF", "R16", h.d) (by simp [Model.Head.segments]) rfl (by
    show 5120 ≤ h.d
    omega)
  case NFH => exact key .NFH ("NFH", "R16", h.d) (by simp [Model.Head.segments]) rfl (by
    show 5120 ≤ h.d
    omega)
  case HD0 => exact key .HD0 ("HD0", "R16", L.JV) (by simp [Model.Head.segments]) rfl (by
    show 202048 ≤ L.JV
    omega)
  case HD1 => exact key .HD1 ("HD1", "R16", L.JV) (by simp [Model.Head.segments]) rfl (by
    show 202048 ≤ L.JV
    omega)
  case ROW =>
    exact key .ROW ("ROW", "R8", Model.ledNRH h.XL) (by simp [Model.Head.segments]) rfl hR
  case HD2 => exact key .HD2 ("HD2", "R8", L.JV) (by simp [Model.Head.segments]) rfl (by
    show 202048 ≤ L.JV
    omega)
  case HE0 => exact key .HE0 ("HE0", "FE", L.JVa) (by simp [Model.Head.segments]) rfl (by
    show 131072 ≤ L.JVa
    omega)
  case HE1 => exact key .HE1 ("HE1", "FE", L.JV - L.JVa) (by simp [Model.Head.segments]) rfl (by
    show 70976 ≤ L.JV - L.JVa
    omega)
  case CNF => exact key .CNF ("CNF", "FC", h.d) (by simp [Model.Head.segments]) rfl (by
    show 5120 ≤ h.d
    omega)

/-! ## The request's form -/

/-- The last test of stFromCall: r < e ≤ T, and the reply is 0 if e < T. -/
theorem stFromCall_tests {P Q : Array UInt32} {T : ℕ} {so : Model.Head.StOwn}
    (h : Model.Head.stFromCall P Q T = .ok so) :
    so.r < so.e ∧ so.e ≤ T ∧ (so.e < T → so.y = 0) := by
  unfold Model.Head.stFromCall at h
  obtain ⟨-, h⟩ := ok_of_needed h
  obtain ⟨-, h⟩ := ok_of_needed h
  obtain ⟨e, h⟩ := ok_of_needed h
  cases h
  obtain ⟨a, c3⟩ := nor_true_split e
  obtain ⟨c1, c2⟩ := or_false_split a
  refine ⟨Nat.not_le.mp (of_decide_eq_false c1), Nat.not_lt.mp (of_decide_eq_false c2),
    fun hlt => ?_⟩
  by_contra hne
  have hlt' : (P.getD (T + 1) 0).toNat < T := hlt
  have hne' : ¬ (Q.getD 0 0).toNat = 0 := hne
  have k : (decide ((P.getD (T + 1) 0).toNat < T) && ((Q.getD 0 0).toNat != 0)) = true := by
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hlt', bne_iff_ne.mpr hne'⟩
  rw [c3] at k
  cases k

/-- **The request's form, as the library asks it, from the verifier's test**: for an instance with
the request's r and e and the caller's reply as y. -/
theorem head3_of_call {P Q : Array UInt32} {so : Model.Head.StOwn}
    (hs : Model.Head.stFromCall P Q 1024 = .ok so) (x : Instance ppref) (hr : x.r = so.r)
    (he : x.e = so.e) (hy : x.y.val = so.y) : Head3 x := by
  obtain ⟨t1, t2, t3⟩ := stFromCall_tests hs
  refine ⟨by rw [hr, he]; exact t1, by rw [he]; exact t2, fun hlt => ?_⟩
  rw [hy]
  exact t3 (by rw [← he]; exact hlt)

#print axioms ledgerRF_of_calls
#print axioms rinfR_of_calls
#print axioms callsFitL_of_layout
#print axioms head3_of_call

end OnBytes.Road.Hd
