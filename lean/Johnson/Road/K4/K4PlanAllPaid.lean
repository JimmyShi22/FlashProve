-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanAllPaid.lean: ALL 24 OF K4's CLOSED TESTS ARE NO TESTS, UNDER FOUR
NAMED CONDITIONS. `WrittenAt Z` (five parts of the public parameters are the written values: other
files' pins), `XNine Z.p.X` (the nine matrices of a feed-forward link have the reference owners and
sizes), `NamesTied Z` (the names' tie), and Z.p.X is the programs' public data of files
with the public core. Under these the twelve `firstFastB Z g` accept, by the closed fact that Lean's
kernel has decided (`first_written`, Johnson/Road/K4/K4PlanWrittenFirst.lean); the other twelve by
Johnson/Road/K4/K4PlanPaid.lean. So `K4PlanFit` and `K4PlanFitF` take no test. Five theorems,
without an evaluation.

  `firstClosed_sent`: `firstClosedCoreB` reads of D the codes, the shape and the layout alone.
  `first_paid`: `firstFastB Z g = true`, g < 12.
  `all_paid`: `allFastB Z = true`.
  `k4PlanFit_free`, `k4PlanFitF_free`: the two structures, as `k4PlanFit_fast` and `k4PlanFitF_fast`
    conclude them, with no test among the premises.

Limits. K04_law IS NOT PROVED BY THIS. THE FOUR CONDITIONS ARE PREMISES: `XNine` in scope is shown
by nothing here (`xNine_of_head`, Johnson/Road/K4/K4PlanOfLaid.lean, has it
in scope where the value is laid, under three premises more, none paid there: the return of
`publicOf`, the public core, the accept of `laidThere`); `WrittenAt` and `NamesTied` in scope are
other files' to pay. BESIDE THEM the two last laws take what `k4PlanFit_fast` takes that is no test:
`PublicSteps` and `RefPub` among them. The reference sizes alone.
-/
import Johnson.Road.K4.K4PlanPaid
import Johnson.Road.K4.K4PlanWrittenFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.PlanWritten (PublicSteps proofSizedFull)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent szOf pubAt stepOf)
open VerifiableInference.Desc.Sound (Mem msOf)
open Johnson.G (layoutFull)
open Meaning (seatBy fLay)
open Inst.Model.Layout (kRef hRef)

/-- **The test at the numerals reads of D the codes, the shape and the layout alone.** -/
theorem firstClosed_sent (c : Codes) (s : Params.ReqShape) (l : Params.ReqLayout)
    (a a' : Array (Array (ℕ × String))) (ps : List P5T.PSeat) (N : Numbers) (ms : List Mem) (g : ℕ)
    (num arr : ℕ → ℕ → ℕ) :
    firstClosedCoreB ⟨c, s, l, a⟩ ps N ms g num arr =
      firstClosedCoreB ⟨c, s, l, a'⟩ ps N ms g num arr := rfl

variable {Z : ProofFile.Pub} (W : WrittenAt Z) (H : XNine Z.p.X) (T : NamesTied Z)

include W H T in
/-- **The test at group g accepts.** -/
theorem first_paid {g : ℕ} (hg : g < 12) : firstFastB Z g = true := by
  have e := List.all_eq_true.1 first_written g (List.mem_range.2 hg)
  have e' : firstClosedCoreB (sentAt Z) (seatsAt Z) (numbersAt Z) (msOf (lists0At Z)) g
      (fun l k => (seatKeys (allSeatsAt Z)).idxOf (0, l, k))
      (fun j t => ((arrTab (seatKeys (allSeatsAt Z)) (allSeatsAt Z)).lookup (j, t)).getD
        (seatKeys (allSeatsAt Z)).length) = true := by
    rw [seatsAt_written W, numbersAt_written W, lists0At_written W, allSeatsAt_written W]
    have d : sentAt Z = ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
        Z.made.p.built.links.map (·.arrayOf)⟩ := by
      unfold sentAt
      rw [show Z.made.p.chains.proof.first.codes = proofSizedFull.codes from W.codes,
        show Z.made.p.chains.proof.first.shape = proofSizedFull.request from
          W.shape.trans shape_one,
        show Z.made.p.chains.proof.first.layout = layoutFull from W.layout]
    rw [d, firstClosed_sent _ _ _ _ #[]]
    exact e
  exact firstCore_of_closed H hg (T g hg) _ _ _ _ _ e'

variable {pol KL : ByteArray} {lay : Option ByteArray}

include W H T in
/-- **All 24 accept.** -/
theorem all_paid (h : publicOf pol KL lay = .ok Z.p.X) (C : Hd.PublicCore Z.p.X.P) :
    allFastB Z = true := by
  rw [allFast_eq, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨⟨common_paid W h C, fun g hg => first_paid W H T (List.mem_range.1 hg)⟩,
    fun i hi => seam_paid W h C (Nat.succ_pos i) (by have := List.mem_range.1 hi; omega)⟩

variable {rows cols : ℕ}

include W H T in
/-- **`K4PlanFit` with no test among its premises.** -/
theorem k4PlanFit_free {polS KLS : ByteArray} {tk : Array Nat}
    (h : publicOf pol KL lay = .ok Z.p.X) (C : Hd.PublicCore Z.p.X.P) (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    (p : Par) (hg0 : 0 < p.g) (hg : p.g < 12)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * p.g)
    (hG : Z.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin rows → Fin cols → Cb.Gl.E) → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (hd : ℕ) (St : PublicSteps polS KLS Z.p.X)
    (B : RefPub Z.p.X p.g) (hP : p.P = { Z.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Z.p.X = p.g) (hhd : 2 * p.g ≠ hd) :
    K4PlanFit (X := Z.p.X) (p := p) x (pubAt Z.p.X (2 * p.g / stepOf Z.p.X)) (sentAt Z) rad
      (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z) (P5T.msAtR Z radM) N' (2 * p.g)
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) hd :=
  k4PlanFit_paid W h C radM hs hi p (first_paid W H T hg) hg0 hg x hx hG rad posI oW enc wOf hd St B
    hP P0 hgr hhd

include W H T in
/-- **`K4PlanFitF` with no test among its premises.** -/
theorem k4PlanFitF_free {polS KLS : ByteArray} {tk : Array Nat} (radM : ℕ → ℕ → ℕ)
    {N' : Numbers} (hs : N'.sent = (numbersAt Z).sent) (hi : N'.index = (numbersAt Z).index)
    (p : Par) (hg : p.g < 12)
    (x : VerifiableInference.Desc.First.Look.Place) (hx : x.link = 2 * p.g)
    (hG : Z.p.X.G[p.g]? = some p.hp) (rad : OnBytes.OracleShape → ℕ) (posI : ℕ → Bool × ℕ × ℕ)
    (oW : Cb.OMsg Cb.Gl.E) (enc : (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (hd : ℕ) (St : PublicSteps polS KLS Z.p.X)
    (B : RefPub Z.p.X p.g) (hP : p.P = { Z.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Z.p.X = p.g) (hhd : 2 * p.g ≠ hd) :
    K4PlanFitF (X := Z.p.X) (p := p) x (pubAt Z.p.X (2 * p.g / stepOf Z.p.X)) (sentAt Z) rad
      (seatTAt Z rad x.link) posI oW enc wOf (arrAt Z) (P5T.msAtR Z radM) N' (2 * p.g)
      (szOf p.hp.tl).NM ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (Meaning.sizesOf Z.p.X)) hd :=
  k4PlanFitF_fast Z radM hs hi p (first_paid W H T hg) hg x hx hG rad posI oW enc wOf hd St B hP P0
    hgr hhd

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.firstClosed_sent
#print axioms OnBytes.Road.K4.first_paid
#print axioms OnBytes.Road.K4.all_paid
#print axioms OnBytes.Road.K4.k4PlanFit_free
#print axioms OnBytes.Road.K4.k4PlanFitF_free
