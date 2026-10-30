-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttentionEndFactor.lean: the factor beta that a masked sumcheck's
last round lays on the end values' mask entries is not 0 in the field, at every part of the attention
segments' own rounds (kind K5) that sends end values, wherever the test drawsFit holds at the part's
rounds. Statements with their proofs, and one definition.

Why. Each end value is sent as its value plus beta times its mask entry (sumPart, Honest/Sum.lean).
At beta = 0 it goes out as it is, and the field exact fails there: at this kind's rows said here
without a theorem; no theorem of this folder shows it. At sumPart itself, at a challenge that reads
0 there, what the part shows and what its simulator yields differ in law: fails_beta
(Honest/SumLaw/SumExactAt.lean): at the job whose lists are all empty, one shape and one fixed list
of challenges. What shuts that list of challenges out is drawFit (Honest/Frame.lean): the format
marks beta as never 0, drawsMarkedNonzeroHaveNonzeroWords asks that its three words are not all 0, and the word test asks each
word below the prime. Together they say "not 0 in the field": the library's beta_ne_zero
(Honest/SumLaw/BetaMarked.lean), over read_ne_zero and elemOf_ne_zero. What is proved here is a
corollary of it at this kind's members: which term is beta, and that the member's declared rounds
meet its premise.

  endFactor                  the term that the part's last move multiplies the mask entries by
  endFactor_eq_last          it is the last element of the first challenge and the variables': the term
                             in sumMsgs (Honest/SumLaw/SumShown.lean)
  ends_of_shape              every masked sumcheck of the row has end values
  endFactor_ne_zero          CONDITIONAL: betaMarked; drawsFit; the call has end values
  attention_endFactor_ne_zero   CONDITIONAL: K5Block; the side's row; the member's shape is .sum k;
                             drawsFit at the member's rounds
  attention_endFactor_at_row CONDITIONAL: the library's head (P5J.AtMgA); the same at every member of
                             every row of the lot

Limits. Nothing on how often drawsFit holds: that a typed challenge of the IOP gives such a list is
not shown here. That the lot has rows, each with a side, at the maker's return:
k5_lot_not_empty_at_return (Honest/K5/Law/LotNotEmptyAtMaker.lean). No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionRowSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Chain Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Call shapeOk)
open VerifiableInference.Desc.First.Att
open H2K5.Honest (shapes PartShape)
open ProofFile.Honest.SumLaw (betaMarked beta_ne_zero)
open P5J (AtMgA TS)

/-- **The factor on the end values' mask entries**, at the list of a masked sumcheck's own challenges:
the last element of the first k.vs.length + 2 of them. In sumPart's last move this is the term
ds.getLastD zeroE, where that move's ds are the challenges that the part has heard by then. -/
def endFactor (k : Call) (ds : List Fmt.Drawn) : E :=
  (drawnE (ds.take (k.vs.length + 2))).getLastD zeroE

/-- It is the term of sumMsgs: the last element of the first challenge and the variables', Y's among
them, at a list cut as sumOut_vals cuts it. -/
theorem endFactor_eq_last (k : Call) (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn)
    (hv : dv.length = k.vs.length + 1) :
    endFactor k (d0 :: (dv ++ dl)) = (drawnE (d0 :: dv)).getLastD zeroE := by
  unfold endFactor
  rw [show k.vs.length + 2 = (k.vs.length + 1) + 1 from rfl, List.take_succ_cons, ← hv,
    List.take_left]

/-- Every masked sumcheck of the row has end values. -/
theorem ends_of_shape {x : OnBytes.Params.AttentionRounds} {k : Call}
    (h : PartShape.sum k ∈ shapes x) : k.ends.isSome = true := by
  obtain ⟨e, he, -⟩ := sum_stage _ 0 k h
  rw [he]
  rfl

/-- **At challenges that fit, the factor is not 0 in the field.** CONDITIONAL: hb; hd; he. -/
theorem endFactor_ne_zero (k : Call) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hb : betaMarked k rs = true) {ds : List Fmt.Drawn} (hd : drawsFit (rs.map (·.1)) ds = true)
    (he : k.ends.isSome = true) : Reading.gl.val (endFactor k ds) ≠ 0 := by
  obtain ⟨R, hR, hne⟩ := beta_ne_zero k rs ds hb hd he
  have hlen : k.vs.length + 1 < ds.length := (List.getElem?_eq_some_iff.1 hR).1
  obtain ⟨d0, dv, dl, rfl, hv, -⟩ := SumLaw.split_draws ds (k.vs.length + 1)
    (ds.length - (k.vs.length + 2)) (by omega)
  rw [endFactor_eq_last k d0 dv dl hv, SumLaw.last_is_Y d0 dv dl k.vs.length R hv hR]
  exact hne

variable {W₀ Rc Xi Tr X Pb S Cl : Type}

/-- **At a member of K5's side that is a masked sumcheck, wherever drawsFit holds at its rounds, the
factor is not 0 in the field.** CONDITIONAL: hB; hr; hk: the shape of the member's number is .sum k;
hd. -/
theorem attention_endFactor_ne_zero
    {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {cells : Tr → Cells} {Z : Seat5}
    {p : P.Par} (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z)
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} (hu : u ∈ σ.members) {k : Call}
    (hk : (shapes Z.P.x)[u.number]? = some (.sum k)) {ds : List Fmt.Drawn}
    (hd : drawsFit (u.rounds.map (·.1)) ds = true) : Reading.gl.val (endFactor k ds) ≠ 0 := by
  obtain ⟨j, s, hq, rfl⟩ := member_at hr hu
  obtain rfl : s = .sum k := Option.some.inj (hq.symm.trans hk)
  exact endFactor_ne_zero k _ (SumLaw.betaMarked_of_like _ _ (stretch_like hB hq).2) hd
    (ends_of_shape (List.mem_of_getElem? hq))

/-- **The same at every member of every row of the lot, under the library's head.** The row's public
data are named, so that the member's shape can be. CONDITIONAL: h; hG; hr; hσ. -/
theorem attention_endFactor_at_row {Zf : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Zf D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {r : Row5 W₀ Rc Xi Tr X Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) {fs₀ : List (Fall TS)}
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀) :
    ∃ y ∈ H2K5.k5Places G, ∃ Y : Seat5, seatAtK keyOf Zp G y.1 y.2.1 y.2.2 = some Y ∧
      r = r5 cells Y ∧ ∀ u ∈ σ₀.members, ∀ k,
      (shapes Y.P.x)[u.number]? = some (.sum k) → ∀ ds,
        drawsFit (u.rounds.map (·.1)) ds = true → Reading.gl.val (endFactor k ds) ≠ 0 := by
  obtain ⟨y, hy, Y, p, hY, e, hrow, hB, -⟩ := seat_at_place h hG hr hσ
  exact ⟨y, hy, Y, hY, e, fun u hu k hk ds hd => attention_endFactor_ne_zero hB hrow hu hk hd⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.endFactor
#print axioms ProofFile.Honest.K5.endFactor_eq_last
#print axioms ProofFile.Honest.K5.ends_of_shape
#print axioms ProofFile.Honest.K5.endFactor_ne_zero
#print axioms ProofFile.Honest.K5.attention_endFactor_ne_zero
#print axioms ProofFile.Honest.K5.attention_endFactor_at_row
