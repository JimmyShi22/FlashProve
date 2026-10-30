-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/CellsSmallFullIn.lean: CONDITIONAL: on h and hA.

What is here. THE PREMISE's FORM `K4CellsSmall` (Law/W/CellsOfSyms.lean: at an input that meets Vd
each column of each matrix of the plan's list but the planes' is the image of a small integer
column) HOLDS AT THE FRAME's FULL-SIZE CHOICE OF FIELDS: at the filling `widerFillAt fullIn`
(Honest/AtPureFullIn.lean), at cells := id, at Vd := `ReadyInput` (Honest/Thread/ReadyInput.lean:
the input's trace is the prover's own at the input's index and instance). General in the plan tl, in
Qp, weights, tokens and look: whatever key the honest side of the feed-forward layers' own rounds
(sub-protocol K4) asks the trace at, the answer is the image of an integer below 129 in absolute
value. Two statements with their proofs. The road: the prover's trace is the filling's
(`atPure_trace`, Honest/AtPureLaw.lean); where it is there, it is the library's full-size trace read
by `cellOf`, at a served request (`fullIn_trace_some`); the public part is the head's
(`atPure_at_laid_ground`, Honest/AtHeadGround.lean); in the goals' scope every entry of that trace
is below 129 (the field small of `MeetsAll`, Johnson/HonestTrace/Full.lean, by `meetsAll_in_scope`,
with `planesOf_01`, Johnson/HonestTrace/FullPlanes.lean); `cellOf` answers the image of an entry, or
0.

  `cellOf_int`   what `cellOf` answers is the image of an integer below 129, where every entry of
      the trace is.
  `k4CellsSmall_fullIn`   **`K4CellsSmall` at `widerFillAt fullIn`, id and `ReadyInput`.**

Not shown here. hA: THAT THE MAKER `onlineProverFromPublicFiles` RETURNS AT THAT FILLING: a hypothesis here;
AtFullSide/K4/AtPureFullInAtFull.lean, in the side library, has it under h and the library's test
`protocolDataWellFormed`. h: the library's hypothesis `P5J.AtMgA` on the public files. AT A REQUEST THAT IS NOT
SERVED `ReadyInput` HOLDS OF NO INPUT, and the statement is idle there. At another choice of fields
than `fullIn`, at another reader than id, or at another Vd, nothing is said. It is a bound and no
more: nothing on which integer a cell is. All limits of Honest/Thread/ReadyInput.lean's head hold
here. Of its three clauses this proof spends the third alone (the trace is the prover's own); nor
does it spend the form's own two premises: the bound holds at the planes' number and beyond the
columns too. THE STATEMENT RESTS ON A LAW OF A FILE UNDER Johnson/Goal/, CALLED BY NAME
(`meetsAll_in_scope`), as Honest/K6/Law/TraceCellsInScope.lean calls it. All limits of the heads of
the files that it imports hold here; among them: closed facts by evaluation in Lean's kernel lie
beneath; no independent checker that its writers know of has replayed them; through its imports it
stands over files under Johnson/Goal/. THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a part of the proof file's description
may import this one. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.CellsOfSyms
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinReader
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Desc.ProofFile.Honest.AtHeadGround
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Desc.ProofFile.Honest.K6.Law.TraceCellsInScope
import Johnson.HonestTrace.FullPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model (HTailF2 Reading)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.HonestTrace (Tr planesOf_01 meetsAll_in_scope)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.First.Look (szOf)
open P5J (AtMgA TS)

/-- CONDITIONAL: every entry of the trace is below 129 in absolute value. What `cellOf` answers, at
every number, string, row and column, is the image of an integer below 129. -/
theorem cellOf_int {X : OnBytes.Model.Verify.Public} {T : Tr}
    (hT : ∀ k a r c, |T k a r c| < 129) (k : ℕ) (s : String) (r c : ℕ) :
    ∃ z : ℤ, |z| < 129 ∧ OnBytes.HonestTrace.cellOf X T k s r c = ((z : ℤ) : Cb.Gl.F) := by
  unfold OnBytes.HonestTrace.cellOf
  split
  · split
    · refine ⟨OnBytes.HonestTrace.byName X T _ _ r c, ?_, rfl⟩
      unfold OnBytes.HonestTrace.byName
      split_ifs
      · split
        · exact hT _ _ _ _
        · norm_num
      · norm_num
    · exact ⟨0, by norm_num, by simp⟩
  · exact ⟨0, by norm_num, by simp⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h and hA. **THE TRACE's CELLS ARE SMALL, AT THE FRAME's FULL-SIZE CHOICE OF
FIELDS.** F: any description; it stands in `ReadyInput` alone. ON THE FORM's RIDER: this is the
form that it asks ("had from Vd, by name"), met at I := fullIn, in its first arm; at a free I
 the form stays a premise, and the rider stays.
The form is had from Vd := `ReadyInput`, which asks three things of an input: its instance passes
the description's test on the start; its index is in range; its trace is the prover's own at its own
index and instance. At a request that is not served the prover has no trace: `ReadyInput` holds of
no input there, and this statement is idle. -/
theorem k4CellsSmall_fullIn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {o : SecondHashFunctionArgument}
    {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A : OnlineProverWithDescription Cm.Idx IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt fullIn o S O) = .ok A)
    (F : FileDescription ProofFile.Inst) (tl : HTailF2) (Qp : K4Pub) (weights : Cm.Idx → Weights)
    (tokens : ProofFile.Inst → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    K4CellsSmall (ReadyInput F A.H) tl Qp id weights tokens look := by
  intro v hv i c _ _
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
    Op.W ▸ Op.public
  have ht := hv.2.2
  rw [atPure_trace hA] at ht
  obtain ⟨x, -, Sv, eC⟩ := fullIn_trace_some ht
  rw [(atPure_at_laid_ground h.laid Op.blank hA).1] at Sv eC
  have M := meetsAll_in_scope h.scope h.reads hpub (pl := OnBytes.HonestTrace.plOf Zp.p.X v.w₀ x)
    (fun k a b => planesOf_01 _ _ _ _ k a b) Sv
  have H : ∀ a : Fin (tl.mats.getD i {}).m, ∃ z : ℤ, |z| < 129 ∧
      OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X v.w₀ x)
        (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c) = ((z : ℤ) : Cb.Gl.F) :=
    fun a => cellOf_int M.small _ _ _ _
  choose col hcol using H
  have eB : (((szOf tl).beta : ℕ) : ℤ) = 2 ^ 17 := by
    show ((2 ^ 17 : ℕ) : ℤ) = 2 ^ 17
    norm_num
  refine ⟨col, fun a => ?_, fun a => ?_⟩
  · rw [eB]
    exact lt_trans (hcol a).1 (by norm_num)
  · show _ = Reading.gl.val (OnBytes.ofF (OnBytes.Slice.ofF
      ((id v.trace).cell (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c))))
    rw [gl_slice]
    show _ = algebraMap Cb.Gl.F Cb.Gl.E
      (v.trace.cell (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c))
    rw [eC]
    show _ = algebraMap Cb.Gl.F Cb.Gl.E
      (OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X v.w₀ x)
        (k4Owner Qp i).1 (k4Owner Qp i).2.1 a.val ((k4Owner Qp i).2.2 + c))
    rw [(hcol a).2, map_intCast]

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.cellOf_int
#print axioms ProofFile.Honest.K4.W.k4CellsSmall_fullIn
