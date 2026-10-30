-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FormPortZE.lean: the row that `Send.form` makes for an oracle message's sample,
read in the field, is the row of the library's sample map for that message's shape, for a shape with
a mask row or with main rows over the extension field. Statements and proofs.

`Send.form` is the verifier program's (OnBytes/Iop/Send.lean); the sample map is `portZ`
(Johnson/Pack/PortZ.lean). The two agree coefficient by coefficient in the case `CaseE`: the case
that Johnson/Pack/FormPortZF.lean leaves (its "What is not claimed"). There is no new mathematics:
it is the sister of the library's `form_portZ_F`, from the library's own lemmas.
In this case the pad is one place: the last place of the last row of the mask table (of the main
table, where the message has no mask row). The program gives it the coefficient beta; the library
beta times the weight 1. Off the pad both sides have the weight of the seed's point at the entry's
corner of the message's cube.
Main names:
  `form_portZ_E`: from `Send.form cs s o seed 0 = some row`, s.answers = 1, `CaseE s`, the seed's
    point having as many coordinates as the cube has bits, and β a unit whose value is the seed's
    factor, read: for every entry j of the message, coefAt row o (j's table) (j's index in it) =
    (portZ cs s).mat (the seed's point read, β) () j. The statement is that of `form_portZ_F`,
    letter for letter, with `CaseE` in the place of `CaseF`.
  `form_portZ`: both cases: under `CaseE s ∨ CaseF s`, which is what the library's law of a sending
    asks (`MeetsAt`, Johnson/Pack/PortF.lean).
Limits (as in the sister's head), not claimed: anything for more than one answer; the row's target;
other oracle messages (the library's `coefAt_form_other`: 0); indices of the table that are no entry
of the message; a run of the program's block. That the hypotheses hold together at some size is not
shown here. The premise on the seed's point is an equality of lengths: by the program's own text a
real seed's point is as long as the largest cube of its round, so at a round that sends messages
with cubes of two sizes the premise is false at the smaller; `form_take`
(Johnson/Desc/K12/Law/FormTake.lean) has the form with "at most".
Still between this and "o.Z.val σ.1 m = σ.2": a row's value on words as the sum of coefAt times the
entries (`Says` and "short of its target", Johnson/Desc/Means/Says.lean), the target as the sample's
answer, and the library's `sig_rows`.
No soundness is claimed, and nothing is said on hiding.
Lemmas of the library that are called (none runs in a context of `verify-on-bytes`):
`coefAt_form_one`, `coefAt_form`, `pad_cases`, `tableW_eq_eqW`, `cube_hasMask_eq`
(OnBytes/Slice/BlkSend.lean); `pad_mem`, `cube_bits` (Johnson/Pack/PortTie.lean); `wZ_one`
(Johnson/Pack/PortZ.lean); `form_portZ_F_hasPart`, `form_portZ_F_locZ_lt`, `form_portZ_F_cubeIdx`,
`form_portZ_F` (Johnson/Pack/FormPortZF.lean).
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Pack.FormPortZF

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Slice Cb Cb.Ood Johnson.Pack

/-- **The program's sample row, read, is the library's**, with the pad on one place over the
extension field (CaseE). -/
theorem form_portZ_E (cs : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (row : Row)
    (h : Send.form cs s o seed 0 = some row) (h1 : s.answers = 1) (hE : CaseE s)
    (hz : seed.z.length = bitsZ cs s) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (j : (portCode cs s).J) :
    coefAt row o (partZ cs s j) (locZ cs s j) =
      (portZ cs s).mat (readP (bitsZ cs s) seed.z, β) () j := by
  have he : ((Send.cube cs s).hasMask || s.mainDeg == 3) = true := by
    rw [cube_hasMask_eq]
    rcases hE with h0 | h0
    · simp [h0]
    · simp [h0]
  have hp : hasPart (Send.cube cs s) (padPart (Send.cube cs s)) = true := by
    unfold padPart
    by_cases hm : (Send.cube cs s).hasMask = true
    · rw [if_pos hm]
      exact hm
    · rw [if_neg hm]
      rcases j with x | x
      · exact form_portZ_F_hasPart cs s (.inl x)
      · exact absurd (form_portZ_F_hasPart cs s (.inr x)) hm
  obtain ⟨places, hpl, _⟩ := coefAt_form cs s o seed 0 row h (partZ cs s j) (locZ cs s j)
  have hmem := pad_mem cs s h1 places hpl j
  rw [pad_cases cs s h1 he] at hpl
  have hpl' : places = [⟨padPart (Send.cube cs s), padIndex cs s, 0, thetaE 0⟩] := by
    split at hpl
    · cases hpl
    · exact (Option.some.inj hpl).symm
  rw [coefAt_form_one cs s o seed row h h1 he hp]
  by_cases hpj : padP cs s j
  · obtain ⟨p, hpm, e1, e2⟩ := hmem.1 hpj
    rw [hpl'] at hpm
    obtain rfl := List.mem_singleton.1 hpm
    rw [if_pos ⟨e1.symm, e2.symm⟩]
    have e : sigmaZ cs s j = Sum.inr ⟨j, hpj⟩ := by
      simp [sigmaZ, Equiv.sumCompl, hpj]
    show _ = Sum.elim _ _ (sigmaZ cs s j)
    rw [e]
    show _ = (β : GE) * wZ cs s ⟨j, hpj⟩
    rw [wZ_one cs s hE, mul_one, hβ]
  · have hno : ¬ (partZ cs s j = padPart (Send.cube cs s) ∧ locZ cs s j = padIndex cs s) :=
      fun q => hpj (hmem.2 ⟨_, by rw [hpl']; exact List.mem_singleton.2 rfl, q.1.symm, q.2.symm⟩)
    rw [if_neg hno, if_pos (form_portZ_F_hasPart cs s j),
      tableW_eq_eqW cs s seed.z _ _ (by rw [cube_bits]; exact hz)
        (form_portZ_F_hasPart cs s j) (form_portZ_F_locZ_lt cs s j),
      form_portZ_F_cubeIdx cs s j, cube_bits]
    have e : sigmaZ cs s j = Sum.inl ⟨j, hpj⟩ := by
      simp [sigmaZ, Equiv.sumCompl, hpj]
    show _ = Sum.elim _ _ (sigmaZ cs s j)
    rw [e]
    rfl

/-- Both cases: whichever the library's law of a sending allows (MeetsAt's "CaseE ∨ CaseF"). -/
theorem form_portZ (cs : Codes) (s : OracleShape) (o : ℕ) (seed : SampleSeed) (row : Row)
    (h : Send.form cs s o seed 0 = some row) (h1 : s.answers = 1) (hc : CaseE s ∨ CaseF s)
    (hz : seed.z.length = bitsZ cs s) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (j : (portCode cs s).J) :
    coefAt row o (partZ cs s j) (locZ cs s j) =
      (portZ cs s).mat (readP (bitsZ cs s) seed.z, β) () j :=
  hc.elim (fun c => form_portZ_E cs s o seed row h h1 c hz β hβ j)
    fun c => form_portZ_F cs s o seed row h h1 c hz β hβ j

end H2K.Pin

#print axioms H2K.Pin.form_portZ_E
#print axioms H2K.Pin.form_portZ
