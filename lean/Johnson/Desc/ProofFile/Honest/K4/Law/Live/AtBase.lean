-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/AtBase.lean: CONDITIONAL.

What is here. TWO NUMBERS OF THE LAYERS' LAYOUT, ll - 1 = 1 AND LamM ≤ 2, AT `Bs.G₀.W.layers`, UNDER
THE HYPOTHESIS h : `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). They are the hypotheses hll and hLam of
`k4_live` (Law/Live/Whole.lean); what the two numbers mean stands in the head of
Law/Live/AtFull.lean. h says that the public files lie in the goals' scope and are read, and that
the proof file's description is made of them. It says more (tests on the plan, the head's place, a
number of columns, two more tests): THE PROOF SPENDS FOUR OF ITS NINE FIELDS: scope, reads, laid,
pubOne. Bs is what `ProofFile.baseOf` returns at these public data; `Bs.G₀` are its letters made at a
request of zeros, and `Bs.G₀.W` their public data. One statement and its proof.

The steps. h opens (`h.laid.opened`), and what is opened has made the base: so hB names that same
base (`IM.Open`, its field made, Johnson/IMR/SeatOpen.lean). `Bs.G₀.W` is what the verifier's public
part returns (`IM.Open.W`, there). Under h that return's layout is what the verifier's function
`layout` returns for the shape of the parameter file, and that shape has ll = 2: by
`Meaning.P34.pub34_all`. The library's `rowLight_of_head` (Johnson/Road/K4/RowLightOfHead.lean)
calls that statement in the same way inside its proof. `llLam_of_layout` (Law/Live/AtFull.lean) has
both numbers at such a layout.

  `llLam_at_base`   **ll - 1 = 1 and LamM ≤ 2 at `Bs.G₀.W.layers.y`, under h and hB.**

Kin. That the shape has ll = 2, and LamM = 2 at the public part's return, stand as steps inside two
proofs of the library: `rowLight_of_head` (Johnson/Road/K4/RowLightOfHead.lean) and its like under
the scope alone (Johnson/Road/K4/RowLightInScope.lean). `llLam_of_scan` (Law/Live/AtFull.lean) has
both numbers at the public part's return where the scan is `Pv v`. Beside it its writers, who sought
through the statements on LamM and ll under Johnson/Desc/, Road/, Top/, P1K8R/, IMR/, P5J/ and
AtFull/, and under OnBytes/ and AtFullSide/, found none that ends in either number at the public
part's return or at a base.

Not shown here. THAT h CAN HOLD is not shown here; the side library proves, with no hypothesis, that
h has a member at one place (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean, whose own
limits say what it is worth). hB: that `baseOf` returns: a hypothesis; under h it does (the proof's
first step), so hB only names the base. THE FULL SIZE ALONE, and the format's second hash function alone:
both come with h: ll = 2 is a number that h's scope tests of the parameter file; this law carries it
to the layout and to the base, and evaluates no file.

A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
By a program's walk from import to import, over the library as it stood when this file was written,
which stops unopened at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/
and at every module whose name begins Cb.Bridge, its imports reach 21 modules under Johnson/Goal/
and 5 under Johnson/Bridge/: 25 of the 26 through Johnson/Road/K4/RowLightOfHead.lean, one
(Johnson.Goal.Meaning.ScopeScan) through Law/Live/AtFull.lean alone. What lies behind the 26 is not
counted. The proof calls `Meaning.P34.pub34_all`, a statement of a file under Johnson/Goal/.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.AtFull
import Johnson.Road.K4.RowLightOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h and hB. **ll - 1 = 1 AND LamM ≤ 2 AT `Bs.G₀.W.layers.y`.** -/
theorem llLam_at_base (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Bs.G₀.W.layers.y.h.ll - 1 = 1 ∧ Bs.G₀.W.layers.y.LamM ≤ 2 := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  rw [O.W]
  have hX : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  obtain ⟨⟨hy, _, _, _, Zd, _, _, _, _, _, _, _⟩, _⟩ :=
    Meaning.P34.pub34_all h.scope h.reads hX OnBytes.Road.gl_numerals
  have hy' : Layer.layout (Verify.layerShape Zp.p.X.P) Zp.p.X.P.polCalls =
      .ok Zp.p.X.layers.y := hy
  have ell : (Verify.layerShape Zp.p.X.P).ll = 2 := by
    rw [← Zd.lL]
    rfl
  exact llLam_of_layout hy' ell

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.llLam_at_base
