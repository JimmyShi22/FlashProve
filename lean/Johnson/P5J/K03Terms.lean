-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Terms.lean: the kind "lookup" (K3): THE LEDGER's SENTENCES ON THE CONSTANT's OWN
TERMS, SHOWN THERE: the five fields of `K3OwedR` (Johnson/Desc/Sound/MgAt/K3Owed.lean) that speak of
𝔇 and Mg alone, and the premise "Dl.up is what the parameters send" of `k03_kind_owed`
(Johnson/P5J/K03Kind.lean), at 𝔇 := h.toAtMg.𝔇 h.𝔇 (the closed structure of parameters,
Johnson/P5J/MgAtAll.lean, LettersAll.lean) and Mg := `mgBase`.

Main names: `At.dl`: the door's own form of "what the list of rounds sends", off the constant ·
`k03_hDl` · `k03_hM` · `k03_es` (at seats := `At.seats Zp`) · `k03_hD` · `k03_hd` · `k03_hIn`:
each by unfolding.

Limits: six of the ledger's sentences; none of its tests, none of the facts along the fold, none of
its fields "where the piece accepts". Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.Sound.MgAt.K3Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- What the list of rounds sends, in the door's own form, off the constant. -/
def At.dl (Zp : ProofFile.Pub) : VerifiableInference.Desc.K3Asks.Sent :=
  ⟨At.cs Zp, At.shape Zp, At.layout Zp, Zp.made.p.built.links.map (·.arrayOf)⟩

theorem k03_hDl (h : AtMgA o Z D r Zp Np cF x) : (At.dl Zp).up = (h.toAtMg.𝔇 h.𝔇).sent := rfl

theorem k03_hM {P W : Type} :
    (mgBase : VerifiableInference.Desc.First.Meaning P W).more = {} := rfl

theorem k03_es (h : AtMgA o Z D r Zp Np cF x) :
    (h.toAtMg.𝔇 h.𝔇).smp = smpNamed (h.toAtMg.𝔇 h.𝔇).cs (At.seats Zp) := rfl

theorem k03_hD (h : AtMgA o Z D r Zp Np cF x) :
    (h.toAtMg.𝔇 h.𝔇).digitsPart =
      digitsPartK3 (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3 := rfl

theorem k03_hd (h : AtMgA o Z D r Zp Np cF x) :
    ∀ c (y y' : ProofFile.InstPub × VerifiableInference.Desc.First.S), y'.1 = y.1 →
      (h.toAtMg.𝔇 h.𝔇).decT c y' = (h.toAtMg.𝔇 h.𝔇).decT c y := by
  rintro c ⟨z, s⟩ ⟨z', s'⟩ e
  obtain rfl : z' = z := e
  rfl

theorem k03_hIn {P W : Type} :
    InOrderReads (mgBase : VerifiableInference.Desc.First.Meaning P W) := fun _ _ _ _ _ _ => rfl

end P5J

#print axioms P5J.k03_hDl
#print axioms P5J.k03_hM
#print axioms P5J.k03_es
#print axioms P5J.k03_hD
#print axioms P5J.k03_hd
#print axioms P5J.k03_hIn
