-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Asks.lean: TWO FIELDS OF K10's NAMED CONDITION (asks and dec of `K10OwesAt`,
Johnson/Desc/First/Close/Law/KindK10Owes.lean) AT THE CLOSED CONSTANT. Calls of
Johnson/Desc/First/Close/Law/AsksAtMgAll.lean and OracleAsksK10.lean, and two evaluations by the
kernel. Beside Johnson/P5J/K10Kind.lean.

What is said.
  `pubFitK_full`, `saidFitK_full`: K10's two tests on the table's lists say yes at `moreAll`,
    `fullLinks`, `At.ps`: by the kernel.
  `k10_dec_at`: at the closed meaning `mgAtAll h`: "decodes" rides from (z, s) to (z, s') at ALL s,
    s', along `Behind F base`, at every base: the constant's decoder does not read the first chain's
    state: by definition.
  `k10_asks_at`: `fenceFit`'s yes at the constant's numbers (hfen); At.ps[k]? = some p of the kind
    K10; the plan's count of trees at that place is at most base (hb): THEN `K10AsksR OutF (At.N Zp
    cF) (mgAtAll h)` at the k-th and (k + 1)-th open sets and public sets, at `Behind F base`.
Limits. hfen IS A PREMISE: a test on the constant's numbers: the table's files' to show; no kind's.
hb is a fact on the seated piece's first tree: a premise. The fence `OutF` (the index masks'
message is a member of no group) is owed at reached states. Nothing on soundness.

-/
import Johnson.P5J.K10Kind
import Johnson.Desc.First.Close.Law.OracleAsksK10

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start openSets pubSets fenceFit)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (pubFitK saidFitK K10AsksR OutF Behind k10_dec_mg
  k10_asksR_mg k10_oracleAsks)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

theorem pubFitK_full : pubFitK moreAll fullLinks At.ps = true := by decide +kernel

theorem saidFitK_full : saidFitK moreAll fullLinks At.ps = true := by decide +kernel

/-- **"decodes" rides at every state, at the closed meaning.** -/
theorem k10_dec_at (h : AtMgA o Z D r Zp Np cF x) {F : Frame} (base : ℕ) :
    ∀ z (s s' : VerifiableInference.Desc.First.S) y y', Behind F base y y' →
      (mgAtAll h).decodes (z, s) y → (mgAtAll h).decodes (z, s') y' :=
  k10_dec_mg _ mgBase base fun _ _ _ _ => rfl

/-- **WHAT K10's SECOND TIE ASKS, AT THE CLOSED MEANING.** -/
theorem k10_asks_at (h : AtMgA o Z D r Zp Np cF x) {F : Frame}
    (hfen : fenceFit (At.N Zp cF) fullLinks At.ps = true) (k base : ℕ) (p : Place)
    (hp : At.ps[k]? = some p) (hK : p.kind = KindName.K10)
    (hb : (At.N Zp cF).treesAt At.ps[k]? ≤ base) :
    K10AsksR OutF (At.N Zp cF) (mgAtAll h)
      ((openSets fullLinks At.ps (start fullLinks))[k]?.getD [])
      ((openSets fullLinks At.ps (start fullLinks))[k + 1]?.getD [])
      ((pubSets (mgAtAll h).more fullLinks At.ps)[k]?.getD [])
      ((pubSets (mgAtAll h).more fullLinks At.ps)[k + 1]?.getD []) (Behind F base) :=
  k10_asksR_mg _ (At.N Zp cF) fullLinks At.ps k base p pubFitK_full saidFitK_full hp hK
    fun z _ _ _ hs => k10_oracleAsks (At.cs Zp) _ (At.seats Zp) (At.N Zp cF) fullLinks At.ps
      z k base hfen (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp).1) hb (fun _ _ _ => rfl) hs

end P5J

#print axioms P5J.pubFitK_full
#print axioms P5J.saidFitK_full
#print axioms P5J.k10_dec_at
#print axioms P5J.k10_asks_at
