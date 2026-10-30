-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/VocabAtHead.lean: THE FILES' VOCABULARY SIZE IS THE REFERENCE's, IN THE GOALS' SCOPE AND SO UNDER THE HEAD. Two theorems. The head's token maps At.put | At.f (Johnson/P5J/LettersAt.lean) are typed at Fin Inst.Model.ppref.V: could public files in scope carry another vocabulary size?
  vocab_in_scope: in scope, where Verify.publicOf returns X: the three places where X holds the files' vocabulary size all hold ppref.V: the scanned parameter file's header X.P.h.V · the output head's shape X.hS.V · the layers' public part X.layers.V. THREE CALLS of landed theorems: Hd.core_of_scope (the 41 numbers; V is number 11 of coreOf, counted from 0) · Meaning.HeadS.sizes_in_scope · Meaning.Emb.emb_public_in_scope.
  vocab_at_head: the same at the head's own letter At.X Zp.
Why it holds: VerifierAndGoals.InScope asks Z.pol = VerifierAndGoals.policyFile (VerifierAndGoals.freeLinesOf pp): the stored parameter file with the lines of EIGHT free numbers set (eps1 · eps2 · epsF · MF · KF · C · theta · cap): the vocabulary's line is not among them.
Beside: the settings pp : Inst.Model.ScalesAndPolicy that VerifierAndGoals.readFiles returns hold NO vocabulary size (the 48 layers' scales · the final normalisation · the policy's three numbers): the integer program (Inst/Model/Program.lean) is general in its sizes P : Params; THE GOALS TAKE IT AT ppref: VerifierAndGoals.settingsOfRead pp := settingsOf (Cm.Scales.of pp), and settingsOf scales := settingsArraysOf ppref … (IntegerModel/Arrays/OfIndex.lean): in Ladder.lean's own words "settingsOfRead always has the reference model's sizes".
Limits. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.AtMg
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.Goal.Meaning.EmbScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open Inst.Model (ppref)

/-- **In the goals' scope the files' vocabulary size is the reference's**, at the three places where the
public parameters hold it. -/
theorem vocab_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : Verify.publicOf Z.pol Z.KL lay = .ok X) :
    X.P.h.V = ppref.V ∧ X.hS.V = ppref.V ∧ X.layers.V = ppref.V :=
  ⟨(OnBytes.Road.Hd.core_of_scope hZ hR h).num 11, (Meaning.HeadS.sizes_in_scope hZ hR h).2.2.1,
    (Meaning.Emb.emb_public_in_scope hZ hR h).2.2.2⟩

/-- **Under the head.** -/
theorem vocab_at_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} (h : AtMg o Z D r Zp Np cF) :
    (At.X Zp).P.h.V = ppref.V ∧ (At.X Zp).hS.V = ppref.V ∧ (At.X Zp).layers.V = ppref.V :=
  vocab_in_scope h.scope h.reads h.pubOne

end P5J

#print axioms P5J.vocab_in_scope
#print axioms P5J.vocab_at_head
