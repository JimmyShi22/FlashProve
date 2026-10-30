-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/InstOfInScope.lean: the three premises on public numbers of the laws on
`ProofFile.instOf` (InstOf.lean, InstOfTies.lean) hold at all public files in the goals' scope. Calls of
theorems of the library. No definition: no goal is stated.
The letters. W : VerifierAndGoals.PublicFiles, the three public files; hW: they are in the goals' scope; hR: the
goals' reader returns pp; Z : ProofFile.Pub, the proof file's public part; hX: its public record `Z.p.X`
is what `verify-on-bytes`'s `publicOf` returns at W's parameter file and scale file and at lay,
which is any layout bytes or none and is not tied to W's layout file.
  `window_in_scope`: Z.p.X.T = ppref.T (`T_in_scope`, Johnson/Goal/Meaning/HeadStartScope.lean;
    `sizes_in_scope`, HeadShapeScope.lean). `vocab_in_scope`: Z.p.X.P.h.V = ppref.V
    (`Hd.core_of_scope`, Johnson/Goal/Meaning/ScopeCore.lean: number 11 of the 41, from 0).
    `headScope_in_scope`: `HeadScope ppref` at the sizes of `Z.p.X.hS` (`sizes_in_scope`,
    `d_in_scope`).
  **`instOf_agrees_in_scope`**, **`instOf_of_hold_in_scope`**, **`sameRequest_in_scope`**: the three
    laws with these premises paid.
Limits. hW, hR and hX are premises: that a public part Z with hX exists at given files is not shown
here. hX SPEAKS OF `publicOf`, WHOSE ROUTINES CALL THE FORMAT'S EARLIER HASH `OnBytes.secondHashFunction` BY
NAME (`callsDigest`, OnBytes/Model/VerifyPublic.lean; `tableDigest`, OnBytes/Model/Config.lean). The
description makes its own public record by `publicOfO o`, with that hash as a letter o
(Johnson/Desc/ProofFile/PlanPlain.lean). With secondHashFunction for o this is `publicOf` itself
(`publicOfO_older`, Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean): there the laws below speak of
the description's own Z. For any other o the library has `publicOfO_two`
(Johnson/Desc/Ok/PlanWritten/PublicAtTwo.lean): if both functions return, their records are equal
outside the field `digests`. T, V and the output head's sizes are not in that field, so the three
premises could be had for such a Z as well; this file does not do it, and hX holds of such a Z only
if its digests are secondHashFunction's too. IN `instOf_of_hold_in_scope` o IS A FREE LETTER BESIDE hX: by
Pub.lean's comment on `holdBy`, with `verify-on-bytes`'s planner every instance is refused unless o
is the format's second hash function: so at another o that law may well speak of nothing. The reference
sizes alone. Nothing on a trace, on an honest prover or on whether anything is accepted. Nothing on
soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness of
extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.InstOfTies
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.Goal.Meaning.HeadStartScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile
open OnBytes OnBytes.Flat OnBytes.Model
open _root_.Inst.Model (ppref Instance)
open VerifiableInference.Desc.Kinds.Head (Sizes Request Token sizesOf requestOf)
open VerifiableInference.Desc.Kinds.Head.Law (HeadScope SameRequest)

section
variable {W : VerifierAndGoals.PublicFiles} {pp : _root_.Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {Z : Pub}
  (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
  (hX : Verify.publicOf W.pol W.KL lay = .ok Z.p.X)
include hW hR hX

/-- In scope the window is the reference's. -/
theorem window_in_scope : Z.p.X.T = ppref.T := by
  rw [VerifiableInference.Desc.Kinds.Head.Law.InScope.T_in_scope hW hR hX,
    (Meaning.HeadS.sizes_in_scope hW hR hX).1]
  rfl

/-- In scope the vocabulary is the reference's. -/
theorem vocab_in_scope : Z.p.X.P.h.V = ppref.V := (OnBytes.Road.Hd.core_of_scope hW hR hX).num 11

/-- In scope the output head's four numbers are as `HeadScope ppref` asks: T, V and d are `ppref`'s;
the fourth, the head's own sh, is 8. -/
theorem headScope_in_scope : @HeadScope (sizesOf Z.p.X.hS) ppref := by
  letI : Sizes := sizesOf Z.p.X.hS
  obtain ⟨e1, -, e3, e4, -, -, -⟩ := Meaning.HeadS.sizes_in_scope hW hR hX
  refine ⟨?_, e3, Meaning.HeadS.d_in_scope hW hR hX, e4⟩
  show 2 ^ Z.p.X.hS.lt = ppref.T
  rw [e1]
  rfl

variable {ξ : Inst} {x : Instance ppref}

/-- **`instOf_agrees` in scope.** -/
theorem instOf_agrees_in_scope (h : instOf ξ = some x) :
    startS Z ξ.pub = Z.s₀.withReq (Verify.words32 ξ.pub.request) ∧
      (requestOf (startS Z ξ.pub)).r = x.r ∧ (requestOf (startS Z ξ.pub)).e = x.e ∧
      (∀ t : Fin ppref.T, (requestOf (startS Z ξ.pub)).tok t.val = (x.prompt t).val) ∧
      (∀ i, ppref.T ≤ i → (requestOf (startS Z ξ.pub)).tok i = 0) ∧
      OnBytes.Desc.Reply.tokOf ξ.asked = x.y.val ∧
      OnBytes.Desc.Reply.isToken ppref.V ξ.asked = true ∧
      OnBytes.Desc.Reply.reqForm ppref.T x.r x.e x.y.val = true :=
  instOf_agrees (window_in_scope hW hR hX) (vocab_in_scope hW hR hX) h

/-- **`instOf_of_hold` in scope.** On the free letter o: see "Limits" at the top of this file. -/
theorem instOf_of_hold_in_scope {o : SecondHashFunctionArgument} {mk : LinksBy} {G : Ground}
    (h : holdBy o mk Z ξ = .ok G) : (instOf ξ).isSome = true :=
  instOf_of_hold (window_in_scope hW hR hX) (vocab_in_scope hW hR hX) h

/-- **`sameRequest_of_instOf` in scope.** -/
theorem sameRequest_in_scope (h : instOf ξ = some x) :
    @SameRequest (sizesOf Z.p.X.hS) (requestOf (startS Z ξ.pub))
      ⟨OnBytes.Desc.Reply.tokOf ξ.asked⟩ ppref x :=
  sameRequest_of_instOf (window_in_scope hW hR hX) (vocab_in_scope hW hR hX) h
    (headScope_in_scope hW hR hX)

end

end ProofFile

#print axioms ProofFile.window_in_scope
#print axioms ProofFile.vocab_in_scope
#print axioms ProofFile.headScope_in_scope
#print axioms ProofFile.instOf_agrees_in_scope
#print axioms ProofFile.instOf_of_hold_in_scope
#print axioms ProofFile.sameRequest_in_scope
