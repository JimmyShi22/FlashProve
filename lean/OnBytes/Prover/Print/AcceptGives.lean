-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/AcceptGives.lean: WHERE THE INTERACTIVE VERIFIER OF A WHOLE FILE ACCEPTS A
TRANSCRIPT, THE TEST ON THE SILENT ROUNDS HAS SAID YES AT THE PLAIN PARTS OF EVERY PROOF STRING THAT
HOLDS THE TRANSCRIPT's PLAIN PARTS. So, at the key file's and the proof file's tests, the printer's
clauses on the fronts follow from the accepts.

Main names.
  silents_of_plains   the three silent rounds' plain parts of a string (pls₁, pls₂, pls₃,
    OnBytes/TypedOracleCompiler/Joined/Verifier.lean) are the transcript's, if the string's plain parts are.
  silent_of_accept    the test's yes at the string's three silent plain parts.
  key_front, proof_front   at silK and silP (OnBytes/Flat/FilesAt.lean): the front's answers are the
    record's as the printer writes them; the joining round repeats them; at the key file the copy's
    number is 0.

By: wholeIOR_out_silent (OnBytes/Maker/WholeLaws.lean) · Tr.plains_snd (Iop/ShapeKit.lean) ·
silK_gives, silP_gives (OnBytes/Prover/Print/Answers.lean).

Does not show: that a transcript is accepted. The proof file's test does not read the copy's number.
Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Answers
import OnBytes.Maker.WholeLaws
import OnBytes.TypedOracleCompiler.Joined.Verifier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

theorem silents_of_plains (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (τ : Tr (chainsOf C D tF tJ t3).sh) (h : π.plains = τ.plains) :
    (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1 = ((chainsOf C D tF tJ t3).msgF τ).2 ∧
      (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1 = ((chainsOf C D tF tJ t3).msgJ τ).2 ∧
      (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = ((chainsOf C D tF tJ t3).msg3 τ).2 := by
  unfold pls₁ pls₂ pls₃
  rw [h]
  refine ⟨rfl, ?_, ?_⟩
  · show (Plains.snd (s := (chainsOf C D tF tJ t3).s₁) (Tr.plains τ.2.2)).1 = _
    rw [← Tr.plains_snd]
    rfl
  · show (Plains.snd (s := (chainsOf C D tF tJ t3).s₂)
      (Plains.snd (s := (chainsOf C D tF tJ t3).s₁) (Tr.plains τ.2.2)).2).1 = _
    rw [← Tr.plains_snd]
    show (Plains.snd (s := (chainsOf C D tF tJ t3).s₂)
      (Tr.plains ((chainsOf C D tF tJ t3).trJ τ).2.2)).1 = _
    rw [← Tr.plains_snd]
    rfl

theorem silent_of_accept (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (τ : Tr (chainsOf C D tF tJ t3).sh) (h : π.plains = τ.plains)
    (ha : (wholeDesc C D tF tJ t3 silent run).batch.loc.accept x y τ = true) :
    silent x (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1
      (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1
      (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = true := by
  obtain ⟨e1, e2, e3⟩ := silents_of_plains C D tF tJ t3 silent run π τ h
  rw [e1, e2, e3]
  exact wholeIOR_out_silent C D tF tJ t3 silent run x y τ ha

end

section
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {v lg s : ℕ}

/-- **The key file's front, from the accept.** -/
theorem key_front (run : RecP NZ v lg s → View → View → View → Bool) (rec : RecP NZ v lg s)
    (y : (oneExternalString (2 ^ D.a) SgX).Str) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silK run).batch)
    (τ : Tr (chainsOf C D tF tJ t3).sh) (h : π.plains = τ.plains)
    (ha : (wholeDesc C D tF tJ t3 silK run).batch.loc.accept rec y τ = true) :
    (pls₁ (wholeDesc C D tF tJ t3 silK run) π).1.answers =
        (trAns rec.2).map OnBytes.E.ofTriple ∧
      (pls₁ (wholeDesc C D tF tJ t3 silK run) π).1.copy = 0 ∧
      (pls₂ (wholeDesc C D tF tJ t3 silK run) π).1.answers =
        (pls₁ (wholeDesc C D tF tJ t3 silK run) π).1.answers :=
  silK_gives rec _ _ _ (silent_of_accept C D tF tJ t3 silK run rec y π τ h ha)

/-- **The proof file's front, from the accept.** -/
theorem proof_front {X : Type} (run : X × RecP NZ v lg s → View → View → View → Bool)
    (z : X × RecP NZ v lg s) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silP run).batch)
    (τ : Tr (chainsOf C D tF tJ t3).sh) (h : π.plains = τ.plains)
    (ha : (wholeDesc C D tF tJ t3 silP run).batch.loc.accept z y τ = true) :
    (pls₁ (wholeDesc C D tF tJ t3 silP run) π).1.answers =
        (trAns z.2.2).map OnBytes.E.ofTriple ∧
      (pls₂ (wholeDesc C D tF tJ t3 silP run) π).1.answers =
        (pls₁ (wholeDesc C D tF tJ t3 silP run) π).1.answers :=
  silP_gives z _ _ _ (silent_of_accept C D tF tJ t3 silP run z y π τ h ha)

end

end OnBytes.Prover.Print

#print axioms OnBytes.Prover.Print.silents_of_plains
#print axioms OnBytes.Prover.Print.silent_of_accept
#print axioms OnBytes.Prover.Print.key_front
#print axioms OnBytes.Prover.Print.proof_front
