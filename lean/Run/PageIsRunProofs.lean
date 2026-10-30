-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsRunProofs.lean: the proofs of the statements of Run/PageIsRun.lean. Many statements of
this library are written twice: a definition in the namespace `Spec` states a proposition, and a
theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Limits: what the four statements do not claim is told in the head of Run/PageIsRun.lean, under 4.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIsRun
import Run.PageIsProofs
import Run.ThinTieProofs

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

section
variable (S : _root_.Fmt.Spec)
  (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)

/-- The verifier that the run functions over typed oracle functions run (`VPC`, Run/PlanQS.lean) is
the plain verifier at the typed oracle functions of the format's oracle (`VO Fmt.oracle`,
Run/PageIs.lean). -/
theorem vpc_vo (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) :
    VPC S C K chal dec cm π = VO _root_.Fmt.oracle S C K chal dec cm π := by
  rw [vpc_eq, famP_eq]
  exact (thin_verify Unit Unit 256 (K + 1) (LbS C (rds S) dec)
    (famOf _root_.Fmt.oracle (PDS S C dec) (K + 1)) Unit E0 (256 + 8 * S.plan.salt)
    256 .onl (PSof C (rds S) dec) (wqS C K chal (rds S) dec) _ _ some
    (fun s => some (.inl s)) 0 [cm] () π).symm

/-- Under `hs : smallB S file = true`: the lenient parser `parseLaxWP` gives the same at the
oracle's hash `Fmt.HO Fmt.oracle` and at the format's hash `Fmt.formatHash`. -/
theorem laxP_HO (file : ByteArray) (hs : smallB S file = true) :
    parseLaxWP (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle)
        (PSof C (rds S) dec) S (TYS S C dec) file =
      parseLaxWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file := by
  rw [(parseThin_parse (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) _ S _ file).2.1,
    (parseThin_parse (m := Id) _root_.Fmt.formatHash _ S _ file).2.1]
  exact lax_HO _ _ _ S _ file hs

end

theorem run_who : Spec.run_who := by
  intro S C K chal dec file hok hs
  rw [(runC_readers S C K chal dec file).2, ← laxP_HO S C dec file hs]
  unfold runOnC laxV
  rw [if_pos hok]
  unfold parseLaxWP
  simp only [idb, idp]
  cases hl : laxWhole (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S file with
  | none => rfl
  | some o =>
    have hf : LaxFacts (_root_.Fmt.HO _root_.Fmt.oracle) S o :=
      pi_facts _ (size_HO _ _root_.Fmt.size_oracle) S file o hok hl
    obtain ⟨run, pl, -, -, ht⟩ := pi_typed' (_root_.Fmt.HO _root_.Fmt.oracle) S C dec o hf
    show (match toBPrfP (PSof C (rds S) dec) (TYS S C dec) o with
      | some ([cm], π) => if VPC S C K chal dec cm π = true then Who.accepted else Who.verifier
      | _ => Who.reader) = if (match toBPrfP (PSof C (rds S) dec) (TYS S C dec) o with
      | some ([cm], π) => VO _root_.Fmt.oracle S C K chal dec cm π
      | _ => false) = true then Who.accepted else Who.verifier
    rw [ht]
    show (if VPC S C K chal dec _ _ = true then Who.accepted else Who.verifier) =
      if VO _root_.Fmt.oracle S C K chal dec _ _ = true then Who.accepted else Who.verifier
    rw [vpc_vo]

theorem run_lax : Spec.run_lax := by
  intro S C K chal dec file hok hs
  rw [run_who S C K chal dec file hok hs]
  cases hl : laxWhole (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S file with
  | none =>
    have : laxV _root_.Fmt.oracle S C K chal dec file = false := by
      unfold laxV parseLaxWP
      simp only [idb, idp, hl]
      rfl
    rw [this]
    rfl
  | some o =>
    dsimp only
    cases laxV _root_.Fmt.oracle S C K chal dec file <;> rfl

theorem run_two : Spec.run_two := by
  intro S dec file hok hs
  show runLaxC S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file =
    runLaxC S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file
  rw [run_who S _ _ _ dec file hok hs, run_who S _ _ _ dec file hok hs, two_kits S hok dec file]

theorem run_half : Spec.run_half := by
  intro S dec file hok hs hv
  have h1 : runLaxSP S dec file = .accepted :=
    of_decide_eq_true
      ((run_lax S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file hok hs).trans
        (pi_half _ S _ _ _ dec file (fit_pull S hok) hv))
  exact ⟨h1, (run_two S dec file hok hs).trans h1⟩

end Run.PQ
