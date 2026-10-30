-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ExitServed.lean: the exit code 0 of verify-on-bytes: the clauses of `main_zero_stages`
(OnBytes/K/ExitZero.lean), at the same values, and three more at the end. For proofs only; the
program does not import this file.

  `main_zero_served`: the three more: the common beginning C of the stages holds the public values
    and the links that the planner made of the three public files; each of the six other files that
    were read is within its limit; and, if the options are the served ones (an ID, 128 bits, neither
    -no-proof-of-work nor -policy), the user's statement as read passes `servedAt`
    (OnBytes/K/Served.lean) at the three public files as read.
  `servedAt_pins`: `servedAt Z x` is the three pins and `servedAt` at x's own three files.
So at the exit code 0 "served" asks of the user's statement the three pins and the options, and
nothing else.
What is not claimed: see the heads of OnBytes/K/Served.lean, ExitStages.lean and ExitZero.lean.

-/
import OnBytes.K.ExitZero
import OnBytes.K.ServedLaws

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event fileLimit wholeReads kindOf Asked)
open OnBytes.Proof

/-- `servedAt Z x` is the three pins and `servedAt` at x's own three files. -/
theorem servedAt_pins (Z : Pub) (x : UserStm) :
    servedAt Z x = true ↔
      x.pol = Z.pol ∧ x.lay = Z.lay ∧ x.KL = Z.KL ∧ servedAt ⟨x.pol, x.lay, x.KL⟩ x = true := by
  unfold servedAt
  simp only [Bool.and_eq_true, decide_eq_true_eq, true_and, and_assoc]

/-- The exit code 0 of the entry function (`YES` or `WITHIN LIMITS`). In words: the head of this
file. -/
theorem main_zero_served {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (r : Model.Verify.Read)
      (lay ent : ByteArray)
      (t : List Event) (p : Model.Verify.Planned) (C : Model.Verify.Common)
      (table further : Params.TableName) (id : String) (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof r.entry (.bytes r.pol) (.bytes r.KL)
        (.bytes lay) (.bytes r.key) (.bytes r.request) (.bytes r.y) (.bytes r.proof)
        (.bytes ent) ++ t) s s' ∧
      r.layout = some lay ∧ r.key.size ≤ fileLimit ∧ ent.size ≤ fileLimit ∧
      Model.Verify.planned r.pol r.KL (some lay) = .ok p ∧
      Model.Verify.commonOfCall r = .ok C ∧ C.chains = p.chains ∧
      Key.check p.chains.key r.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table ent = .ok further ∧
      (∃ so cov item links,
        Model.Head.stFromCall (Model.Verify.words32 r.request) (Model.Verify.words32 r.y) C.X.T =
          .ok so ∧
        Model.Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
        Proof.requestItem r.pol r.KL r.request = some item ∧
        Model.Verify.linksOf C.X cov = .ok links ∧
        Proof.check p.chains.proof further r.entry item r.request (Model.ofNat so.y)
          (Model.Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first C.X.layers.wsLay) r.proof = .accepted) ∧
      a.options.id = some id ∧
      Model.Verify.idAsked id =
        some (Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg table)) ∧
      a.options.bits = 128 ∧
      Tie.SameChains p (Params.configurationDigest [r.pol, lay, r.KL]) ∧
      StagesPassed C 128 ∧
      (∃ ac w, Model.Verify.requestStage C a.options r ent = .ok (.passed, ac, w)) ∧
      (C.X = p.X ∧ C.built = p.built) ∧
      (r.pol.size ≤ Shell.textLimit ∧ lay.size ≤ Shell.textLimit ∧ r.KL.size ≤ fileLimit ∧
        r.request.size ≤ fileLimit ∧ r.y.size ≤ fileLimit ∧ r.proof.size ≤ fileLimit) ∧
      (optionsServed a.options = true →
        servedAt ⟨r.pol, lay, r.KL⟩ ⟨r.pol, lay, r.KL, r.request, r.y, a.options⟩ = true) := by
  rw [Shell.main_eq] at h
  obtain ⟨config, ivk, request, y, proof, a, pol, kl, lay, key, req, yy, prf, ent, k, e, l, k1, _,
    h2, hp, k2, k3, sz⟩ := Shell.program_zero_run h
  rw [← k3] at hp
  obtain ⟨r, entb, p, C, table, further, g1, g2, g3, g4, g5, g6, g7, g8, g9, _⟩ :=
    Model.Verify.wholeCall_passed k2 hp
  obtain ⟨⟨id, i1, i2⟩, i3⟩ := Model.Verify.wholeCall_id k2 hp g1 g4 g7
  obtain ⟨_, _, q3, q4⟩ := wholeCall_stages hp g1 g3 g5
  obtain ⟨x1, _, x3⟩ := common_fields g5 g4
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := Model.Verify.readCall_ok g1
  obtain ⟨layb, hl⟩ := Model.Verify.planned_layout g4
  rw [hl] at f3 g4
  have q5 := fun ho => wholeCall_served k2 hp g1 g3 g5 hl g4 ho
  cases Shell.fileIn_some f1
  cases Shell.fileIn_some f2
  cases Shell.layoutIn_some f3
  cases Shell.fileIn_some f4
  cases Shell.fileIn_some f5
  cases Shell.fileIn_some f6
  cases Shell.fileIn_some f7
  cases Shell.fileIn_some g3
  subst g2
  obtain ⟨pre, post, e⟩ := Shell.whole_id_named k1 i1
  obtain ⟨so, cov, item, links, c1, c2, c3, c4, c5⟩ := g9
  rw [i3] at q4
  exact ⟨config, ivk, request, y, proof, a, r, layb, entb, _, p, C, table, further, id, pre, post,
    e, k1, h2, hl, Nat.le_of_lt_succ (sz (ivk ++ "/key.bin") _ _ (by simp [wholeReads])),
    Nat.le_of_lt_succ (sz (ivk ++ "/leaf/" ++ toString r.entry ++ ".bin") _ _
      (by simp [wholeReads])), g4, g5, g6, g7, g8, ⟨so, cov, item, links, c1, c2, c3, c4, c5⟩, i1,
    i2, i3, Tie.checks_same g4 g7 g8 c5, q4, q3, ⟨x1, x3⟩,
    ⟨Nat.le_of_lt_succ (sz (config ++ "/policy.txt") _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz (config ++ "/layout.txt") _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz (config ++ "/KL.bin") _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz request _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz y _ _ (by simp [wholeReads])),
      Nat.le_of_lt_succ (sz proof _ _ (by simp [wholeReads]))⟩, q5⟩

end OnBytes.K

#print axioms OnBytes.K.servedAt_pins
#print axioms OnBytes.K.main_zero_served
