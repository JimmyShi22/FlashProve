-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/InsOf.lean: the request file and the reply file as an instance: one definition, and its
law at the exit code 0 of verify-on-bytes.

`insOf P x` is `buildOf P` (Johnson/Flat/Instance.lean) at the prompt, the output and the further
tokens that OnBytes/K/Tokens.lean reads off the user's statement x. The field `insOf` of `K.Shape`
(OnBytes/K/TopVC.lean) is laid in Johnson/Top/TieInnerCompiledVerifier.lean as the
description's letter `buildInstance` at these three lists; here `buildOf P` stands for that letter. No
statement of this file says that an input's `buildInstance` is `buildOf P`.

Main names:
  `insOf`: the definition.
  `insOf_words`: where the program's reader of request and reply returns at the window P.T and
    `Head.coveredOf` returns at P.T and P.V: `insOf P x` returns an instance i, AND THE WORDS THAT
    SAY i (`requestWordsOf`, `replyWordsOf`) ARE THE WORDS OF THE TWO FILES. So every law that
    starts from an instance's words speaks of the files' words. Its r, e, y are the reader's, r < e,
    and y = 0 if e is before the window's end.
  `PortIns F o P p i cov ls`: a record of fourteen facts with names. `portIns_of_port`: from what
    the exit code 0 says of the bytes (`K.PortYesAt`), at the sizes P that `sizesAt` reads off the
    parameter file, there are p, i, cov, ls with that record: p is the plan of the three public
    files, of which P.T and P.V are the window and the vocabulary, with their bounds; i is what
    `insOf` returns, and its words are the two files' words; what the program's reader,
    `Head.coveredOf` and `Verify.linksOf` have returned in the call is said in i's own r, e and y.
    Each of the four is the one value of a function at the call's files. `insOf_port`: eight of
    these facts as one conjunction, for those who take it apart by place.
Limits: `sizesAt policy = .ok P` IS A PREMISE OF ITS OWN, NOT A CONSEQUENCE OF THE EXIT CODE 0:
`sizesAt` refuses a parameter file whose acceptance policy is not exact match; the program's own
condition of that name (`exactMatch` among the served conditions, OnBytes/Model/VerifyStages.lean)
is also met where the caller names a policy and where no covered position checks a token of the
request: so, by reading, the exit code 0 does not give the premise. Where it fails this file says
nothing. No guard shows the two premises of `insOf_port` met together at any files. Nothing on what
a yes says of the instance.

-/
import Johnson.Top.TokensBuild
import Johnson.Flat.SizesPlanned
import Johnson.Flat.InstanceLaws
import OnBytes.K.Top

set_option autoImplicit false

namespace OnBytes.Flat

open Inst.Model OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- **The request and the reply as an instance**, at the sizes P. -/
def insOf (P : Params) (x : K.UserStm) : Option (Instance' P) :=
  buildOf P (K.promptOf x, K.outputOf x) (K.auxOf x)

/-- What the reader's second test says of the two files' lengths. -/
theorem stFromCall_sizes {R Q : Array UInt32} {T : Nat} {so : Head.StOwn}
    (h : Head.stFromCall R Q T = .ok so) : R.size = T + 2 ∧ Q.size = 1 := by
  unfold Head.stFromCall at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, h2, _⟩ := exc_bind h
  unfold Head.needed at h2
  split at h2
  · rename_i hb
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hb
    exact hb
  · cases h2

/-- **The words that say the built instance are the words of the two files.** -/
theorem insOf_words {P : Params} {x : K.UserStm} {so : Head.StOwn} {cov : Head.Covered}
    (h : Head.stFromCall (words32 x.request) (words32 x.y) P.T = .ok so)
    (hc : Head.coveredOf so P.T P.V = .ok cov) :
    ∃ i : Instance' P, insOf P x = some i ∧ requestWordsOf i = words32 x.request ∧
      replyWordsOf i = words32 x.y ∧ i.r = so.r ∧ i.e = so.e ∧ i.y.val = so.y ∧ i.r < i.e ∧
      (i.e < P.T → i.y.val = 0) := by
  obtain ⟨i, hb, e1, e2, e3, e4⟩ := K.build_of_files h hc
  obtain ⟨hT, hl, r1, r2, r3, r4, _⟩ := K.read_of h
  obtain ⟨sR, sQ⟩ := stFromCall_sizes h
  have hz := K.reply_zero_of h
  refine ⟨i, hb, ?_, ?_, e1, e2, e3, ?_, ?_⟩
  · apply Array.ext
    · simp [requestWordsOf, sR]
    · intro j h1 h2
      rw [sR] at h2
      by_cases hj : j < P.T
      · have a1 : (requestWordsOf i)[j] = UInt32.ofNat (i.prompt ⟨j, hj⟩).val := by
          simp [requestWordsOf, hj]
        have a2 : (K.tokensOf x).getD j 0 = ((words32 x.request)[j]).toNat := by
          unfold K.tokensOf
          rw [hT]
          simp [List.getD_eq_getElem?_getD, hj, sR]
        rw [a1, e4 ⟨j, hj⟩, a2]
        exact UInt32.ofNat_toNat
      · by_cases hj2 : j = P.T
        · subst hj2
          have a1 : (requestWordsOf i)[P.T] = UInt32.ofNat i.r := by
            simp [requestWordsOf]
          have a2 : so.r = ((words32 x.request)[P.T]).toNat := by
            rw [r1]
            unfold K.rOf
            rw [hT]
            simp [Array.getD_eq_getD_getElem?, sR]
          rw [a1, e1, a2]
          exact UInt32.ofNat_toNat
        · have hj3 : j = P.T + 1 := by omega
          subst hj3
          have a1 : (requestWordsOf i)[P.T + 1] = UInt32.ofNat i.e := by
            simp [requestWordsOf]
          have a2 : so.e = ((words32 x.request)[P.T + 1]).toNat := by
            rw [r2]
            unfold K.eOf
            rw [hT]
            simp [Array.getD_eq_getD_getElem?, sR]
          rw [a1, e2, a2]
          exact UInt32.ofNat_toNat
  · apply Array.ext
    · simp [replyWordsOf, sQ]
    · intro j h1 h2
      have hj : j = 0 := by
        rw [sQ] at h2
        omega
      subst hj
      have a2 : so.y = ((words32 x.y)[0]).toNat := by
        rw [r3]
        unfold K.yOf
        simp [Array.getD_eq_getD_getElem?, sQ]
      show UInt32.ofNat i.y.val = _
      rw [e3, a2]
      exact UInt32.ofNat_toNat
  · rw [e1, e2, r1, r2]
    exact r4
  · intro he
    rw [e3, r3]
    rw [e2, r2] at he
    exact hz he

/-- **What the exit code 0 gives of the request and the reply, said by the instance.** F: the call's
files; o: any options; P: the sizes; p: the plan of the three public files; i: the instance; cov:
the covered positions; ls: the links made at them. -/
structure PortIns (F : K.Files) (o : Options) (P : Params) (p : Planned) (i : Instance' P)
    (cov : Head.Covered) (ls : Array Stages.LinkH) : Prop where
  /-- p is what the planner returns at the call's three public files -/
  plan : planned F.pol F.KL (some F.lay) = .ok p
  /-- the sizes' window and vocabulary are the plan's, and their bounds -/
  window : P.T = p.X.T
  vocabulary : P.V = p.X.P.h.V
  window_lt : P.T < 2 ^ 32
  vocabulary_le : P.V ≤ 2 ^ 32
  vocabulary_pos : 0 < P.V
  /-- i is what `insOf` returns at the call's statement -/
  built : insOf P (K.stmOf F o) = some i
  /-- the words that say i are the words of the call's two files -/
  request_words : requestWordsOf i = words32 F.request
  reply_words : replyWordsOf i = words32 F.y
  /-- the reader's test on the instance -/
  range : i.r < i.e
  reply_zero : i.e < P.T → i.y.val = 0
  /-- what the program's reader has returned at the two files, in i's own numbers -/
  read : Head.stFromCall (words32 F.request) (words32 F.y) p.X.T =
    .ok { req := words32 F.request, r := i.r, e := i.e, y := i.y.val }
  /-- the covered positions and the links that the program has made of it -/
  covered : Head.coveredOf { req := words32 F.request, r := i.r, e := i.e, y := i.y.val } p.X.T
    p.X.P.h.V = .ok cov
  links : Verify.linksOf p.X cov = .ok ls

/-- **From what the exit code 0 says of the bytes.** In words: the head of this file. -/
theorem portIns_of_port {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options) {P : Params}
    (hP : sizesAt F.pol = .ok P) : ∃ p i cov ls, PortIns F o P p i cov ls := by
  obtain ⟨_, p, C, _, _, _, _, _, _, _, _, _, _, hpl, _, _, _, _,
    ⟨so, cov, _, ls, k1, k2, _, k4, _⟩, _, _, _, _, ⟨eX, _⟩, _⟩ := hp
  obtain ⟨a, b, c, d⟩ := sizesAt_planned hP hpl
  rw [eX] at k1 k2 k4
  have h1 : Head.stFromCall (words32 (K.stmOf F o).request) (words32 (K.stmOf F o).y) P.T =
      .ok so := by
    rw [a]
    exact k1
  have h2 : Head.coveredOf so P.T P.V = .ok cov := by
    rw [a, b]
    exact k2
  obtain ⟨i, g0, g1, g2, _, _, _, g3, g4⟩ := insOf_words h1 h2
  have hs := stFromCall_wordsOf i c d g3 g4
  rw [g1, g2, a] at hs
  have eso : so = { req := words32 F.request, r := i.r, e := i.e, y := i.y.val } :=
    Except.ok.inj (k1.symm.trans hs)
  rw [eso] at k2
  exact ⟨p, i, cov, ls, hpl, a, b, c, d, Nat.lt_of_le_of_lt (Nat.zero_le _) i.y.isLt, g0, g1, g2,
    g3, g4, hs, k2, k4⟩

/-- Eight of these facts as one conjunction. -/
theorem insOf_port {F : K.Files} {id : String} {table further : Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options) {P : Params}
    (hP : sizesAt F.pol = .ok P) :
    ∃ (p : Planned) (i : Instance' P),
      planned F.pol F.KL (some F.lay) = .ok p ∧ P.T = p.X.T ∧ P.V = p.X.P.h.V ∧
      insOf P (K.stmOf F o) = some i ∧ requestWordsOf i = words32 F.request ∧
      replyWordsOf i = words32 F.y ∧ i.r < i.e ∧ (i.e < P.T → i.y.val = 0) := by
  obtain ⟨p, i, _, _, I⟩ := portIns_of_port hp o hP
  exact ⟨p, i, I.plan, I.window, I.vocabulary, I.built, I.request_words, I.reply_words, I.range,
    I.reply_zero⟩

end OnBytes.Flat
