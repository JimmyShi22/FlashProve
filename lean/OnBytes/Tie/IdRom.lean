-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/IdRom.lean: the key behind a commitment ID on query logs of the library's generic
language, and the bound under a random oracle with the event on two algorithms and the oracle alone.
No probability of the program.

In this file "the commitment ID" ("the ID"), where it stands by itself, is not the format's. It is
the hash function's answer at a shorter string, the format's string for its ID without the record's
seed (`idCode`, OnBytes/Tie/IdKey.lean). The format's rule (R4.11; `Fmt.publishedBytes`,
Fmt/Rules4.lean) hashes the string with the seed.

OnBytes/Tie/IdKey.lean and OnBytes/Tie/IdBound.lean speak of logs and algorithms in the library's
language of one oracle (`ZKCP.Trace`, `ZKCP.OComp`). The bounds of OnBytes/Slice/ stand in its
generic language over the family with one oracle (`Rom.Trace (rom 256)`, `Rom.OComp`). This file has
what is on logs in that second language, with the reader `idRead` (OnBytes/Tie/IdRead.lean) in the
place of a choice, and a form of the bound that holds no verifier; that form still stands in the
first language, with `ZKCP.firstKey`, and OnBytes/Slice/IdMaker.lean carries it over. A key
(`IdKey`) is a shape, 32 bytes for the digest of the public files, and a table; it is the library's
word for what a digest stands for, not the key file.

Main definition: `firstId`.
Main theorems.
- `firstId_trOf`: `firstId d σ` is the library's `ZKCP.firstKey idCode d` on σ as a log of the first
  language.
- `id_of_romLog`: `id_of_log` (OnBytes/Tie/IdKey.lean) on logs of the second language; no
  probability. It uses `answerRepeats_trOf`.
- `first_id_at`: under a random oracle f. A first algorithm with at most tC queries puts out a value
  b, off which `dig` reads a digest; a second one with at most tP queries, given b, puts out x, off
  which `key` reads a key. With probability at most (tC + tP + 2)^2 / 2^256 two different entries of
  the two logs have one answer, or the key has a code at which f answers the digest and is not the
  first key of that digest in the first log (which may hold none).

What is not claimed. No probability is stated of the program, which is the Lean port built from
OnBytes/, or of BLAKE2b: `first_id_at` is on an oracle that is drawn at random, and its event speaks
of the two algorithms' logs. No verifier stands in it: that some verifier says yes only if the
oracle answers the digest at the key's code is a matter of that verifier, and no checker of OnBytes/
compares an ID (`commonOf`, OnBytes/Model/VerifyStages.lean, the steps that the model's stages
share, compares the caller's ID with `Key.commitmentId`: at the program's own hash, and at the
string with the seed). Nothing on soundness. The bound is not tight and says nothing once it reaches
1. All limits in the heads of the three files named above hold here too. For proofs only; the
program does not import this file.

-/
import OnBytes.Tie.IdRead
import OnBytes.Tie.IdBound
import Rom.Bridge

set_option autoImplicit false

namespace OnBytes.Tie

open ZKCP ZKCP.DigestKey
open Rom (rom)
open scoped ENNReal

/-- The first key of a digest in a log of the generic language: the first value that `idRead`
returns on a query of the log whose answer is the digest. Nothing in it is taken by choice. -/
def firstId (d : Digest 256) (σ : Rom.Trace (rom 256)) : Option IdKey :=
  σ.findSome? fun e => if e.2.2 = d then idRead e.2.1 else none

/-- `firstId` is the library's `ZKCP.firstKey` at `idCode`, on the log in the language of one
oracle. -/
theorem firstId_trOf (d : Digest 256) (σ : Rom.Trace (rom 256)) :
    firstKey idCode d (Rom.trOf σ) = firstId d σ := by
  rw [firstKey_idRead]
  unfold firstId Rom.trOf
  rw [List.findSome?_map]
  rfl

/-- Two logs of the generic language, taken to the language of one oracle, with one entry between
them and one behind, and taken back: the two logs with these entries. -/
theorem trTo_mid {lam : ℕ} (σC σP : Rom.Trace (rom lam)) (x y : Str × Digest lam) :
    Rom.trTo (Rom.trOf σC ++ x :: (Rom.trOf σP ++ [y])) =
      σC ++ ⟨(), x.1, x.2⟩ :: (σP ++ [⟨(), y.1, y.2⟩]) := by
  have h1 : ∀ a b : ZKCP.Trace lam, Rom.trTo (a ++ b) = Rom.trTo a ++ Rom.trTo b :=
    fun _ _ => List.map_append
  have h2 : ∀ (z : Str × Digest lam) (a : ZKCP.Trace lam),
      Rom.trTo (z :: a) = ⟨(), z.1, z.2⟩ :: Rom.trTo a := fun _ _ => rfl
  rw [h1, h2, h1, Rom.trTo_trOf, Rom.trTo_trOf]
  rfl

/-- The library's event `ZKCP.AnswerRepeats` on two logs of the generic language, taken to the
language of one oracle, with one entry between them and one behind, is its step event
`ZKCP.DigestKey.RepeatsAt` on the two logs with these entries. -/
theorem answerRepeats_trOf {lam : ℕ} (σC σP : Rom.Trace (rom lam)) (q1 : Str) (r1 : Digest lam)
    (q2 : Str) (r2 : Digest lam) :
    AnswerRepeats (Rom.trOf σC ++ (q1, r1) :: (Rom.trOf σP ++ [(q2, r2)])) ↔
      Rom.StepEvent RepeatsAt (σC ++ ⟨(), q1, r1⟩ :: (σP ++ [⟨(), q2, r2⟩])) := by
  unfold AnswerRepeats
  rw [trTo_mid σC σP (q1, r1) (q2, r2)]

/-- On query logs of the generic language; no probability. σC and σP are two logs, d a digest, k a
key with the code s. If the library's step event `ZKCP.DigestKey.RepeatsAt` has not happened in σC,
then a query at d written as bits, then σP, then the query at s with the answer d, then
`firstId d σC` is k, and two entries of σC and σP with one answer have one query. -/
theorem id_of_romLog (σC σP : Rom.Trace (rom 256)) (d r0 : Digest 256) (k : IdKey) (s : Str)
    (hs : idCode k = some s)
    (hno : ¬ Rom.StepEvent RepeatsAt (σC ++ ⟨(), spelling d, r0⟩ :: (σP ++ [⟨(), s, d⟩]))) :
    firstId d σC = some k ∧
      ∀ e ∈ σC ++ σP, ∀ e' ∈ σC ++ σP, e.2.2 = e'.2.2 → e.2.1 = e'.2.1 := by
  have hno' : ¬ AnswerRepeats (Rom.trOf σC ++ (spelling d, r0) :: (Rom.trOf σP ++ [(s, d)])) :=
    fun h => hno ((answerRepeats_trOf σC σP (spelling d) r0 s d).1 h)
  obtain ⟨h1, h2⟩ := id_of_log (Rom.trOf σC) (Rom.trOf σP) d r0 k s hs hno'
  refine ⟨(firstId_trOf d σC).symm.trans h1, fun e he e' he' ha => ?_⟩
  by_contra hne
  have m : ∀ x ∈ σC ++ σP, ((x.2.1, x.2.2) : Str × Digest 256) ∈ Rom.trOf σC ++ Rom.trOf σP := by
    intro x hx
    unfold Rom.trOf
    rw [← List.map_append]
    exact List.mem_map_of_mem hx
  exact h2 _ (m e he) _ (m e' he') (fun h => hne (congrArg Prod.fst h)) ha

/-- **A clash, or another key under the ID, under a random oracle; the event is on two algorithms
and the oracle.** See the head. It stands in the library's language of one oracle. The two further
queries in the bound, at the digest written as bits and at the key's code, are made in the analysis
alone. No verifier stands in the statement; no probability is stated of the program or of BLAKE2b;
the bound says nothing once it reaches 1. -/
theorem first_id_at {β X : Type} (Ct : OComp 256 β) (dig : β → Digest 256)
    (Pt : β → OComp 256 X) (key : X → IdKey) (tC tP : ℕ) (hC : Ct.QueryBound tC)
    (hP : ∀ b, (Pt b).QueryBound tP) :
    Pr (Ct.withTrace.bind fun o => (Pt o.1).withTrace.bind fun o' => .pure (o, o'))
      (fun f => {y | Clash (y.1.2 ++ y.2.2) ∨ ∃ s, idCode (key y.2.1) = some s ∧
        f s = dig y.1.1 ∧ firstKey idCode (dig y.1.1) y.1.2 ≠ some (key y.2.1)})
      ≤ (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_)
    (Pr_answerRepeats_le (committerProverAndKeyCodeQueryRun idCode (Ct.mapO fun b => (dig b, b))
        fun b => (Pt b).mapO fun x => ((), (key x, ()))) _
      (queryBound_committerProverAndKeyCodeQueryRun idCode (OComp.QueryBound.mapO _ _ tC hC)
        fun b => OComp.QueryBound.mapO _ _ tP (hP b)))
  show prob ((Ct.withTrace.bind fun o => (Pt o.1).withTrace.bind fun o' =>
      .pure (o, o')).run f) _ ≤
    prob ((committerProverAndKeyCodeQueryRun idCode (Ct.mapO fun b => (dig b, b))
      fun b => (Pt b).mapO fun x => ((), (key x, ()))).withTrace.run f) {o | AnswerRepeats o.2}
  rw [withTrace_joined, OComp.withTrace_mapO, OComp.mapO_bind, run_bind, run_bind, prob_bind,
    prob_bind]
  refine expect_mono _ fun o => ?_
  simp only [OComp.withTrace_mapO, OComp.mapO_bind]
  show _ ≤ prob (((Pt o.1).withTrace.bind fun o' =>
      (askCode idCode (key o'.1)).withTrace.bind fun c =>
        .pure ((), o.2 ++ (spelling (dig o.1), f (spelling (dig o.1))) :: (o'.2 ++ c.2))).run f)
    {o | AnswerRepeats o.2}
  rw [run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o' => ?_
  have mem : ∀ (tl : ZKCP.Trace 256), ∀ e ∈ o.2 ++ o'.2,
      e ∈ o.2 ++ (spelling (dig o.1), f (spelling (dig o.1))) :: (o'.2 ++ tl) := by
    intro tl e he
    rcases List.mem_append.1 he with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have clash : ∀ (tl : ZKCP.Trace 256), Clash (o.2 ++ o'.2) →
      AnswerRepeats (o.2 ++ (spelling (dig o.1), f (spelling (dig o.1))) :: (o'.2 ++ tl)) := by
    rintro tl ⟨e1, h1, e2, h2, hne, ha⟩
    exact answerRepeats_of_two (mem tl e1 h1) (mem tl e2 h2) hne ha
  show prob (PMF.pure (o, o')) _ ≤ _
  rw [prob_pure]
  split
  · rename_i hE
    cases hs : idCode (key o'.1) with
    | none =>
      have er : askCode (lam := 256) idCode (key o'.1) = .pure () := by
        unfold askCode
        rw [hs]
      rw [er]
      show 1 ≤ prob (PMF.pure ((), o.2 ++
        (spelling (dig o.1), f (spelling (dig o.1))) :: (o'.2 ++ []))) {o | AnswerRepeats o.2}
      rw [prob_pure]
      rcases hE with hc | ⟨s, h1, _⟩
      · have hm : ((), o.2 ++ (spelling (dig o.1), f (spelling (dig o.1))) :: (o'.2 ++ [])) ∈
            {o : Unit × ZKCP.Trace 256 | AnswerRepeats o.2} := clash [] hc
        rw [if_pos hm]
      · have h1' : idCode (key o'.1) = some s := h1
        rw [hs] at h1'
        cases h1'
    | some s =>
      rw [askCode_of_some hs]
      show 1 ≤ prob (PMF.pure ((), o.2 ++ (spelling (dig o.1), f (spelling (dig o.1))) ::
        (o'.2 ++ [(s, f s)]))) {o | AnswerRepeats o.2}
      have hm : ((), o.2 ++ (spelling (dig o.1), f (spelling (dig o.1))) :: (o'.2 ++ [(s, f s)])) ∈
          {o : Unit × ZKCP.Trace 256 | AnswerRepeats o.2} := by
        rcases hE with hc | ⟨s', h1, h2, hk⟩
        · exact clash _ hc
        · have h1' : idCode (key o'.1) = some s' := h1
          rw [hs] at h1'
          obtain rfl := Option.some.inj h1'
          have h2' : f s = dig o.1 := h2
          show AnswerRepeats (o.2 ++ (spelling (dig o.1), f (spelling (dig o.1))) ::
            (o'.2 ++ [(s, f s)]))
          rw [h2']
          exact answerRepeats_of_hit idCode_oneToOne o.2 o'.2 (dig o.1) _ hs hk
      rw [prob_pure, if_pos hm]
  · exact zero_le _

end OnBytes.Tie
