-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/IdBound.lean: under a random oracle, and for any verifier that says no unless the ID is
the oracle's answer at the code of the key that it is brought: the key behind an ID is the first one
in the committer's own query log, except with probability at most (tC + tP + 2)^2 / 2^256. No
probability of the program.

OnBytes/Tie/IdKey.lean codes a key one to one. Its string is without the record's seeds, so it is
not the string that the programs hash for a commitment ID (`Key.commitmentId`,
OnBytes/Key/Table.lean; on that string: OnBytes/Tie/IdKeySeed.lean, OnBytes/Tie/IdKeySeedFmt.lean).
"The ID" in this file is the oracle's answer at `idCode`, and nothing ties it to the programs' ID.
A key (`IdKey`) is a shape, 32
bytes for the digest of the public files, and a table; it is the library's word for what a digest
stands for, not the key file. The library proves, inside its theorem on a scheme whose verifier
holds the digest of a key (`HasIndexBindingWith.of_verifyDigestKey`, Compile/DigestKeyBinding.lean),
that the key which a prover brings under a digest is the first key of that digest in the committer's
log, outside an event on the log. Here that step is stated by itself, at `idCode`, for a verifier
that is a variable.

Main definition: `Clash`. Main theorems: `first_id`; `hV_verifyDigestKey`, a verifier that meets its
hypothesis.

The experiment. The oracle is drawn: a function from bit strings to strings of 256 bits, each value
uniform, all independent. A committer with at most tC queries puts out a digest d and a state. A
prover with at most tP queries, given the state, puts out a value x. A verifier V, given d and x,
says yes or no. All three may toss coins. `key` reads a key off x. The event: two different entries
of the committer's and the prover's logs have one answer (`Clash`); or V says yes and the first key
in the committer's log whose code has the answer d is not `key x` (the log may hold none). Its
probability is at most (tC + tP + 2)^2 / 2^256. V's own queries are not counted: the two further
queries, at d written as bits and at the key's code, are made in the analysis alone.

What is not claimed. V is a variable with one hypothesis, `hV`: under every oracle f, unless `key x`
has a code at which f answers d, V says no. The library's `ZKCP.verifyDigestKey` at `idCode` meets
it, whatever runs behind its comparison (`hV_verifyDigestKey`); no function of OnBytes/ is shown to:
no checker there compares an ID, and the program hashes with BLAKE2b. A form of the program's
comparison at an oracle would say no at a key without a code only with the limit on the files'
lengths, which is the shell's (`Shell.fileLimit`) and not `Key.check`'s; and that comparison is with
the hash at the string of the format's rule (`Key.commitmentId`, OnBytes/Key/Table.lean), not at
`idCode`: it does not meet `hV`. Nothing on soundness. No probability is stated of the program,
which is the Lean port built from OnBytes/, or of BLAKE2b. V's run is a step of the experiment, and
the theorem stands in the library's language of one oracle (`ZKCP.OComp`, `ZKCP.Pr`), not in that of
OnBytes/Slice/OneWorld.lean. OnBytes/Tie/IdRom.lean has the bound without a verifier, with the event
on the two makers and the oracle, and OnBytes/Slice/IdMaker.lean carries it to the other language.
The digest of the public files is part of the key, so it is the prover's to bring, and a query by
which the prover forms it counts in tP; that it is the digest of any files is not stated.
`ZKCP.firstKey` inverts the code by choice, not by an algorithm. The bound is not tight and says
nothing once it reaches 1. All limits in the head of OnBytes/Tie/IdKey.lean hold here too. Nothing
is said of the C++ program `cp_verify`. For proofs only; the program does not import this file.

-/
import OnBytes.Tie.IdKey

set_option autoImplicit false

namespace OnBytes.Tie

open ZKCP ZKCP.DigestKey
open scoped ENNReal

/-- Two different entries of a query log have one answer. -/
def Clash (log : ZKCP.Trace 256) : Prop := ∃ e1 ∈ log, ∃ e2 ∈ log, e1 ≠ e2 ∧ e1.2 = e2.2

/-- **The key behind an ID, under a random oracle, for an abstract verifier.** See the head for the
experiment. `hV`: under every oracle f, unless `key x` has a code at which f answers d, V says no on
d and x. Then with probability at most (tC + tP + 2)^2 / 2^256 two different entries of the
committer's and the prover's logs have one answer, or V says yes while `key x` is not the first key
in the committer's log whose code has the answer d. One event, bounded by the library's
`ZKCP.AnswerRepeats` on one log. The library's `ZKCP.verifyDigestKey` meets `hV`
(`hV_verifyDigestKey`); no function of OnBytes/ is shown to; no probability is stated of the program
or of BLAKE2b; the bound says nothing once it reaches 1. -/
theorem first_id {St X : Type} (Ct : OComp 256 (Digest 256 × St)) (Pt : St → OComp 256 X)
    (V : Digest 256 → X → OComp 256 Bool) (key : X → IdKey)
    (hV : ∀ f d x, (¬ ∃ s, idCode (key x) = some s ∧ f s = d) → (V d x).run f = PMF.pure false)
    (tC tP : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    Pr (Ct.withTrace.bind fun o => (Pt o.1.2).withTrace.bind fun o' =>
        (V o.1.1 o'.1).bind fun b => .pure (o, o', b))
      (fun _ => {y | Clash (y.1.2 ++ y.2.1.2) ∨
        (y.2.2 = true ∧ firstKey idCode y.1.1.1 y.1.2 ≠ some (key y.2.1.1))})
      ≤ (((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  refine le_trans (Pr_le_of_forall _
      (committerProverAndKeyCodeQueryRun idCode Ct fun st => (Pt st).mapO fun x => ((), (key x, ()))).withTrace _
      {o | AnswerRepeats o.2} fun f => ?_)
    (Pr_answerRepeats_le _ _ (queryBound_committerProverAndKeyCodeQueryRun idCode hC
      fun st => OComp.QueryBound.mapO _ _ tP (hP st)))
  rw [withTrace_joined, run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o => ?_
  simp only [OComp.withTrace_mapO, OComp.mapO_bind]
  show _ ≤ prob (((Pt o.1.2).withTrace.bind fun o' =>
      (askCode idCode (key o'.1)).withTrace.bind fun c =>
        .pure ((), o.2 ++ (spelling o.1.1, f (spelling o.1.1)) :: (o'.2 ++ c.2))).run f)
    {o | AnswerRepeats o.2}
  rw [run_bind, run_bind, prob_bind, prob_bind]
  refine expect_mono _ fun o' => ?_
  have mem : ∀ (tl : ZKCP.Trace 256), ∀ e ∈ o.2 ++ o'.2,
      e ∈ o.2 ++ (spelling o.1.1, f (spelling o.1.1)) :: (o'.2 ++ tl) := by
    intro tl e he
    rcases List.mem_append.1 he with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ h))
  have clash : ∀ (tl : ZKCP.Trace 256), Clash (o.2 ++ o'.2) →
      AnswerRepeats (o.2 ++ (spelling o.1.1, f (spelling o.1.1)) :: (o'.2 ++ tl)) := by
    rintro tl ⟨e1, h1, e2, h2, hne, ha⟩
    exact answerRepeats_of_two (mem tl e1 h1) (mem tl e2 h2) hne ha
  cases hs : idCode (key o'.1) with
  | none =>
    rw [run_bind, hV f o.1.1 o'.1 (by rintro ⟨s, h1, _⟩; rw [hs] at h1; cases h1), PMF.pure_bind]
    have er : askCode (lam := 256) idCode (key o'.1) = .pure () := by
      unfold askCode
      rw [hs]
    rw [er]
    show prob (PMF.pure (o, o', false)) _ ≤ prob (PMF.pure ((), o.2 ++
      (spelling o.1.1, f (spelling o.1.1)) :: (o'.2 ++ []))) {o | AnswerRepeats o.2}
    rw [prob_pure, prob_pure]
    split
    · rename_i hE
      rcases hE with hc | ⟨hb, _⟩
      · have hm : ((), o.2 ++ (spelling o.1.1, f (spelling o.1.1)) :: (o'.2 ++ [])) ∈
            {o : Unit × ZKCP.Trace 256 | AnswerRepeats o.2} := clash [] hc
        rw [if_pos hm]
      · cases hb
    · exact zero_le _
  | some s =>
    rw [askCode_of_some hs]
    show _ ≤ prob (PMF.pure ((), o.2 ++ (spelling o.1.1, f (spelling o.1.1)) ::
      (o'.2 ++ [(s, f s)]))) {o | AnswerRepeats o.2}
    rw [prob_pure]
    split
    · exact prob_le_one _ _
    · rename_i hno
      refine le_of_eq ?_
      rw [run_bind]
      by_cases hd : f s = o.1.1
      · refine prob_bind_eq_zero _ _ _ fun b => ?_
        show prob (PMF.pure (o, o', b)) _ = 0
        rw [prob_pure, if_neg]
        rintro (hc | ⟨_, hk⟩)
        · exact hno (clash _ hc)
        · refine hno ?_
          show AnswerRepeats (o.2 ++ (spelling o.1.1, f (spelling o.1.1)) :: (o'.2 ++ [(s, f s)]))
          rw [hd]
          exact answerRepeats_of_hit idCode_oneToOne o.2 o'.2 o.1.1 _ hs hk
      · rw [hV f o.1.1 o'.1 (by
          rintro ⟨s', h1, h2⟩
          rw [hs] at h1
          exact hd ((Option.some.inj h1) ▸ h2)), PMF.pure_bind]
        show prob (PMF.pure (o, o', false)) _ = 0
        rw [prob_pure, if_neg]
        rintro (hc | ⟨hb, _⟩)
        · exact hno (clash _ hc)
        · cases hb

/-- The hypothesis `hV` of `first_id` can be met: the library's verifier for a key behind a digest,
at `idCode`, with any verifier V behind its comparison, says no unless the key that it is brought
has a code at which the oracle answers the digest. It is `ZKCP.run_verifyDigestKey_of_ne`. -/
theorem hV_verifyDigestKey {X Pf : Type} (V : IdKey → X → Pf → OComp 256 Bool)
    (f : ZKCP.Oracle 256) (d : Digest 256) (x : X × (IdKey × Pf))
    (h : ¬ ∃ s, idCode x.2.1 = some s ∧ f s = d) :
    (verifyDigestKey V idCode d x.1 x.2).run f = PMF.pure false :=
  run_verifyDigestKey_of_ne V f d x.1 x.2 fun s hs he => h ⟨s, hs, he⟩

end OnBytes.Tie
