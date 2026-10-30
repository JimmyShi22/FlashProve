-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsKeyStage.lean: the entry's arm with the answers alone, against a
committer that publishes the first root with its record, and a prover.

In LinkAnsTwoStage.lean the committer publishes the first root alone, and the prover names both
records. Here the first stage publishes two fields of the typed key (`FullKey`, Cms.lean): the root and
the record of the first table; the prover makes the further root, its record and the proof string. A
corollary of `arm_pr_two`: the record is handed on inside the committer's state.

  `exp3`          the experiment over one hash function: committer (root, record), prover, arm, with
                  the two logs of strings
  `arm_pr_key`    the bound, the same as `arm_pr_two`'s

Limits: soundness alone.
  * "Publish" means: hand a typed root and a typed record to the arm. There is no commitment ID, no
    key file and no byte in it. Not here, and needed for a whole verifier: the ID's step, the key's
    arm (that the first table decodes) and the proof file's arm in two stages, and their join.
  * Where the first table decodes to nothing, nothing is said of the further table.
  * The word under the further root is read off both logs, as they stand at the end of the prover's
    run. The arm's calls stand in neither log.
  * The theorem is for every coding m, and none is given here. One exists where the instances are
    countable, by choice (Johnson/Flat/EntryCoding.lean [not in this library; so here read: not
    proved in this library]); none is shown to be
    the programs'. m, the wires, the code of the answers and the arm are fixed before the function
    is drawn, `S.cfg` with them. Committer and prover put out typed values, not bytes.
  * n counts the two stages' calls on strings, one query for the announcement, and the arm's typed
    queries, five times.
  * The bullets under "Limits" in the heads of LinkAnsPr.lean and LinkAnsOne.lean hold of this file
    too, but for those that begin "In this file"; for t read tC + tP + 1.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsTwoStage

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-- The log of an algorithm whose output is passed through a map. -/
theorem withTrace_map {Sp : OSpec} {α β : Type} (c : OComp Sp α) (f : α → β) :
    (c.bind fun a => OComp.pure (f a)).withTrace =
      c.withTrace.bind fun o => OComp.pure (f o.1, o.2) := by
  rw [Rom.withTrace_bind]
  refine congrArg _ (funext fun o => ?_)
  simp only [OComp.withTrace, OComp.bind, List.append_nil]

/-- what the prover puts out here: the further root, its record, Link's proof string -/
abbrev Out3 (lam : ℕ) (L : HolographicProtocol I X) (aL : RoundSplits L.link.shape) : Type :=
  Dig lam × L.Rec × OneProtocolProof lam (batLC L aL)

/-- The experiment over one hash function: the committer publishes the first root and its record;
the prover; the arm; with the two logs of strings. -/
def exp3 (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {St : Type}
    (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St)) (Pt : St → OComp (rom lam) (Out3 lam L aL)) :
    OComp (rom lam)
      ((((Dig lam × L.Rec) × St) × Trace (rom lam)) × (Out3 lam L aL × Trace (rom lam)) × Bool) :=
  Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b =>
    ((V (a.1.1.1, b.1.1, a.1.1.2, b.1.2.1, b.1.2.2)).overOne m).bind fun v => OComp.pure (a, b, v)

/-- the committer, its record handed on inside the state -/
def toCt {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St)) :
    OComp (rom lam) (Dig lam × (L.Rec × St)) :=
  Ct.bind fun a => OComp.pure (a.1.1, (a.1.2, a.2))

/-- the prover, naming the committer's record -/
def toPt {St : Type} (Pt : St → OComp (rom lam) (Out3 lam L aL)) :
    L.Rec × St → OComp (rom lam) (Out2 lam L aL) :=
  fun s => (Pt s.2).bind fun b => OComp.pure (b.1, s.1, b.2.1, b.2.2)

/-- The experiment in two stages at these two is the experiment here, its output passed through a
map. -/
theorem exp2_to (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {St : Type}
    (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St)) (Pt : St → OComp (rom lam) (Out3 lam L aL)) :
    exp2 W V m (toCt Ct) (toPt Pt) =
      (exp3 W V m Ct Pt).bind fun x =>
        OComp.pure (((x.1.1.1.1, (x.1.1.1.2, x.1.1.2)), x.1.2),
          ((x.2.1.1.1, x.1.1.1.2, x.2.1.1.2.1, x.2.1.1.2.2), x.2.1.2), x.2.2) := by
  unfold exp2 exp3 toCt toPt
  simp only [withTrace_map, OComp.bind_assoc, OComp.bind]

/-- An arm that begins with the seed queries is sound against every committer and prover over one
hash function, the committer publishing the first root with its record: the arm accepts, and what it
promises fails of the word that the committer's own log of strings determines under the first root
and the word that both logs determine under the further root, with probability at most
n εs + 2 (n + 1)² / 2^lam, where n = 5 (tC + tP + 1 + tVL), tC bounds the committer's queries (hC)
and tP the prover's at every state (hP). The premises are those of `arm_pr` (LinkAnsPr.lean): Link's
soundness round by round (hsL), its locality (hlL), the annotation's coherence (hcL), `OKLA W`,
`AnsOK cA`, `S.Law εs`, the bound on the rounds' errors (hbL), `IsArm`; and the arm begins with the
seed queries (`HeadSeeds`), and lam is not 0. m is any coding. -/
theorem arm_pr_key {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (hH : HeadSeeds W S V) (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pt : St → OComp (rom lam) (Out3 lam L aL))
    (tC tP : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    Rom.Pr (exp3 W V m Ct Pt)
        (fun _ => {x | x.2.2 = true ∧
          ¬ LinkHoldsAt L (extEnc W (singleTr m x.1.2) x.1.1.1.1)
            (extEnc W (singleTr m (x.1.2 ++ x.2.1.2)) x.2.1.1.1) x.1.1.1.2 x.2.1.1.2.1}) ≤
      (((tC + tP + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hC' : (toCt (L := L) Ct).QueryBound tC := by
    have h : (toCt (L := L) Ct).QueryBound (tC + 0) := hC.bind fun _ => trivial
    exact h
  have hP' : ∀ s, (toPt (aL := aL) Pt s).QueryBound tP := fun s => by
    have h : (toPt (aL := aL) Pt s).QueryBound (tP + 0) := (hP s.2).bind fun _ => trivial
    exact h
  have h := arm_pr_two hsL hlL hcL hW hA hSd hbL hV hH hlam m (toCt Ct) (toPt Pt) tC tP hC' hP'
  rw [exp2_to, Rom.Pr_bind_pure] at h
  exact h

end TypedOracleCompiler.Compile.Batch.Cms
