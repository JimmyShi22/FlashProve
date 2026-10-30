-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFoldSess.lean: a bound over one drawn hash function for a check of the
proof file, in the form in which the check itself asks the function for its public digests
(`ArmBoundD`, Johnson/Top/ArmsD.lean). The session's soundness round by round and the other
hypotheses of `armB_pr_pub` are assumed; everything is an arbitrary parameter.

What this file states. `armBoundD_sess`: `ArmBoundD (fun _ => Pub) (armSessOf V m Pub) (holdsSessOf
Rno m) ε` with ε tC tP = n εs + 2 (n + 1)² / 2^lam at n = 3 (tC + tP + tVB). `armSessOf V m Pub` is
the check on a key, an instance and a proof: a proof without the session's string is refused; else
the public reading Pub (the function that asks for the public digests), then the check at its value,
at the further root, the instance, the further record and that string, through the coding at its
value. It reads neither the key nor the number of the stored copy. `holdsSessOf Rno m` is the
promise at the reading's value: of the word that the committer's log with the prover's behind it
determines under the further root. `noCoin_armSessOf`: where the reading tosses no coin and each
member of the family is a check in the sense of `IsArmB`, the check tosses no coin. No second hash
function appears in the statement. The fields `proofArm` of `CoreArmsD`
(Johnson/Top/OnFilesArmsD.lean) and of `CoreArmsCD` (Johnson/Top/OnFilesArmsCD.lean) are bounds of
this form. After Johnson/Top/ArmsFoldTest.lean, which has this for the key's check. The proof:
committer and prover, run one behind the other, are one algorithm (a maker) with at most tC + tP
queries, whose log is the committer's with the prover's behind it: `armBoundD_of_maker`
(Johnson/Top/ArmsFold.lean). That step does not show the instance to what it packs, so it is taken
at proofs that carry the instance (`armSessOf_fold`), and brought back by `ArmBoundD.comap`
(Johnson/Top/ArmsComap.lean).

Under which hypotheses. Those of `armB_pr_pub` (Johnson/TypedOracleCompiler/RecCompile/ProofAnsPublic.lean) but for
the maker's. The session's soundness (hsB) is taken at `L.early` and `L.late`: what of an instance
is written into a chain's first query, and the round into whose query it is written whole. At an
object L whose `early` is the identity the instance appears whole in the first query. That is a
property of L, which is a parameter here. The object, the wire, the family of checks, the family of
codings, the reading and the type of keys are arbitrary parameters.

What it does not show. All are parameters, and that the premises of `armBoundD_sess` can be met
together is not shown; until it is, it may be true and empty. At an ε of at least 1 it says nothing.
The reading `Pub` (an algorithm, which may ask a string made of an earlier answer) and the set of
its public strings are fixed before the function is drawn: a committer or a prover that writes the
public files after asking the function is not covered. Soundness alone: no yes is shown, and the
bound would hold of a check that refuses everything. The session's soundness is a hypothesis. Where
the word under the further root and the further record decode to nothing, and the record's seed is
no collision seed of that word, the promise holds whatever the instance is: that exception is
`ProofHoldsAt`'s own, and nothing in this file closes it: in the record of hypotheses on the three
checks the key's and the entry's checks' promises close it together, so no sentence on a false
instance rests on this bound alone. The further root, the further record and the instance are the
prover's. The word is read off both logs, not off the committer's alone. A check that also tests the
number of the stored copy, or a part of the key, is not this term: Johnson/Top/ArmsFoldGuard.lean
carries the bound to such checks. The reading's and the check's own queries appear in no log and in
no budget. The run's value, which the byte format hashes from a parameters' digest and bytes of the
proof string, is no public digest and is not reached. The other limits in the heads of
ProofAnsPublic.lean and ArmsFold.lean hold.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsFold
import Johnson.Top.ArmsComap
import Johnson.TypedOracleCompiler.RecCompile.ProofAnsPublic
import Johnson.TypedOracleCompiler.RecCompile.FrontRoot
import OnBytes.TypedOracleCompiler.Joined.YesByCutsMore
import Rom.NoCoinExits

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {D Wn Kt : Type}

/-- The proof's check on a key, an instance and a proof. -/
def armSessOf (V : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D)
    (_ : Kt) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) : OComp (rom lam) Bool :=
  match π.piB with
  | some p => Pub.bind fun d => (V d (π.link.1, x, π.link.2.1, p)).overOne (m d)
  | none => .pure false

/-- The promise at the reading's value d: of the word that the one-block entries, under the coding
at d, of the committer's log with the prover's behind it determine under the further root. -/
def holdsSessOf (Rno : I → X → Wn → Prop)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (d : D) (_ : Kt)
    (trC : Trace (rom lam)) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) (trP : Trace (rom lam)) : Prop :=
  ProofHoldsAt L (fun i x => ∃ w, Rno i x w) (extEnc W (singleTr (m d) (trC ++ trP)) π.link.1) x
    π.link.2.1

/-- What the fold packs of an instance and a proof: the further root, the instance, the further
record and the session's string, where the proof has one. -/
def packSess (_ : Kt) (xp : X × OfflineLinkOnlineProof lam L aT aL) : Option (OutBA lam L) :=
  match xp.2.piB with
  | some p => some (xp.2.link.1, xp.1, xp.2.link.2.1, p)
  | none => none

/-- The check in the form of Johnson/Top/ArmsFold.lean, at proofs that carry the instance. -/
theorem armSessOf_fold (V : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D) :
    armSessOf (Kt := Kt) (aT := aT) (aL := aL) V m Pub =
      fun k x π => ZKCP.Gen.foldArm (X := X) Pub (fun d z => (V d z).overOne (m d))
        (packSess (Kt := Kt) (aT := aT) (aL := aL)) k x (x, π) := by
  funext k x π
  obtain ⟨copy, piT, link, _ | p⟩ := π <;> rfl

/-- The check tosses no coin, if the reading has none and each member of the family is a check. -/
theorem noCoin_armSessOf {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)}
    {r₀ : L.Rec} {V : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d))
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {Pub : OComp (rom lam) D}
    (hPc : Pub.NoCoin) (k : Kt) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) :
    (armSessOf V m Pub k x π).NoCoin := by
  obtain ⟨copy, piT, link, _ | p⟩ := π
  · trivial
  · exact hPc.bind fun d =>
      Rom.noCoin_overOne (m d) _ (TypedOracleCompiler.Joined.noCoin_of_detBound ((hV d).det _))

/-- From the premises of `armB_pr_pub`: the proof's check that asks for its public digests itself is
sound in the frame with a reading. For every committer with at most tC queries and every prover with
at most tP: the check accepts, and what it promises at the reading's value fails of the word that
the committer's log with the prover's behind it determines under the further root, with probability
at most n εs + 2 (n + 1)² / 2^lam, where n = 3 (tC + tP + tVB). -/
theorem armBoundD_sess (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs) (hbB : Err.Below εB εs)
    {V : D → OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d)) (hH : ∀ d, HeadSeedB W (S d) (V d))
    (hlam : 0 < lam) (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (Pt : List Bool → Prop)
    (hT : ∀ d s, Pt s → ((m d).dec s).1 ≠ OracleName.leaf ∧ ((m d).dec s).1 ≠ OracleName.node)
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt s)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) :
    ZKCP.Gen.ArmBoundD (fun _ : Kt => Pub) (armSessOf (aT := aT) (aL := aL) V m Pub)
      (holdsSessOf (W := W) Rno m) fun tC tP =>
        (((tC + tP + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
          2 * (((tC + tP + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  rw [armSessOf_fold]
  refine ZKCP.Gen.ArmBoundD.comap (IVK' := Kt) (X' := X) (Pf' := OfflineLinkOnlineProof lam L aT aL)
    (fun _ => hPc)
    (ZKCP.Gen.armBoundD_of_maker (X := X) (K := Kt) hPc
      (verd := fun d z => (V d z).overOne (m d))
      (packSess (Kt := Kt) (aT := aT) (aL := aL))
      (Bad := fun d z tr => ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w)
        (extEnc W (singleTr (m d) tr) z.1) z.2.1 z.2.2.1)
      (ε := fun t => (((t + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam)
      (Holds := fun d _ trC _ xp trP => ProofHoldsAt L (fun i x => ∃ w, Rno i x w)
        (extEnc W (singleTr (m d) (trC ++ trP)) xp.2.link.1) xp.1 xp.2.link.2.1)
      (fun d k trC x xp trP z hz hn' => ?_)
      (fun Mk t hq => ?_))
    id (fun x π => (x, (x, π)))
  · obtain ⟨x', copy, piT, link, _ | p⟩ := xp
    · have hz' : (none : Option (OutBA lam L)) = some z := hz
      cases hz'
    · obtain rfl := Option.some.inj hz
      exact hn'
  · have h' := armB_pr_pub Rno wit hsB hlB hco hW hA hSd hbB hV hH hlam m Pt hT hno Pub hPc hPa hPr
      Mk t hq
    unfold expP verdP at h'
    unfold ZKCP.Gen.foldExp
    exact h'

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.noCoin_armSessOf
#print axioms TypedOracleCompiler.Compile.Batch.Cms.armBoundD_sess
