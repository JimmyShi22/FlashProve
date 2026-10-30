-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFoldTest.lean: a bound over one drawn hash function for a check of the
key file, in the form in which the check itself asks the function for its public digests
(`ArmBoundD`, Johnson/Top/ArmsD.lean). Test's soundness round by round and the other hypotheses of
`armT_pr_key_pub` are assumed; everything is an arbitrary parameter.

What this file states. `armBoundD_test`:
`ArmBoundD (fun _ => Pub) (armTestOf V m Pub) (holdsTestOf m) ε` with ε tC tP = n εs + 2 (n + 1)² /
2^lam at n = 3 (tC + tP + 1 + tVT). `armTestOf V m Pub` is the check on a key and a proof: a proof
without Test's string is refused; else the public reading Pub (a computation that queries the hash
function), then the check at its value through the coding at its value. `holdsTestOf m` is the
promise at the reading's value: of the word that the committer's own log determines under the key's
root. It reads neither the instance, nor the proof, nor the prover's log. `armBoundD_of_testPub`:
the same from a bound on the experiment and the event of `armT_pr_key_pub`
(Johnson/TypedOracleCompiler/RecCompile/KeyAnsPublic.lean) for all committers and provers, at the same numbers of
queries, where the reading tosses no coin (hn). `armTestOf_fold`: the check in the form of
Johnson/Top/ArmsFold2.lean. After Johnson/Top/ArmsFoldKey.lean [not in this library], which says
this of the entry's check. The step is that file's: `armBoundD_of_two` (Johnson/Top/ArmsFold2.lean),
which keeps the two stages' logs apart. The statement that joins a link at every hash function to a
bound (`JoinsOneArmD`, Johnson/Top/TailViaD.lean [not in this library]) takes
`ArmBoundD rd v Holds ε` as its first premise. It is intended for a check v whose first step is the
reading rd; the definition does not require that.

Under which hypotheses. Those of `armT_pr_key_pub`. hsT, hbT: Test's soundness round by round, with
no error above εs, a shared round's error being counted 2 ^ depthReqT times; hlT, hcT: locality and
coherence; hW, hA, hSd: the laws of the wiring, of the code of the answers and of the seeds; hV:
each member of the family is a check in the sense of `IsArmT`; hlam: lam is positive; of a set Pt of
public strings: a string of Pt codes no leaf and no node (hT), the check asks no string of Pt (hno),
the reading asks strings of Pt alone and none twice and tosses no coin (hPa, hPr, hPc). The object,
the wire, the family of checks, the family of codings and the reading are arbitrary parameters.

What it does not show. Nothing on any concrete check, coding or reading: all are parameters, and
that the premises of `armBoundD_test` can be met together is not shown; until it is, it may be true
and empty. At an ε of at least 1 it says nothing. At a reading that asks nothing and puts out a
fixed d, with no public string, it is the bound at that d and says nothing of public digests. The
reading's and the check's own queries appear in no log and in no budget. The reading `Pub`, and so
the public strings that it can ask, are fixed before the function is drawn (`Pub` is an algorithm,
and may ask a string made of an earlier answer): a committer that writes the public files after
asking the function is not covered. Soundness alone: no yes is shown, and the bound would hold of a
check that refuses everything. Test's soundness is a hypothesis. The limits in the heads of
KeyAnsPublic.lean and ArmsFold2.lean hold. No linking statement is joined here. Behind a joining the
promise is read at the committer's log with the key's reading's log behind it: that this is still
the committer's own word wants a reading that asks no string that codes a leaf or a node; that is
not shown here.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsFold2
import Johnson.TypedOracleCompiler.RecCompile.KeyAnsPublic
import Johnson.TypedOracleCompiler.RecCompile.FrontRoot

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {D X' : Type}

/-- The key's check on a key and a proof: a proof without Test's string is refused; else the public
reading, then the check at its value through the coding at its value. -/
def armTestOf (V : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D)
    (k : KeyRoot lam L) (_ : X') (π : OfflineLinkOnlineProof lam L aT aL) : OComp (rom lam) Bool :=
  match π.piT with
  | some p => Pub.bind fun d => (V d (k.cm, k.rcd, p)).overOne (m d)
  | none => .pure false

/-- The promise at the reading's value d: of the word that the one-block entries, under the coding
at d, of the committer's own log determine under the key's root. -/
def holdsTestOf (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (d : D) (k : KeyRoot lam L)
    (trC : Trace (rom lam)) (_ : X') (_ : OfflineLinkOnlineProof lam L aT aL) (_ : Trace (rom lam)) : Prop :=
  KeyHoldsAt L (extEnc W (singleTr (m d) trC) k.cm) k.rcd

/-- The check in the form of Johnson/Top/ArmsFold2.lean. -/
theorem armTestOf_fold (V : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D) :
    armTestOf (X' := X') (aL := aL) V m Pub =
      ZKCP.Gen.foldArm2 Pub
        (fun d (ka : Dig lam × L.Rec) (zb : OneProtocolProof lam (batTC L aT)) =>
          (V d (ka.1, ka.2, zb)).overOne (m d))
        (fun k => (k.cm, k.rcd)) (fun π => π.piT) := by
  funext k x π
  obtain ⟨copy, _ | p, link, piB⟩ := π <;> rfl

/-- The bound of the key's check in two stages, in the frame with a reading. -/
theorem armBoundD_of_testPub (V : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {Pub : OComp (rom lam) D}
    (hn : Pub.NoCoin) {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ∀ (St : Type) (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
      (Pv : St → OComp (rom lam) (OneProtocolProof lam (batTC L aT))) (tC tP : ℕ), Ct.QueryBound tC →
      (∀ st, (Pv st).QueryBound tP) →
      Rom.Pr (expP (fun d (y : (((Dig lam × L.Rec) × St) × Trace (rom lam)) ×
            (OneProtocolProof lam (batTC L aT) × Trace (rom lam))) =>
            (V d (y.1.1.1.1, y.1.1.1.2, y.2.1)).overOne (m d)) Pub (run2 Prod.snd (Ct, Pv)))
          (fun _ => {x | x.2.2 = true ∧
            ¬ KeyHoldsAt L (extEnc W (singleTr (m x.2.1) x.1.1.2) x.1.1.1.1.1) x.1.1.1.1.2}) ≤
        ε tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := X') (aL := aL) V m Pub)
      (holdsTestOf (W := W) m) ε := by
  rw [armTestOf_fold]
  exact ZKCP.Gen.armBoundD_of_two hn _ _
    (Bad := fun d (ka : Dig lam × L.Rec) trC _ _ =>
      ¬ KeyHoldsAt L (extEnc W (singleTr (m d) trC) ka.1) ka.2)
    (fun d k trC x π trP z _ hn' => hn')
    (fun St Ct Pv tC tP hC hP => by
      have h' := h St Ct Pv tC tP hC hP
      unfold expP verdP run2 at h'
      unfold ZKCP.Gen.foldExp2
      exact h')

/-- From the premises of `armT_pr_key_pub`: the key's check that asks for its public digests itself
is sound in the frame with a reading. For every committer with at most tC queries and every prover
with at most tP: the check accepts, and what it promises at the reading's value fails of the word
that the committer's own log determines under the key's root, with probability at most n εs + 2 (n +
1)² / 2^lam, where n = 3 (tC + tP + 1 + tVT). -/
theorem armBoundD_test {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)}
    {V : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {εT : Err L.offline.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : ∀ d, AnsOK (cA d))
    (hSd : ∀ d, (S d).Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hV : ∀ d, IsArmT W (S d) (cA d) (V d)) (hlam : 0 < lam)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pt : List Bool → Prop)
    (hT : ∀ d s, Pt s → ((m d).dec s).1 ≠ OracleName.leaf ∧ ((m d).dec s).1 ≠ OracleName.node)
    (hno : ∀ d z, ((V d z).overOne (m d)).AsksIn fun _ s => ¬ Pt s)
    (Pub : OComp (rom lam) D) (hPc : Pub.NoCoin) (hPa : Pub.AsksIn fun _ s => Pt s)
    (hPr : NoRepeat Pub) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := X') (aL := aL) V m Pub)
      (holdsTestOf (W := W) m) fun tC tP =>
        (((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
          2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  armBoundD_of_testPub V m hPc fun _ Ct Pv tC tP hC hP =>
    armT_pr_key_pub hsT hlT hcT hW hA hSd hbT hV hlam m Pt hT hno Pub hPc hPa hPr Ct Pv tC tP hC hP

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.armBoundD_of_testPub
#print axioms TypedOracleCompiler.Compile.Batch.Cms.armBoundD_test
