-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFoldGuard.lean: the fields `keyArm` and `proofArm` of `CoreArmsCD`
(Johnson/Top/OnFilesArmsCD.lean: the bounds on the input's checks of the key file and of the
proof file, the public data being in the typed key), for every input whose check says yes only where
the check whose bound is assumed here (b) says yes. The two bounds themselves (`armBoundD_test`,
`armBoundD_sess`) are hypotheses here.

What this file states. The check that the bound b speaks of reads a root, a record, an instance and
a typed string. The check that an input holds also tests plain data: the part c of the public data
that is in the key, against the reading's value; the number of the stored copy, against the string's
plain parts. Such tests only make the check say no more often. `keyArmC_holds`, `proofArmC_holds`:
the two bounds at the wide key, their promises unweakened. `keyArmC_of_test`, `proofArmC_of_sess`:
the two fields of `CoreArmsCD`, at every b whose type of digests, reading and word are D, "Pub at
every key" and `wordL m` (`wordL m`: the word under a root, read at d off a log of strings, through
the coding at d). `wordL_codings`, `keyArmC_of_test_at`, `proofArmC_of_sess_at`: the two fields
where the word is `wordL m₀` at another family of codings m₀ that agrees with the check's own, at
every d, on the leaf and node oracles (`SameTrees`, Johnson/TypedOracleCompiler/RecCompile/WordCodings.lean).
`proofArm_of_sess`: the field of `CoreArmsD` (Johnson/Top/OnFilesArmsD.lean), at `wordAt m`
(Johnson/Top/ArmsFoldTestCore.lean). `armGd gd V m Pub g z`: one concrete form of such a check
(concrete: defined in this library, not a parameter): the public reading; the check at its value d
on z, through the coding at d; then the plain test gd d g; the verdict is "both say yes". The order
is that of `ArmIn.armPN` (Johnson/Top/TieArmProofOver.lean [not in this library]). `noCoin_armGd`,
`armGd_yes`,
`keyArmC_of_armGd`, `proofArmC_of_armGd`: it tosses no coin if the reading and the members of V toss
none, its yes gives the yes of "the reading, then the check at its value", and so hn and hy are met
at an input whose checks are `armGd`: the two fields follow there from hV, hPc, b and hε.

Under which hypotheses. b: a bound `ArmBoundD` of `armTestOf V m Pub`
(Johnson/Top/ArmsFoldTest.lean), or of `armSessOf V m Pub` (Johnson/Top/ArmsFoldSess.lean), with the
promise `holdsTestOf m` (`holdsSessOf Rno m`) and the reading Pub at every key; hε: its error is at
most the field's; hV: at every d the member V d is a check in the sense of `IsArmT` (`IsArmB`); hPc:
the reading Pub tosses no coin; hn: the input's check tosses no coin; hy: at every function the
input's check says yes only where "the reading, then the check at its value" says yes.

What it does not show. The fields are had from bounds that are premises here (b). Those bounds' own
premises, Test's soundness and the session's soundness round by round among them, are proved in none
of the files named above: what a field requires moves to them and is not proved. Nothing that this
file imports proves Test's soundness at the programs' default setting. No written road to Test's
soundness at the programs' default setting is known to the writer of this file. The fields are
stated at a b whose reading is the check's own reading Pub and whose type of digests is that
reading's: a check that reads more public digests than b's reading is carried there by another step
(Johnson/Top/ArmsLeftOf.lean). In `keyArmC_of_test`, `proofArmC_of_sess` and `proofArm_of_sess` the
half "no collision seed" of the check's promise is dropped, and so in the four theorems that call
the first two (`keyArmC_of_test_at`, `proofArmC_of_sess_at`, `keyArmC_of_armGd`,
`proofArmC_of_armGd`); `keyArmC_holds` and `proofArmC_holds` keep it. Two fields of five: nothing on
`entryArm`, `reading`, `noCoin`. The three promises of `CoreArmsCD` read one word, through
`b.wordOf`: here that is the word through the coding m of the check in hand, or through an m₀ that
agrees with it on leaves and nodes; that the key's, the entry's and the proof's codings can agree
so, at one wiring W, one D and one Pub, is not shown here. r is a parameter; that its checks toss no
coin and say yes only where those checks do are hypotheses, met by `armGd` at every gd. Nothing is
promised of what gd tests: at gd := "no" the check refuses everything and the field holds vacuously:
it claims nothing there. No concrete input is defined here. All that the heads of ArmsFoldTest.lean,
ArmsFoldSess.lean, ArmsComap.lean and ArmsMonoD.lean do not claim.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsFoldTestCore
import Johnson.Top.ArmsFoldSess
import Johnson.Top.ArmsMonoD
import Johnson.Top.OnFilesArmsCD
import Johnson.TypedOracleCompiler.RecCompile.WordCodings

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Letters
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {D Z G : Type}

/-- The public reading; the check at its value d on z, through the coding at d; then the plain test
gd d g. The verdict is "both say yes". -/
def armGd (gd : D → G → Bool) (V : D → Z → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D) (g : G)
    (z : Z) : OComp (rom lam) Bool :=
  Pub.bind fun d => ((V d z).overOne (m d)).bind fun v => .pure (gd d g && v)

/-- It tosses no coin, if the reading and the checks toss none. -/
theorem noCoin_armGd (gd : D → G → Bool) {V : D → Z → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hc : ∀ d z, (V d z).NoCoin) (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    {Pub : OComp (rom lam) D} (hPc : Pub.NoCoin) (g : G) (z : Z) :
    (armGd gd V m Pub g z).NoCoin :=
  hPc.bind fun d => (Rom.noCoin_overOne (m d) _ (hc d z)).bind fun _ => trivial

/-- Its yes at a function holds the yes of "the reading, then the check at its value". -/
theorem armGd_yes (gd : D → G → Bool) (V : D → Z → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D) (g : G)
    (z : Z) (f : Fam (rom lam)) (h : (armGd gd V m Pub g z).det f = true) :
    (Pub.bind fun d => (V d z).overOne (m d)).det f = true := by
  unfold armGd at h
  rw [OComp.det_bind, OComp.det_bind] at h
  rw [OComp.det_bind]
  have h2 : (gd (Pub.det f) g && ((V (Pub.det f) z).overOne (m (Pub.det f))).det f) = true := h
  rw [Bool.and_eq_true] at h2
  exact h2.2

/-- The word under a root, read at d off a log of strings: what its one-block entries, under the
coding at d, determine. -/
def wordL (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (d : D) (tr : Trace (rom lam))
    (cm : Dig lam) : Fin L.wordLength → L.Symbol :=
  extEnc W (singleTr (m d) tr) cm

/-- Two families of codings that agree, at every d, on the leaf and node oracles read one word. -/
theorem wordL_codings (hlam : 0 < lam)
    {m₀ m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam}
    (hm : ∀ d, SameTrees W (m₀ d) (m d)) : wordL m₀ = wordL m := by
  funext d tr cm
  exact extEnc_codings hlam (hm d) tr cm

end Letters

open VerifiableInference.OnPublicFiles

section Wide
variable {r : InputArmsC} {Bd D : Type} {W : QueryLayout 256 (typedOracleCarrier r.L Bd r.aT r.aL)}

/-- The bound of the key file's check at the wide key, with the promise of `armBoundD_test`
unweakened: no collision seed, and word and record decode. For every input whose key file's check
tosses no coin and says yes only where "the reading, then the check at its value" says yes. -/
theorem keyArmC_holds {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)}
    {V : D → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmT W (S d) (cA d) (V d))
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (hn : ∀ c cm rc p, (r.armK c cm rc p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) c cm rc p, (r.armK c cm rc p).det f = true →
      (armKOf V m Pub cm rc p).det f = true)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := r.X) V m Pub)
      (holdsTestOf (W := W) m) ε) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftKC r)
      (fun d k trC _ _ _ => KeyHoldsAt r.L (wordL m d trC k.2.cm) k.2.rcd) ε := by
  have b0 := ZKCP.Gen.ArmBoundD.comap (fun _ => hPc) b
    (Prod.snd : r.C × KeyRoot 256 r.L → KeyRoot 256 r.L)
    (fun (x : r.X) (π : OfflineLinkOnlineProof 256 r.L r.aT r.aL) => (x, π))
  exact ZKCP.Gen.ArmBoundD.mono_of_det (v' := liftKC r) (fun _ => hPc)
    (fun k x π => noCoin_armTestOf hV m hPc k.2 x π)
    (fun k x π => by
      obtain ⟨copy, _ | p, link, piB⟩ := π
      · trivial
      · exact hn _ _ _ _) b0
    (fun f k x π h => by
      obtain ⟨copy, _ | p, link, piB⟩ := π
      · exact h
      · exact hy f _ _ _ _ h)

/-- The field `keyArm` of `CoreArmsCD`: for every input whose key file's check tosses no coin and
says yes only where "the reading, then the check at its value" says yes. The typed check's bound b
and the comparison hε of the two errors are premises. -/
theorem keyArmC_of_test {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)}
    {V : D → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmT W (S d) (cA d) (V d))
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (hn : ∀ c cm rc p, (r.armK c cm rc p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) c cm rc p, (r.armK c cm rc p).det f = true →
      (armKOf V m Pub cm rc p).det f = true)
    (q₀ : ℕ) (Wn : Type) (Rno : r.I → r.X → Wn → Prop) (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : r.X)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := r.X) V m Pub)
      (holdsTestOf (W := W) m) ε) (hε : ∀ tC tP, ε tC tP ≤ εK tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftKC r)
      (KeyHoldsCD (r := r) ⟨D, fun _ => Pub, q₀, wordL m, Wn, Rno, εK, εE, εP, x₀⟩) εK :=
  (keyArmC_holds hV m hPc hn hy b).weakenLe (fun _ _ _ _ _ _ hh => Or.inr hh.2) hε

/-- The bound of the proof file's check at the wide key, with the promise of `armBoundD_sess`
unweakened: no collision seed; and word and record decode to nothing, or to an index at which the
instance is true. For every input whose proof file's check tosses no coin and says yes only where
"the reading, then the check at its value" says yes. -/
theorem proofArmC_holds {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)} {r₀ : r.L.Rec}
    {V : D → OutBA 256 r.L → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d))
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (hn : ∀ c cm x rc n p, (r.armP c cm x rc n p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) c cm x rc n p, (r.armP c cm x rc n p).det f = true →
      (Pub.bind fun d => (V d (cm, x, rc, p)).overOne (m d)).det f = true)
    {Wn : Type} (Rno : r.I → r.X → Wn → Prop) {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ : r.C × KeyRoot 256 r.L => Pub)
      (armSessOf (aT := r.aT) (aL := r.aL) V m Pub) (holdsSessOf (W := W) Rno m) ε) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftPC r)
      (fun d _ trC x π trP => ProofHoldsAt r.L (fun i x => ∃ w, Rno i x w)
        (wordL m d (trC ++ trP) π.link.1) x π.link.2.1) ε :=
  ZKCP.Gen.ArmBoundD.mono_of_det (v' := liftPC r) (fun _ => hPc)
    (fun k x π => noCoin_armSessOf hV m hPc k x π)
    (fun k x π => by
      obtain ⟨copy, piT, link, _ | p⟩ := π
      · trivial
      · exact hn _ _ _ _ _ _) b
    (fun f k x π h => by
      obtain ⟨copy, piT, link, _ | p⟩ := π
      · exact h
      · exact hy f _ _ _ _ _ _ h)

/-- The field `proofArm` of `CoreArmsCD`: for every input whose proof file's check tosses no coin
and says yes only where "the reading, then the check at its value" says yes. The typed check's bound
b and the comparison hε of the two errors are premises. -/
theorem proofArmC_of_sess {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)} {r₀ : r.L.Rec}
    {V : D → OutBA 256 r.L → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d))
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (hn : ∀ c cm x rc n p, (r.armP c cm x rc n p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) c cm x rc n p, (r.armP c cm x rc n p).det f = true →
      (Pub.bind fun d => (V d (cm, x, rc, p)).overOne (m d)).det f = true)
    (q₀ : ℕ) (Wn : Type) (Rno : r.I → r.X → Wn → Prop) (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : r.X)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ : r.C × KeyRoot 256 r.L => Pub)
      (armSessOf (aT := r.aT) (aL := r.aL) V m Pub) (holdsSessOf (W := W) Rno m) ε)
    (hε : ∀ tC tP, ε tC tP ≤ εP tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftPC r)
      (ProofHoldsCD (r := r) ⟨D, fun _ => Pub, q₀, wordL m, Wn, Rno, εK, εE, εP, x₀⟩) εP :=
  (proofArmC_holds hV m hPc hn hy Rno b).weakenLe (fun _ _ _ _ _ _ hh => Or.inr hh.2) hε

/-- The field `keyArm` where the frame's word is read through another family of codings m₀, which
agrees with the check's own at every d on the leaf and node oracles. -/
theorem keyArmC_of_test_at {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)}
    {V : D → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmT W (S d) (cA d) (V d))
    (m₀ m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256)
    (hm : ∀ d, SameTrees W (m₀ d) (m d)) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (hn : ∀ c cm rc p, (r.armK c cm rc p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) c cm rc p, (r.armK c cm rc p).det f = true →
      (armKOf V m Pub cm rc p).det f = true)
    (q₀ : ℕ) (Wn : Type) (Rno : r.I → r.X → Wn → Prop) (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : r.X)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := r.X) V m Pub)
      (holdsTestOf (W := W) m) ε) (hε : ∀ tC tP, ε tC tP ≤ εK tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftKC r)
      (KeyHoldsCD (r := r) ⟨D, fun _ => Pub, q₀, wordL m₀, Wn, Rno, εK, εE, εP, x₀⟩) εK := by
  rw [wordL_codings (by norm_num) hm]
  exact keyArmC_of_test hV m hPc hn hy q₀ Wn Rno εK εE εP x₀ b hε

/-- The field `proofArm` where the frame's word is read through another family of codings m₀,
likewise. -/
theorem proofArmC_of_sess_at {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)} {r₀ : r.L.Rec}
    {V : D → OutBA 256 r.L → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d))
    (m₀ m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256)
    (hm : ∀ d, SameTrees W (m₀ d) (m d)) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (hn : ∀ c cm x rc n p, (r.armP c cm x rc n p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) c cm x rc n p, (r.armP c cm x rc n p).det f = true →
      (Pub.bind fun d => (V d (cm, x, rc, p)).overOne (m d)).det f = true)
    (q₀ : ℕ) (Wn : Type) (Rno : r.I → r.X → Wn → Prop) (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : r.X)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ : r.C × KeyRoot 256 r.L => Pub)
      (armSessOf (aT := r.aT) (aL := r.aL) V m Pub) (holdsSessOf (W := W) Rno m) ε)
    (hε : ∀ tC tP, ε tC tP ≤ εP tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftPC r)
      (ProofHoldsCD (r := r) ⟨D, fun _ => Pub, q₀, wordL m₀, Wn, Rno, εK, εE, εP, x₀⟩) εP := by
  rw [wordL_codings (by norm_num) hm]
  exact proofArmC_of_sess hV m hPc hn hy q₀ Wn Rno εK εE εP x₀ b hε

/-- So at an input whose key file's check is `armGd`: gd sees the reading's value, the part c of the
key and the typed string. -/
theorem keyArmC_of_armGd {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)}
    {V : D → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmT W (S d) (cA d) (V d))
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (gd : D → r.C × OneProtocolProof 256 (batTC r.L r.aT) → Bool)
    (h : r.armK = fun c cm rc p => armGd gd V m Pub (c, p) (cm, rc, p))
    (q₀ : ℕ) (Wn : Type) (Rno : r.I → r.X → Wn → Prop) (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : r.X)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := r.X) V m Pub)
      (holdsTestOf (W := W) m) ε) (hε : ∀ tC tP, ε tC tP ≤ εK tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftKC r)
      (KeyHoldsCD (r := r) ⟨D, fun _ => Pub, q₀, wordL m, Wn, Rno, εK, εE, εP, x₀⟩) εK :=
  keyArmC_of_test hV m hPc
    (fun c cm rc p => by
      rw [h]
      exact noCoin_armGd gd
        (fun d z => TypedOracleCompiler.Joined.noCoin_of_detBound ((hV d).det z)) m hPc _ _)
    (fun f c cm rc p hh => by
      rw [h] at hh
      exact armGd_yes gd V m Pub _ _ f hh)
    q₀ Wn Rno εK εE εP x₀ b hε

/-- So at an input whose proof file's check is `armGd`: gd sees the reading's value, the part c of
the key, the number of the stored copy and the typed string. -/
theorem proofArmC_of_armGd {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)} {r₀ : r.L.Rec}
    {V : D → OutBA 256 r.L → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d))
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (gd : D → r.C × ℕ × OneProtocolProof 256 r.L.onlineBatch → Bool)
    (h : r.armP = fun c cm x rc n p => armGd gd V m Pub (c, n, p) (cm, x, rc, p))
    (q₀ : ℕ) (Wn : Type) (Rno : r.I → r.X → Wn → Prop) (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : r.X)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ : r.C × KeyRoot 256 r.L => Pub)
      (armSessOf (aT := r.aT) (aL := r.aL) V m Pub) (holdsSessOf (W := W) Rno m) ε)
    (hε : ∀ tC tP, ε tC tP ≤ εP tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftPC r)
      (ProofHoldsCD (r := r) ⟨D, fun _ => Pub, q₀, wordL m, Wn, Rno, εK, εE, εP, x₀⟩) εP :=
  proofArmC_of_sess hV m hPc
    (fun c cm x rc n p => by
      rw [h]
      exact noCoin_armGd gd
        (fun d z => TypedOracleCompiler.Joined.noCoin_of_detBound ((hV d).det z)) m hPc _ _)
    (fun f c cm x rc n p hh => by
      rw [h] at hh
      exact armGd_yes gd V m Pub _ _ f hh)
    q₀ Wn Rno εK εE εP x₀ b hε

end Wide

section Narrow
variable {r : InputArms} {Bd D : Type} {W : QueryLayout 256 (typedOracleCarrier r.L Bd r.aT r.aL)}

/-- The field `proofArm` of `CoreArmsD`: for every input whose proof file's check tosses no coin and
says yes only where "the reading, then the check at its value" says yes. -/
theorem proofArm_of_sess {S : D → OutOfDomainSampleQueryLayout 256 W.K r.L Bd r.aT r.aL}
    {cA : D → r.L.OutOfDomainAnswer → List (Dig 256)} {r₀ : r.L.Rec}
    {V : D → OutBA 256 r.L → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool}
    (hV : ∀ d, IsArmB W (S d) (cA d) r₀ (V d))
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) {Pub : OComp (rom 256) D}
    (hPc : Pub.NoCoin) (hn : ∀ cm x rc n p, (r.armP cm x rc n p).NoCoin)
    (hy : ∀ (f : Fam (rom 256)) cm x rc n p, (r.armP cm x rc n p).det f = true →
      (Pub.bind fun d => (V d (cm, x, rc, p)).overOne (m d)).det f = true)
    (q₀ : ℕ) (Wn : Type) (Rno : r.I → r.X → Wn → Prop) (εK εE εP : ℕ → ℕ → ℝ≥0∞) (x₀ : r.X)
    {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ : KeyRoot 256 r.L => Pub)
      (armSessOf (aT := r.aT) (aL := r.aL) V m Pub) (holdsSessOf (W := W) Rno m) ε)
    (hε : ∀ tC tP, ε tC tP ≤ εP tC tP) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftP r)
      (ProofHoldsD (r := r) ⟨D, fun _ => Pub, q₀, wordAt m, Wn, Rno, εK, εE, εP, x₀⟩) εP := by
  have b1 := ZKCP.Gen.ArmBoundD.mono_of_det (v' := liftP r) (fun _ => hPc)
    (fun k x π => noCoin_armSessOf hV m hPc k x π)
    (fun k x π => by
      obtain ⟨copy, piT, link, _ | p⟩ := π
      · trivial
      · exact hn _ _ _ _ _) b
    (fun f k x π h => by
      obtain ⟨copy, piT, link, _ | p⟩ := π
      · exact h
      · exact hy f _ _ _ _ _ h)
  exact b1.weakenLe (fun _ _ _ _ _ _ hh => Or.inr hh.2) hε

end Narrow

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.armGd_yes
#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyArmC_holds
#print axioms TypedOracleCompiler.Compile.Batch.Cms.proofArmC_holds
#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyArmC_of_test
#print axioms TypedOracleCompiler.Compile.Batch.Cms.proofArmC_of_sess
#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyArmC_of_test_at
#print axioms TypedOracleCompiler.Compile.Batch.Cms.proofArmC_of_sess_at
#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyArmC_of_armGd
#print axioms TypedOracleCompiler.Compile.Batch.Cms.proofArmC_of_armGd
#print axioms TypedOracleCompiler.Compile.Batch.Cms.proofArm_of_sess
