-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsFoldTestJoin.lean: two facts on the key's check `armTestOf`
(Johnson/Top/ArmsFoldTest.lean) that are needed in addition to its bound: it tosses no coin, if the
reading tosses none and each member of the family is a check; and it is the key file's check `liftK
r` (Johnson/Top/OnFilesArms.lean) of every input r whose field `armK` is "the public reading, then
the check at its value through the coding at its value", which is a hypothesis.

What this file states. `noCoin_armTestOf`: no coin, if the reading has none and each member of the
family is a check (`IsArmT`). `armKOf V m Pub`: the term that an input's field `armK` must be.
`liftK_eq_armTestOf`: at such an input `liftK r` is `armTestOf V m Pub`. `armBoundD_liftK`: so a
bound `ArmBoundD` of `armTestOf V m Pub` is one of `liftK r`. The use: `JoinsOneArmD`
(Johnson/Top/TailViaD.lean [not in this library]) takes, among its premises, that none of rd, v and
v' tosses a coin; and a linking statement for the key file speaks of `r.armK` at an input r.

Under which hypotheses. hV, hPc for `noCoin_armTestOf`: each member V d is a check in the sense of
`IsArmT`, and the reading Pub tosses no coin. h for the two others: `r.armK = armKOf V m Pub`. b for
`armBoundD_liftK`: the bound of `armTestOf V m Pub`.

What it does not show. No concrete input is defined: r is a parameter, and that its field is that
term is a hypothesis (at a concrete input it is intended to hold by definition). Nothing on the two
other checks of r. `liftK` is the key file's check for an input of the type `InputArms`, whose key
holds a root and a record alone; an input of the form `ArmFam.asking`
(Johnson/Top/ArmsTwoSpellings.lean) at a family whose `vK d` is "the check V d through the coding m
d" has that field by definition, and `coreCD_of_coreD` there leads from the hypotheses at such an
input (`CoreArmsD`) to those at the input with the public data in the key (`CoreArmsCD`). No linking
statement and no joining is stated. All that the head of Johnson/Top/ArmsFoldTest.lean does not
claim.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.ArmsFoldTest
import Johnson.Top.OnFilesArms
import OnBytes.TypedOracleCompiler.Joined.YesByCutsMore
import Rom.NoCoinExits

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Letters
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {D X' : Type}

/-- The key's check on a key and a proof tosses no coin, if the reading has none and each member of
the family is a check. -/
theorem noCoin_armTestOf {S : D → OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : D → L.OutOfDomainAnswer → List (Dig lam)}
    {V : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : ∀ d, IsArmT W (S d) (cA d) (V d))
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {Pub : OComp (rom lam) D}
    (hPc : Pub.NoCoin) (k : KeyRoot lam L) (x : X') (π : OfflineLinkOnlineProof lam L aT aL) :
    (armTestOf V m Pub k x π).NoCoin := by
  obtain ⟨copy, _ | p, link, piB⟩ := π
  · trivial
  · exact hPc.bind fun d =>
      Rom.noCoin_overOne (m d) _ (TypedOracleCompiler.Joined.noCoin_of_detBound ((hV d).det _))

/-- The term that an input's field `armK` must be: the public reading, then the check at its value
through the coding at its value. -/
def armKOf (V : D → OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (m : D → OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (Pub : OComp (rom lam) D)
    (cm : Dig lam) (rcd : L.Rec) (p : OneProtocolProof lam (batTC L aT)) : OComp (rom lam) Bool :=
  Pub.bind fun d => (V d (cm, rcd, p)).overOne (m d)

end Letters

open VerifiableInference.OnPublicFiles

variable (r : InputArms) {Bd D : Type} {W : QueryLayout 256 (typedOracleCarrier r.L Bd r.aT r.aL)}

/-- At an input whose field `armK` is `armKOf V m Pub` the key file's check is `armTestOf V m Pub`.
-/
theorem liftK_eq_armTestOf
    (V : D → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool)
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) (Pub : OComp (rom 256) D)
    (h : r.armK = armKOf V m Pub) : liftK r = armTestOf (X' := r.X) V m Pub := by
  funext k x π
  obtain ⟨copy, _ | p, link, piB⟩ := π
  · rfl
  · show r.armK k.cm k.rcd p = _
    rw [h]
    rfl

/-- So a bound of `armTestOf V m Pub` in the frame with a reading is one of `liftK r`. -/
theorem armBoundD_liftK
    (V : D → OutTA 256 r.L r.aT → TypedOracleComputation 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL) Bool)
    (m : D → OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier r.L Bd r.aT r.aL)) 256) (Pub : OComp (rom 256) D)
    (h : r.armK = armKOf V m Pub) {ε : ℕ → ℕ → ℝ≥0∞}
    (b : ZKCP.Gen.ArmBoundD (fun _ => Pub) (armTestOf (X' := r.X) V m Pub)
      (holdsTestOf (W := W) m) ε) :
    ZKCP.Gen.ArmBoundD (fun _ => Pub) (liftK r) (holdsTestOf (W := W) m) ε := by
  rw [liftK_eq_armTestOf r V m Pub h]
  exact b

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.noCoin_armTestOf
#print axioms TypedOracleCompiler.Compile.Batch.Cms.liftK_eq_armTestOf
#print axioms TypedOracleCompiler.Compile.Batch.Cms.armBoundD_liftK
