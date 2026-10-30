-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/KindsLawsAtHead.lean: `kindsLaws_at_head`: under every head, each of the
sixteen fields of `KindsLaws h h.free` taken from another file's theorem "from the head" (one call
for each kind, three for `frame`), written out field by field, so that a reader sees which theorem
proves what.
It leans on no cut of Johnson/Goal/Skeleton/KindsOfConds.lean. And `sound_of_rows_read_at`:
`sound_of_bare_laws_head_at` (Johnson/Goal/Skeleton/SoundOfBareLawsHead.lean) with its hypothesis
`kinds` proved so: soundness at one set of public files from one test on these files, `rowsRead Z`,
which the fourteenth entry test asks.

Which theorem proves which field: k1 `P5J.k01_kind_of_head` · k2 `K2Caller.k02_kind_of_head` · k3
`P5J.k03_kind_head` · k4 `OnBytes.Road.K4.k04_of_head` · k5 `H2K5.Door.k05_kind_of_head` · k6
`AtTable.k06_counted_head` · k7 `k07_kind_of_head` · k8 `P1K8T.k08_kind_head` · k9
`P5J.k09_kind_of_head` · k10 `P5J.k10_kind_free` · k11 `K11.k11_kind_head` · k12
`H2K12.k12_kind_at_head` (behind its condition on the public parameters) · k13
`K13.Law.k13_kind_of_head` · k14, k15: no place on the first chain · frame `P1L20.frame_of_behind`
at `P1L20.frameBehind_of_k9` at `P5J.k09_cond_of_head`.

Limits. Calls alone: nothing is proved in this file. What it is worth is what the called theorems
and the definitions in the statement are worth. The head under which the
sixteen (fourteen lemmas with content: the fields k14 and
k15 are idle, these kinds having no place on the first chain) are had is built inside the top from
the scope, the reading, the yes of `protocolDataWellFormed` and `rowsRead`; where `protocolDataWellFormed` says no, `verify`
rejects everything and the statement holds for that reason. That `protocolDataWellFormed` says yes at the release's
files as bytes, and that the honest proof is accepted there, is evaluated, not proved. Soundness (index binding) alone: no opening-form binding, no correctness
of extraction, no completeness, nothing on hiding, nor anything else that names the honest committer or prover. One set of public files at a time, fixed
before the hash function is drawn; the second hash function is a fixed function; at the full size
alone; the description's own parser. Beneath five of the called theorems (the tenth and the twelfth
kind's lemmas on the first chain, the key file's, the one that gives the five rows, the shared
chain's among them, and the one on the last chain's rest) stand files on coding theory adapted from
third-party Lean (lean/LIMITS.md, L15).
-/
import Johnson.Goal.Skeleton.SoundOfBareLawsHead
import Johnson.Goal.Skeleton.KindsWithoutPlaceAtMg
import Johnson.Goal.Skeleton.K13OfHead
import Johnson.Loose.H2K12.K12AtHead
import Johnson.P1L20R.FrameOfBehind
import Johnson.Desc.AtSeats.K01CondOfHead
import Johnson.P1K2R.K2FromHead
import Johnson.P5J.K03FromHead
import Johnson.Road.K4.K04OfHead
import Johnson.Desc.First.Att.Door.Law.K5KindWhole
import Johnson.Desc.Kinds.Law.K06CountedHead
import Johnson.Desc.Kinds.Law.K07KindOfHead
import Johnson.P1K8R.KindFromHead
import Johnson.P5J.K09EndC
import Johnson.P5J.K09CondHead
import Johnson.P5J.K10Free
import Johnson.K11R.KindAtFree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open P5J

/-- **The sixteen fields under a head, each taken from another file's theorem from the head: one
call for each kind, three for `frame`.** -/
theorem kindsLaws_at_head {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x) :
    KindsLaws h h.free where
  k1 := k01_kind_of_head h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k2 := VerifiableInference.Desc.First.K2Caller.k02_kind_of_head h h.free h.free_q₁ h.free_q₂
    h.free_q₃
  k3 := k03_kind_head h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k4 := OnBytes.Road.K4.k04_of_head h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k5 := H2K5.Door.k05_kind_of_head h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k6 := VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_counted_head h h.free h.free_q₁
    h.free_q₂ h.free_q₃
  k7 := VerifiableInference.Desc.Kinds.Head.Law.k07_kind_of_head h h.free h.free_q₁ h.free_q₂
    h.free_q₃
  k8 := P1K8T.k08_kind_head h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k9 := k09_kind_of_head h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k10 := k10_kind_free h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k11 := K11.k11_kind_head h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k12 := fun hT => H2K12.k12_kind_at_head h h.free h.free_q₁ hT
  k13 := VerifiableInference.Desc.K13.Law.k13_kind_of_head h h.free h.free_q₁ h.free_q₂ h.free_q₃
  k14 := h.kind_K14 h.free
  k15 := h.kind_K15 h.free
  frame := P1L20.frame_of_behind h h.free h.free_q₁ h.free_q₂ h.free_q₃
    (P1L20.frameBehind_of_k9 h h.free (k09_cond_of_head h h.free h.free_q₁ h.free_q₂ h.free_q₃))

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES FROM ONE TEST ON THESE FILES.** -/
theorem sound_of_rows_read_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z) :
    VerifiableInference.Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_bare_laws_head_at Z pp scope read exact owed fun _ _ _ _ _ h => kindsLaws_at_head h

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.kindsLaws_at_head
#print axioms VerifierAndGoals.AtTheName.sound_of_rows_read_at
