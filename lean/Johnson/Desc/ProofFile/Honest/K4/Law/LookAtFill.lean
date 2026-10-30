-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookAtFill.lean: CONDITIONAL.

What is here. THE PARAMETER `look` OF THE FEED-FORWARD LAYERS' OWN ROUNDS (the sub-protocol K4) AT
THE TEXT `k4LookAt` (Honest/K4/Look.lean), which is the text that the frame's wider filling of the
honest prover lays there (`widerFill`, Honest/AtPureWider.lean; not imported here). (1) `k4LookOf`
and the text `lookHeardAt` of the writers of the sub-protocol K3 (lookups)
(Honest/K3/HeardWhole.lean), at one shape and one number of rounds in front, agree in nine fields:
shape, theta, alpha, zx, zy, zk, e, zb0, zb1: by unfolding. (2) The public test on the sizes of what
the lookup has sampled (`k4LookFits`, Honest/K4/Part.lean) reads four fields alone (shape, zx, e,
zk); so it accepts `k4LookAt` at the member's own public data, AT EVERY LIST OF CHALLENGES, under h
and `LaidK4`: that is the hypothesis hLk of `k4Seated_member` (Law/SeatedMember.lean) at look :=
`k4LookAt`. It asks neither of the two hypotheses in the head of Honest/K4/Look.lean. (3) The two
sentences on `look` over which the statements on the member's points stand (`LookIsK3`,
Law/LookPtsHead.lean; `LookIsK3Wide`, Law/LookOpenHead.lean) hold at `k4LookAt`, from h, `LaidK4`
and ONE EQUATION ON NUMBERS (hbase): the count of rounds in front of the member, less the lookup's
own number of rounds, is the number of rounds of the chain's first 28 g + 3 members. Of the shape it
spends `callsShape_head` (Law/LookFitsFill.lean): the layout's shape is the shape of the site on the
calls at the link in the list of lookups; by reading, not by a statement, that is the second
hypothesis of Honest/K4/Look.lean's head.

Not shown here. hbase: a hypothesis here; `lookBase_head` (Law/LookBaseHead.lean) proves it under h
and `LaidK4`, and `k4LookAt_head` (Law/LookAtHead.lean) joins the two. THE TWO TEXTS ARE NOT ONE
STRUCTURE: `k4LookOf` lays the field a and leaves tT and leavesA at their defaults; `lookHeardAt`
lays tT and leavesA and leaves a at its default: AN EQUATION BETWEEN THE TWO WHOLE STRUCTURES IS
FALSE wherever the shape has a call (`lookOf_ne`). Nothing else on a, tT or leavesA. The statements
speak of sizes and of the texts of nine fields alone: that these fields are those of the verifier's
hearing is other files' (`layers_tie_head`, the authors' Honest/K3/Law/Thread/LayersTieHead.lean;
`lookPts_head`). THAT ANY PROVER's HALF IS LAID OVER `k4LookAt` is not shown here. `LaidK4` follows
from h at each of the twelve groups (`laid_head`, Law/SeatedHead.lean, with the library's
`atK4_full`). THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has a
member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). `LaidK4` ASKS NOTHING BEYOND h: `laid_head` (Law/SeatedHead.lean)
has it at the library's `atK4_full`, at each group below 12. `lookFits_lookAt` and `lookAt_isK3`:
THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone; the other statements are general. Among what
stands beneath are comparisons by Lean's own kernel: beneath `lookFits_lookAt`, `light_head`
(Johnson/Road/K4/C/PublicLight.lean), of which one clause is spent and which rests on five facts of
Johnson/Road/K4/C/Free/ by `kernel_rfl`; beneath it and `lookAt_isK3`, `nine_head`
(Law/ElevenHead.lean), which has one `decide +kernel`. No independent checker has replayed them. THE
FILES OF THE AUTHORS OF THE KIND "lookup" ARE READING COPIES FOR US BY THEIR OWN WORD. A LAW, NOT A
PART: no file that defines a part of the proof file's description may import this one: as
Law/LookFitsFill.lean says of itself. Transitive imports: those of Law/LookFitsFill.lean and
Law/LookOpenHead.lean, and Honest/K4/Look.lean: not counted. No property is claimed.

  `lookOf_open`   the nine fields.
  `lookOf_ne`   the two whole structures differ where the shape has a call.
  `lookOf_ne_any`   the same at any two shapes, numbers and lists.
  `lookFits_congr`   the test reads four fields alone.
  `lookFits_lookOf`   the test at `k4LookOf` of the public data's own shape.
  `lookFits_lookAt`   **hLk at `k4LookAt`, at the member's own public data.**
  `lookAt_isK3`   **`LookIsK3Wide` and `LookIsK3` at `k4LookAt`, from hbase.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Look
import Johnson.Desc.ProofFile.Honest.K4.Law.LookFitsFill
import Johnson.Desc.ProofFile.Honest.K4.Law.LookOpenHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4.C (light_head)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K3 (lookHeardAt)
open ProofFile.Honest.K3.Law.AtThr (lookOfK3 callsShape)

/-- The two texts agree in nine fields, at one shape and one number of rounds in front. -/
theorem lookOf_open (s : Forest.Shape) (base : ℕ) (hd : List Fmt.Drawn) :
    (k4LookOf s base hd).zx = (lookHeardAt s base hd).zx ∧
      (k4LookOf s base hd).zk = (lookHeardAt s base hd).zk ∧
      (k4LookOf s base hd).e = (lookHeardAt s base hd).e ∧
      (k4LookOf s base hd).shape = (lookHeardAt s base hd).shape ∧
      (k4LookOf s base hd).zb0 = (lookHeardAt s base hd).zb0 ∧
      (k4LookOf s base hd).zb1 = (lookHeardAt s base hd).zb1 ∧
      (k4LookOf s base hd).zy = (lookHeardAt s base hd).zy ∧
      (k4LookOf s base hd).theta = (lookHeardAt s base hd).theta ∧
      (k4LookOf s base hd).alpha = (lookHeardAt s base hd).alpha :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- CONDITIONAL: on hc. The two texts are not one structure where the shape has a call: the field tT
is empty in the one and has one element for each call in the other. -/
theorem lookOf_ne (s : Forest.Shape) (base : ℕ) (hd : List Fmt.Drawn) (hc : s.calls.size ≠ 0) :
    k4LookOf s base hd ≠ lookHeardAt s base hd := by
  intro e
  have e1 : (k4LookOf s base hd).tT.size = (lookHeardAt s base hd).tT.size :=
    congrArg (fun H : Forest.Heard => H.tT.size) e
  have e2 : (lookHeardAt s base hd).tT.size = s.calls.size := by
    show (s.calls.map _).size = s.calls.size
    rw [Array.size_map]
  have e3 : (k4LookOf s base hd).tT.size = 0 := rfl
  exact hc (e2.symm.trans (e1.symm.trans e3))

/-- CONDITIONAL: on hc, which speaks of s', the shape at which `lookHeardAt` is taken. The same at
any two shapes, numbers of rounds in front and lists of challenges: the field tT alone tells the
two texts apart. -/
theorem lookOf_ne_any (s s' : Forest.Shape) (base base' : ℕ) (hd hd' : List Fmt.Drawn)
    (hc : s'.calls.size ≠ 0) : k4LookOf s base hd ≠ lookHeardAt s' base' hd' := by
  intro e
  have e1 : (k4LookOf s base hd).tT.size = (lookHeardAt s' base' hd').tT.size :=
    congrArg (fun H : Forest.Heard => H.tT.size) e
  have e2 : (lookHeardAt s' base' hd').tT.size = s'.calls.size := by
    show (s'.calls.map _).size = s'.calls.size
    rw [Array.size_map]
  have e3 : (k4LookOf s base hd).tT.size = 0 := rfl
  exact hc (e2.symm.trans (e1.symm.trans e3))

/-- CONDITIONAL: on hs, hx, he and hk. The test on the sizes reads four fields alone. -/
theorem lookFits_congr (Q : K4Pub) {A B : Forest.Heard} (hs : A.shape = B.shape)
    (hx : A.zx = B.zx) (he : A.e = B.e) (hk : A.zk = B.zk) :
    k4LookFits Q A = k4LookFits Q B := by
  unfold k4LookFits OnBytes.Desc.First.K4.shapeFits
  dsimp only
  rw [hs, hx, he, hk]

/-- CONDITIONAL: on hok and hla. The test at `k4LookOf` of the public data's own shape, at every
number base of rounds in front and every list hd of challenges. -/
theorem lookFits_lookOf (Q : K4Pub) (hok : FoNums.ok Q.P.y.fo = true)
    (hla : Q.P.y.h.la ≤ Q.P.y.fo.dT) (base : ℕ) (hd : List Fmt.Drawn) :
    k4LookFits Q (k4LookOf Q.P.y.fo base hd) = true :=
  (lookFits_congr Q (A := k4LookOf Q.P.y.fo base hd) (B := lookHeardAt Q.P.y.fo base hd)
    rfl rfl rfl rfl).trans (lookFits_at Q hok hla base hd)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h and Lh. **hLk AT `k4LookAt`**: the test at the member's own public data, at
every list fr of challenges. -/
theorem lookFits_lookAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (fr : List Fmt.Drawn) :
    k4LookFits (k4PubAt cF k x) (k4LookAt (k4PubAt cF k x) fr) = true := by
  have N := nine_head h Lh
  rw [pubAt_is Lh]
  unfold k4LookAt
  exact lookFits_lookOf (k4PubAtX (P5J.At.X Zp) x.2.hp g (roundsTo cF.blocksInOrder k))
    (OnBytes.Road.K4.pub_ok N.Sx.pubOf) (light_head h Lh.lt Lh.hp).2.1 _ fr

/-- CONDITIONAL: on h, Lh and hbase. **THE TWO SENTENCES ON `look` AT `k4LookAt`.** ξ: an instance;
the text of the writers of the sub-protocol K3 (lookups) does not read it. -/
theorem lookAt_isK3 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) (ξ : ProofFile.Inst)
    (hbase : (k4PubAt cF k x).r0 - k4LookRounds (k4PubAt cF k x).P.y.fo =
      ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length) :
    LookIsK3Wide k4LookAt (k4PubAt cF k x) Zp cF g ξ ∧
      LookIsK3 k4LookAt (k4PubAt cF k x) Zp cF g ξ := by
  have eS : callsShape Zp g = (k4PubAt cF k x).P.y.fo :=
    (callsShape_head h Lh).trans
      (congrArg (fun P : OnBytes.Model.Layer.Pub => P.y.fo) Lh.P.symm)
  have e : ∀ hd, lookOfK3 Zp cF g ξ hd = lookHeardAt (k4PubAt cF k x).P.y.fo
      ((k4PubAt cF k x).r0 - k4LookRounds (k4PubAt cF k x).P.y.fo) hd := by
    intro hd
    show lookHeardAt (callsShape Zp g)
      ((cF.blocksInOrder.take (28 * g + 3)).flatMap (·.rounds)).length hd = _
    rw [eS, hbase]
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rw [e hd]
    obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := lookOf_open (k4PubAt cF k x).P.y.fo
      ((k4PubAt cF k x).r0 - k4LookRounds (k4PubAt cF k x).P.y.fo) hd
    exact ⟨a1, a2, a3, a4, a5, a6⟩
  · rw [e hd]
    obtain ⟨a1, a2, a3, -⟩ := lookOf_open (k4PubAt cF k x).P.y.fo
      ((k4PubAt cF k x).r0 - k4LookRounds (k4PubAt cF k x).P.y.fo) hd
    exact ⟨a1, a2, a3⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.lookOf_open
#print axioms ProofFile.Honest.K4.W.lookOf_ne
#print axioms ProofFile.Honest.K4.W.lookOf_ne_any
#print axioms ProofFile.Honest.K4.W.lookFits_congr
#print axioms ProofFile.Honest.K4.W.lookFits_lookOf
#print axioms ProofFile.Honest.K4.W.lookFits_lookAt
#print axioms ProofFile.Honest.K4.W.lookAt_isK3
