-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/HsemSays.lean: THE RECORDS' ROAD's END: THE STATEMENTS ALONE: «hsem» of the
library's fr_link_joh | sr_link_joh (OnBytes/Slice/FullRecLink.lean:151 | SmallRecLink.lean) AT
dec := THE LINK's DESCRIPTION's OWN run. NOTHING IS PROVED IN THIS FILE. AS TYPED HERE NEITHER
HsemFull NOR HsemSmall IS PROVED: WHAT IS PROVED (Johnson/Desc/K15/HsemAt.lean: fr_yes_desc |
sr_yes_desc) CARRIES TWO PREMISES
MORE: BatOk AND OpensAt (Johnson/Desc/K15/HsemProof.lean). Without OpensAt these two may be
unprovable or false. p12Of AND PubAt ARE USED BY THE PROOFS.
  p12Of P      the numbers of the proximity test's place at the link, as testBlock lays them
  (Johnson/Desc/Link/LinkDesc.lean:139-141)
  PubAt P c K  the four PUBLIC premises of the law of K12 (Johnson/Desc/K12/Law/Top.lean:
  StartK.stages | pub; k12_step_acc's early | answers) at a chain c and codes K
  HsemFull     **the statement at the full size**: for any parameters P whose shape and codes are
  the typed recordRead's, with one answer to a sample and PubAt at frC: any plan,
               any public test, any two keys that hold the pair of records r (under the two tests
               that the run makes): WHENEVER THE LIBRARY's WRITTEN LINK AT
               dec := (descOf P plan ok).run (first, further) ACCEPTS A TRANSCRIPT, THE CHAIN's YES
               IN THE FIELD HOLDS: frC.Acc at the claim that the batching makes of frRows at r, at
               the first tree read by frW and frF: TO THE LETTER the conclusion of the library's
               fr_yes (OnBytes/Slice/FullRecYes.lean), whose premise hdec («dec's yes gives the
               yes of `verify-on-bytes`'s link») is gone.
  HsemSmall    the small twin.
WHAT IT GIVES: with fr_link_joh | sr_link_joh: «(written … dec).Sound …» at the library's own
counts; with soundAt_full_of_joh | soundAt_small_of_joh
(Johnson/Flat/Dec/SoundAtOfWritten.lean): the frame's named premise SoundAt … decE, under
Cb.BCHKS46At.
WHAT LIES TOWARDS IT, PROVED: HandsOnLink | HandsOnRun (the five rounds: LinkRanR) · LinkClaim (the
batched row read in the field is sumStmR of st4R's rows) · K12's files'
k12_step_acc | k12_step_accG (a yes of Block.step of proximityTestKind guardedProximityTestParts p gives c.Acc, general in the
chain c, under StartK | StartG).
WHERE IT RESISTS: StartK's three sentences on the reading (rounds · shown · tie) at the view that
«written» forms (PQ.viewX of manyTr): the library says what that view shows BY KEY
(shows_many: Shows · ShowsFrom, OnBytes/Slice/ManyView.lean:142); K12's law wants it BY GROUP,
behind Block.step's groupsOf | regroup; and the words: frW | frF against K12's G.word | frOf.
NOT ATTACKED YET: whether the premises can be met together, and whether PubAt is all that is public
in StartK.

-/
import Johnson.Desc.K15.K15Head
import Johnson.Desc.K12.Law.K12Law
import OnBytes.Slice.FullRecYes
import OnBytes.Slice.SmallRecYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain Iop Prob Cb Cb.Ood _root_.Run Blocks
open OnBytes.Params (recordRead smallRecordRead)
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK (stagesOf stagesAt)

def p12Of (P : P15) : P12 := ((numsOf P).map (H2U.proximityTestParametersAt ⟨1, none, 6, .K12⟩)).getD
    (H2U.noP12 ⟨1, none, 6, .K12⟩)

structure PubAt (P : P15) {s : Sg} (c : Chain s) (K : Codes) : Prop where
  early : (p12Of P).early = true
  answers : (p12Of P).answers = 1
  stages : stagesOf c = (p12Of P).nums.stages
  pub : ∀ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (cu : IoppStage)
      (restI : List IoppStage),
    (p12Of P).nums.stages = first :: rest → stageAt (p12Of P) 0 first = some cu →
    stagesAt (p12Of P) 1 rest = some restI → c.Pub K cu restI

def HsemFull : Prop :=
  ∀ (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (first further : TableKey) (xs : List PQ.XO)
      (r : (frS.lkR frZ).X0),
    P.set.samples = 1 → P.S = recordRead.link → P.codes = recordRead.codes → PubAt P frC
        recordRead.codes →
    (first.fits recordRead.link.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index first r.1) →
    (further.fits recordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index further r.2) →
    ∀ (y : (frS.lkR frZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : frC.Bl),
      (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
          (fun V => (descOf P plan ok).run (first, further) V)).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, frC.trL b) = true →
      frC.Acc (sumStmR frN 97
          (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
              c5).1).1
          (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
              c5).1).2
          (drawnE (frRd 5) cA))
        (frW m2.1) (frF m2.1) (frW m2.1) b

def HsemSmall : Prop :=
  ∀ (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (first further : TableKey) (xs : List PQ.XO)
      (r : (srS.lkR srZ).X0),
    P.set.samples = 1 → P.S = smallRecordRead.link → P.codes = smallRecordRead.codes → PubAt P srC
        smallRecordRead.codes →
    (first.fits smallRecordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index first r.1) →
    (further.fits smallRecordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index further r.2) →
    ∀ (y : (srS.lkR srZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : srC.Bl),
      (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
          (fun V => (descOf P plan ok).run (first, further) V)).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, srC.trL b) = true →
      srC.Acc (sumStmR srN 97
          (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
              c5).1).1
          (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
              c5).1).2
          (drawnE (srRd 5) cA))
        (srW m2.1) (srF m2.1) (srW m2.1) b

end Desc.K15
