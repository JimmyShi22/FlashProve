-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Row15AtName.lean (it takes what the tables' filler holds: DK at the frame's depth is the written data; and it brings the fit): THE LAST JOIN OF ROW 1.15 OF THE KEY FILE's TABLES (ITS FIRST PROXIMITY TEST): THE FIELD r1_15 AT The21AtName's TERMS (Johnson/Top/Fire/Code/KeyAtName.lean), IN SCOPE, WITH THE WEIGHT NOT A PREMISE: the premise Gives15 of r1_15_of_facts (K12Facts15M.lean) is paid by gives15_at_fill (K12Gives15Is.lean), whose premise on the law's composition is paid by coreFacts_15 (K12Facts15D.lean); what these ask on the list of rounds and of the filling is paid by calls. One statement with its proof: calls alone. NO PREMISE ON THE WEIGHT IS LEFT: IT GIVES THE FIELD FROM THE SCOPE's FOUR, WHAT THE SEAT's ACCEPTING RUN HANDS, AND q₁.
OBJECT. `LPFD.The21`'s field r1_15 at the letters that The21AtName fixes. USER. The21AtName's filler.
ALL PREMISES. The scope's four: the public files are in scope · the policy read · the chains made, at any digest · the source of them. Of what the seat's accepting run hands: the place's numbers are made of the same m · the tests planOk and wantedOk of the IOP as written in Lean · its data of the key file are DK's at the frame's depth. DK at the frame's depth is the written data. q₁. These nine are what the seat's accepting run hands, by reading (Key.keyDataAndDecisionAtFixedDigest's yes taken apart; the written data by a theorem on the built key); The21AtName binds q₁ itself. That the data stand at the name "key file" is that reading's too. PAID INSIDE, OF EVERY REACHED STATE IN FRONT OF THE TEST: no open row is marked as a sample row (openKinds_at_reached₁, Johnson/RunOne/KeyWalkAny.lean) · the plain test on message 1's OOD sample accepts (hm_15_scope, Johnson/RunOne/KeyAt15Nums.lean) · the word off the plain strings is the word as sent (word_15_on, Johnson/RunOne/Law/Word15.lean).
WHAT IT SAYS AND DOES NOT SAY OF BITS. Each of the 23 rounds' count is at most 2⁻¹²⁸ of ITS OWN round's written verifier messages (proof of work among them), by exact numbers in the kernel; one round at a time, no sum.

  six_one: the list's second entry.
  r1_15_at_name: the field.
  fit_1_15: a check by Lean, in the form of another file on the shared chain's rows: a member of The21 at the written reading tabN and the written offsets takes this theorem as its field r1_15.
THE LETTER rd. The kind's files' law and the composition bear a letter rd: a radius for each member's index, which the library's member object carries (gpG, Johnson/Desc/K12/Law/FirstOkLaw.lean). Both hold at every rd; the field names none. It is laid at the member's own radius.
Limits. THAT ITS PREMISES CAN BE MET TOGETHER IS NOT SHOWN HERE: no public files, no m, no accepting run are exhibited. It stands on every file beneath it. One field of twenty-one. One size. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15J
import Johnson.RunOne.Law.K12Facts15D
import Johnson.RunOne.Law.K12Facts15P
import Johnson.RunOne.Law.K12Gives15Is
import Johnson.RunOne.KeyAt15Fits
import Johnson.RunOne.KeyWalkAny
import Johnson.RunOne.KeyAt15Nums
import Johnson.RunOne.Law.Word15
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.RunOne.Law.AllAtO
import Johnson.RunOne.Law.AtFreeCfg
import Johnson.Desc.First.Look.KeyLaw.HeldFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.K12AtThe21
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open OnBytes.Slice (Sg)
open H2K.Pin (NTuple)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt johOk batV0 codes_of_johOk)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ R₁ open₁)
open LPFD

open Johnson.Pack
open Johnson.Top.H (csKey shMul eRng1)
open VerifiableInference.Desc.Key.Fill (six)
open Johnson.RunOne.KeyRows23 (numSix atSix seatAt)
open H2K.Pin (tabP)
open OnBytes.Means (OpenKinds)
open Johnson.RunOne.Law.K12Law15At Johnson.RunOne.Law.K12Back15
open Johnson.RunOne.Law.AtFreeCfg (ReadOf seat_in_scope)
open Johnson.RunOne.Law.AllAtO (answers_in_scope)
open Johnson.RunOne.Law.KeyInScope (key_in_scope five_in_scope)
open Johnson.G.OfPlan (Made)
open Lk6.AtPlan (keyFull)

theorem six_one : six.get i₁ = (shMul, eRng1) := rfl

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
  (DK : WholeD) (tab : MsgN → ℕ → ℕ → OnBytes.F)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))

/-- **THE FIELD r1_15 AT The21AtName's TERMS, IN SCOPE: THE WEIGHT IS NO PREMISE.** -/
theorem r1_15_at_name {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
    (hD : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab) collN)
      (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tab))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 15 := by
  obtain ⟨-, hr, hlin, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  have hl := hl_in_scope hZ hP hm hX hp
  have hk := key_in_scope hZ hP hm
  have hset := K12Facts15.set_in_scope hZ hP hm
  have plan := K12Facts15.plan_of X N P hp
  have hL := (Johnson.RunOne.Sound.rounds_in_scope hZ hP hm hX hp hw).1
  have hLf : (Fk X N P).first.blocksInOrder.map (·.rounds.length) = K12Facts15.roundsFull := hL.trans rfl
  have hn : X.Y.k.oneTime.ranges.lookups.length = 2 := by
    rw [hr]
    exact VerifiableInference.Desc.K3.KeyLaw.held_full_two
  have hds : (DK.at frS.P.T.a).ds₁ = Johnson.G.writtenKFull.ds₁ := congrArg WholeD.ds₁ hDK
  have hD' : (Fk X N P).data "key file" = .ok Johnson.G.writtenKFull := by
    rw [hD, hDK]
  have hbase : ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 15), (atSix k).1 <
      cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15 := by
    rw [hds, ← K12Facts15.at_ds₁ Johnson.G.writtenKFull frS.P.T.a]
    exact Johnson.RunOne.KeyLetters.base_15_scope X N P c₁ k₁ hp hD' hL q₁ hl
  have hno : ∀ d ∈ (DK.at frS.P.T.a).ds₁.take (((c₁ :: k₁).take 15).flatMap (·.rounds)).length,
      (d.entry.name == "BAT") = false := by
    rw [hds, ← K12Facts15.at_ds₁ Johnson.G.writtenKFull 0]
    exact K12Facts15.hno_scope (c₁ :: k₁) (q₁ ▸ hLf) 0
  have joh := K12Facts15.joh_scope hN plan hk
  have hft : (rangesParams N).nums.firstTree = 0 := by
    rw [(K12Facts15.nums_of_early N (PlanPays.rng_pays plan).1).1]
    exact (K12Facts15.numbers_parts hN).2.1
  have hseed : ∀ a, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → ∃ ρ y, K1.SeedIs csKey (six.get i₁).1 a.2.d.st 1 ρ y :=
    fun a h => Johnson.RunOne.KeyLetters.hseed_fits X N P hp hc hr _ a h
  have hlog := Johnson.RunOne.KeyLetters.hlog_fits X N P hi hc hr
  have le : Le15 (W := Unit) X N P DK c₁ k₁ capRest K12Facts15.radRng :=
    le15_of X N P DK c₁ k₁ capRest "key file" K12Facts15.radRng (H2K.Pub.brOfT K12Facts15.testRng) m hX hN hp hD q₁ hl hno
      joh (fun _ => rfl) (K12Facts15.small_scope hN plan hk hset) (K12Facts15.price_scope hN plan hk)
  refine r1_15_of_facts X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tab)
    collN "key file" K12Facts15.radRng (fun _ => eRng1) m hX hN hp hD q₁ hl hno joh le ?_
  exact gives15_at_fill X N P DK c₁ k₁ capRest decN recBack tab collN (fun _ => 1)
    (fun o => if o = 1 then some x₁ else none) (fun x u part i => tabP csKey (x.1.l.get x.2).1 u part i)
    hp (K12Facts15.numbers_parts hN).2.1 hl hn (seat_in_scope hZ hP hm hX hp).2.2 (answers_in_scope hZ hP hm hX hp)
    rfl rfl (fun _ _ _ _ => rfl) (fun a h => Johnson.RunOne.KeyWalk.openKinds_at_reached₁ _ 15 a h)
    hseed hlog (Johnson.RunOne.KeyLetters.told_fits X N P hi hc hr) (fun _ => eRng1)
    (K12Core15At.coreFacts_15 X N P DK decN recBack tab collN (fun _ => 1) (fun o => if o = 1 then some x₁ else none)
      hp hl K12Facts15.radRng joh
      (fun a rest hs => K12Facts15.hfit_scope hN plan hk a rest hs)
      (hc.trans Johnson.RunOne.KeyLetters.codes_full) rfl rfl
      hseed (Johnson.RunOne.KeyLetters.hm_15_scope X N P hp hc hr _) (nlAt (rangesParams N) 0) (fun _ => eRng1)
      (Word15.word_15_on X N P DK decN recBack tab collN "key file" "" hp hD hl hft hseed
        (Johnson.RunOne.KeyLetters.n01_scope X N P hi hc hr "" "").2 hlog))
    (fun y y' r h => (cellOnly_collN y y' r h).1) hbase

/-- **THE FIT**: the theorem's conclusion IS The21's field r1_15 at the written reading and offsets: by Lean's own check of types. -/
def fit_1_15 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Made}
    (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
    (hD : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N :=
  { H with r1_15 := r1_15_at_name DK tabN c₁ k₁ c₂ k₂ c₃ k₃ hZ hP hm hX hN hp hw hD hDK q₁ }

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.six_one
#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_at_name
#print axioms Johnson.RunOne.Law.K12AtThe21.fit_1_15
