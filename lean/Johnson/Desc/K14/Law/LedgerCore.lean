-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerCore.lean: THE LAST CALL AT THE SEAM OF THE SHARED CHAIN's TWO PROXIMITY
TESTS. nine_at_K | ten_at_K (Johnson/Desc/K14/Law/LedgerNineTen.lean) have ONE premise "core":
TupleNine | TupleTen at the promise pmE. That core stands as one
theorem a seat at a filling of the members (tupleNine_rec | tupleTen_rec,
Johnson/Desc/Sound/SeamRec.lean), general in the promise's letter, under three premises on what the
promise holds of the record: hcod, hI, hrec. HERE it is called BY NAME at Pm₀ := pmE, and the three
are paid out of the filling of record XK.

  core_nine_K, core_ten_K   **the core at pmE**: hcod := codes_of_on · hI := tidy_of_on · hrec :=
                  msgU_of_on | msgO_of_on and msgS_of_on (the record's message has the plan's shape)
                  with the letter Y's content (letter_of_on and hYc).
WHAT STAYS. Every other binder of tupleNine_rec | tupleTen_rec, TO THE LETTER (the plan and the
piece · the description's · the members' · K1's ties · the sizes · hfit) · hYc: what the letter Y
says of a record at the border: the message at each of the test's two numbers passes K12's test on a
member's sample at every seat of that shape and number: at Y := smpK by that test's own text and
"the test reads of a seat its shape and number alone".
What is not claimed. NO MEMBER IS SHOWN. It closes no row. No soundness of a verifier; no level.

-/
import Johnson.Desc.Sound.SeamRec
import Johnson.Desc.K14.Law.LedgerAtSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open OnBytes.Maker OnBytes.Params
open _root_.Run
open H2K.First (Seat1 Plain)
open H2K.Pub (sgOf johOk)
open Desc.K14.Law.Fence

variable {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (N : NumbersS)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (Pm₁ : PromMeaning St) (n nU : ℕ)
  (Y : ℕ → St → Bool) (Oc : P₁ → Strs → Prop) {Fr : Frame} (Q : P14)
  (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem)
  (rd : (x : Mem) → ((sigOf Q.codes x.1.l).om x.2).Msg → Part → ℕ → GE)
  (π : P12) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
  (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (S : LinShape) (rU rO rSp t₁ t₂ : ℕ)
  (ch : Model.Verify.Chains) (tests : List (Block St Unit))
  (last : List (Block St Unit) → Block St Unit)

/-- **THE CORE AT BLOCK 9, AT pmE.** -/
theorem core_nine_K
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hsU : sentU.size = 2)
    (hsO : (withOmega Q.S).size = 2)
    (hrd : ∀ z m part i, rd z m part i = tabP Q.codes (z.1.l.get z.2).1 m part i)
    (hb : Alike (VerifiableInference.Desc.Sound.held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block
        T12 Unit))) x.b)
    (hG : VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf ch Q tests last).blocksInOrder)
    (hlo : (VerifiableInference.Desc.oraclesOf G.first.blocksInOrder).length = t₁)
    (hU : withU Q.S = some sentU) (hlU : layTrees Q.codes sentU = some layU)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO)
    (hS : Q.S.sharedSplitNeeded = true) (hm : Q.S.masksAhead = true)
    (hN : N.tenant = tenantSh t₁ layU layO)
    (hd : ∀ j o, G.oracleAt j = some o → ∀ e ∈ Fr.all, e.no = j → e.a ≤ o.logLength)
    (hFU : SeatFits G Q.codes (sendingU S rU t₁ layU layO).l (sendingU S rU t₁ layU layO).seat)
    (hFO : SeatFits G Q.codes (sendingO S rO rSp t₁ layU layO).l (sendingO S rO rSp t₁ layU
        layO).seat)
    (hB : ∀ m, SentBefore N f l 9 x m)
    (hTU : K1.Tie Q.codes S.fold.u) (hTS : K1.Tie Q.codes S.sharedSplit)
    (hmU : mem 0 = some (memSh S rU rO rSp t₁ layU layO .oU))
    (hmS : mem (sentU.size + 1) = some (memSh S rU rO rSp t₁ layU layO .oSp))
    (fU : 0 < S.fold.u.mainRows ∧ (S.fold.u.maskRows = 0 → Q.codes.mask.size ≤ S.fold.u.maskCode))
    (fSp : ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < S.sharedSplit.maskRows ∧
      Q.codes.base.size ≤ S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit : ∀ a₀ rest, π.nums.stages = a₀ :: rest →
      r (sgOf a₀).st < (rU + 1) * 2 ^ ((sgOf a₀).C.a - aOf Q.codes S.fold.u) ∧
      r (sgOf a₀).st < (rSp + 1) * 2 ^ ((sgOf a₀).C.a - aOf Q.codes S.sharedSplit))
    (hYc : ∀ s : St, Y 9 s = true →
      (∀ z, s.st.oracles[0]? = some z → ∀ m : Seat1, m.sh = S.fold.u → m.id = 0 →
        ok (sampleL Q.codes m z) = true) ∧
      ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : Seat1, m.sh = S.sharedSplit →
        m.id = sentU.size + 1 → ok (sampleL Q.codes m z) = true) :
    TupleNine Q.codes G (msSh S rU rO rSp t₁ layU layO) N (pmE decT₂ Pm₁ Q n nU sentU.size
        (S.fold.u, S.omega, S.sharedSplit, Y)) Oc (oNoSh sentU.size) Q sentU layU layO f l mem rd π
        t₁ t₂ 1
      (fun s => r s.st) rdN x := by
  refine tupleNine_rec Q.codes G N (pmE decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega,
      S.sharedSplit, Y)) Oc Q sentU layU layO f l mem rd π r rdN x S rU rO rSp t₁ t₂ ch tests
    last hj he hp hsU hsO hrd hb hG hlo hU hlU hlO hS hm hN hd hFU hFO hB
    (fun a ha => codes_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega, S.sharedSplit, Y)
        Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU layO f l 9 a
        ha)
    (fun a ha => (tidy_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega, S.sharedSplit, Y)
        Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU layO f l 9 a
        ha).inOrder)
    hTU hTS hmU hmS fU fSp hfit fun a ha => ?_
  have hY := hYc a.1.2 (letter_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega, S.sharedSplit,
      Y) Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU layO f l 9 a
      ha)
  obtain ⟨z1, e1, s1, _⟩ := msgU_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega,
      S.sharedSplit, Y) Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU
      layO f l 9 a ha (by omega)
  obtain ⟨z2, e2, s2, _⟩ := msgS_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega,
      S.sharedSplit, Y) Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU
      layO f l 9 a ha (by omega)
  exact ⟨⟨z1, e1, s1, hY.1 z1 e1⟩, z2, e2, s2, hY.2 z2 e2⟩

/-- **THE CORE AT BLOCK 10, AT pmE.** -/
theorem core_ten_K
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hsU : sentU.size = 2)
    (hsO : (withOmega Q.S).size = 2)
    (hrd : ∀ z m part i, rd z m part i = tabP Q.codes (z.1.l.get z.2).1 m part i)
    (hb : Alike (VerifiableInference.Desc.Sound.held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π :
        Block T12 Unit))) x.b)
    (hG : VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf ch Q tests last).blocksInOrder)
    (hlo : (VerifiableInference.Desc.oraclesOf G.first.blocksInOrder).length = t₁)
    (hU : withU Q.S = some sentU) (hlU : layTrees Q.codes sentU = some layU)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO)
    (hS : Q.S.sharedSplitNeeded = true) (hm : Q.S.masksAhead = true)
    (hN : N.tenant = tenantSh t₁ layU layO)
    (hd : ∀ j o, G.oracleAt j = some o → ∀ e ∈ Fr.all, e.no = j → e.a ≤ o.logLength)
    (hFO : SeatFits G Q.codes (sendingO S rO rSp t₁ layU layO).l (sendingO S rO rSp t₁ layU
        layO).seat)
    (hB : ∀ m, SentBefore N f l 10 x m)
    (hTU : K1.Tie Q.codes S.omega) (hTS : K1.Tie Q.codes S.sharedSplit)
    (hmU : mem sentU.size = some (memSh S rU rO rSp t₁ layU layO .oOmega))
    (hmS : mem (sentU.size + 1) = some (memSh S rU rO rSp t₁ layU layO .oSp))
    (fU : 0 < S.omega.mainRows ∧ (S.omega.maskRows = 0 → Q.codes.mask.size ≤ S.omega.maskCode))
    (fSp : ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < S.sharedSplit.maskRows ∧
      Q.codes.base.size ≤ S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit : ∀ a₀ rest, π.nums.stages = a₀ :: rest →
      r (sgOf a₀).st < (rO + 1) * 2 ^ ((sgOf a₀).C.a - aOf Q.codes S.omega) ∧
      r (sgOf a₀).st < (rSp + 1) * 2 ^ ((sgOf a₀).C.a - aOf Q.codes S.sharedSplit))
    (hYc : ∀ s : St, Y 10 s = true →
      (∀ z, s.st.oracles[sentU.size]? = some z → ∀ m : Seat1, m.sh = S.omega → m.id = sentU.size →
        ok (sampleL Q.codes m z) = true) ∧
      ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : Seat1, m.sh = S.sharedSplit →
        m.id = sentU.size + 1 → ok (sampleL Q.codes m z) = true) :
    TupleTen Q.codes G (msSh S rU rO rSp t₁ layU layO) N (pmE decT₂ Pm₁ Q n nU sentU.size (S.fold.u,
        S.omega, S.sharedSplit, Y)) Oc (oNoSh sentU.size) Q sentU layU layO f l mem rd π t₁ t₂ 1
      (fun s => r s.st) rdN x := by
  refine tupleTen_rec Q.codes G N (pmE decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega,
      S.sharedSplit, Y)) Oc Q sentU layU layO f l mem rd π r rdN x S rU rO rSp t₁ t₂ ch tests
    last hj he hp hsU hsO hrd hb hG hlo hU hlU hlO hS hm hN hd hFO hB
    (fun a ha => codes_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega, S.sharedSplit, Y)
        Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU layO f l 10 a
        ha)
    (fun a ha => (tidy_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega, S.sharedSplit, Y)
        Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU layO f l 10 a
        ha).inOrder)
    hTU hTS hmU hmS fU fSp hfit fun a ha => ?_
  have hY := hYc a.1.2 (letter_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega, S.sharedSplit,
      Y) Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU layO f l 10 a
      ha)
  obtain ⟨z1, e1, s1, _⟩ := msgO_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega,
      S.sharedSplit, Y) Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU
      layO f l 10 a ha (by omega)
  obtain ⟨z2, e2, s2, _⟩ := msgS_of_on decT₂ Pm₁ Q n nU sentU.size (S.fold.u, S.omega,
      S.sharedSplit, Y) Q.codes G (msSh S rU rO rSp t₁ layU layO) N Oc (oNoSh sentU.size) sentU layU
      layO f l 10 a ha (by omega)
  exact ⟨⟨z1, e1, s1, hY.1 z1 e1⟩, z2, e2, s2, hY.2 z2 e2⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.core_nine_K
#print axioms Desc.K14.Law.core_ten_K
