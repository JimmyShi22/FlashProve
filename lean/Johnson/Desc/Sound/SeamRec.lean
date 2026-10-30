-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamRec.lean: **THE SEAM's CORE AT THE TWO PROXIMITY TESTS, AT THE FILLING, FROM THE CONTENT OF THE PROMISE's TESTS ON THE RECORD: MemberFacts' (2) AND (6) PAID BY seed_at_record | sampleL_at_record.** Two statements; each proof is one call of tupleNine_fin | tupleTen_fin (SeamFin.lean) with these two (Johnson/Desc/Sound/SeedAtRecord.lean) and sits_nine | sits_ten.
  **tupleNine_rec | tupleTen_rec**   against tupleNine_fin | tupleTen_fin: OUT: hseed (K1.SeedIs at the record) · hmsg · hQ (sampleL's yes at each member of the data). IN: ONE BINDER: hrec: inside the promise, at each of the test's two messages' numbers the record holds a message of the plan's shape that passes the test sampleL (Johnson/Desc/K12/Law/SampleOk.lean) at that shape and number: THE CONTENT OF msgY AND OF THE BOOL smpY.
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamFin
import Johnson.Desc.Sound.SeedAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
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

variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (N : NumbersS)
  (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) {Fr : Frame} (P : P14)
  (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (π : P12) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
  (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (S : LinShape) (rU rO rSp t₁ t₂ : ℕ)
  (ch : Model.Verify.Chains) (tests : List (Block St Unit))
  (last : List (Block St Unit) → Block St Unit)

/-- **AT THE TEST ON G_u.** -/
theorem tupleNine_rec
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hsU : sentU.size = 2)
    (hsO : (withOmega P.S).size = 2)
    (hrd : ∀ z m part i, rd z m part i = tabP cs (z.1.l.get z.2).1 m part i)
    (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (hG : VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf ch P tests last).blocksInOrder)
    (hlo : (VerifiableInference.Desc.oraclesOf G.first.blocksInOrder).length = t₁)
    (hU : withU P.S = some sentU) (hlU : layTrees P.codes sentU = some layU)
    (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (hS : P.S.sharedSplitNeeded = true) (hm : P.S.masksAhead = true)
    (hN : N.tenant = tenantSh t₁ layU layO)
    (hd : ∀ j o, G.oracleAt j = some o → ∀ e ∈ Fr.all, e.no = j → e.a ≤ o.logLength)
    (hFU : SeatFits G cs (sendingU S rU t₁ layU layO).l (sendingU S rU t₁ layU layO).seat)
    (hFO : SeatFits G cs (sendingO S rO rSp t₁ layU layO).l (sendingO S rO rSp t₁ layU layO).seat)
    (hB : ∀ m, SentBefore N f l 9 x m)
    (hcod : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU layU
      layO) Oc true f l 9 a → a.1.2.st.codes = cs)
    (hI : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU layU
      layO) Oc true f l 9 a → InOrder a.1.2.st)
    (hTU : K1.Tie cs S.fold.u) (hTS : K1.Tie cs S.sharedSplit)
    (hmU : mem 0 = some (memSh S rU rO rSp t₁ layU layO .oU))
    (hmS : mem (sentU.size + 1) = some (memSh S rU rO rSp t₁ layU layO .oSp))
    (fU : 0 < S.fold.u.mainRows ∧ (S.fold.u.maskRows = 0 → cs.mask.size ≤ S.fold.u.maskCode))
    (fSp : ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < S.sharedSplit.maskRows ∧
      cs.base.size ≤ S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit : ∀ a₀ rest, π.nums.stages = a₀ :: rest →
      r (sgOf a₀).st < (rU + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.fold.u) ∧
      r (sgOf a₀).st < (rSp + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.sharedSplit))
    (hrec : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 9 a →
      (∃ z, a.1.2.st.oracles[0]? = some z ∧ z.shape = S.fold.u ∧
        ∀ m : Seat1, m.sh = S.fold.u → m.id = 0 → ok (sampleL cs m z) = true) ∧
      ∃ z, a.1.2.st.oracles[sentU.size + 1]? = some z ∧ z.shape = S.sharedSplit ∧
        ∀ m : Seat1, m.sh = S.sharedSplit → m.id = sentU.size + 1 → ok (sampleL cs m z) = true) :
    TupleNine cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ Oc (oNoSh sentU.size) P sentU layU layO f l
      mem rd π t₁ t₂ 1 (fun s => r s.st) rdN x := by
  refine tupleNine_fin cs G N Pm₀ Oc P sentU layU layO f l mem rd π r rdN x S rU rO rSp t₁ t₂ ch tests last hj he
    hp hsU hsO hrd hb hG hlo hU hlU hlO hS hm hN hd hFU hFO hB hcod hI hTU hTS
    (fun a ha => ⟨seed_at_record (t := ⟨a.1.2.st, a.1.2.book, 0, 0, .nothing, none⟩) rfl
        (hcod a ha) (hrec a ha).1 hTU,
      seed_at_record (t := ⟨a.1.2.st, a.1.2.book, 0, 0, .nothing, none⟩) rfl (hcod a ha)
        (hrec a ha).2 hTS⟩)
    hmU hmS
    (fun a ha => ⟨(hrec a ha).1.imp fun _ h => ⟨h.1, h.2.1⟩, (hrec a ha).2.imp fun _ h => ⟨h.1, h.2.1⟩⟩)
    fU fSp hfit ?_
  intro a τ b t ha hout ht a₀ rest G0 Ly D hf j
  have hX := x_of_on cs G _ N Pm₀ Oc _ P sentU layU layO f l 9 a ha
  obtain ⟨_, hq⟩ := sits_nine P sentU layU layO t₁ t₂ a.1.2 (by omega) (by omega) hX π t ht a₀ rest G0 Ly D hf
  have hst : t.st = a.1.2.st := by cases ht; rfl
  rcases hq j with ⟨_, hid, _⟩ | ⟨_, hid, _⟩
  · exact sampleL_at_record hst (hrec a ha).1 hf default j hid
  · exact sampleL_at_record hst (hrec a ha).2 hf default j hid

/-- **AT THE TEST ON G_omega.** -/
theorem tupleTen_rec
    (hj : johOk π r = true) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hsU : sentU.size = 2)
    (hsO : (withOmega P.S).size = 2)
    (hrd : ∀ z m part i, rd z m part i = tabP cs (z.1.l.get z.2).1 m part i)
    (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (hG : VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf ch P tests last).blocksInOrder)
    (hlo : (VerifiableInference.Desc.oraclesOf G.first.blocksInOrder).length = t₁)
    (hU : withU P.S = some sentU) (hlU : layTrees P.codes sentU = some layU)
    (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (hS : P.S.sharedSplitNeeded = true) (hm : P.S.masksAhead = true)
    (hN : N.tenant = tenantSh t₁ layU layO)
    (hd : ∀ j o, G.oracleAt j = some o → ∀ e ∈ Fr.all, e.no = j → e.a ≤ o.logLength)
    (hFO : SeatFits G cs (sendingO S rO rSp t₁ layU layO).l (sendingO S rO rSp t₁ layU layO).seat)
    (hB : ∀ m, SentBefore N f l 10 x m)
    (hcod : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU layU
      layO) Oc true f l 10 a → a.1.2.st.codes = cs)
    (hI : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU layU
      layO) Oc true f l 10 a → InOrder a.1.2.st)
    (hTU : K1.Tie cs S.omega) (hTS : K1.Tie cs S.sharedSplit)
    (hmU : mem sentU.size = some (memSh S rU rO rSp t₁ layU layO .oOmega))
    (hmS : mem (sentU.size + 1) = some (memSh S rU rO rSp t₁ layU layO .oSp))
    (fU : 0 < S.omega.mainRows ∧ (S.omega.maskRows = 0 → cs.mask.size ≤ S.omega.maskCode))
    (fSp : ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < S.sharedSplit.maskRows ∧
      cs.base.size ≤ S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit : ∀ a₀ rest, π.nums.stages = a₀ :: rest →
      r (sgOf a₀).st < (rO + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.omega) ∧
      r (sgOf a₀).st < (rSp + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.sharedSplit))
    (hrec : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 10 a →
      (∃ z, a.1.2.st.oracles[sentU.size]? = some z ∧ z.shape = S.omega ∧
        ∀ m : Seat1, m.sh = S.omega → m.id = sentU.size → ok (sampleL cs m z) = true) ∧
      ∃ z, a.1.2.st.oracles[sentU.size + 1]? = some z ∧ z.shape = S.sharedSplit ∧
        ∀ m : Seat1, m.sh = S.sharedSplit → m.id = sentU.size + 1 → ok (sampleL cs m z) = true) :
    TupleTen cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ Oc (oNoSh sentU.size) P sentU layU layO f l
      mem rd π t₁ t₂ 1 (fun s => r s.st) rdN x := by
  refine tupleTen_fin cs G N Pm₀ Oc P sentU layU layO f l mem rd π r rdN x S rU rO rSp t₁ t₂ ch tests last hj he
    hp hsU hsO hrd hb hG hlo hU hlU hlO hS hm hN hd hFO hB hcod hI hTU hTS
    (fun a ha => ⟨seed_at_record (t := ⟨a.1.2.st, a.1.2.book, 0, 0, .nothing, none⟩) rfl
        (hcod a ha) (hrec a ha).1 hTU,
      seed_at_record (t := ⟨a.1.2.st, a.1.2.book, 0, 0, .nothing, none⟩) rfl (hcod a ha)
        (hrec a ha).2 hTS⟩)
    hmU hmS
    (fun a ha => ⟨(hrec a ha).1.imp fun _ h => ⟨h.1, h.2.1⟩, (hrec a ha).2.imp fun _ h => ⟨h.1, h.2.1⟩⟩)
    fU fSp hfit ?_
  intro a τ b t ha hout ht a₀ rest G0 Ly D hf j
  have hX := x_of_on cs G _ N Pm₀ Oc _ P sentU layU layO f l 10 a ha
  obtain ⟨_, hq⟩ := sits_ten P sentU layU layO t₁ t₂ a.1.2 (by omega) hX π t ht a₀ rest G0 Ly D hf
  have hst : t.st = a.1.2.st := by cases ht; rfl
  rcases hq j with ⟨_, hid, _⟩ | ⟨_, hid, _⟩
  · exact sampleL_at_record hst (hrec a ha).1 hf default j hid
  · exact sampleL_at_record hst (hrec a ha).2 hf default j hid

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.tupleNine_rec
#print axioms Desc.K14.Law.Fence.tupleTen_rec
