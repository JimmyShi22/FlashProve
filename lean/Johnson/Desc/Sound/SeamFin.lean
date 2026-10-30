-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamFin.lean: **THE SEAM's CORE AT THE TWO PROXIMITY TESTS, AT THE FILLING, WITH MemberFacts' FIRST CLAUSE PAID BY site_nine | site_ten.** Two statements; each proof is one call of tupleNine_shQ | tupleTen_shQ (SeamAtShQ.lean) with site_nine | site_ten (Johnson/Desc/K12/Coin/SiteAtSeats.lean), "the yes of gpL" taken out of NTuple.
  **tupleNine_fin | tupleTen_fin**   against tupleNine_shQ | tupleTen_shQ: OUT: hK. IN: hmsg (inside the promise the record's two messages have the plan's shapes: msgY's content) · fU | fSp (three facts on the plan's shapes, two sizes of the codes and one tree's depth: site_nine | site_ten's own premises, handed on) · hfit (the two comparisons, at the plan's first stage: fit_of) · hQ (sampleL's yes at each member: from the Bool smpY, when it stands).
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamAtShQ
import Johnson.Desc.K12.Coin.SiteAtSeats

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
theorem tupleNine_fin
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
    (hseed : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 9 a →
      (∃ ρ yv, K1.SeedIs cs S.fold.u a.1.2.st 0 ρ yv) ∧
        ∃ ρ yv, K1.SeedIs cs S.sharedSplit a.1.2.st (sentU.size + 1) ρ yv)
    (hmU : mem 0 = some (memSh S rU rO rSp t₁ layU layO .oU))
    (hmS : mem (sentU.size + 1) = some (memSh S rU rO rSp t₁ layU layO .oSp))
    (hmsg : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 9 a →
      (∃ z, a.1.2.st.oracles[0]? = some z ∧ z.shape = S.fold.u) ∧
        ∃ z, a.1.2.st.oracles[sentU.size + 1]? = some z ∧ z.shape = S.sharedSplit)
    (fU : 0 < S.fold.u.mainRows ∧ (S.fold.u.maskRows = 0 → cs.mask.size ≤ S.fold.u.maskCode))
    (fSp : ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < S.sharedSplit.maskRows ∧
      cs.base.size ≤ S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit : ∀ a₀ rest, π.nums.stages = a₀ :: rest →
      r (sgOf a₀).st < (rU + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.fold.u) ∧
      r (sgOf a₀).st < (rSp + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.sharedSplit))
    (hQ : ∀ a τ b t, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 9 a → x.ior.red.out a τ = some b → inGu a.1.2 = .ok t →
      ∀ (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
        Fixes π t a₀ rest G0 Ly D → ∀ j : Fin D.mems.length,
        ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
          ok (sampleL cs (D.mems.get j) o) = true) :
    TupleNine cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ Oc (oNoSh sentU.size) P sentU layU layO f l
      mem rd π t₁ t₂ 1 (fun s => r s.st) rdN x := by
  refine tupleNine_shQ cs G N Pm₀ Oc P sentU layU layO f l mem rd π r rdN x S rU rO rSp t₁ t₂ ch tests
    last hj he hp hsU hsO hrd hb hG hlo hU hlU hlO hS hm hN hd hFU hFO hB hcod hI hTU hTS hseed hmU hmS
    ?_
  intro a τ b t ha hout ht a₀ rest G0 Ly D hf hNt j
  obtain ⟨row₀, hok, _⟩ := hNt
  have hX := x_of_on cs G _ N Pm₀ Oc _ P sentU layU layO f l 9 a ha
  obtain ⟨_, hs, hM, _⟩ := (sharedX_parts P sentU layU layO 9 a.1.2).1 hX
  have hst : t.st = a.1.2.st := by cases ht; rfl
  have hcs : D.st.codes = cs := by
    rw [codes_fixed π t a₀ rest G0 Ly D hf, hst]; exact hcod a ha
  obtain ⟨mU, mSp⟩ := hmsg a ha
  exact ⟨site_nine P sentU layU layO a.1.2 (by omega) (by omega) hs hM π t ht a₀ rest G0 Ly D hf row₀ hok
      cs hcs S.fold.u S.sharedSplit mU mSp fU (fSp a₀ rest hf.1) j,
    hQ a τ b t ha hout ht a₀ rest G0 Ly D hf j, (hfit a₀ rest hf.1).1, (hfit a₀ rest hf.1).2⟩

/-- **AT THE TEST ON G_omega.** -/
theorem tupleTen_fin
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
    (hseed : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 10 a →
      (∃ ρ yv, K1.SeedIs cs S.omega a.1.2.st sentU.size ρ yv) ∧
        ∃ ρ yv, K1.SeedIs cs S.sharedSplit a.1.2.st (sentU.size + 1) ρ yv)
    (hmU : mem sentU.size = some (memSh S rU rO rSp t₁ layU layO .oOmega))
    (hmS : mem (sentU.size + 1) = some (memSh S rU rO rSp t₁ layU layO .oSp))
    (hmsg : ∀ a, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 10 a →
      (∃ z, a.1.2.st.oracles[sentU.size]? = some z ∧ z.shape = S.omega) ∧
        ∃ z, a.1.2.st.oracles[sentU.size + 1]? = some z ∧ z.shape = S.sharedSplit)
    (fU : 0 < S.omega.mainRows ∧ (S.omega.maskRows = 0 → cs.mask.size ≤ S.omega.maskCode))
    (fSp : ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < S.sharedSplit.maskRows ∧
      cs.base.size ≤ S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit : ∀ a₀ rest, π.nums.stages = a₀ :: rest →
      r (sgOf a₀).st < (rO + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.omega) ∧
      r (sgOf a₀).st < (rSp + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.sharedSplit))
    (hQ : ∀ a τ b t, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 10 a → x.ior.red.out a τ = some b → inGomega a.1.2 = .ok t →
      ∀ (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
        Fixes π t a₀ rest G0 Ly D → ∀ j : Fin D.mems.length,
        ∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
          ok (sampleL cs (D.mems.get j) o) = true) :
    TupleTen cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ Oc (oNoSh sentU.size) P sentU layU layO f l
      mem rd π t₁ t₂ 1 (fun s => r s.st) rdN x := by
  refine tupleTen_shQ cs G N Pm₀ Oc P sentU layU layO f l mem rd π r rdN x S rU rO rSp t₁ t₂ ch tests
    last hj he hp hsU hsO hrd hb hG hlo hU hlU hlO hS hm hN hd hFO hB hcod hI hTU hTS hseed hmU hmS
    ?_
  intro a τ b t ha hout ht a₀ rest G0 Ly D hf hNt j
  obtain ⟨row₀, hok, _⟩ := hNt
  have hX := x_of_on cs G _ N Pm₀ Oc _ P sentU layU layO f l 10 a ha
  obtain ⟨_, hs, hM, _⟩ := (sharedX_parts P sentU layU layO 10 a.1.2).1 hX
  have hst : t.st = a.1.2.st := by cases ht; rfl
  have hcs : D.st.codes = cs := by
    rw [codes_fixed π t a₀ rest G0 Ly D hf, hst]; exact hcod a ha
  obtain ⟨mU, mSp⟩ := hmsg a ha
  exact ⟨site_ten P sentU layU layO a.1.2 (by omega) hs hM π t ht a₀ rest G0 Ly D hf row₀ hok
      cs hcs S.omega S.sharedSplit mU mSp fU (fSp a₀ rest hf.1) j,
    hQ a τ b t ha hout ht a₀ rest G0 Ly D hf j, (hfit a₀ rest hf.1).1, (hfit a₀ rest hf.1).2⟩

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.tupleNine_fin
#print axioms Desc.K14.Law.Fence.tupleTen_fin
