-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamAtSh.lean: **THE SEAM's CORE AT THE TWO PROXIMITY TESTS, AT THE FILLING ms := msSh · N.tenant := tenantSh · oNo := oNoSh: ALL THAT IS TYPED, JOINED IN ONE CALL: WHAT IS LEFT, AS ONE LIST OF BINDERS.** One statement; its proof is calls: tupleNine_members (SeamLast.lean) ·
memberFacts_of (SeamMemberOf.lean) · word_nine (SeamWordSh.lean) · huniq_nine · memSh's lemmas (SeamNumbersSh.lean) · sits_nine (K12/Coin/MemberSits.lean).
  **tupleNine_sh | tupleTen_sh**   TupleNine | TupleTen … AT THAT FILLING. THEIR PREMISES ARE THE SEAM's WHOLE DEBT AT BLOCKS 9 | 10 (at 10: o_omega in o_u's place; tupleTen_members · word_ten · huniq_ten · sits_ten):
    THE PLAN AND THE PIECE: hb · hj · he · hp · hsU · hsO · the two layouts · a split · masks ahead   [the join at the laid value: K12's files]
    THE DESCRIPTION: hG · hlo · hd (the depth) · SeatFits at the two sendings
    THE PROMISE: hcod · hI (codX · tidY) · **hseed: at each of the test's two messages the record holds the sendings' own invariant K1.SeedIs at the plan's shape** [no clause of the promise holds it yet]
    THE NUMBERS: hB (SentBefore: sb_sh) · hN
    A MEMBER: Tie · siteL's yes · sampleL's yes · the test's radius against the member's (fit_of) · mem
Limits. Every binder is a premise. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamLast
import Johnson.Desc.Sound.SeamMemberOf
import Johnson.Desc.Sound.SeamWordSh

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

/-- **THE CORE AT THE TEST ON G_u, AT THE FILLING.** -/
theorem tupleNine_sh
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
    (hK : ∀ a τ b t, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 9 a → x.ior.red.out a τ = some b → inGu a.1.2 = .ok t →
      ∀ (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
        Fixes π t a₀ rest G0 Ly D → ∀ j : Fin D.mems.length,
        ok (siteL cs a₀ (D.mems.get j)) = true ∧
        (∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
          ok (sampleL cs (D.mems.get j) o) = true) ∧
        r (sgOf a₀).st < (rU + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.fold.u) ∧
        r (sgOf a₀).st < (rSp + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.sharedSplit)) :
    TupleNine cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ Oc (oNoSh sentU.size) P sentU layU layO f l
      mem rd π t₁ t₂ 1 (fun s => r s.st) rdN x := by
  have e3 := memSh_entry S rU rO rSp t₁ layU layO
  refine tupleNine_members cs G _ N Pm₀ Oc _ P sentU layU layO f l mem rd π t₁ t₂ 1 r rdN x hj he hp
    hsU hsO hrd hb hcod hI (memSh S rU rO rSp t₁ layU layO .oU) (memSh S rU rO rSp t₁ layU layO .oSp)
    rU rSp
    (memSh_ne S rU rO rSp t₁ layU layO P.codes sentU (withOmega P.S) hlU hlO (by omega) (by omega) _ _
      (by decide))
    (huniq_nine S rU rO rSp t₁ layU layO P.codes sentU (withOmega P.S) hlU hlO (by omega) (by omega) N
      hN) ?_
  intro a τ b t ha hout ht a₀ rest G0 Ly D hf j
  have hX := x_of_on cs G _ N Pm₀ Oc _ P sentU layU layO f l 9 a ha
  obtain ⟨_, hq⟩ := sits_nine P sentU layU layO t₁ t₂ a.1.2 (by omega) (by omega) hX π t ht a₀ rest G0
    Ly D hf
  obtain ⟨k1, k2, k3, k4⟩ := hK a τ b t ha hout ht a₀ rest G0 Ly D hf j
  obtain ⟨⟨ρU, yU, sdU⟩, ρS, yS, sdS⟩ := hseed a ha
  have hst : t.st = a.1.2.st := by cases ht; rfl
  constructor
  · intro e
    rcases hq j with ⟨_, hid, _⟩ | ⟨e', _, _⟩
    · have hid0 : (D.mems.get j).id = 0 := hid
      have sd : K1.SeedIs cs S.fold.u t.st (D.mems.get j).id ρU yU := by rw [hst, hid0]; exact sdU
      have hsh : (D.mems.get j).sh = S.fold.u := (member_of_seedIs hf default j sd).1
      refine memberFacts_of cs G Fr _ _ _ mem a.2 _ _ π t a₀ rest G0 Ly D hf j _ S.fold.u rU e3.1 hTU ρU
        yU sd ?_ k1 k2 k3 (by rw [hid0]; exact hmU) ?_
      · rw [hst, hid0]; rfl
      · have w := (word_nine cs G N Pm₀ Oc _ P sentU layU layO f l S rU rO rSp t₁ t₂ ch tests last hG
          hlo hU hlU hlO hS hm hsU hsO hN hd a ha x hB hFU hFO π t ht a₀ rest G0 Ly D hf j
          (fun _ => by rw [hsh]; exact e3.1) (fun h => by omega)).1 e
        rw [hsh] at w
        exact w
    · omega
  · intro e
    rcases hq j with ⟨e', _, _⟩ | ⟨_, hid, _⟩
    · omega
    · have hid1 : (D.mems.get j).id = sentU.size + 1 := hid
      have sd : K1.SeedIs cs S.sharedSplit t.st (D.mems.get j).id ρS yS := by
        rw [hst, hid1]; exact sdS
      have hsh : (D.mems.get j).sh = S.sharedSplit := (member_of_seedIs hf default j sd).1
      refine memberFacts_of cs G Fr _ _ _ mem a.2 _ _ π t a₀ rest G0 Ly D hf j _ S.sharedSplit rSp e3.2.2
        hTS ρS yS sd ?_ k1 k2 k4 (by rw [hid1]; exact hmS) ?_
      · rw [hst, hid1]; rfl
      · have w := (word_nine cs G N Pm₀ Oc _ P sentU layU layO f l S rU rO rSp t₁ t₂ ch tests last hG
          hlo hU hlU hlO hS hm hsU hsO hN hd a ha x hB hFU hFO π t ht a₀ rest G0 Ly D hf j
          (fun h => by omega) (fun _ => by rw [hsh]; exact e3.2.2)).2 e
        rw [hsh] at w
        exact w

/-- **THE CORE AT THE TEST ON G_omega, AT THE FILLING.** The data's first member is o_omega, its second o_sp. -/
theorem tupleTen_sh
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
    (hK : ∀ a τ b t, onQ₂ N (pmX cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ (oNoSh sentU.size) P sentU
      layU layO) Oc true f l 10 a → x.ior.red.out a τ = some b → inGomega a.1.2 = .ok t →
      ∀ (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
        Fixes π t a₀ rest G0 Ly D → ∀ j : Fin D.mems.length,
        ok (siteL cs a₀ (D.mems.get j)) = true ∧
        (∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧
          ok (sampleL cs (D.mems.get j) o) = true) ∧
        r (sgOf a₀).st < (rO + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.omega) ∧
        r (sgOf a₀).st < (rSp + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs S.sharedSplit)) :
    TupleTen cs G (msSh S rU rO rSp t₁ layU layO) N Pm₀ Oc (oNoSh sentU.size) P sentU layU layO f l
      mem rd π t₁ t₂ 1 (fun s => r s.st) rdN x := by
  have e3 := memSh_entry S rU rO rSp t₁ layU layO
  refine tupleTen_members cs G _ N Pm₀ Oc _ P sentU layU layO f l mem rd π t₁ t₂ 1 r rdN x hj he hp
    hsU hsO hrd hb hcod hI (memSh S rU rO rSp t₁ layU layO .oOmega)
    (memSh S rU rO rSp t₁ layU layO .oSp) rO rSp
    (memSh_ne S rU rO rSp t₁ layU layO P.codes sentU (withOmega P.S) hlU hlO (by omega) (by omega) _ _
      (by decide))
    (huniq_ten S rU rO rSp t₁ layU layO P.codes sentU (withOmega P.S) hlU hlO (by omega) (by omega) N
      hN) ?_
  intro a τ b t ha hout ht a₀ rest G0 Ly D hf j
  have hX := x_of_on cs G _ N Pm₀ Oc _ P sentU layU layO f l 10 a ha
  obtain ⟨_, hq⟩ := sits_ten P sentU layU layO t₁ t₂ a.1.2 (by omega) hX π t ht a₀ rest G0
    Ly D hf
  obtain ⟨k1, k2, k3, k4⟩ := hK a τ b t ha hout ht a₀ rest G0 Ly D hf j
  obtain ⟨⟨ρU, yU, sdU⟩, ρS, yS, sdS⟩ := hseed a ha
  have hst : t.st = a.1.2.st := by cases ht; rfl
  constructor
  · intro e
    rcases hq j with ⟨_, hid, _⟩ | ⟨e', _, _⟩
    · have hid0 : (D.mems.get j).id = sentU.size := hid
      have sd : K1.SeedIs cs S.omega t.st (D.mems.get j).id ρU yU := by rw [hst, hid0]; exact sdU
      have hsh : (D.mems.get j).sh = S.omega := (member_of_seedIs hf default j sd).1
      refine memberFacts_of cs G Fr _ _ _ mem a.2 _ _ π t a₀ rest G0 Ly D hf j _ S.omega rO e3.2.1 hTU ρU
        yU sd ?_ k1 k2 k3 (by rw [hid0]; exact hmU) ?_
      · rw [hst, hid0]; rfl
      · have w := (word_ten cs G N Pm₀ Oc _ P sentU layU layO f l S rU rO rSp t₁ t₂ ch tests last hG
          hlo hU hlU hlO hS hm hsU hsO hN hd a ha x hB hFO π t ht a₀ rest G0 Ly D hf j
          (fun _ => by rw [hsh]; exact e3.2.1) (fun h => by omega)).1 e
        rw [hsh] at w
        exact w
    · omega
  · intro e
    rcases hq j with ⟨e', _, _⟩ | ⟨_, hid, _⟩
    · omega
    · have hid1 : (D.mems.get j).id = sentU.size + 1 := hid
      have sd : K1.SeedIs cs S.sharedSplit t.st (D.mems.get j).id ρS yS := by
        rw [hst, hid1]; exact sdS
      have hsh : (D.mems.get j).sh = S.sharedSplit := (member_of_seedIs hf default j sd).1
      refine memberFacts_of cs G Fr _ _ _ mem a.2 _ _ π t a₀ rest G0 Ly D hf j _ S.sharedSplit rSp e3.2.2
        hTS ρS yS sd ?_ k1 k2 k4 (by rw [hid1]; exact hmS) ?_
      · rw [hst, hid1]; rfl
      · have w := (word_ten cs G N Pm₀ Oc _ P sentU layU layO f l S rU rO rSp t₁ t₂ ch tests last hG
          hlo hU hlU hlO hS hm hsU hsO hN hd a ha x hB hFO π t ht a₀ rest G0 Ly D hf j
          (fun h => by omega) (fun _ => by rw [hsh]; exact e3.2.2)).2 e
        rw [hsh] at w
        exact w

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.tupleNine_sh
#print axioms Desc.K14.Law.Fence.tupleTen_sh
