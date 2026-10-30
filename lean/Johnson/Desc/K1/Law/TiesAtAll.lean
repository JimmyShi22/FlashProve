-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TiesAtAll.lean: PREMISES OF THE LAW ON THE SUB-PROTOCOL K1 AT ITS TWO OTHER
PLACES (the first segment's opening, number 2; W's commitment, number 356): the names W_… and G_… of
k01_kind_atThree (Johnson/Desc/AtSeats/K01KindAtThree.lean [not in this library]), AT THE
CLOSED CONSTANT
(`hA.𝔇`, Johnson/P5J/MgAtAll.lean), each in the premise's own type at Dm := hA.𝔇 · Z := Zp ·
c := cF · seats := `P5J.At.seats Zp` · the data := `D.at frS.P.T.a` · W_msg := `wMsgFull`. In the
manner of TestsAtAll.lean (this folder). Statements with their proofs; nothing is evaluated here:
the closed facts are TiesWritten.lean's (this folder) and those of Johnson/HB/LLHARD/*.lean.

THE PREMISES: hA, O, hP1, hP2: as in TestsAtAll.lean.

  `treesAre_of_cut`, `nums_of`, `baseK_atThree`   three small joints, at letters
  `eG_atAll`, `eW_atAll`   under hP1 the two places' parameters ARE the written ones, whole
  `nums_atAll`   the numbers' two counts at the borders 2, 3, 356, 357
  `baseK_atAll`   the trees that the data tell in front of sub-protocol number k < 357 are the
                  numbers' count there
  `index_atAll`, `indexNo_atAll`, `ms_seats_atAll`   the index masks' seat and number; every member
                  of the constant's list of sampled oracle messages sits at a written seat with an
                  out-of-domain (OOD) sample
  W's: `W_hm` `W_hcs` `W_h1` `W_hNt` `W_hNm` `W_hFlC` `W_h4` `W_hsmp` `W_sits` (W_hPl's end)
    `W_hbase` `W_hbaseT` `W_hsam` `W_hpl`, each with the ending _atAll
  G's: `G_hU` `G_hX` (there is such a G_X) `G_h1` `G_hNt` `G_hNm` `G_hFlC` `G_hSeats` `G_hft1`
    `G_hb0` `G_hownB` `G_hbaseT` `G_hsam` `G_hpl`, each with the ending _atAll
W_hft and G_hft are rfl at dk := ⟨0, LFull, MFull⟩ (`dk_atAll`, TestsAtAll.lean).

What is not claimed. That hP1 or hP2 accept at any files. No member of the head hA. The other names
of the two places (the radii's tests, PlanAt, the laws on a step, the facts along reached states).
W_hFlC, G_hFlC, W_hcs: true by the make of the constant: proved (general), no example. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.TiesWritten
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.K1.Law.HWOf
import Johnson.Desc.K13.Law.PlanTestsM4
import Johnson.Desc.K13.Law.SmpNamedReads
import Johnson.Desc.First.SentTerms
import Johnson.Desc.AtSeats.FillsAtBase
import Johnson.IMR.FirstUnder
import Johnson.P5T.MembersByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull toldBy smpNamed nTrees six_together base_at_flat
  SitsAt mgAll mgBase)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf blockPlaces)
open VerifiableInference.Desc.K13.Law (openAt countsFull CountsAre TreesAre seatsFull LFull MFull
  gpFull wMsgFull PlanM4 PlanGSeats SmpOld FillsK13C planSitsB planSeatB)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Desc.First.Walk (LayPar)
open P5T (N0Full psFull)
open ProofFile (Cl)
open IM (Open)

/-! ## 1 Three joints, at letters -/

/-- The written cut has, tree by tree, the written numbers of tenants. -/
theorem treesAre_of_cut {T C : Type} {bs : List (Block T C)}
    (h : PlanWritten.cutOf bs = PlanWritten.cutFirstFull) : TreesAre (First.toldOf bs) := by
  rw [First.toldOf_cut, h]
  exact K13.Law.treesAre_cut

/-- The numbers' two counts at a border, off the written list's entry. -/
theorem nums_of {T C : Type} {N N₀ : Numbers} {s : ReqShape} {links : List ModelPart}
    {bs : List (Block T C)} (hN : N = N₀.atBlocks s links bs)
    (hps : blockPlaces bs = flatPlacesOf linksFull true) (hC : CountsAre (First.toldOf bs))
    {k m t : ℕ} (hk : k ≤ 358) (h : countsFull[k]? = some (m, t)) :
    N.msgsAt psF[k]? = m ∧ N.treesAt psF[k]? = t := by
  have e := counts_at_blocks hN hps hC hk
  rw [h] at e
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj e)
  exact ⟨e1.symm, e2.symm⟩

/-- The trees that the IOP's own data tell in front of sub-protocol number k are the numbers' count
of trees there. -/
theorem baseK_atThree {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {D : WholeD} {file : String}
    (hD : (FD Z A B c).data file = .ok D) (hp : (FD Z A B c).planOk = true)
    {b₁ : Block (FD Z A B c).S₁ (FD Z A B c).Cl} {l₁ : List (Block (FD Z A B c).S₁ (FD Z A B c).Cl)}
    {b₂ : Block (FD Z A B c).S₂ (FD Z A B c).Cl} {l₂ : List (Block (FD Z A B c).S₂ (FD Z A B c).Cl)}
    {b₃ : Block (FD Z A B c).S₃ (FD Z A B c).Cl} {l₃ : List (Block (FD Z A B c).S₃ (FD Z A B c).Cl)}
    (q₁ : (FD Z A B c).first.blocksInOrder = b₁ :: l₁) (q₂ : (FD Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FD Z A B c).second.blocksInOrder = b₃ :: l₃)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true) (N : Numbers)
    (hBook : First.bookFit N (flatPlacesOf linksFull true) (toldBy c.blocksInOrder) = true) (k : ℕ)
    (hk : k < 357) : nTrees (D.ds₁.take (inFront c k)) = N.treesAt psF[k]? := by
  obtain ⟨R₁, R₂, R₃, hDD, w₁, hRoots, -, -⟩ := six_together (W := Unit) hD hp q₁ q₂ q₃
  subst hDD
  obtain ⟨e7, hflat7, _, hu7⟩ := K13.Law.k13_sits_flat357 hS hR O
  have hlen : k < c.blocksInOrder.length := Nat.lt_trans hk (List.getElem?_eq_some_iff.1 hflat7).1
  have hroom := K13.Law.room_of_later c.blocksInOrder k 357 c.blocksInOrder[k] e7 (List.getElem?_eq_getElem hlen)
    hflat7 hk (by rw [hu7.1]; exact Nat.zero_lt_one)
  exact base_at_flat _ R₁ R₂ R₃ c w₁ hRoots (fun b hb => (hOk b hb).2) N _ hBook k
    (by rw [K13.Law.places_fit.1]; omega) (by omega)

/-- From the test `samB` to the premise's own text. -/
theorem sam_of {ms : List Sound.Mem} {ss : List (ℕ × ℕ)} (hms : ∀ m' ∈ ms, Sound.seatOf m' ∈ ss)
    {P : Par} {nT : ℕ} (h : samB P nT ss = true) :
    ∀ j : Fin (shapesOf P).length, ∀ m' ∈ ms,
      SitsAt m' (seatOfMsg P nT j.val).1 (seatOfMsg P nT j.val).2 → sampledAt P j := by
  intro j m' hm hs
  have e : Sound.seatOf m' = seatOfMsg P nT j.val := hs
  have hc : ss.contains (seatOfMsg P nT j.val) = true := by
    rw [← e]
    exact List.contains_iff_mem.2 (hms m' hm)
  have h1 := List.all_eq_true.1 h j (List.mem_finRange j)
  rw [hc] at h1
  exact of_decide_eq_true h1

/-! ## 2 At the constant -/

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}

/-- By the make of the constant. The matrix is the constant's own. -/
theorem W_hFlC_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    FillsK13C (whereOf Zp) hA.𝔇.N (mgAll hA.𝔇 mgBase) hA.𝔇.pubD.cs hA.𝔇.arr hA.𝔇.mat13 hA.𝔇.G
      hA.𝔇.smp hA.𝔇.ms hA.𝔇.decT :=
  K13.Law.fillsK13C_base hA.𝔇

/-- The same sentence: the opening's name for it. -/
theorem G_hFlC_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    FillsK13C (whereOf Zp) hA.𝔇.N (mgAll hA.𝔇 mgBase) hA.𝔇.pubD.cs hA.𝔇.arr hA.𝔇.mat13 hA.𝔇.G
      hA.𝔇.smp hA.𝔇.ms hA.𝔇.decT :=
  K13.Law.fillsK13C_base hA.𝔇

theorem W_hcs_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (msg : Array OracleNotice) : (parWZ Zp msg).codes = hA.𝔇.pubD.cs := rfl

variable (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
include hA O

theorem G_hU_atAll : ∃ (e : Block S Cl) (nm : String) (G_X : LayPar), cF.blocksInOrder[2]? = some e ∧
    Johnson.Desc.First.Walk.Seat.zeroAt Zp.p.built.links Zp.p.X = some G_X ∧
    e.UnderR (openingZero Bs.G₀.first (gpOf Zp) nm G_X
      (Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links) Zp.first.lin.kCol : Block S Cl) :=
  IM.first_under hA.scope hA.reads O

theorem G_hX_atAll :
    ∃ G_X : LayPar, Johnson.Desc.First.Walk.Seat.zeroAt Zp.p.built.links Zp.p.X = some G_X := by
  obtain ⟨_, _, X, _, hX, _⟩ := G_hU_atAll hA O
  exact ⟨X, hX⟩

/-- The trees that the data tell in front of sub-protocol number k. -/
theorem baseK_atAll (k : ℕ) (hk : k < 357) :
    nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF k)) = hA.𝔇.N.treesAt psF[k]? := by
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth hA.scope hA.laid]
    exact hA.laid.data
  obtain ⟨⟨b₁, l₁, q₁⟩, ⟨b₂, l₂, q₂⟩, ⟨b₃, l₃, q₃⟩⟩ := P5J.LaidAt.heads OnBytes.secondHashFunction Zp Np cF
  exact baseK_atThree hA.scope hA.reads O hD hA.laid.planOk q₁ q₂ q₃ (hOk_atAll hA O) hA.𝔇.N
    (hBook_atAll hA O) k hk

theorem W_hbaseT_atAll :
    hA.𝔇.N.treesAt psF[356]? = nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)) :=
  (baseK_atAll hA O 356 (by decide)).symm

theorem G_hbaseT_atAll :
    hA.𝔇.N.treesAt psF[2]? = nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2)) :=
  (baseK_atAll hA O 2 (by decide)).symm

variable (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hP1

/-- The opening's parameters are the written ones. -/
theorem eG_atAll : firstPar Bs.G₀.first (gpOf Zp) = parGF := by
  have hF : LikeFull Bs.G₀.first := by
    rw [O.first]
    exact K13.Law.likeFull_in_scope hA.scope hA.laid.pub hP1
  have e : firstPar Bs.G₀.first (gpOf Zp) = firstPar qFull gpFull := by
    rw [K13.Law.gpOf_in_scope hA.scope hA.laid.pub hP1, firstPar_full hF]
  exact e

/-- The parameters of W's commitment are the written ones. -/
theorem eW_atAll : parWZ Zp wMsgFull = parWF := by
  have e : parW Zp.first ⟨Zp.P.samples, Zp.P.firstTree⟩ 4 wMsgFull =
      parW qFull gpFull 4 wMsgFull := by
    rw [K13.Law.gp_in_scope hA.scope hA.laid.pub hP1,
      parW_full (K13.Law.likeFull_in_scope hA.scope hA.laid.pub hP1)]
  exact e

theorem index_atAll : hA.𝔇.N.index = (1, 0) :=
  (congrArg (·.index) (atAll_letters hA O hP1).1).trans (congrArg Prod.fst P5T.N0Full_seats)

/-- Every member of the constant's list sits at a written seat with an OOD sample. -/
theorem ms_seats_atAll : ∀ m' ∈ hA.𝔇.ms, Sound.seatOf m' ∈ smpdFull := by
  intro m' hm
  have hm' : m' ∈ P5T.msAtR Zp (P5J.At.rad Zp Zl.lay) := hm
  have h1 : ((m'.1.l.get m'.2).1, Sound.seatOf m') ∈
      (P5T.msAtR Zp (P5J.At.rad Zp Zl.lay)).map fun x => ((x.1.l.get x.2).1, Sound.seatOf x) :=
    List.mem_map.2 ⟨m', hm', rfl⟩
  have h2 := (P5T.memsSame_atR Zp _ _).1 h1
  rw [(P5T.seats_in_scope hA.scope hA.laid.pub hP1 (laidP_atAll hA)).1] at h2
  obtain ⟨p, hp, e⟩ := List.mem_map.1 h2
  have e2 : p.seat = Sound.seatOf m' := congrArg Prod.snd e
  rw [← e2]
  exact List.mem_map.2 ⟨p, hp, rfl⟩

theorem W_hm_atAll : linMessageW Zp.first.lin = some wMsgFull :=
  K13.Law.wMsg_in_scope hA.scope hA.laid.pub hP1

theorem W_h1_atAll : (parWZ Zp wMsgFull).seeds = 1 :=
  (congrArg Par.seeds (eW_atAll hA O hP1)).trans sizes_two.2.2.2.2.2

theorem G_h1_atAll : (firstPar Bs.G₀.first (gpOf Zp)).seeds = 1 :=
  (congrArg Par.seeds (eG_atAll hA O hP1)).trans sizes_two.2.2.1

theorem G_hft1_atAll : (firstPar Bs.G₀.first (gpOf Zp)).gp.firstTree = 0 :=
  congrArg (·.gp.firstTree) (eG_atAll hA O hP1)

variable (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
include hP2

/-- The numbers' two counts at the four borders. -/
theorem nums_atAll :
    (hA.𝔇.N.msgsAt psF[2]? = 0 ∧ hA.𝔇.N.treesAt psF[2]? = 0) ∧
      (hA.𝔇.N.msgsAt psF[2 + 1]? = 5 ∧ hA.𝔇.N.treesAt psF[2 + 1]? = 2) ∧
      (hA.𝔇.N.msgsAt psF[356]? = 197 ∧ hA.𝔇.N.treesAt psF[356]? = 82) ∧
      (hA.𝔇.N.msgsAt psF[356 + 1]? = 199 ∧ hA.𝔇.N.treesAt psF[356 + 1]? = 83) := by
  have hN := (atAll_letters hA O hP1).1
  have hps := LPFK9.blockPlaces_full hA.scope hA.reads O
  have hC := atAll_counts hP2
  exact ⟨nums_of hN hps hC (by decide) counts_four.1,
    nums_of hN hps hC (by decide) counts_four.2.1,
    nums_of hN hps hC (by decide) counts_four.2.2.1,
    nums_of hN hps hC (by decide) counts_four.2.2.2⟩

theorem indexNo_atAll : hA.𝔇.N.indexNo = 4 := by
  rw [(atAll_letters hA O hP1).1,
    atBlocks_written N0Full _ _ cF.blocksInOrder (LPFK9.blockPlaces_full hA.scope hA.reads O)]
  exact K13.Law.indexNo_of (N := N0Full.withRows _ _ _) (congrArg Prod.fst P5T.N0Full_seats)
    (treesAre_of_cut (bs := cF.blocksInOrder) (cutIs_eq hP2).1) _

/-! ### W's commitment -/

theorem W_hNt_atAll : hA.𝔇.N.treesAt psF[356 + 1]? =
    hA.𝔇.N.treesAt psF[356]? + (layOf (parWZ Zp wMsgFull)).shapes.size := by
  rw [eW_atAll hA O hP1, (nums_atAll hA O hP1 hP2).2.2.2.2, (nums_atAll hA O hP1 hP2).2.2.1.2,
    sizes_two.2.2.2.1]

theorem W_hNm_atAll : hA.𝔇.N.msgsAt psF[356 + 1]? =
    hA.𝔇.N.msgsAt psF[356]? + (parWZ Zp wMsgFull).sent.size := by
  rw [eW_atAll hA O hP1, (nums_atAll hA O hP1 hP2).2.2.2.1, (nums_atAll hA O hP1 hP2).2.2.1.1,
    sizes_two.2.2.2.2.1]

theorem W_h4_atAll {dk : K12Data} (hL : dk.L = LFull) (hM : dk.M = MFull) :
    PlanM4 0 dk.L dk.M hA.𝔇.N psF[356]? (parWZ Zp wMsgFull) := by
  rw [eW_atAll hA O hP1, hL, hM]
  have h := K13.Law.w_written (N := hA.𝔇.N) (p := psF[356]?)
    (nums_atAll hA O hP1 hP2).2.2.1.1 (nums_atAll hA O hP1 hP2).2.2.1.2
  have h1 := K13.Law.planPlaces_gives h.1
  have h2 := K13.Law.planTrees_gives h.2.1
  have h3 := K13.Law.planShapes_gives h.2.2
  exact ⟨rfl, h1, h2, h3⟩

theorem W_hsmp_atAll : SmpOld hA.𝔇.N psF[356]? hA.𝔇.ms hA.𝔇.smp := by
  have hn : (P5J.At.seats Zp).idxOf hA.𝔇.N.index < hA.𝔇.N.msgsAt psF[356]? := by
    rw [(atAll_letters hA O hP1).2.1, (atAll_letters hA O hP1).1,
      atBlocks_written N0Full _ _ cF.blocksInOrder (LPFK9.blockPlaces_full hA.scope hA.reads O)]
    exact K13.Law.idxIndex_of_counts (N := N0Full.withRows _ _ _) rfl (atAll_counts hP2)
      (by decide) (by decide)
  exact K13.Law.smpOld_named hA.𝔇.cs (P5J.At.seats Zp) hA.𝔇.N _ hA.𝔇.ms hn

/-- The end of W_hPl. -/
theorem W_sits_atAll : planSitsB (whereOf Zp) (parWZ Zp wMsgFull) = true ∧
    planSeatB hA.𝔇.N psF[356]? (parWZ Zp wMsgFull) = true := by
  rw [eW_atAll hA O hP1]
  have el : (whereOf Zp).lin = qFull.lin :=
    (K13.Law.likeFull_in_scope hA.scope hA.laid.pub hP1).lin
  have hw : hA.𝔇.N.w = N0Full.w := congrArg (·.w) (atAll_letters hA O hP1).1
  constructor
  · unfold planSitsB
    rw [el]
    exact planSits_written
  · unfold planSeatB
    rw [(nums_atAll hA O hP1 hP2).2.2.1.2, hw]
    exact planSeat_written

theorem W_hbase_atAll :
    hA.𝔇.N.index.1 < nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)) := by
  rw [baseK_atAll hA O 356 (by decide), (nums_atAll hA O hP1 hP2).2.2.1.2, index_atAll hA O hP1]
  decide

theorem W_hsam_atAll : ∀ j : Fin (shapesOf (parWZ Zp wMsgFull)).length, ∀ m' ∈ hA.𝔇.ms,
    SitsAt m'
      (seatOfMsg (parWZ Zp wMsgFull)
        (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356))) j.val).1
      (seatOfMsg (parWZ Zp wMsgFull)
        (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356))) j.val).2 →
    sampledAt (parWZ Zp wMsgFull) j := by
  rw [eW_atAll hA O hP1, baseK_atAll hA O 356 (by decide), (nums_atAll hA O hP1 hP2).2.2.1.2]
  exact sam_of (ms_seats_atAll hA O hP1) samW_written

theorem W_hpl_atAll : ∀ j : Fin (shapesOf (parWZ Zp wMsgFull)).length,
    (P5J.At.seats Zp)[hA.𝔇.N.msgsAt psF[356]? + j.val]? = some (seatOfMsg (parWZ Zp wMsgFull)
      (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356))) j.val) := by
  rw [eW_atAll hA O hP1, baseK_atAll hA O 356 (by decide), (nums_atAll hA O hP1 hP2).2.2.1.2,
    (nums_atAll hA O hP1 hP2).2.2.1.1, (atAll_letters hA O hP1).2.1]
  intro j
  exact of_decide_eq_true (List.all_eq_true.1 seatsW_written j.val (List.mem_range.2 j.isLt))

/-! ### The first segment's opening -/

theorem G_hNt_atAll : hA.𝔇.N.treesAt psF[2 + 1]? =
    hA.𝔇.N.treesAt psF[2]? + (layOf (firstPar Bs.G₀.first (gpOf Zp))).shapes.size := by
  rw [eG_atAll hA O hP1, (nums_atAll hA O hP1 hP2).2.1.2, (nums_atAll hA O hP1 hP2).1.2,
    sizes_two.1]

theorem G_hNm_atAll : hA.𝔇.N.msgsAt psF[2 + 1]? =
    hA.𝔇.N.msgsAt psF[2]? + (firstPar Bs.G₀.first (gpOf Zp)).sent.size := by
  rw [eG_atAll hA O hP1, (nums_atAll hA O hP1 hP2).2.1.1, (nums_atAll hA O hP1 hP2).1.1,
    sizes_two.2.1]

theorem G_hSeats_atAll {dk : K12Data} (hL : dk.L = LFull) (hM : dk.M = MFull) :
    PlanGSeats dk.L dk.M hA.𝔇.N psF[2]? (firstPar Bs.G₀.first (gpOf Zp)) := by
  rw [eG_atAll hA O hP1, hL, hM]
  have h := K13.Law.first_written (N := hA.𝔇.N) (p := psF[2]?)
    (nums_atAll hA O hP1 hP2).1.1 (nums_atAll hA O hP1 hP2).1.2
  have h1 := K13.Law.planPlaces_gives h.1
  have h2 := K13.Law.planTrees_gives h.2.1
  have h3 := K13.Law.planShapes_gives h.2.2
  have h4 := K13.Law.planIndexLast_gives
    (K13.Law.indexLast_written (N := hA.𝔇.N) (indexNo_atAll hA O hP1 hP2))
  exact ⟨h1, h2, h3, h4⟩

theorem G_hb0_atAll : First.FillSent.baseAt hA.𝔇.N Sound.linksFull psF 0 = 0 :=
  (congrArg hA.𝔇.N.msgsAt find0_written).trans (nums_atAll hA O hP1 hP2).1.1

theorem G_hownB_atAll : ownSeatsB hA.𝔇.N (openAt Sound.linksFull psF (2 + 1))
    (firstPar Bs.G₀.first (gpOf Zp))
    (((hA.𝔇.shape.link[0]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length
    (hA.𝔇.N.treesAt psF[2]?) = true := by
  rw [eG_atAll hA O hP1, hDsh_atAll hA O hP1, (nums_atAll hA O hP1 hP2).1.2]
  have e : hA.𝔇.N.sent = N0Full.sent := congrArg (·.sent) (atAll_letters hA O hP1).1
  have h := ownSeats_written
  unfold ownSeatsB at h ⊢
  rw [e]
  exact h

theorem G_hsam_atAll : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Zp))).length,
    ∀ m' ∈ hA.𝔇.ms,
    SitsAt m'
      (seatOfMsg (firstPar Bs.G₀.first (gpOf Zp))
        (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2))) j.val).1
      (seatOfMsg (firstPar Bs.G₀.first (gpOf Zp))
        (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2))) j.val).2 →
    sampledAt (firstPar Bs.G₀.first (gpOf Zp)) j := by
  rw [eG_atAll hA O hP1, baseK_atAll hA O 2 (by decide), (nums_atAll hA O hP1 hP2).1.2]
  exact sam_of (ms_seats_atAll hA O hP1) samG_written

theorem G_hpl_atAll : ∀ j : Fin (shapesOf (firstPar Bs.G₀.first (gpOf Zp))).length,
    (P5J.At.seats Zp)[hA.𝔇.N.msgsAt psF[2]? + j.val]? =
      some (seatOfMsg (firstPar Bs.G₀.first (gpOf Zp))
        (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2))) j.val) := by
  rw [eG_atAll hA O hP1, baseK_atAll hA O 2 (by decide), (nums_atAll hA O hP1 hP2).1.2,
    (nums_atAll hA O hP1 hP2).1.1, (atAll_letters hA O hP1).2.1]
  intro j
  exact of_decide_eq_true (List.all_eq_true.1 seatsG_written j.val (List.mem_range.2 j.isLt))

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.treesAre_of_cut
#print axioms VerifiableInference.Desc.K1.nums_of
#print axioms VerifiableInference.Desc.K1.baseK_atThree
#print axioms VerifiableInference.Desc.K1.sam_of
#print axioms VerifiableInference.Desc.K1.W_hFlC_atAll
#print axioms VerifiableInference.Desc.K1.G_hFlC_atAll
#print axioms VerifiableInference.Desc.K1.W_hcs_atAll
#print axioms VerifiableInference.Desc.K1.G_hU_atAll
#print axioms VerifiableInference.Desc.K1.G_hX_atAll
#print axioms VerifiableInference.Desc.K1.baseK_atAll
#print axioms VerifiableInference.Desc.K1.W_hbaseT_atAll
#print axioms VerifiableInference.Desc.K1.G_hbaseT_atAll
#print axioms VerifiableInference.Desc.K1.eG_atAll
#print axioms VerifiableInference.Desc.K1.eW_atAll
#print axioms VerifiableInference.Desc.K1.index_atAll
#print axioms VerifiableInference.Desc.K1.ms_seats_atAll
#print axioms VerifiableInference.Desc.K1.W_hm_atAll
#print axioms VerifiableInference.Desc.K1.W_h1_atAll
#print axioms VerifiableInference.Desc.K1.G_h1_atAll
#print axioms VerifiableInference.Desc.K1.G_hft1_atAll
#print axioms VerifiableInference.Desc.K1.nums_atAll
#print axioms VerifiableInference.Desc.K1.indexNo_atAll
#print axioms VerifiableInference.Desc.K1.W_hNt_atAll
#print axioms VerifiableInference.Desc.K1.W_hNm_atAll
#print axioms VerifiableInference.Desc.K1.W_h4_atAll
#print axioms VerifiableInference.Desc.K1.W_hsmp_atAll
#print axioms VerifiableInference.Desc.K1.W_sits_atAll
#print axioms VerifiableInference.Desc.K1.W_hbase_atAll
#print axioms VerifiableInference.Desc.K1.W_hsam_atAll
#print axioms VerifiableInference.Desc.K1.W_hpl_atAll
#print axioms VerifiableInference.Desc.K1.G_hNt_atAll
#print axioms VerifiableInference.Desc.K1.G_hNm_atAll
#print axioms VerifiableInference.Desc.K1.G_hSeats_atAll
#print axioms VerifiableInference.Desc.K1.G_hb0_atAll
#print axioms VerifiableInference.Desc.K1.G_hownB_atAll
#print axioms VerifiableInference.Desc.K1.G_hsam_atAll
#print axioms VerifiableInference.Desc.K1.G_hpl_atAll
