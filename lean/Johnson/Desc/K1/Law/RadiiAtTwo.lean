-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RadiiAtTwo.lean: THE RADII AT THE TWO OTHER PLACES OF THE SUB-PROTOCOL K1 (the
first segment's opening, number 2; W's commitment, number 356), AND WHAT OF THE PREMISES W_HP AND
G_HP OF k01_kind_atThree (Johnson/Desc/AtSeats/K01KindAtThree.lean [not in this library]) FALLS
WITH THEM, AT THE CLOSED CONSTANT (`hA.𝔇`, Johnson/P5J/MgAtAll.lean).
Beside RadiiAtAll.lean (this folder), at the same letters and premises.
Definitions (one test) and statements with their proofs.

  `radTwo_written`, `radTwo_rejects`   BY LEAN's KERNEL: the test `radAtB`
      (Johnson/Desc/AtSeats/RadAtTest.lean) accepts at the two written places, at the written
      list's radii and the radii `radRec 0`, `radRec 81`; it rejects with every radius turned by
      one, and at W with the sending number 80's in the place of 81's. SO W_rad := `radRec 81 …` IS
      NO CHOICE ANY MORE: it is the one that fits the written radii
  `seatsInB`, `seatsIn_of`, `seatsIn_written`, `seatsIn_rejects`   BY LEAN's KERNEL: each tenant
      that the table's numbers give the place is the seat of a message of the place with an
      out-of-domain (OOD) sample; the masks' messages' seats are not
  `radAt_two_of_rows`   `RadAt` at the two places from the one equation on the rows
  `planAt_atD`   `planAt_of_parts` (PlanParts.lean, this folder) at the IOP's own data D
  `W_rest_atAll`, `G_rest_atAll`   `PlanRest` (six of PlanAt's ten fields) at the two places, at the
      constant's own letters
  `W_HP_atAll`, `G_HP_atAll`   **W_HP, G_HP, each in its own type, FROM TWO LEFTOVERS EACH**: the
      fields listed and told of PlanAt at the place's two rounds

What is not claimed. The two leftovers. That the rows' maker returns at any files (RadiiAtAll.lean's
head). That hP1 or hP2 accept. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RadiiAtAll
import Johnson.Desc.K1.Law.TiesAtAll2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull msOf nTrees six_together Frame Mem SeatFits ListedAt)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt wMsgFull)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5T (N0Full psFull)
open ProofFile (Cl)
open IM (Open)

/-! ## 1 Closed facts -/

set_option maxRecDepth 1000000 in
theorem radTwo_written :
    radAtB proofSendsFull.1.sends.length radW psFull parGF (radRec 0 parGF) 0 = true ∧
      radAtB proofSendsFull.1.sends.length radW psFull parWF (radRec 81 parWF) 82 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: every radius turned by one; at W the radii of sending number 80. -/
theorem radTwo_rejects :
    radAtB proofSendsFull.1.sends.length (fun k i => radW k i + 1) psFull parGF (radRec 0 parGF)
        0 = false ∧
      radAtB proofSendsFull.1.sends.length (fun k i => radW k i + 1) psFull parWF
        (radRec 81 parWF) 82 = false ∧
      radAtB proofSendsFull.1.sends.length radW psFull parWF (radRec 80 parWF) 82 = false := by
  decide +kernel

/-- A test: each of the tenants us is the seat, behind nT trees, of a message of the place that has
an OOD sample. -/
def seatsInB (P : Par) (nT : ℕ) (us : List (ℕ × ℕ)) : Bool :=
  us.all fun u => (List.finRange (shapesOf P).length).any fun j =>
    decide (sampledAt P j) && u == seatOfMsg P nT j.val

theorem seatsIn_of {P : Par} {nT : ℕ} {us : List (ℕ × ℕ)} (h : seatsInB P nT us = true) :
    ∀ u ∈ us, ∃ j : Fin (shapesOf P).length, sampledAt P j ∧ u = seatOfMsg P nT j.val := by
  intro u hu
  obtain ⟨j, _, hj⟩ := List.any_eq_true.1 (List.all_eq_true.1 h u hu)
  rw [Bool.and_eq_true] at hj
  exact ⟨j, of_decide_eq_true hj.1, eq_of_beq hj.2⟩

set_option maxRecDepth 1000000 in
theorem seatsIn_written : seatsInB parWF 82 [N0Full.w] = true ∧
    seatsInB parGF 0
      (First.sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) (2 + 1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: the masks' messages' seats. -/
theorem seatsIn_rejects : seatsInB parWF 82 [(82, 1)] = false ∧
    seatsInB parGF 0 [(0, 3)] = false := by
  decide +kernel

/-- **RadAt at the two places, from the one equation on the rows.** -/
theorem radAt_two_of_rows {R : List Johnson.G.SendRow}
    (hR : (P5T.firstRows R).map (·.sampled) = radsFull) :
    RadAt proofSendsFull.1.sends.length (P5T.radOf R) psFull parGF (radRec 0 parGF) 0 ∧
      RadAt proofSendsFull.1.sends.length (P5T.radOf R) psFull parWF (radRec 81 parWF) 82 := by
  constructor
  · intro j hj k hk i p hp hs
    rw [radOf_is hR, ← radW_is]
    exact radAt_of radTwo_written.1 j hj k hk i p hp hs
  · intro j hj k hk i p hp hs
    rw [radOf_is hR, ← radW_is]
    exact radAt_of radTwo_written.2 j hj k hk i p hp hs

theorem own_two : planOkOwn parGF = true ∧ planOkOwn parWF = true := by
  have h1 := radii_written.1
  have h2 := radii_written.2.2.1
  unfold condPort at h1 h2
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1 h2
  exact ⟨h1.1.1, h2.1.1⟩

/-! ## 2 PlanAt from PlanRest, at the IOP's own data -/

theorem planAt_atD {Xi Xj : Type} {F₀ : FileDescription Xj} {D : WholeD} {file : String}
    (hD : F₀.data file = .ok D) (hp : F₀.planOk = true)
    {b₁ : Block F₀.S₁ F₀.Cl} {l₁ : List (Block F₀.S₁ F₀.Cl)}
    {b₂ : Block F₀.S₂ F₀.Cl} {l₂ : List (Block F₀.S₂ F₀.Cl)}
    {b₃ : Block F₀.S₃ F₀.Cl} {l₃ : List (Block F₀.S₃ F₀.Cl)}
    (q₁ : F₀.first.blocksInOrder = b₁ :: l₁) (q₂ : F₀.shared.blocksInOrder = b₂ :: l₂)
    (q₃ : F₀.second.blocksInOrder = b₃ :: l₃)
    {F : Frame} {cs : Codes} {G : FileDescription Xi} {ms : List Mem} {P : Par} {rad : ℕ → ℕ} {base : ℕ}
    {seats : List (ℕ × ℕ)} (h : PlanRest cs G ms P rad base seats) (hB : planOkOwn P = true)
    (n : ℕ) (d₁ d₂ : RDT) (hd : (D.ds₁.drop n).take 2 = [d₁, d₂]) (he : d₁.entry = seedEntry P)
    (hlist : ListedAt F base [d₁, d₂])
    (htold : ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o, G.oracleAt (base + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W) : PlanAt F cs G ms P rad base d₁ d₂ seats := by
  obtain ⟨R₁, R₂, R₃, hDD, -, hRoots, -, -⟩ := six_together (W := Unit) hD hp q₁ q₂ q₃
  subst hDD
  exact planAt_of_parts h hB _ R₁ R₂ R₃ hRoots n d₁ d₂ hd he hlist htold

/-! ## 3 At the constant -/

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
  (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
  (hRad : ∀ R, sendRowsOf Zl.pol Zl.lay Zl.KL = .ok R →
    (P5T.firstRows R).map (·.sampled) = radsFull)
include hA O hP1 hP2 hRad

/-- What the two places share: the members, the codes, the fit, at the written values. -/
theorem shared_atAll : ∃ R, (P5T.firstRows R).map (·.sampled) = radsFull ∧
    hA.𝔇.ms = msOf (P5T.memberListsR proofSendsFull.1.sends.length (P5T.radOf R) psFull) ∧
    hA.𝔇.pubD.cs = codesFull2 ∧
    ∀ x ∈ msOf (P5T.memberListsR proofSendsFull.1.sends.length (P5T.radOf R) psFull),
      SeatFits hA.𝔇.G codesFull2 x.1.l x.1.seat := by
  obtain ⟨R, hR, eR⟩ := rows_atAll hA O hP1
  have eS := PlanWritten.Joined.sends_in_scope hA.scope hA.laid.pub hP1
  have eP := (P5T.seats_in_scope hA.scope hA.laid.pub hP1 (laidP_atAll hA)).1
  have hn : ∀ p ∈ psFull, p.smpd = true → p.send < proofSendsFull.1.sends.length := by
    intro p hp _
    have h := P5T.planSeats_send_lt Zp Zp.D.1 p (by rw [eP]; exact hp)
    rw [eS] at h
    exact h
  refine ⟨R, hRad R hR, ?_, (K13.Law.likeFull_in_scope hA.scope hA.laid.pub hP1).codes,
    fits_of_cut hA.𝔇.G (P5T.radOf R) hn (cutIs_eq hP2).1⟩
  show P5T.msAtR Zp (P5J.At.rad Zp Zl.lay) = _
  unfold P5T.msAtR
  rw [eS, eP, eR]

/-- **PlanRest at W's commitment.** -/
theorem W_rest_atAll : PlanRest hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (parWZ Zp wMsgFull)
    (radRec 81 (parWZ Zp wMsgFull)) (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)))
    [hA.𝔇.N.w] := by
  obtain ⟨R, hR, eM, eC, hf⟩ := shared_atAll hA O hP1 hP2 hRad
  have hw : hA.𝔇.N.w = N0Full.w := congrArg (·.w) (atAll_letters hA O hP1).1
  have hm : memsPairsB pairsFull parWF 82 = true := by
    have h := mems_w
    rw [K13.Law.wMsg_written] at h
    exact h
  have ho : planOwnB parWF = true := by
    have h := own_w
    rw [K13.Law.wMsg_written] at h
    exact h
  rw [eM, eC, eW_atAll hA O hP1, baseK_atAll hA O 356 (by decide),
    (nums_atAll hA O hP1 hP2).2.2.1.2, hw]
  exact ⟨memsAt_byMake rfl hm (radAt_two_of_rows hR).2, seatsIn_of seatsIn_written.1,
    (planOwn_of ho).one, (planOwn_of ho).pad, (planOwn_of ho).row, hf⟩

/-- **PlanRest at the first segment's opening.** -/
theorem G_rest_atAll : PlanRest hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (firstPar Bs.G₀.first (gpOf Zp))
    (radRec 0 (firstPar Bs.G₀.first (gpOf Zp)))
    (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2)))
    (First.sampledIn hA.𝔇.N (openAt Sound.linksFull psF (2 + 1))) := by
  obtain ⟨R, hR, eM, eC, hf⟩ := shared_atAll hA O hP1 hP2 hRad
  have hN := (atAll_letters hA O hP1).1
  have es : First.sampledIn hA.𝔇.N (openAt Sound.linksFull psF (2 + 1)) =
      First.sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) (2 + 1)) :=
    K13.Law.sampledIn_core (congrArg (·.sent) hN) (congrArg (·.keptOf) hN)
      (congrArg (·.index) hN) (congrArg (·.w) hN) _
  rw [eM, eC, eG_atAll hA O hP1, baseK_atAll hA O 2 (by decide),
    (nums_atAll hA O hP1 hP2).1.2, es]
  exact ⟨memsAt_byMake rfl mems_first (radAt_two_of_rows hR).1, seatsIn_of seatsIn_written.2,
    (planOwn_of own_first).one, (planOwn_of own_first).pad, (planOwn_of own_first).row, hf⟩

/-- **W_HP, from the fields listed and told at the place's two rounds.** -/
theorem W_HP_atAll
    (hlist : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Zp wMsgFull) → d₁.kind = .seeds →
      ((D.at frS.P.T.a).ds₁.drop (inFront cF 356)).take 2 = [d₁, d₂] →
      ListedAt (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0) (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356))) [d₁, d₂])
    (htold : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Zp wMsgFull) → d₁.kind = .seeds →
      ((D.at frS.P.T.a).ds₁.drop (inFront cF 356)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      hA.𝔇.G.oracleAt (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parWZ Zp wMsgFull) → d₁.kind = .seeds →
      ((D.at frS.P.T.a).ds₁.drop (inFront cF 356)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0) hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (parWZ Zp wMsgFull)
        (radRec 81 (parWZ Zp wMsgFull)) (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 356)))
        d₁ d₂ [hA.𝔇.N.w] := by
  intro d₁ d₂ he hk hd
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth hA.scope hA.laid]
    exact hA.laid.data
  obtain ⟨⟨b₁, l₁, q₁⟩, ⟨b₂, l₂, q₂⟩, ⟨b₃, l₃, q₃⟩⟩ := P5J.LaidAt.heads OnBytes.secondHashFunction Zp Np cF
  have hB : planOkOwn (parWZ Zp wMsgFull) = true := by
    rw [eW_atAll hA O hP1]
    exact own_two.2
  exact planAt_atD hD hA.laid.planOk q₁ q₂ q₃ (W_rest_atAll hA O hP1 hP2 hRad) hB _ d₁ d₂ hd he
    (hlist d₁ d₂ he hk hd) (htold d₁ d₂ he hk hd)

/-- **G_HP, from the fields listed and told at the place's two rounds.** -/
theorem G_HP_atAll
    (hlist : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Zp)) →
      d₁.kind = .seeds → ((D.at frS.P.T.a).ds₁.drop (inFront cF 2)).take 2 = [d₁, d₂] →
      ListedAt (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0) (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2))) [d₁, d₂])
    (htold : ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Zp)) →
      d₁.kind = .seeds → ((D.at frS.P.T.a).ds₁.drop (inFront cF 2)).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      hA.𝔇.G.oracleAt (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2)) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W) :
    ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (firstPar Bs.G₀.first (gpOf Zp)) → d₁.kind = .seeds →
      ((D.at frS.P.T.a).ds₁.drop (inFront cF 2)).take 2 = [d₁, d₂] →
      PlanAt (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0) hA.𝔇.pubD.cs hA.𝔇.G hA.𝔇.ms (firstPar Bs.G₀.first (gpOf Zp))
        (radRec 0 (firstPar Bs.G₀.first (gpOf Zp)))
        (nTrees ((D.at frS.P.T.a).ds₁.take (inFront cF 2))) d₁ d₂
        (First.sampledIn hA.𝔇.N (openAt Sound.linksFull psF (2 + 1))) := by
  intro d₁ d₂ he hk hd
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth hA.scope hA.laid]
    exact hA.laid.data
  obtain ⟨⟨b₁, l₁, q₁⟩, ⟨b₂, l₂, q₂⟩, ⟨b₃, l₃, q₃⟩⟩ := P5J.LaidAt.heads OnBytes.secondHashFunction Zp Np cF
  have hB : planOkOwn (firstPar Bs.G₀.first (gpOf Zp)) = true := by
    rw [eG_atAll hA O hP1]
    exact own_two.1
  exact planAt_atD hD hA.laid.planOk q₁ q₂ q₃ (G_rest_atAll hA O hP1 hP2 hRad) hB _ d₁ d₂ hd he
    (hlist d₁ d₂ he hk hd) (htold d₁ d₂ he hk hd)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.radTwo_written
#print axioms VerifiableInference.Desc.K1.radTwo_rejects
#print axioms VerifiableInference.Desc.K1.seatsIn_of
#print axioms VerifiableInference.Desc.K1.seatsIn_written
#print axioms VerifiableInference.Desc.K1.seatsIn_rejects
#print axioms VerifiableInference.Desc.K1.radAt_two_of_rows
#print axioms VerifiableInference.Desc.K1.own_two
#print axioms VerifiableInference.Desc.K1.planAt_atD
#print axioms VerifiableInference.Desc.K1.shared_atAll
#print axioms VerifiableInference.Desc.K1.W_rest_atAll
#print axioms VerifiableInference.Desc.K1.G_rest_atAll
#print axioms VerifiableInference.Desc.K1.W_HP_atAll
#print axioms VerifiableInference.Desc.K1.G_HP_atAll
