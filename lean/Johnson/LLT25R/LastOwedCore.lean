-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastOwedCore.lean: CUT OUT OF LastOwed.lean,
TEXTS UNTURNED [by program], SO THAT THE LAW WITH ROW 0's DEBT AS ONE PREMISE DRAWS NO FILE OF ROW
0's OWN LAWS: ALL THAT ROWS 1, 2 AND 3 OF THE LAST CHAIN's FIELD SPEND, IN THE COUNTED FORM: NAMED
LISTS, NO LAW ON A BLOCK AMONG THEM. What each list holds, what is spent and all limits:
LastOwed.lean's head.
  `PlanOk₃` (33 tests on the plan) · `FoldFirst₃` (4) · `FoldRest₃` (1) · `Readers₃` (2) ·
    `LastCore₃` (these, with ocIs, ocBelow, reached: 43).
  `LastCore₃.rest`: the ledger's `LastRest` at the closed letters. `earn₀_tree`: row 0's accepting
    run earns the layer on the last chain's own state at border 1. `LastCore₃.leftB`,
    `own3_of_core`, `e3_of_core`: the field FROM THE CORE AND ROW 0's DEBT AS ONE PREMISE.
    `LastCore₃.atRc`; `FoldFirst₃.ofRcLast`.
Limits: those of LastOwed.lean. NO MEMBER. Nothing on soundness.
-/
import Johnson.LLT25R.LastRowZeroB
import Johnson.LLT25R.LastRowsOpen
import Johnson.LLT25R.OpensPaid
import Johnson.LLT25R.LastMine
import Johnson.LLT25R.LastNum
import Johnson.LLT25R.LastCore
import Johnson.LLT25R.LastOmegaSits
import Johnson.LLT25R.LastMembers
import Johnson.LLT25R.LastFive
import Johnson.LLT25R.LastSample
import Johnson.LLT25R.LastBook
import Johnson.LLT25R.LastTreeO
import Johnson.ToldDescR.RcLast
import Johnson.ToldDescR.HandedAtEnd
import Johnson.Loose.H2K12.LastRestAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl) {Cells Tok
          P₀ : Type} (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT) (dt : List
                 RDT) (get : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf (p14At Z).codes
    s.l).om i).Smp) (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf (p14At
    Z).codes s.l).om i).Smp) (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ ×
    First.S → Option Cells) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (M₁ :
    Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk
    Z (seatK Z N) N c).S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement) (bookOf : St →
    OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (ps :
          List VerifiableInference.Desc.Place) (X : St → Bool) (Oc : (FL o mk Z (seatK Z N) N c).XiPub ×
          (FL o mk Z (seatK Z N) N c).S₁ → Strs → Prop) (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (n₁ ft nΩ : ℕ)
        (V : VerifiableInference.Desc.Last.OwnSeats) (Ld :
    VerifiableInference.Desc.K12.Door.Laid) (Rch : (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁ × (FL o mk Z (seatK Z N) N c).S₂) × (FL o mk Z (seatK Z N) N c).S₃) ×
    (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber).E.Str → Prop)

/-- **THE TESTS ON THE PLAN.** -/
structure PlanOk₃ : Prop extends LastPlan8 o mk Z (seatK Z N) N c D (p14At Z).codes G arr dB dt
    (mineOf ms₁ ms₂ N₁ Ns) N₁ Ns links ps (VerifiableInference.Desc.numAt D.t₁ D.t₂ 2) where
  /-- K12's files' structure at the place: four tests with code, and the chain's errors at
  2⁻¹ ^ 128. PAYER: K12's files. -/
  closed : ∃ ch b₁ b₂ T, ClosedL (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) r ch b₁ b₂ T
  /-- The third piece's stretch of the written rounds is dB :: dt. -/
  stretch : ds₂ D.ds₃ (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁
      × St) (c0 Z)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ ×
      St) (c1 N)) (held (P := (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ ×
      St) (c2 N)) = dB :: dt
  /-- A member of the first table's list sits at W's seat. -/
  someW : ∃ x ∈ ms₁, SitsAt x N₁.w.1 N₁.w.2
  /-- Likewise at the index masks' seat. -/
  someI : ∃ x ∈ ms₁, SitsAt x N₁.index.1 N₁.index.2
  /-- Likewise, of the shared table's list, at Omega's seat. -/
  someO : ∃ x ∈ ms₂, SitsAt x (Ns.tenant .oOmega).1 (Ns.tenant .oOmega).2
  /-- W's seat is not Omega's. -/
  apartWO : N₁.w ≠ Ns.tenant .oOmega
  /-- The index masks' seat is not Omega's. -/
  apartIO : N₁.index ≠ Ns.tenant .oOmega
  /-- The place's first own tree is number 0 of the chain's own. -/
  free0 : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.free = 0
  /-- No two of mine have one seat. -/
  oneSeat : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), ∀ y ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = seatOf y → x = y
  /-- The description's data are made, and are D. -/
  dataIs : ∃ file, (FL o mk Z (seatK Z N) N c).data file = .ok D
  /-- The description's own test on the plan. -/
  planOk : (FL o mk Z (seatK Z N) N c).planOk = true
  /-- The first arm. -/
  ownMask : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.ownMask = false
  /-- Two stages at least. -/
  twoStages : 2 ≤ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages.length
  /-- The places are the plan's. -/
  places : H2U.placesOfMade Z.made = .ok N
  /-- The block's declared rounds open one number only under "taken 1". -/
  oneOmega : ToldDesc.OneOmega (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) nΩ
  /-- One of mine has the seat (D.t₁ + nΩ, 0) and the plan's shape for Omega. -/
  omegaSeat : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + nΩ, 0) ∧ (p14At Z).S.omega =
      (x.1.l.get
      x.2).1
  /-- One of mine has the index masks' seat and shape. -/
  mineI : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = V.index ∧ (x.1.l.get x.2).1 = V.indexShape
  /-- Likewise W's. -/
  mineW : ∃ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = V.w ∧ (x.1.l.get x.2).1 = V.wShape
  /-- The three seats are apart. -/
  seatsApart : V.index ≠ V.w ∧ V.index ≠ (D.t₁ + nΩ, 0) ∧ V.w ≠ (D.t₁ + nΩ, 0)
  /-- Every one of mine has one of the three seats. -/
  allSeats : ∀ z ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf z = V.index ∨ seatOf z = V.w ∨ seatOf z = (D.t₁ +
      nΩ, 0)
  /-- At every one of mine and the test's first stage: `PlanAt`. -/
  planAt : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), ∀ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages =
      st :: rest → PlanAt (p14At Z).codes G (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N
      c).lastChainFirstTreeNumber) r st x
  /-- Whoever of mine sits at Omega's seat has rows of one kind alone (five tests on the shape). -/
  oneTable : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + nΩ, 0) → ToldDesc.OneTable (p14At
      Z).codes (x.1.l.get x.2).1
  /-- The plan's list of the first chain's trees' shapes is what the description tells of these
  trees (a
  test with code: `planShapesB`, Johnson/ToldDescR/BookAtW.lean). -/
  planShapes : ToldDesc.PlanShapes G Ld ft n₁
  /-- TWO COMPARISONS: the two elder seats lie in trees of the first chain. -/
  elderBelow : V.index.1 < D.t₁ ∧ V.w.1 < D.t₁
  /-- The shape that the verifier's own layout makes of the plan's one notice for Omega is what the
  description tells of the tree number D.t₁ + nΩ. -/
  planTreeO : PlanTreeO G (p14At Z).codes (p14At Z).S (D.t₁ + nΩ)

/-- **THE FACTS ON THE VERIFIER's STATE, I: ON WHAT THE FIRST CHAIN HANDS ON**, each at a reached
statement inside the promise at border 2. -/
structure FoldFirst₃ : Prop where
  /-- The handed own group has just two members, at two seats, with two shapes. -/
  two : ∀ a f, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂
      stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc
      2) a → Rch a → (fun q => firstOfS (get q).2) (a.1.1.1, a.1.1.2.1) = some f →
      ToldDesc.HandedTwo V.index V.w V.indexShape V.wShape f
  /-- The two earlier books' trees' numbers. -/
  roots : ∀ a f e, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂
      stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc
      2) a → Rch a → (fun q => firstOfS (get q).2) (a.1.1.1, a.1.1.2.1) = some f → (endedX X)
      a.1.1.2.2 = some e → ToldDesc.HandedRoots n₁ ft nΩ f e
  /-- The handed book's trees have the plan's list's shapes. -/
  carried : ∀ a f, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂
      stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc
      2) a → Rch a → (fun q => firstOfS (get q).2) (a.1.1.1, a.1.1.2.1) = some f →
      VerifiableInference.Desc.K12.Door.seatsCarriedB Ld f.book = true
  /-- The OOD sample at an elder member, AT THE FIRST CHAIN's LAST STATE: the message at a number
  that
  sits, by that state's book, at one of the two elder seats has the shape of whoever of mine sits
  there and passes `sampleL`. -/
  sampleE : ∀ a f, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂
      stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc
      2) a → Rch a → (fun q => firstOfS (get q).2) (a.1.1.1, a.1.1.2.1) = some f → ∀ i, ∀ x ∈
      (mineOf ms₁ ms₂ N₁ Ns), seatBy noFirst f.book i = some (seatOf x) → (seatOf x = V.index ∨
      seatOf x = V.w) → ToldDesc.SampleAt (p14At Z).codes (x.1.l.get x.2).1 f.st i

/-- **THE FACTS ON THE VERIFIER's STATE, II: ON THE SHARED CHAIN's END**, likewise. -/
structure FoldRest₃ : Prop where
  /-- The OOD sample at Omega, AT THE SHARED CHAIN's END: the sendings' invariant. -/
  seedO : ∀ a e, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂
      stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc
      2) a → Rch a → (endedX X) a.1.1.2.2 = some e → ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁
      + nΩ, 0) → ∃ ρ yv, K1.SeedIs (p14At Z).codes (x.1.l.get x.2).1 e.st e.omega ρ yv

/-- **OF MAKE: THE LEDGER's READER OF OOD SAMPLES IS THE READING OFF THE TWO EARLIER CHAINS' ENDS.**
-/
structure Readers₃ : Prop where
  /-- At an elder member: off the first chain's last state. -/
  readE : ∀ a f, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂
      stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc
      2) a → (fun q => firstOfS (get q).2) (a.1.1.1, a.1.1.2.1) = some f → ∀ i, ∀ x ∈ (mineOf ms₁
      ms₂ N₁ Ns), seatBy noFirst f.book i = some (seatOf x) → (seatOf x = V.index ∨ seatOf x = V.w)
      → (smpLast (p14At Z).codes smp₁ smp₂ get Ns) a.1 x.1 x.2 = K1.smpAt (p14At Z).codes (x.1.l.get
      x.2).1 (x.1.l.get x.2).2 f.st i
  /-- At Omega: off the shared chain's end. -/
  readO : ∀ a e, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂
      stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc
      2) a → (endedX X) a.1.1.2.2 = some e → ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + nΩ, 0)
      → (smpLast (p14At Z).codes smp₁ smp₂ get Ns) a.1 x.1 x.2 = K1.smpAt (p14At Z).codes (x.1.l.get
      x.2).1 (x.1.l.get x.2).2 e.st e.omega

/-- **THE FOUR LISTS, WITH WHAT IS ASKED OF THE LETTERS Oc AND Rch**: all that rows 1, 2 and 3
spend. -/
structure LastCore₃ : Prop extends PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft
    nΩ
    V Ld, FoldFirst₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁
    Ns X Oc n₁ ft nΩ V Ld Rch, FoldRest₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS
    stOf bookOf Pm₀ N₁ Ns X Oc nΩ Rch, Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
    M₁ MS stOf bookOf Pm₀ N₁ Ns X Oc nΩ V where
  /-- ON THE LETTER Oc: it gives the first chain's whole promise at its last border. -/
  ocIs : ∀ q y, Oc q y → ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links ps
      q y
  /-- ON THE LETTER Oc: it reads the strings below the last chain's first tree. -/
  ocBelow : OcReadsBelow (D.t₁ + D.t₂) Oc
  /-- THE BRIDGE: the promise at border 2 holds at reached statements alone: the identity once the
  table's field is counted under "reached". -/
  reached : ∀ a, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
      (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂
      stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc
          2) a → Rch a

variable {o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns
    links ps X Oc rd r n₁ ft nΩ V Ld Rch}

/-- **ROWS 1, 2 AND 3: the ledger's `LastRest` at the closed letters, from the four lists.** -/
theorem LastCore₃.rest (L : LastCore₃ o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁
    MS stOf bookOf Pm₀ N₁ Ns links ps X Oc r n₁ ft nΩ V Ld Rch) : LastRest o mk Z (seatK Z N) N c D
    (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) dB dt (mineOf ms₁ ms₂ N₁ Ns)
    get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL
    o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) stOf bookOf Pm₀ N₁ Ns links ps Oc (yTree (p14At
    Z).codes (p14At Z).S) (fun q => firstOfS (get q).2) (endedX X) (VerifiableInference.Desc.numAt
    D.t₁ D.t₂ 2) (ToldDesc.noAt D.t₁ D.t₂ n₁ ft nΩ) rd r := by
  obtain ⟨ch, b₁, b₂, T, hcl⟩ := L.closed
  obtain ⟨file, h⟩ := L.dataIs
  obtain ⟨xI, hxI, sxI, shI⟩ := L.mineI
  obtain ⟨xW, hxW, sxW, shW⟩ := L.mineW
  obtain ⟨xO, hxO, sxO, shO⟩ := L.omegaSeat
  have two := fun a f hon hf => L.two a f hon (L.reached a hon) hf
  have two' := fun a f hon (_ : (yTree (p14At Z).codes (p14At Z).S) 2 a.1.2 = true) hf => two a f
      hon hf
  have F := H2K.AtW.four_at_W o mk Z (seatK Z N) N c file D r ch b₁ b₂ T dB dt hcl L.ownMask L.free0
      h L.stretch
  exact
    { toLastPlan8 := L.toLastPlan8
      ocIs := L.ocIs
      ocBelow := L.ocBelow
      joh := F.1
      batOne := F.2.1
      count := F.2.2.1
      errs := F.2.2.2
      sits := sits_closed _ smp₁ smp₂ get L.someW L.someI L.someO L.apartWO L.apartIO
      numbering := numbering_closed o mk Z (seatK Z N) N c D L.free0
      opens := opens_closed o mk Z (seatK Z N) N c D (p14At Z).codes G arr (smpLast (p14At Z).codes
          smp₁ smp₂ get Ns) (mineOf ms₁ ms₂ N₁ Ns) get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf
          bookOf Pm₀ N₁ Ns Oc (fun q => firstOfS (get q).2) (endedX X) h L.planOk L.ownMask
              L.twoStages L.places n₁ ft nΩ (fun a ha f e hf he
          => L.roots a f e ha (L.reached a ha) hf he)
      seam := seam_at_ends o mk Z (seatK Z N) N c D (p14At Z).codes G arr (smpLast (p14At Z).codes
          smp₁ smp₂ get Ns) (mineOf ms₁ ms₂ N₁ Ns) get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS
          (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit
              Cells
          Tok MsgT)) stOf bookOf Pm₀ N₁ Ns Oc (fun q => firstOfS (get q).2) (endedX X)
              (ToldDesc.noAt D.t₁ D.t₂ n₁ ft nΩ) rd r D.t₁ D.t₂
          L.oneSeat
        (core_of_members _ _ _ _ (p14At Z) _ _ _ G _ _ _ _ r rd _ F.1 L.placeB
          (members_of_five _ _ _ _ (p14At Z) _ _ _ G _ _ _ _ r rd D.t₁ D.t₂ V.index V.w (D.t₁ + nΩ,
              0)
              V.indexShape V.wShape xI xW xO L.oneSeat ⟨hxI, sxI, shI⟩ ⟨hxW, sxW, shW⟩ ⟨hxO, sxO,
              shO.symm⟩ L.seatsApart.1 L.seatsApart.2.1 L.seatsApart.2.2 L.allSeats two'
            (fun a e hon _ he => by
              obtain ⟨f₀, e₀, -, he₀, hk⟩ := shapeAt_of_onL _ _ _ _ _ _ _ _ hon
              obtain rfl : e₀ = e := Option.some.inj (he₀.symm.trans he)
              exact omega_seat_is (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (p14At Z) f₀ e₀ a.1.2 D.t₁ nΩ
                  hk
                  L.oneOmega)
            (fun a t hon hE hP ht hY st rest G0 Ly D' hf hN j x hx hs hsp hcase => by
              obtain ⟨f₀, e₀, hf₀, he₀, hk⟩ := shapeAt_of_onL _ _ _ _ _ _ _ _ hon
              obtain ⟨z, -, hS, -⟩ := hP x hx
              have hPl := L.planAt x hx st rest hf.1
              have hR := L.reached a hon
              obtain ⟨h1, h2, h3⟩ := sample_of_ends (p14At Z) _ f₀ e₀ a.1.2 t _ st rest G0 Ly D' hk
                  ht hf j _ _ ((smpLast (p14At Z).codes smp₁ smp₂ get Ns) a.1 x.1 x.2) hPl.1 (by
                rcases hcase with ⟨f, hf1, hseat, hw⟩ | ⟨hj, hw⟩
                · obtain rfl : f₀ = f := Option.some.inj (hf₀.symm.trans hf1)
                  exact .inl ⟨L.sampleE a f₀ hon hR hf₀ _ x hx hseat hw,
                    L.readE a f₀ hon hf₀ _ x hx hseat hw⟩
                · exact .inr ⟨hj, L.oneTable x hx hw, L.seedO a e₀ hon hR he₀ x hx hw,
                    L.readO a e₀ hon he₀ x hx hw⟩)
              have hB : BookAt G (ToldDesc.noAt D.t₁ D.t₂ n₁ ft nΩ) D' j x := bookAt_W G (p14At Z) _
                  f₀ e₀ a.1.2 t _ st rest G0 Ly D' hk ht hf n₁ ft nΩ D.t₁ D.t₂ (L.roots a f₀ e₀ hon
                  hR hf₀ he₀) j x hs Ld (by
                rcases hcase with ⟨f, -, -, hw⟩ | ⟨hj, hw⟩
                · refine .inl ⟨?_, L.carried a f₀ hon hR hf₀, L.planShapes⟩
                  rcases hw with hw | hw
                  · rw [hw]; exact L.elderBelow.1
                  · rw [hw]; exact L.elderBelow.2
                · refine .inr ?_
                  rw [hj, hw]
                  exact treeO_of_test G (p14At Z).codes (p14At Z).S (D.t₁ + nΩ) a.1.2 hE
                      L.planTreeO)
              exact five_of (p14At Z) G _ _ _ r rd a t st rest G0 Ly D' hf hN (codes_at_W (p14At Z)
                  _ f₀ e₀ a.1.2 t _ hk ht st rest G0 Ly D' hf) j x hsp hPl hB hS h1 h2 h3)))
        (fun a f e hon _ hf he => ⟨ToldDesc.handedSits_of_two (two a f hon hf) _ ⟨xI, hxI, sxI, shI⟩
            ⟨xW, hxW, sxW, shW⟩, by
          obtain ⟨f₀, e₀, -, he₀, hk⟩ := shapeAt_of_onL _ _ _ _ _ _ _ _ hon
          obtain rfl : e₀ = e := Option.some.inj (he₀.symm.trans he)
          exact omegaSits_of_plan (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (p14At Z) f₀ e₀ a.1.2 D.t₁ nΩ _
              hk L.oneOmega L.omegaSeat⟩)
        (fun _ _ _ _ h => h)
      y12 := fun _ => rfl
      y3 := fun _ => rfl
      y4 := fun _ => rfl }

/-- **ROW 0's ACCEPTING RUN EARNS THE LAYER ON THE LAST CHAIN's OWN STATE AT BORDER 1.** -/
theorem earn₀_tree (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z (seatK Z N) N c).XiPub ×
    (FL o mk Z (seatK Z N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃) → Option Cells) (c₀' :
    Cells) : ∀ a τ b, onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N
    c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁
                  decT₁ M₁) (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G
                  smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX
                  X)) Oc 0 a → (yTree (p14At Z).codes (p14At Z).S) 0 a.1.2 = true → (pieceZeroAt (FL o mk Z (seatK
                  Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes
                  G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns)))).ior.red.out
    a τ = some b → (yTree (p14At Z).codes (p14At Z).S) 1 b.1.2 = true :=
  fun a τ b hon _ hb => by
    obtain ⟨f₀, e₀, -, -, hk⟩ := shapeAt_of_onL _ _ _ _ _ _ _ _ hon
    obtain ⟨-, rs, gs, hd⟩ := held_yes (c0 Z) _ rfl a τ b hb
    exact treeOB_of_yes (Cl := Unit) (p14At Z) a.1.2 b.1.2 rs gs hd (start_codes (started_of_shape
        hk).1).2

/-- **The same with row 0's debt as one premise, in its payer's own conclusion's form.** -/
theorem LastCore₃.leftB (L : LastCore₃ o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁
    MS stOf bookOf Pm₀ N₁ Ns links ps X Oc r n₁ ft nΩ V Ld Rch) (decT : (ℕ → Option (ℕ × List
    UInt64)) → (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ × St) × (FL o mk
    Z (seatK Z N) N c).S₃) → Option Cells) (c₀' : Cells) (row0B : RowZeroOwed (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
    Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
    Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf
    Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc (pieceZeroAt
    (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c)
    D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁
    Ns))))) : LastLeftB o mk Z N c D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get
    Ns) decT c₀' dB dt (mineOf ms₁ ms₂ N₁ Ns) get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS (⟨rowsOpen
    (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT))
    stOf bookOf Pm₀ N₁ Ns links ps Oc (yTree (p14At Z).codes (p14At Z).S)
    (VerifiableInference.Desc.numAt D.t₁ D.t₂ 2) (ToldDesc.noAt D.t₁ D.t₂ n₁ ft nΩ) rd r X where
  toLastRest := L.rest
  row0B := row0B
  earn₀ := earn₀_tree decT c₀'

/-- **AT THE TABLES' FILES' OWN CONDITION `ocEnd … ∧ Rc`, Rc A FACT ON WHAT THE FIRST CHAIN HANDS
ON: THE
BRIDGE AND THE TWO FIELDS ON THE LETTER Oc FALL**: `LastCore₃` from the four lists, at Rch := Rc of
what is
handed. -/
theorem LastCore₃.atRc (Rc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ →
    Prop) (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld) (hF :
    FoldFirst₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X
    (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links ps q y ∧ Rc
    q) n₁ ft nΩ V Ld (fun a => Rc (a.1.1.1, a.1.1.2.1))) (hG : FoldRest₃ o mk Z N c D G arr get smp₁
    smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ (meaningSig
    (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links ps q y ∧ Rc q) nΩ (fun a => Rc (a.1.1.1,
    a.1.1.2.1))) (hR : Readers₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf
    bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁)
    links ps q y ∧ Rc q) nΩ V) : LastCore₃ o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁
    decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns links ps X (fun q y => ocEnd get N₁ (meaningSig (p14At
    Z).codes G arr smp₁ ms₁ decT₁ M₁) links ps q y ∧ Rc q) r n₁ ft nΩ V Ld (fun a => Rc (a.1.1.1,
    a.1.1.2.1)) where
  toPlanOk₃ := hP
  toFoldFirst₃ := hF
  toFoldRest₃ := hG
  toReaders₃ := hR
  ocIs := fun _ _ h => h.1
  ocBelow := fun p y y' hc hl h => ⟨ocEnd_readsBelow_sig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁ get
      (D.t₁ + D.t₂) N₁ links ps hP.sampled p y y' hc hl h.1, h.2⟩
  reached := fun _ h => h.1.2

/-- **AT Rc := "FIVE TESTS WITH CODE HOLD OF THE FIRST CHAIN's LAST STATE" (
`rcLastB`, Johnson/ToldDescR/RcLastCode.lean: the
book is in order from 0; the book fits; the own group has just the two members at V's places with
V's
shapes; the two pass `sampleL`; the book's trees have the plan's list's shapes) THE FOUR FACTS ON
WHAT
THE FIRST CHAIN HANDS ON ARE THEOREMS.** -/
theorem FoldFirst₃.ofRcLast (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r
    (N₁.treesAt none) 0 nΩ V Ld) :
    FoldFirst₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X
        (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links ps q y ∧
        ToldDesc.rcLastB 0 V Ld (p14At Z).codes (get q).2 = true) (N₁.treesAt none) 0 nΩ V Ld (fun a
        => ToldDesc.rcLastB 0 V Ld (p14At Z).codes (get (a.1.1.1, a.1.1.2.1)).2 = true) where
  two := fun _ _ _ hR hf => ToldDesc.rcLast_two hR hf
  roots := fun a f e hon hR hf he => by
    obtain ⟨k1, k2⟩ := ToldDesc.rcLast_roots hR hf
    obtain ⟨f₀, e₀, -, he₀, hk⟩ := shapeAt_of_onL _ _ _ _ _ _ _ _ hon
    obtain rfl : e₀ = e := Option.some.inj (he₀.symm.trans he)
    refine ⟨k1.trans ?_, k2, ToldDesc.omega_clause (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) hk
        hP.oneOmega⟩
    have hb := ToldDesc.bookAt_of_ocEnd get N₁ _ links ps _ _ hon.1.1 hon.2.1
    have hf' := hf
    unfold firstOfS at hf'
    obtain ⟨e', -, rfl⟩ := Option.map_eq_some_iff.1 hf'
    exact hb
  carried := fun _ _ _ hR hf => ToldDesc.rcLast_seats hR hf
  sampleE := fun _ f _ hR hf i x hx hi hw => by
    obtain ⟨xI, hxI, sxI, shI⟩ := hP.mineI
    obtain ⟨xW, hxW, sxW, shW⟩ := hP.mineW
    refine ToldDesc.rcLast_sample hR hf hi ?_
    rcases hw with hw | hw
    · obtain rfl := hP.oneSeat x hx xI hxI (hw.trans sxI.symm)
      exact .inl ⟨hw, shI⟩
    · obtain rfl := hP.oneSeat x hx xW hxW (hw.trans sxW.symm)
      exact .inr ⟨hw, shW⟩

variable (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃) → Option Cells) (c₀' : Cells) (a₁ :
    Block (FL o mk Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl) (k₁ : List (Block (FL o mk
    Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl)) (a₂ : Block St (FL o mk Z (seatK Z N) N
    c).Cl) (k₂ : List (Block St (FL o mk Z (seatK Z N) N c).Cl)) (rest₁ : (i : ℕ) → (ds : List RDT)
    → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁) (Wit Cells Tok MsgT) ds) (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP
    .two) (frameAt D (allOf D) D.key₂ 0) (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z
    N) N c).S₁) × St) (Wit Cells Tok MsgT) ds) (d wEnd : Wit Cells Tok MsgT)

/-- **The same from the four lists and row 0's debt as one premise.** -/
theorem e3_of_core (L : LastCore₃ o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS
    stOf bookOf Pm₀ N₁ Ns links ps X Oc r n₁ ft nΩ V Ld Rch) (row0B : RowZeroOwed (tiedNumbers N₁
    Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
    Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
    Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf
    Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc (pieceZeroAt
    (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c)
    D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁
    Ns))))) (b₀ : Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List
    (Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z
    (seatK Z N) N c).second.blocksInOrder = b₀ :: l) : EachLeads (onQ₃ (Fr := frameAt D (allOf D) D.key₃
             (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂
             k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At
             Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d
             wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁
             decT₁ M₁) (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (promSigS (p14At Z).codes G
             smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2)
             (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) Oc) (stepQ₃ (atDesc (FL o mk Z (seatK Z N) N c)
             (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap
             (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At
             Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)) (tiedNumbers N₁ Ns)
             (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
             Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
             Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf
             Pm₀) (besideS (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree
             (p14At Z).codes (p14At Z).S)) Oc) 0 ((atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two)
             (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o
             mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT
             c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP
             .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok)
             (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns)
             decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).l₃) :=
  e3_of_leftB decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (L.leftB (rd := fun _ => 0) decT c₀' row0B) b₀
      l
      hflat
      L.stretch

/-- **The same from the four lists and row 0's debt as one premise.** -/
theorem own3_of_core (L : LastCore₃ o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS
    stOf bookOf Pm₀ N₁ Ns links ps X Oc r n₁ ft nΩ V Ld Rch) (row0B : RowZeroOwed (tiedNumbers N₁
    Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At
    Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁ D.t₂⟩ : MeaningL (FL o mk
    Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf
    Pm₀) (fillAt (p14At Z) (c2 N).rounds (fun q => firstOfS (get q).2) (endedX X)) Oc (pieceZeroAt
    (FL o mk Z (seatK Z N) N c) D (c0 Z) (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c)
    D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁
    Ns))))) (b₀ : Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl) (l : List
    (Block (FL o mk Z (seatK Z N) N c).S₃ (FL o mk Z (seatK Z N) N c).Cl)) (hflat : (FL o mk Z
    (seatK Z N) N c).second.blocksInOrder = b₀ :: l) : EachOwn (onQ₃ (Fr := frameAt D (allOf D) D.key₃
             (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N c) D a₁ k₁ a₂
             k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok :=
             Tok) (FL o mk Z (seatK Z N) N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get
             Ns) decT c₀' (mineOf ms₁ ms₂ N₁ Ns))) d wEnd)).ft₃) (tiedNumbers N₁ Ns) (tiedMeaning get
             (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) (meaningSigS (p14At Z).codes G arr smp₂ ms₂
             decT₂ MS)) (promSigS (p14At Z).codes G smp₂ ms₂ stOf bookOf Pm₀) (besideS (fillAt (p14At Z) (c2
             N).rounds (fun q => firstOfS (get q).2) (endedX X)) (yTree (p14At Z).codes (p14At Z).S)) Oc)
    (meansQ₃ (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁
    M₁) (meaningSigS (p14At Z).codes G arr smp₂ ms₂ decT₂ MS)) (⟨rowsOpen (p14At Z).codes arr D.t₁
    D.t₂⟩ : MeaningL (FL o mk Z (seatK Z N) N c).S₃ (Wit Cells Tok MsgT))) insQ₃ outsQ₃ (· ∈
    startLast) 0 ((atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK Z N) N
    c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N) N c) D
    (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂ N₁
    Ns))) d wEnd)).p₃ :: (atDesc (FL o mk Z (seatK Z N) N c) (piecesAt (ckP .two) (FL o mk Z (seatK
    Z N) N c) D a₁ k₁ a₂ k₂ b₀ l rest₁ rest₂ (restCap (extsLast (Tok := Tok) (FL o mk Z (seatK Z N)
    N c) D (p14At Z).codes G arr (smpLast (p14At Z).codes smp₁ smp₂ get Ns) decT c₀' (mineOf ms₁ ms₂
    N₁ Ns))) d wEnd)).l₃) :=
  own3_of_leftB decT c₀' a₁ k₁ a₂ k₂ rest₁ rest₂ d wEnd (L.leftB (rd := fun _ => 0) decT c₀' row0B)
      b₀ l
      hflat
      L.stretch

end LLT25

#print axioms LLT25.FoldFirst₃.ofRcLast
#print axioms LLT25.e3_of_core
#print axioms LLT25.own3_of_core
