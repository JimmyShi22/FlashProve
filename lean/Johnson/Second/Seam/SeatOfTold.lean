-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/SeatOfTold.lean: SeatFits AT THE SHARED CHAIN's TWO SENDINGS, AT ANY IOP AS WRITTEN IN LEAN WHOSE SHARED CHAIN TELLS WHAT K14's chainOf TELLS, FROM ONE TEST ON THE SEAT's PARAMETERS ALONE. The binders hFU | hFO of the seam (Johnson/Desc/Sound/SeamAtSh.lean | SeamRec.lean) and of the ledger's top row speak of a FileDescription G that is a term with many letters: no test on G can be evaluated there. Here G goes out: what the test seatFaultAt reads of G at the three seats is what K14's two sending sub-protocols tell, and that is a function of P.codes and P.S.
  toldOf codes S       what the eight sub-protocols of Desc.K14.blocks tell: the trees of o_u's sending, then those of o_omega's.
  told_blocks          oraclesOf (blocksOr P) = toldOf P.codes P.S (where withU P.S is there).
  told_chain           oraclesOf (chainOf c P tests last).blocksInOrder = toldOf P.codes P.S ++ ‹what the tests and the end tell›.
  faultIn · fault_eq · fault_none_j   seatFaultAt reads G through G.oracleAt j alone (by rfl), and whether it finds a fault hangs on the tree told, not on its number.
  toldFitB codes S layU layO   THE TEST: at each of the three members the tree that toldOf tells at the member's place in the chain is there and has no fault.
  seats_of_told      hlo · hG · withU · toldFitB's yes ⟹ seatUB and seatOB (SeatFacts.lean) at G.
  seatFits_of_told   so SeatFits G P.codes (sendingU P.S rU t₁ layU layO).l (…).seat and the like at sendingO, at every radius: hFU | hFO TO THE LETTER, G A LETTER.
  THE EVALUATIONS (#guard): toldFitB at p14Of of the planner's chains at VerifierAndGoals.storedPublicFiles · VerifierAndGoals.zGap · the library's small example; three negative tests.
WHAT THE TEST IS WORTH, SHOWN BY TWO NEGATIVE TESTS THAT DO NOT FAIL: toldFitB HOLDS WHAT THE SUB-PROTOCOLS TELL AGAINST THE VERY S AND CODES FROM WHICH THEY TELL IT: with a row more in S.omega, or with no codes at all, BOTH SIDES MOVE and it says yes again (the last two values of the print). So its yes says that K14's telling is of one piece with the shapes and the layouts of trees; it says NOTHING on whether S or the codes are the right ones. The negative tests that stand turn what is asked and leave what is told.
Limits. hlo (the first chain tells t₁ trees) and hG (the shared chain's told trees are chainOf's) stay premises here; in this library Johnson/Desc/K14/Law/LedgerFieldLaid.lean pays them where it calls seatFits_of_told. toldFitB's yes is EVALUATED here, at the planner's own values: an evaluation at one value is no theorem; at a typed value of P.codes | P.S it is a closed test that Lean's kernel can decide. No soundness is claimed.

-/
import Johnson.Second.Seam.SeatFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Desc.K14.Law.Fence (tenantSh sendingU sendingO)

/-- What K14's eight sub-protocols tell. -/
def toldOf (codes : Codes) (S : LinShape) : List VerifiableInference.Desc.Oracle :=
  match _root_.Desc.K14.withU S with
  | none => []
  | some sentU =>
    _root_.Desc.K14.oraclesOf codes sentU [[0], []] ++
      _root_.Desc.K14.oraclesOf codes (_root_.Desc.K14.withOmega S) [[1], [1, 0]]

theorem sent_one (P : _root_.Desc.K14.P14) (i : ℕ) (n : String) (a : Array OracleNotice) :
    (_root_.Desc.K14.parK1 P i n a).sent = a := by
  unfold K1.Par.sent _root_.Desc.K14.parK1
  simp

theorem told_blocks (P : _root_.Desc.K14.P14) {sentU : Array OracleNotice}
    (hU : _root_.Desc.K14.withU P.S = some sentU) :
    oraclesOf (_root_.Desc.K14.blocksOr P) = toldOf P.codes P.S := by
  unfold _root_.Desc.K14.blocksOr _root_.Desc.K14.blocks toldOf
  rw [hU]
  simp only [oraclesOf, _root_.Desc.K14.sendAt, sent_one, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.getD_some, List.flatMap_cons, List.flatMap_nil, id, List.append_nil,
    List.nil_append]
  cases P.S.sharedSplitNeeded <;> simp

theorem oracles_bare {S Cl : Type} (l : List (Block S Cl)) (f : Block S Cl → Bool) :
    oraclesOf (l.map fun b => { b with planOk := f b }) = oraclesOf l := by
  unfold oraclesOf
  rw [List.flatMap_map]

theorem told_chain (c : Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (tests : List (Block _root_.Desc.K14.St Unit))
    (last : List (Block _root_.Desc.K14.St Unit) → Block _root_.Desc.K14.St Unit)
    {sentU : Array OracleNotice} (hU : _root_.Desc.K14.withU P.S = some sentU) :
    ∃ rest, oraclesOf (_root_.Desc.K14.chainOf c P tests last).blocksInOrder = toldOf P.codes P.S ++ rest := by
  refine ⟨oraclesOf tests ++ oraclesOf [last (_root_.Desc.K14.blocksOr P ++ tests)], ?_⟩
  rw [← told_blocks P hU]
  unfold _root_.Desc.K14.chainOf Chain.blocksInOrder
  simp only [oraclesOf, List.map_nil, List.flatMap_nil, List.append_nil, List.flatMap_cons,
    List.flatMap_append, List.flatMap_map, List.nil_append, _root_.Desc.K14.frontBlock, roundlessBlock,
    List.map_append, List.append_assoc]

/-- seatFaultAt's list of what is amiss. -/
def badOf (orc : VerifiableInference.Desc.Oracle) (n : SymbolComponent) (codes : Codes) (s : OracleShape) :
    List String :=
  (if orc.logLength == longOf codes s then []
    else [s!"logLength {orc.logLength} | the code's {longOf codes s}"]) ++
  (if n.main == s.mainRows * s.mainDeg then []
    else [s!"main {n.main} | rows {s.mainRows} * degree {s.mainDeg}"]) ++
  (if n.mask == s.maskRows * 3 then [] else [s!"mask {n.mask} | rows {s.maskRows} * 3"]) ++
  (if s.mainRows == 0 || (codes.base.getD s.code default).logN == longOf codes s
    then [] else ["the mask's code is the longer"]) ++
  (if (orc.tenants.map fun x => x.main + x.mask).sum == orc.words then []
    else [s!"the tenants' words {(orc.tenants.map fun x => x.main + x.mask).sum} | " ++
      s!"the tree's {orc.words}"]) ++
  (if s.mainDeg == 1 || s.mainDeg == 3 then [] else [s!"degree {s.mainDeg}"])

/-- seatFaultAt's text, at what is told of the tree. -/
def faultIn (o : Option VerifiableInference.Desc.Oracle) (codes : Codes) (tag : String) (s : OracleShape) (j t : ℕ) :
    Option String :=
  match o with
  | none => some s!"{tag}: tree {j} is told by no block"
  | some orc =>
    match orc.tenants[t]? with
    | none => some s!"{tag}: tree {j} has no tenant {t} ({orc.tenants.length} told)"
    | some n =>
      if (badOf orc n codes s).isEmpty then none
      else some (s!"{tag}: tree {j} tenant {t} (answers {s.answers}): " ++
        "; ".intercalate (badOf orc n codes s))

theorem fault_eq {Xi : Type} (F : FileDescription Xi) (codes : Codes) (tag : String) (s : OracleShape)
    (j t : ℕ) : seatFaultAt F codes tag s j t = faultIn (F.oracleAt j) codes tag s j t := rfl

theorem fault_none_j (o : Option VerifiableInference.Desc.Oracle) (codes : Codes) (tag : String) (s : OracleShape)
    (j j' t : ℕ) : (faultIn o codes tag s j t).isNone = (faultIn o codes tag s j' t).isNone := by
  unfold faultIn
  cases o with
  | none => rfl
  | some orc =>
    dsimp only
    cases orc.tenants[t]? with
    | none => rfl
    | some n =>
      dsimp only
      cases (badOf orc n codes s).isEmpty <;> rfl

/-- One member: the tree at place i of what is told is there and has no fault at tenant t. -/
def fitAt (told : List VerifiableInference.Desc.Oracle) (codes : Codes) (s : OracleShape) (i t : ℕ) : Bool :=
  decide (i < told.length) && (faultIn told[i]? codes "" s 0 t).isNone

/-- **The test.** -/
def toldFitB (codes : Codes) (S : LinShape) (layU layO : TreeLay) : Bool :=
  fitAt (toldOf codes S) codes S.fold.u (layU.tree.getD 0 0) (layU.part.getD 0 0) &&
  fitAt (toldOf codes S) codes S.omega (layU.shapes.size + layO.tree.getD 0 0) (layO.part.getD 0 0) &&
  fitAt (toldOf codes S) codes S.sharedSplit (layU.shapes.size + layO.tree.getD 1 0)
    (layO.part.getD 1 0)

section
variable {Xi : Type} (G : FileDescription Xi) (t₁ : ℕ) (told rest : List VerifiableInference.Desc.Oracle)

theorem oracleAt_told (hlo : (oraclesOf G.first.blocksInOrder).length = t₁)
    (hG : oraclesOf G.shared.blocksInOrder = told ++ rest) {i : ℕ} (hi : i < told.length) :
    G.oracleAt (t₁ + i) = told[i]? := by
  unfold FileDescription.oracleAt
  rw [hG, List.append_assoc, List.getElem?_append_right (by omega), hlo, Nat.add_sub_cancel_left,
    List.append_assoc, List.getElem?_append_left hi]

theorem seat_of_fit (codes : Codes) (hlo : (oraclesOf G.first.blocksInOrder).length = t₁)
    (hG : oraclesOf G.shared.blocksInOrder = told ++ rest) {s : OracleShape} {i t : ℕ}
    (h : fitAt told codes s i t = true) : seatAtB G codes s (t₁ + i, t) = true := by
  unfold fitAt at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold seatAtB
  rw [fault_eq, oracleAt_told G t₁ told rest hlo hG h.1, fault_none_j _ _ _ _ _ 0]
  exact h.2

end


theorem seats_of_told {Xi : Type} (G : FileDescription Xi) (P : _root_.Desc.K14.P14) (t₁ : ℕ)
    (layU layO : TreeLay) (c : Model.Verify.Chains) (tests : List (Block _root_.Desc.K14.St Unit))
    (last : List (Block _root_.Desc.K14.St Unit) → Block _root_.Desc.K14.St Unit)
    {sentU : Array OracleNotice} (hU : _root_.Desc.K14.withU P.S = some sentU)
    (hlo : (oraclesOf G.first.blocksInOrder).length = t₁)
    (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (_root_.Desc.K14.chainOf c P tests last).blocksInOrder)
    (hB : toldFitB P.codes P.S layU layO = true) :
    seatUB G P.codes P.S t₁ layU layO = true ∧ seatOB G P.codes P.S t₁ layU layO = true := by
  obtain ⟨rest, hr⟩ := told_chain c P tests last hU
  rw [hr] at hG
  unfold toldFitB at hB
  simp only [Bool.and_eq_true] at hB
  obtain ⟨⟨h1, h2⟩, h3⟩ := hB
  refine ⟨seat_of_fit G t₁ _ rest P.codes hlo hG h1, ?_⟩
  unfold seatOB
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · have := seat_of_fit G t₁ _ rest P.codes hlo hG h2
    rw [← Nat.add_assoc] at this
    exact this
  · have := seat_of_fit G t₁ _ rest P.codes hlo hG h3
    rw [← Nat.add_assoc] at this
    exact this

/-- hFU | hFO, G a letter. -/
theorem seatFits_of_told {Xi : Type} (G : FileDescription Xi) (P : _root_.Desc.K14.P14) (t₁ : ℕ)
    (layU layO : TreeLay) (c : Model.Verify.Chains) (tests : List (Block _root_.Desc.K14.St Unit))
    (last : List (Block _root_.Desc.K14.St Unit) → Block _root_.Desc.K14.St Unit)
    {sentU : Array OracleNotice} (hU : _root_.Desc.K14.withU P.S = some sentU)
    (hlo : (oraclesOf G.first.blocksInOrder).length = t₁)
    (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (_root_.Desc.K14.chainOf c P tests last).blocksInOrder)
    (hB : toldFitB P.codes P.S layU layO = true) (rU rO rSp : ℕ) :
    SeatFits G P.codes (sendingU P.S rU t₁ layU layO).l (sendingU P.S rU t₁ layU layO).seat ∧
      SeatFits G P.codes (sendingO P.S rO rSp t₁ layU layO).l
        (sendingO P.S rO rSp t₁ layU layO).seat :=
  have h := seats_of_told G P t₁ layU layO c tests last hU hlo hG hB
  ⟨seatFits_U G P.codes P.S t₁ layU layO h.1 rU, seatFits_O G P.codes P.S t₁ layU layO h.2 rO rSp⟩

/-- The test at the planner's own values; how many trees are told; three negative tests, each of which
turns what is ASKED and leaves what is TOLD: o_omega's shape with a row more · o_omega's and o_sp's
places one tree further · o_u asked at no codes; and two rows that turn S or the codes ON BOTH SIDES. -/
def toldRows (pol lay KL : ByteArray) : Option (Bool × Nat × (Bool × Bool × Bool) × Bool × Bool) :=
  (p14At pol lay KL).bind fun P =>
    match (_root_.Desc.K14.withU P.S).bind (layTrees P.codes),
        layTrees P.codes (_root_.Desc.K14.withOmega P.S) with
    | some layU, some layO =>
      let told := toldOf P.codes P.S
      some (toldFitB P.codes P.S layU layO, told.length,
        (fitAt told P.codes { P.S.omega with mainRows := P.S.omega.mainRows + 1 }
            (layU.shapes.size + layO.tree.getD 0 0) (layO.part.getD 0 0),
          toldFitB P.codes P.S { layU with shapes := layU.shapes.push {} } layO,
          fitAt told {} P.S.fold.u (layU.tree.getD 0 0) (layU.part.getD 0 0)),
        toldFitB P.codes { P.S with omega := { P.S.omega with mainRows := P.S.omega.mainRows + 1 } }
          layU layO,
        toldFitB {} P.S layU layO)
    | _, _ => none

/-- As due: the test yes; three trees; the three negative tests no. -/
def toldAsDue (pol lay KL : ByteArray) : Bool :=
  match toldRows pol lay KL with
  | some (a, n, (x, y, z), _, _) => a && n == 3 && !x && !y && !z
  | none => false

-- THE EVALUATIONS
#eval toldRows VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL
#guard toldAsDue VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL
#guard toldAsDue VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL
open OnBytes.Tie.Pv.Plan in
#eval toldRows (textOf policyS) layoutS.toUTF8 (wordsFile scalesS)
open OnBytes.Tie.Pv.Plan in
#guard toldAsDue (textOf policyS) layoutS.toUTF8 (wordsFile scalesS)

end Second.Seam

#print axioms Second.Seam.told_blocks
#print axioms Second.Seam.told_chain
#print axioms Second.Seam.seats_of_told
#print axioms Second.Seam.seatFits_of_told
