-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/RecFacts.lean: THE FURTHER CLOSED PREMISES OF THE SEAM's NEWER FORM, tupleNine_rec | tupleTen_rec (Johnson/Desc/Sound/SeamRec.lean: the form that the ledger's core calls), AT THE RELEASE's OWN VALUES: fU (at o_u's and at o_omega's shape) · fSp (at the first stage of each of the two proximity tests). Tests with code, their laws, the two theorems called, and evaluations at the IOP as ProofFile.onlineDescription writes it at stored public files.
  mainB cs s · main_of_B     0 < s.mainRows ∧ (s.maskRows = 0 → cs.mask.size ≤ s.maskCode): the binder fU at a shape s.
  splitB cs S layO π · split_of_B   at π's first stage a₀: 0 < S.sharedSplit.maskRows ∧ cs.base.size ≤ S.sharedSplit.code ∧ (the tree of o_sp in o_omega's sending).logN ≤ a₀.Z.a: the binder fSp; where π has no stage the test says no.
  nine_rec_takes · ten_rec_takes   tupleNine_rec | tupleTen_rec CALLED with Facts' ten fields (PlanFacts.lean), hFU | hFO (SeatFacts.lean), fU and fSp: FOURTEEN | THIRTEEN binders gone. Written as «def» without a stated type: the types are what Lean infers.
  lookR pol lay KL   the rows, each with a negative test, at π := proximityTestParametersAt ⟨2, none, 9 | 10, .K12⟩ of the places that H2U.placesOfMade gives.
  THE EVALUATION (#eval prints; #guard holds): the library's small example. The full size: a sheet outside the library (RecFactsFull.lean), as for SeatFacts.lean.
Limits. AN EVALUATION AT ONE VALUE IS NO THEOREM: it pays «is it empty?» alone. hfit (the radii against the members') and hrec (the test sampleL at the verifier's state) are not here. No soundness is claimed.

-/
import Johnson.Second.Seam.SeatFacts
import Johnson.Desc.Sound.SeamRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Second.Seam
open OnBytes OnBytes.Params
open Desc.K14 Desc.K14.Law.Fence
open VerifiableInference.Desc.K12 (P12)

def mainB (cs : Codes) (s : OracleShape) : Bool :=
  decide (0 < s.mainRows) && (decide (s.maskRows ≠ 0) || decide (cs.mask.size ≤ s.maskCode))

theorem main_of_B {cs : Codes} {s : OracleShape} (h : mainB cs s = true) :
    0 < s.mainRows ∧ (s.maskRows = 0 → cs.mask.size ≤ s.maskCode) := by
  unfold mainB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun e => h.2.resolve_left fun n => n e⟩

def splitB (cs : Codes) (S : LinShape) (layO : TreeLay) (π : P12) : Bool :=
  match π.nums.stages with
  | [] => false
  | a₀ :: _ =>
    decide (0 < S.sharedSplit.maskRows) && decide (cs.base.size ≤ S.sharedSplit.code) &&
      decide ((layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)

theorem split_of_B {cs : Codes} {S : LinShape} {layO : TreeLay} {π : P12}
    (h : splitB cs S layO π = true) :
    ∀ a₀ rest, π.nums.stages = a₀ :: rest → 0 < S.sharedSplit.maskRows ∧
      cs.base.size ≤ S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a := by
  intro a₀ rest e
  unfold splitB at h
  rw [e] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

def nine_rec_takes {P : P14} {sentU : Array OracleNotice} {layU layO : TreeLay}
    (F : Facts P sentU layU layO) :=
  fun {Xi P₁ Cl Cells Tok : Type} (G : VerifiableInference.Desc.FileDescription Xi) (t₁ : ℕ) (π : P12)
      (hsu : seatUB G P.codes P.S t₁ layU layO = true) (hso : seatOB G P.codes P.S t₁ layU layO = true)
      (hu : mainB P.codes P.S.fold.u = true) (hs : splitB P.codes P.S layO π = true)
      N Pm₀ Oc {Fr} f l mem rd r rdN x rU rO rSp t₂ ch tests last
      hj he hp hrd hb hG hlo hN hd hB hcod hI hmU hmS hfit hrec =>
    tupleNine_rec (Xi := Xi) (P₁ := P₁) (Cl := Cl) (Cells := Cells) (Tok := Tok) P.codes G N Pm₀ Oc
      (Fr := Fr) P sentU layU layO f l mem rd π r rdN x P.S rU rO rSp t₁ t₂ ch tests last
      hj he hp F.hsU F.hsO hrd hb hG hlo F.hU F.hlU F.hlO F.hS F.hm hN hd
      (seatFits_U G P.codes P.S t₁ layU layO hsu rU) (seatFits_O G P.codes P.S t₁ layU layO hso rO rSp)
      hB hcod hI F.hTU F.hTS hmU hmS (main_of_B hu) (split_of_B hs) hfit hrec

def ten_rec_takes {P : P14} {sentU : Array OracleNotice} {layU layO : TreeLay}
    (F : Facts P sentU layU layO) :=
  fun {Xi P₁ Cl Cells Tok : Type} (G : VerifiableInference.Desc.FileDescription Xi) (t₁ : ℕ) (π : P12)
      (hso : seatOB G P.codes P.S t₁ layU layO = true)
      (hu : mainB P.codes P.S.omega = true) (hs : splitB P.codes P.S layO π = true)
      N Pm₀ Oc {Fr} f l mem rd r rdN x rU rO rSp t₂ ch tests last
      hj he hp hrd hb hG hlo hN hd hB hcod hI hmU hmS hfit hrec =>
    tupleTen_rec (Xi := Xi) (P₁ := P₁) (Cl := Cl) (Cells := Cells) (Tok := Tok) P.codes G N Pm₀ Oc
      (Fr := Fr) P sentU layU layO f l mem rd π r rdN x P.S rU rO rSp t₁ t₂ ch tests last
      hj he hp F.hsU F.hsO hrd hb hG hlo F.hU F.hlU F.hlO F.hS F.hm hN hd
      (seatFits_O G P.codes P.S t₁ layU layO hso rO rSp)
      hB hcod hI F.hTO F.hTS hmU hmS (main_of_B hu) (split_of_B hs) hfit hrec

end Second.Seam

end

namespace Second.Seam
open OnBytes OnBytes.Params
open VerifiableInference.Desc

def lookR (pol lay KL : ByteArray) : Except String (List Line) :=
  match ProofFile.pureRoad.pub OnBytes.secondHashFunction pol lay KL with
  | .ok Z =>
    match H2U.placesOfMade Z.made with
    | .ok N =>
      let P := _root_.Desc.K14.p14Of Z.p.chains (_root_.Desc.K14.beforePointOf N)
      match layTrees P.codes (_root_.Desc.K14.withOmega P.S), N.O with
      | some layO, some nO =>
        let π9 := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U
        let π10 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO
        .ok
          [("fU at o_u's shape (negative test: no main row)", mainB P.codes P.S.fold.u,
              mainB P.codes { P.S.fold.u with mainRows := 0 }),
           ("fU at o_omega's shape (negative test: its mask code := 0, no mask row)",
              mainB P.codes P.S.omega, mainB P.codes { P.S.omega with maskCode := 0, maskRows := 0 }),
           ("fSp at the first proximity test's place (negative test: a place without stages)",
              splitB P.codes P.S layO π9,
              splitB P.codes P.S layO { π9 with nums := { π9.nums with stages := [] } }),
           ("fSp at the second proximity test's place (negative test: o_sp's code := 0)",
              splitB P.codes P.S layO π10,
              splitB P.codes { P.S with sharedSplit := { P.S.sharedSplit with code := 0 } } layO π10),
           ("the two places have stages and are early (negative test: the stand-by place of another chain)",
              !π9.nums.stages.isEmpty && !π10.nums.stages.isEmpty && π9.early && π10.early,
              !(H2U.proximityTestParametersAt ⟨3, none, 9, .K12⟩ N.U).nums.stages.isEmpty)]
      | _, _ => .error "the layout of o_omega's sending or the second test's place is not there"
    | .error _ => .error "the places refuse"
  | .error _ => .error "the public part refuses"

def allAsDueR (pol lay KL : ByteArray) : Bool :=
  match lookR pol lay KL with
  | .ok l => !l.isEmpty && l.all fun x => x.2.1 && !x.2.2
  | .error _ => false

-- THE EVALUATION
open OnBytes.Tie.Pv.Plan in
#eval lookR (textOf policyS) layoutS.toUTF8 (wordsFile scalesS)
open OnBytes.Tie.Pv.Plan in
#guard allAsDueR (textOf policyS) layoutS.toUTF8 (wordsFile scalesS)

end Second.Seam

#print axioms Second.Seam.main_of_B
#print axioms Second.Seam.split_of_B
#print axioms Second.Seam.nine_rec_takes
#print axioms Second.Seam.ten_rec_takes
