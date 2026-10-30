-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6AtMgAll.lean: WHAT THE TIE OF THE
SUB-PROTOCOL AT THE OUTPUT HEAD ASKS OF THE TABLE'S MEANING, AT THE COMPOSED MEANING OF ALL KINDS
"mgAll D Mg" (Johnson/Desc/Sound/MgAll.lean: its
reference form; all parameters in one structure MgData): premises on the meaning become theorems
at that one term, under a few sentences on the structure's fields.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  (wtK6, K6's sentence on the claim on the weights, under the guard on the witness:
      Law/WtK6.lean.)
  MgFitsK6 D ...: EIGHT FIELDS. On the public parameters: seg (the head's segment's number,
      headLink, is 24). On D: ns (the plan's number of slots of segment 24's ledger is the head's
      plan's) · own, join, planes (the map of names at (24, 4, "own"), (24, 4, "join"), (24, 3,
      "planes") gives the driver's runs) · hid (the hidden values are read off the seats) · head
      (the head's part of the model's relation is headPartK6) · wt (by report,
          not shown, the parameter wt IS wtK6: an equation again). (The head's shape, the number
      of the array of the reads, the sizes, the policy and the map of addresses are made off the
      public parameters.)
  statedAt_of_is: StatedAt from the dispatcher's own sentence StatedIs
      (Johnson/Desc/Sound/StatedAll.lean) at the head's arm uHeadK6 (Law/StatedHeadArm.lean).
  sigFields_mgAll: SigFields at mgAll: six times rfl.
  pubSays_mgAll: PubSays Wp mgAll 24.
  formsSay_mgAll: FormsSay at mgAll, all three fields. planesSay_mgAll: the like for the planes'
      forms.
  base_mgAll: the item "constr 24 small" at mgAll gives base24.
  order_mgAll: "in order" is left by a step that turns the ledger, what is heard and the squares'
      sumcheck of an open head's own part alone, where the innermost meaning's is blind to where the
      chain stands.
  ns_of_asked: where the public test freeAbove m accepts, a ledger is open with just the plan's
      number of slots.

Every letter under "there is": ns_of_asked: n0 (pinned by D.pubD.nsOf m), F (by the state's own
reader of its ledger).
What it does not say. THAT MgFitsK6 CAN BE MET: no closed structure of parameters lies. "In order"
says nothing on the request's words or the check.
Nothing on soundness.
-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.Kinds.Law.StatedHeadArm
import Johnson.Desc.Sound.OnParts
import Johnson.P5J.CellQ
import Johnson.Desc.Kinds.Law.K6OpenedCut
import Johnson.Desc.Kinds.Law.FillK6K7Says
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Desc.Kinds.Law.WtK6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.Sound (Mem MsgT Frame SigFields SeatsNamed GroupsSeated MgData mgAll
    onQ
  onParts_of_on)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout)
  (num : ℕ → ℕ → ℕ) (n rb : ℕ) (tokV : Tok → Fin Inst.Model.ppref.V)
  (req : P × P5J.TS → P5J.TReq)
  (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
  (hN : SeatsNamed D.arr D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num)) (hG : GroupsSeated D.ms
      D.N) (tab : ℕ → ℕ)
  (tokH : P × P5J.TS → Fin Inst.Model.ppref.V)

/-- **The composed meaning's parameters are the head's.** -/
structure MgFitsK6 : Prop where
  seg : VerifiableInference.OnPublicFiles.headLink Wp = 24
  ns : D.pubD.nsOf 24 = some Wp.H.ns
  own : D.runs 24 4 "own" = [(3, "norm"), (3, "policy"), (3, "logits")]
  join : D.runs 24 4 "join" = [(3, "join")]
  planes : D.runs 24 3 "planes" = [(2, "planes")]
  hid : D.H = P5J.hidAtSeat Wp D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num)
      tokV req dec hN hG
  head : D.headPart = headPartK6 D.cs D.arr D.ms D.N (Meaning.sizesOf Wp) (seatLay Wp lay6 num)
      Wp (plAt n rb) tab D.put
    (Sound.oneDec D.decT D.H) tokH
  wt : D.wt = wtK6 D.cs D.arr D.ms D.N Wp lay6 num n rb

/-- What the head asks of the stated data, from the dispatcher's own sentence at this arm. -/
theorem statedAt_of_is (X : OnBytes.Model.Verify.Public) (l : ℕ) (St : Sound.Stated) (s : S)
    (cU : ℕ × String) (h : Sound.StatedIs St (uHeadK6 X l) s) (h2 : Sound.second s cU = true) :
    StatedAt X (p8K6 X l) St s cU :=
  fun D => ⟨fun j => congrFun (h.mask D) j, fun pos => h.cell D cU 0 pos h2⟩

/-- **The six parameters on the oracles, at the composed meaning.** -/
theorem sigFields_mgAll : SigFields D.cs D.G D.arr D.smp D.ms D.decT (mgAll D Mg) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {D lay6 num n rb tokV req dec hN hG tab tokH}

/-- **Three public items give three of the kind's tests, at the composed meaning.** -/
theorem pubSays_mgAll (F : MgFitsK6 D lay6 num n rb tokV req dec hN hG tab tokH) :
    PubSays Wp (mgAll D Mg) 24 := by
  refine ⟨fun a h => wellLaidB_of_ledgerB Wp a.2 h, fun a h => ?_, fun a h => ?_⟩
  · have h' : tokenHeardB Wp.hS (readsOf Wp) a.2 = true := h
    exact tokenB_of_heard Wp a.2 h'
  · rw [Sound.mgAll_pub, First.pubAll_look_head D.pubD Mg.pub 24 (by
      show ((24 : ℕ) == VerifiableInference.OnPublicFiles.headLink Wp) = true
      rw [F.seg]
      rfl) a] at h
    have h' : lookHeadB Wp.hS (readsOf Wp) a.2 = true := h
    exact h'

/-- **What three of the table's items say, at the composed meaning.** -/
theorem formsSay_mgAll (F : MgFitsK6 D lay6 num n rb tokV req dec hN hG tab tokH) :
    FormsSay D.cs D.arr D.ms D.N Wp lay6 num n rb (mgAll D Mg) D.St (D.Rd 24) := by
  refine ⟨fun a y w h r hr => ?_, fun a y w h => ?_, fun a y w hR h => ?_⟩
  · exact h.1 (3, r) (by
      rw [F.own]
      rcases hr with rfl | rfl | rfl <;> simp)
  · exact h.1 (3, "join") (by
      rw [F.join]
      simp)
  · have h1 := h.2 rfl
    rw [F.wt] at h1
    exact h1 rfl hR

/-- The item on the planes' forms, in the forms' sentence's words. -/
theorem planesSay_mgAll (F : MgFitsK6 D lay6 num n rb tokV req dec hN hG tab tokH) (a : P × S)
    (y : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (h : (mgAll D Mg).formsT 24 3 "planes" a y w) :
    Sound.formsTQ (D.Rd 24) D.St (D.N.sent 24 0) 2 "planes" a.2
      (Sound.seatTab D.cs D.arr D.ms w) :=
  h.1 (2, "planes") (by
    rw [F.planes]
    simp)

/-- **"small" at segment 24 gives the packing, at the composed meaning.** -/
theorem base_mgAll (F : MgFitsK6 D lay6 num n rb tokV req dec hN hG tab tokH) (a : P × S)
    (y : Strs) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (h : (mgAll D Mg).constr 24 .small a y w) : base24 D.cs D.arr D.ms D.N (Meaning.sizesOf Wp)
        (seatLay Wp lay6 num) w := by
  have h1 : P5J.constrQAt (VerifiableInference.OnPublicFiles.headLink Wp) D.put (Sound.oneDec D.decT
            D.H) D.headPart D.digitsPart 24 .small a y
      w := h
  rw [F.seg] at h1
  have h2 : (Sound.oneDec D.decT D.H).base 24 w :=
    P5J.constrQ_small_base D.put _ D.headPart D.digitsPart 24 a y w h1
  have h3 : D.H.base 24 w := h2
  rw [F.hid] at h3
  exact h3

variable (D)

/-- **"In order" is left by a step that turns, of an open head's own part, the ledger, what is heard
and the squares' sumcheck alone: at the composed meaning.** -/
theorem order_mgAll
    (hMg : ∀ (z : P) (t : S) h, Mg.inOrder (z, { t with here := h }) = Mg.inOrder (z, t))
    (z : P) (t : S) (o : First.HeadOwn) (ho : t.here = .head o) (F1 : OnBytes.Model.Fork)
    (X : Option OnBytes.Model.Head.Heard) (Q : Option OnBytes.Model.Psc) :
    (mgAll D Mg).inOrder (z, { t with here := .head { o with F := F1, x := X, squaresP := Q } }) =
      (mgAll D Mg).inOrder (z, t) := by
  rw [Sound.mgAll_inOrder_at, Sound.mgAll_inOrder_at, hMg]

/-- **"Free above" at the composed meaning.** -/
theorem ns_of_asked (m : ℕ) (x : P × S) (h : (mgAll D Mg).pub (.freeAbove m) x = true) :
    ∃ n0 F, D.pubD.nsOf m = some n0 ∧ x.2.fork? = some F ∧ F.ns = n0 := by
  have h' : ((D.pubD.nsOf m).any fun n => First.freeAboveB n x.2) = true := h
  cases e : D.pubD.nsOf m with
  | none =>
    rw [e] at h'
    cases h'
  | some n0 =>
    rw [e] at h'
    have h2 : First.freeAboveB n0 x.2 = true := h'
    unfold First.freeAboveB at h2
    cases f : x.2.fork? with
    | none =>
      rw [f] at h2
      cases h2
    | some F =>
      rw [f] at h2
      have h3 : (((List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true) &&
        F.ns == n0) = true := h2
      exact ⟨n0, F, rfl, rfl, eq_of_beq (Eq.mp (Bool.and_eq_true _ _) h3).2⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.sigFields_mgAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pubSays_mgAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.formsSay_mgAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.base_mgAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.order_mgAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.ns_of_asked
