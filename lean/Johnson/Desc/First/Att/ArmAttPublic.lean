-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/ArmAttPublic.lean: kind K5: THREE SMALL PUBLIC PREMISES OF THE ATTENTION
SEGMENTS' HALF OF THE EXCHANGE (armCellIn_att, Johnson/Desc/First/Att/ArmAtt.lean)
AS LAWS OFF THE PLANNER's RETURN: hNM, hu3, htab; with hfun beside them, at one closed
structure tl'.

Why. armCellIn_att speaks of the plan's tail A.seam.tl and of "the closed structure tl' behind the
sending". Three of its premises say that the two agree where the arm reads them. They hold because
(i) A is what the planner returns (OfPlan, Johnson/Desc/First/Att/Claims/OfPlan.lean) and (ii) the
quiet step at piece 4 closes the list of tables and turns nothing else of the tail
(K8.Order.close_lays, Johnson/Desc/First/K8/OrderLays.lean).

The lemma K5Law.reads_closes stands in the library
(Johnson/Desc/First/Att/Claims/ReadsCloses.lean:64) and is called here.


Main names:
  `ofPlan_size`: **hNM**: A.seam.tl.NM = A.seam.tl.mats.size (over Fo.planA_size).
  `ofPlan_u3Of`: the plan's tail's number of the array of the reads is A.iU3 (both are 0).
  `close_tabAt`, `close_u3Of`: a closing leaves tabAt, at every table, and u3Of.
  `block4_closes`: the sub-protocol at piece 4 from a to b: b's tail is a closing of a's (over the
    library's reads_closes, Johnson/Desc/First/Att/Claims/ReadsCloses.lean).
  `armAtt_public`: **at the sub-protocol at piece 4, from a to b, where a's tail is the plan's:**
    b has a tail tl' with hfun, htab, hu3 at tl'; and hNM.
PREMISES LEFT OF armAtt_public: block4_funs' own (the block's yes from a to b · a stands in an
attention segment · the ledger has the array of the reads) · OfPlan A · htl : a₀.tl = A.seam.tl:
"the tail in the verifier's state in front of piece 4 is the plan's": NOT PAID HERE: the link's
opening lays the built link's tail, which is the plan's (Johnson/Desc/ProofFile/PlanPlain.lean:54,
by reading), and each sub-protocol in front must leave it.
THE LETTERS UNDER "FOR ALL": Fn, c, sg in htab: free on purpose: the two sides are one term.
IS IT EMPTY HERE? NO MEMBER IS SHOWN.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.Desc.First.Att.Claims.FunsAtTl
import Johnson.Desc.First.Att.Claims.ReadsCloses
import Johnson.Desc.First.K8.OrderLays
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanSize
import OnBytes.Tie.Pv.Tail.EndsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn Block)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First (K8.Order.close K8.Order.close_lays)
open OnBytes.Tie.Pv.Tail.Port (u3Of)

/-- **hNM**: the tail's number of matrices is its list's size. -/
theorem ofPlan_size {A : Attention.Plan} (h : OfPlan A) :
    A.seam.tl.NM = A.seam.tl.mats.size := by
  obtain ⟨st, j, cf, A0, pf, h0, rfl⟩ := h
  exact Fo.planA_size st j cf A0 h0

/-- The plan's tail's number of the array of the reads is the plan's. -/
theorem ofPlan_u3Of {A : Attention.Plan} (h : OfPlan A) : u3Of A.seam.tl = A.iU3 := by
  unfold u3Of
  rw [ofPlan_U h, (ofPlan_u3_tree h).1]
  rfl

/-- A closing leaves the numbering of the tables' places. -/
theorem close_tabAt {tl tl' : HTailF2} {funs : Array HFun} (h : K8.Order.close tl funs = .ok tl')
    (Fn : HFun) (c sg : ℕ) : tl.tabAt Fn c sg = tl'.tabAt Fn c sg := by
  rw [K8.Order.close_lays tl tl' funs h]
  rfl

/-- A closing leaves the number of the array of the reads. -/
theorem close_u3Of {tl tl' : HTailF2} {funs : Array HFun} (h : K8.Order.close tl funs = .ok tl') :
    u3Of tl' = u3Of tl := by
  rw [K8.Order.close_lays tl tl' funs h]
  rfl

/-- **THE SUB-PROTOCOL AT PIECE 4, FROM a TO b: b's tail is a closing of a's.** -/
theorem block4_closes {Cl : Type} (q : Params.First) (gp : Desc.Plain.GPar)
    (link piece moment : ℕ) (arrays : Option (List ℕ)) (name : String) (W : Verify.Public)
    (l g : ℕ) (z : Block First.S Cl) (hz : readsAtO W l g = some z) {A : Attention.Plan}
    (hA : W.A[g]? = some A) {a b : First.S} {a₀ : First.AttOwn} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : ((VerifiableInference.Desc.K1.laterAt (Cl := Cl) q gp link piece moment arrays).andThen
      name z).decide a rs gs = .ok b) (ha : a.here = .att a₀) :
    ∃ tl' funs, b.tl? = some tl' ∧ K8.Order.close a₀.tl funs = .ok tl' := by
  obtain ⟨m, h1, h2⟩ := except_bind_ok h
  unfold readsAtO at hz
  rw [hA] at hz
  obtain rfl := Option.some.inj hz
  have h2' : readsAtSO A m = .ok b := h2
  obtain ⟨_, F, _, y, _, _, _, em, _⟩ := VerifiableInference.Desc.K1.commitAtS_slots h1
  have hm := here_commit ha y.w y.L y.F
  rw [← em] at hm
  obtain ⟨a', _, _, _, t, tl', e, _, _, _, _, hc, h7, _⟩ := reads_closes A m b h2'
  obtain rfl : ({ a₀ with L := y.L, F := y.F } : First.AttOwn) = a' :=
    VerifiableInference.Desc.First.Here.att.inj (hm.symm.trans e)
  exact ⟨tl', _, h7, hc⟩

/-- **hfun · htab · hu3 AT ONE tl', AND hNM.** -/
theorem armAtt_public {Cl : Type} (q : Params.First) (gp : Desc.Plain.GPar)
    (link piece moment : ℕ) (arrays : Option (List ℕ)) (name : String) (W : Verify.Public)
    (l g : ℕ) (z : Block First.S Cl) (hz : readsAtO W l g = some z) {A : Attention.Plan}
    (hA : W.A[g]? = some A) {a b : First.S} {a₀ : First.AttOwn} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : ((VerifiableInference.Desc.K1.laterAt (Cl := Cl) q gp link piece moment arrays).andThen
      name z).decide a rs gs = .ok b) (ha : a.here = .att a₀)
    (hT : (a₀.F.trees[A.iU3]?).isSome = true) (hP : OfPlan A) (htl : a₀.tl = A.seam.tl) :
    ∃ tl', b.tl? = some tl' ∧ tl'.funs.toList = funsAt A a ∧
      (∀ Fn c sg, A.seam.tl.tabAt Fn c sg = tl'.tabAt Fn c sg) ∧ u3Of tl' = A.iU3 ∧
      A.seam.tl.NM = A.seam.tl.mats.size := by
  obtain ⟨tl', funs, e, hc⟩ := block4_closes q gp link piece moment arrays name W l g z hz hA h ha
  have hf := block4_funs q gp link piece moment arrays name W l g z hz hA h ha hT
  rw [e] at hf
  rw [htl] at hc
  exact ⟨tl', e, Option.some.inj hf, close_tabAt hc, (close_u3Of hc).trans (ofPlan_u3Of hP),
    ofPlan_size hP⟩

end K5Law

#print axioms K5Law.ofPlan_size
#print axioms K5Law.ofPlan_u3Of
#print axioms K5Law.close_tabAt
#print axioms K5Law.close_u3Of
#print axioms K5Law.block4_closes
#print axioms K5Law.armAtt_public
