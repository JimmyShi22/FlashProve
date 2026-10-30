-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RidesPast.lean: CONDITIONAL: `RidesPast` T b
(Honest/Thread/Pays.lean) WHOLE at the member at an attention segment's own rounds (kind K5),
b := `borderOf g`, WITH THE `Thread` T A VARIABLE: every item that is open in front of the member
and that its row neither shuts nor owes says, of every state that T.keeps ties to the state in
front and at the strings of any list of played rounds, what it says in front.

The premises on T's letters are two structures of another file each: `K5AtT`
(Honest/K5/Law/AtT.lean: T.bs, T.ft, T.begun, T.handed, T.form and T.formP at the border) and
`K5RidersT` (Honest/K5/Law/RidersT.lean: which items ride; T.means at the riding sorts; T.keeps at
the border gives `K5Keeps`; T.strs behind played rounds agrees with T.strs in front at the stored
table and at the trees already sent). The first chain's `Thread` at the library's own letters meets
the first outright, and the second where its letter `keeps` at the border gives `K5Keeps` (the two
files' own theorems).

ONE PREMISE BESIDE THEM, ON A LETTER THAT HAS NO TEXT: `AnsOn`: what the letter ans (a pin's
sentence on the honest side) says at the index masks' tenant it says of every state that `K5Keeps`
ties to it, at all strings that agree at the stored table and at the trees below a number n
(`StrsKept`, Honest/K5/Law/RidersT.lean); here n is the number of trees that are stated in front of
the border. Of the six sorts that ride, this pin is the only one that can read a string. Whoever
lays ans is meant to show it. An ans that reads the tenant's own tree can meet it only if that tree
has a number below n: not shown here.

Sort by sort: "no mark", the pile, the other segments' parts (the head's among them), the open
segment's classes of rows: Johnson/Desc/K5/Honest/Law/RidesK5.lean at
Johnson/Desc/K5/Honest/Law/RidesAtHead.lean's letters. The lookup's forms "objects":
`objects_on_head` there: the one sort that wants the promise in front, which `Thr` T hands
(`reach_T`, `onAt_T`, Honest/K5/Law/DebtsT.lean).

Main names:
  `AnsOn`: the named premise.
  `riders_go_at_head`: every rider goes on: with no `Thread` in the sentence.
  `k5_ridesPast_T`: **the riders' sentence at the kind's member, T a variable.**
  `k5_ridesPast`: the same at the first chain's `Thread` at the library's own letters.

NOT SPENT OF T: T.wit, T.hs, T.rides, T.valid, T.table, T.stored. No half's text, no step
of the member and no yes is in it.

Limits. The hypothesis `P5J.AtMgA` is not shown. That `Thr` T holds of any run is not shown. Where
it holds of none the theorem says nothing. `AnsOn` and "T.keeps gives `K5Keeps`" are premises.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.DebtsT
import Johnson.Desc.ProofFile.Honest.K5.Law.RidersT
import Johnson.Desc.K5.Honest.Law.RidesAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Strs Chain)
open VerifiableInference.Desc.First (Item onAt openSets pubSets start leavesName)
open VerifiableInference.Desc.First.Att.P (riderB)
open H2K5.Door (moreOver9)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifiableInference.Desc.Sound (mgBase mgAll)
open H2K5.Honest (K5Keeps GoesOn relK5 relK5Y relK5Y_le riders_on constr_on_head
  row_on_head pile_on_head objects_on_head)
open ProofFile.Honest.FirstThread (Script WtF honest noStrs)
open P5J (AtMgA mgAtAll TS CellsM)

/-- **A NAMED PREMISE: at the tenant z, what the letter `ans` says of a state and strings it says of
every state that `K5Keeps` ties to it, at all strings that agree with these at the stored table and
at the trees below n.** It is a definition: a premise's form. Nothing is claimed of it, and it
is not shown: the letter has no text. -/
def AnsOn {P Wt : Type} (ans : Nat → Nat → P × TS → Strs → Wt → Prop) (z : Nat × Nat) (n : Nat) :
    Prop :=
  ∀ π s s' y y' v, StrsKept n y y' → K5Keeps s s' → ans z.1 z.2 (π, s) y v →
    ans z.1 z.2 (π, s') y' v

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}

/-- **EVERY RIDER GOES ON, WITH NO `Thread` IN THE SENTENCE.** i: "no mark", or an item that passes
the library's test `riderB` at the segment's number; not the digits' part. From a state that is
reached at the border in front of the member, bears no mark and meets the table's promise there, to
every state that `K5Keeps` ties to it, at two strings that agree at the stored table and at the
trees below n. c: the constant that the honest side's decoder returns. CONDITIONAL: under the
hypothesis h; g is below 12; hans. -/
theorem riders_go_at_head (hg : g < 12) (c : CellsM OnBytes.Flat.numsFull) {n : Nat}
    (hans : AnsOn ans (P5J.At.N Zp cF).index n) (i : Item)
    (hi : i = .unmarked ∨ riderB (2 * g + 1) i = true) (hd : ∀ n, i ≠ .constr n .lookDigits)
    (π : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF)
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (borderOf g) (π, s)) (hu : s.failed = none)
    (hon : onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (some ⟨1, some (2 * g + 1), 3, .K5⟩)
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[borderOf g]?).getD [])
      (((pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
      (π, s) noStrs)
    (K : K5Keeps s s') (hY : StrsKept n y y')
    (hm : Item.holds (P5J.At.N Zp cF)
      (honest (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase) ans test) i
      (π, s) y v) :
    Item.holds (P5J.At.N Zp cF)
      (honest (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase) ans test) i
      (π, s') y' v := by
  by_cases hf : ∃ n q r', i = .formsT n q r'
  · obtain ⟨n, q, r', rfl⟩ := hf
    have hi' : riderB (2 * g + 1) (.formsT n q r') = true := by
      rcases hi with hi | hi
      · cases hi
      · exact hi
    simp only [riderB, Bool.and_eq_true, beq_iff_eq] at hi'
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hi'
    obtain ⟨blk, a, -, Pl, -⟩ := k5_member h hg
    obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
    obtain ⟨x₁, hx⟩ := H2K5.Door.lookC_all h hg
    exact objects_on_head h c carryX hL hg Pl.plan hx (honest (mgAtAll h) ans test) rfl rfl _ _
      (open8_at hg) hr hu hon K y y' v hm
  · exact riders_on (P5J.At.N Zp cF)
      (honest (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase) ans test)
      (2 * g + 1) (relK5Y ProofFile.InstPub (StrsKept n)) (relK5Y_le ProofFile.InstPub (StrsKept n))
      (fun n p _ hp => constr_on_head h c carryX n p hp)
      (fun a y b y' w hr ha => by
        obtain ⟨π, t⟩ := a
        obtain ⟨π', t'⟩ := b
        obtain rfl : π = π' := hr.1
        exact hans π t t' y y' w hr.2.2 hr.2.1 ha)
      (fun cl => row_on_head h c carryX (2 * g + 1) cl) (pile_on_head h c carryX) i hi hd
      (fun n q r' e => hf ⟨n, q, r', e⟩) (π, s) y (π, s') y' v ⟨rfl, K, hY⟩ hm

/-- **THE RIDERS' SENTENCE AT THE KIND's MEMBER, WHOLE, T A VARIABLE.** CONDITIONAL: under the
hypothesis h; g is below 12; A, R: the two structures on T's letters; hans: `AnsOn` at the index
masks' tenant, at the number of trees that the sub-protocols in front of the border state. -/
theorem k5_ridesPast_T (hg : g < 12) (A : K5AtT h T g it pb wt ans test carryX cq)
    (R : K5RidersT h T g it pb wt ans test carryX cq)
    (hans : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g))) :
    RidesPast T (borderOf g) := by
  intro k s m E s' ps j v hT hk hj hs ho hm
  obtain ⟨i, rfl, hi, hd⟩ := R.riders j hj hs ho
  have hm' := (R.means i hi _ _ _ _).1 hm
  refine (R.means i hi _ _ _ _).2 ?_
  obtain ⟨blk, a, hb, -, -⟩ := k5_member h hg
  obtain ⟨hu, hon⟩ := onAt_T h A hg hT
  have hr := reach_T h A (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) hT
  have hp : pb (T.seat k m s).1 = m.st.input.x.pub := A.handed _ _ _
  have hp' : pb (T.seat k m s').1 = m.st.input.x.pub := A.handed _ _ _
  have hsent : E.sent = treesTo cF.blocksInOrder (borderOf g) := by
    rw [← A.bs]
    exact hT.2.2.2.2.1.2.2.1
  have hY := R.strs E ps
  rw [hsent] at hY
  rw [hp] at hm'
  rw [hp']
  exact riders_go_at_head h hg (cq m.st.input) hans i hi hd _ s s' _ _ _ hr hu hon
    (R.keeps s s' hk) hY hm'

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **The same at the first chain's `Thread` at the library's own letters.** CONDITIONAL: under the
hypothesis h; g is below 12; Kq: the letter `keeps` at the border gives `K5Keeps`; hans: `AnsOn` at
the number of trees that are stated in front of the border. -/
theorem k5_ridesPast {g : Nat} (hg : g < 12)
    (Kq : ∀ s s', keeps (borderOf g) s s' → K5Keeps s s')
    (hans : AnsOn ans (P5J.At.N Zp cF).index (treesTo cF.blocksInOrder (borderOf g))) :
    RidesPast (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) :=
  k5_ridesPast_T h hg
    (k5AtT_thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg)
    (k5RidersT_thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg Kq) hans

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.riders_go_at_head
#print axioms ProofFile.Honest.K5.k5_ridesPast_T
#print axioms ProofFile.Honest.K5.k5_ridesPast
