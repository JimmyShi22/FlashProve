-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Ready.lean: CONDITIONAL: in front of an attention segment's own
rounds (kind K5) the verifier's state is ready for the kind's hearing (`ReadyO`,
Johnson/Desc/First/Att/K05SeatAccepts.lean): an attention segment stands open, the lookup on the
calls has laid what it heard, the segment's own rounds have not been heard, the ledger has its
arrays' lengths and room for the kind's slots, no count of rows waits, and there is no mark of
failure. All of it is read off the public book-keeping that the table of joints
(Johnson/Desc/First/Borders.lean) promises at the border: its test on where the chain stands, and
three of its public items: the ledger, "free above", and the caller's condition in front.

  `mayWait_k5`      at the kind's place no count of rows may wait
  `readyO_of_onAt`  GENERAL in the meaning of the table's items: from the table's promise `onAt` in
                    front of the kind's place, at any meaning whose public tests are the library's
                    composed ones (`pubAll`, Johnson/Desc/First/PubAll.lean)
  `thrAt`           the first chain's `Thread` at the library's own letters (`lettersAt`,
                    Honest/Thread/FirstAt.lean), as one name
  `open_k5`         the six public items that the kind's row asks are open at the border
  `readyO_of_thr`   CONDITIONAL: **from `Thr` in front of the kind's member of group g: the
                    state is ready**

Who is meant to pay the premises. `PlanAt`: `k5_member` (Honest/K5/Law/Member.lean). `Thr` in
front: whoever shows it along the chain. The hypothesis `P5J.AtMgA`: not shown here.

Limits. Every theorem is conditional. Nothing shows that `Thr` holds at any run. That the items
are open is the library's decision at the table's text as it stands.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Member
import Johnson.Desc.First.Att.K05SeatAccepts
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.First.Att.Door.Law.K5RestPublic
import Johnson.Desc.First.Att.Door.Law.K5ListsFull
import Johnson.Desc.First.Att.Door.Law.K5MgIsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain Claim First.S First.Pub)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers PubData pubAll onAt shapeAt
  mayWait pubSets pubRowOf leavesName pubAll_freeAbove pubAll_callerIn_att)
open VerifiableInference.Desc.First.FillK4 (isLay)
open H2K5.Door (moreOver9)
open VerifiableInference.Desc.Sound (doorsFitB_parts)
open VerifiableInference.Desc.K3 (sizedB)
open VerifiableInference.Desc.First.Att.P
open ProofFile.Honest.FirstThread (lettersAt Script WtF honest noStrs)
open P5J (AtMgA mgAtAll TS CellsM)

/-! ## 1 General in the meaning -/

/-- At the kind's place no count of rows may wait. CONDITIONAL: pl is piece 3 of an attention
segment of the list. -/
theorem mayWait_k5 {links : List ModelPart} {m : Nat} {pl pl' : Place} (Ix : K5Place links m pl pl') :
    mayWait links pl = false := by
  unfold mayWait
  rw [Ix.link]
  simp only [Ix.sub, Ix.piece, Option.getD_some]
  cases (m == 0) <;> rfl

/-- **From the table's promise in front of the kind's place: the state is ready.** GENERAL in the
meaning Mg. CONDITIONAL: Mg's public tests are the composed ones over data Dt in which segment m is
an attention segment, with the caller's first slot `first` and the ledger's number of slots
`nsPlan`; the kind's slots fit; the three items are open; the state bears no mark. -/
theorem readyO_of_onAt {Pp W : Type} {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart} {m : Nat}
    {pl pl' : Place} {O : List Item} {Q : List First.Pub} {π : Pp} {s : First.S} {y : Strs}
    (Dt : PubData) (base : First.Pub → Pp × First.S → Bool) (hpub : Mg.pub = pubAll Dt base)
    (Ix : K5Place links m pl pl') (hatt : Dt.d5.isAtt m = true) (hlay : isLay Dt.links m = false)
    {first nsPlan : Nat} (hf : Dt.d5.first? m = some first) (hn : Dt.nsOf m = some nsPlan)
    (p : Par) (hfit : first + slotsOf (script p.own) ≤ nsPlan)
    (qL : First.Pub.ledger m ∈ Q) (qF : First.Pub.freeAbove m ∈ Q) (qC : First.Pub.callerIn m ∈ Q)
    (hu : s.failed = none) (hon : onAt N Mg links (some pl) O Q (π, s) y) : ReadyO p s := by
  have hsh := onAt_shape hon hu
  obtain ⟨a, e⟩ := H2K5.Door.k5_here Ix hsh
  have hp := onAt_pub hon hu
  have qL' : s.fork?.any sizedB = true := by
    have h1 := hp _ qL
    rw [hpub] at h1
    exact h1
  have qF' : freeAboveB nsPlan s = true := by
    have h1 := hp _ qF
    rw [hpub, pubAll_freeAbove, hn] at h1
    exact ((H2K5.Door.keeper_freeAbove_is nsPlan s).trans
      (H2K5.Door.freeAboveB_is nsPlan s)).symm.trans h1
  have qC' : k5CallerIn3 first s = true := by
    have h1 := hp _ qC
    rw [hpub, pubAll_callerIn_att Dt base m hlay hatt, hf] at h1
    exact h1
  obtain ⟨h5, hg, R⟩ := callerIn_at e (callerIn_of3 e qL' qF' qC' hfit)
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 hg
  refine ⟨⟨a, g, e, hg, h5, R.sized, by rw [R.next]; exact R.free⟩, hu, ?_⟩
  unfold shapeAt at hsh
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hsh
  rcases hsh.1.2 with h1 | h1
  · exact h1
  · rw [mayWait_k5 Ix] at h1
    cases h1

/-! ## 2 At the library's own letters -/

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

/-- The first chain's `Thread` at the library's own letters. -/
noncomputable abbrev thrAt : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr)
    (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst :=
  (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread

/-- The kind's place of group g and the next, in the written lists. CONDITIONAL: g is below 12. -/
theorem place_k5 {g : Nat} (hg : g < 12) :
    K5Place P5J.At.links (2 * g + 1) ⟨1, some (2 * g + 1), 3, .K5⟩ ⟨1, some (2 * g + 1), 4, .K1⟩ :=
  ⟨rfl, rfl, H2K5.Door.sub_full hg, rfl, rfl⟩

/-- **What the kind's row asks is open at its border**, at the closed list of extra public tests. By
two of the library's decisions on the written lists: the items are open at a wider list, and what is
open there and is none of the wider list's own names is open here. CONDITIONAL: g is below 12. -/
theorem open_k5 {g : Nat} (hg : g < 12) (q : First.Pub)
    (hq : q ∈ [First.Pub.ledger (2 * g + 1), .look (2 * g + 1), .left (2 * g + 1),
      .linkFresh (2 * g + 1), .freeAbove (2 * g + 1), .callerIn (2 * g + 1)]) :
    q ∈ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[borderOf g]?.getD
      [] := by
  have hw : H2K5.Door.isWideQ q = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have ha : q ∈ (pubRowOf P5J.At.links ⟨1, some (2 * g + 1), 3, .K5⟩).asks := by
    rw [(k5_pubRow (place_k5 hg)).1]
    exact hq
  rcases (doorsFitB_parts (H2K5.Door.doors_full hg)).2.1 q (H2K5.Door.asks_full hg q ha) with
    h1 | h1
  · rw [hw] at h1
    cases h1
  · exact h1

/-- **FROM `Thr` IN FRONT OF THE KIND's MEMBER OF GROUP g: THE STATE IS READY.** CONDITIONAL:
under the hypothesis h, the plan's facts, and `Thr` at the border: none is shown here. -/
theorem readyO_of_thr {g : Nat} (hg : g < 12) {a : Attention.Plan} (Pl : PlanAt Zp g a)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      k s m E) : ReadyO (parAt Zp g a) s := by
  obtain ⟨hf0, hon0⟩ := hT.2.2.1
  have hu : s.failed = none := Option.isNone_iff_eq_none.1 hf0
  have hpl : P5J.At.ps[borderOf g]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ :=
    H2K5.Door.place_full hg
  have hm : (honest (mgAtAll h) ans test).more = (moreOver9 {}).strike leavesName :=
    H2K5.Door.hm_all h
  have hon : onAt (P5J.At.N Zp cF) (honest (mgAtAll h) ans test) P5J.At.links
      (P5J.At.ps[borderOf g]?)
      (((VerifiableInference.Desc.First.openSets P5J.At.links P5J.At.ps
        (VerifiableInference.Desc.First.start P5J.At.links))[borderOf g]?).getD [])
      (((pubSets (honest (mgAtAll h) ans test).more P5J.At.links P5J.At.ps)[borderOf g]?).getD [])
      (m.st.input.x.pub, s) noStrs := hon0
  rw [hpl, hm] at hon
  have Ix := place_k5 hg
  have T := H2K5.Door.dataIs_all h (2 * g + 1)
  obtain ⟨x₁, hx⟩ := Pl.look
  exact readyO_of_onAt (Mg := honest (mgAtAll h) ans test) h.𝔇.pubD _ (H2K5.Door.hpub_all h) Ix
    (H2K5.Door.isAtt_of _ (by rw [T.d5links]; exact Ix.sub))
    (H2K5.Door.att_not_lay (by rw [T.links]; exact Ix.sub))
    (H2K5.Door.first_at _ (by rw [T.d5W]; exact Pl.planIs) (by rw [T.d5W]; exact Pl.p4)
      (by rw [T.d5W]; exact Pl.plan) (by rw [T.d5W]; exact hx))
    (H2K5.Door.nsOf_all h hg Pl.plan) (parAt Zp g a) Pl.fits
    (open_k5 hg _ (by simp)) (open_k5 hg _ (by simp)) (open_k5 hg _ (by simp)) hu hon

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.mayWait_k5
#print axioms ProofFile.Honest.K5.readyO_of_onAt
#print axioms ProofFile.Honest.K5.place_k5
#print axioms ProofFile.Honest.K5.open_k5
#print axioms ProofFile.Honest.K5.readyO_of_thr
