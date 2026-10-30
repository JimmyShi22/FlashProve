-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormAtTwo.lean: THE THREAD's CLAUSE `Form` BEHIND THE KIND K1's
OPENING (number 2 of the first chain's flat list), AT ProofFile's `lettersHead`, FROM THE THREAD IN FRONT
AND THE MEMBER's STEP. The column `hF` of `owesS_head_form` at number 2. Under the library's head: a
hypothesis.

  `front_two`     `unheard` and `noneSent` are open or tied at border 2: by Lean's kernel
  `pubs_thr`      where the thread holds, every public item open or tied at the border passes
  `k1_form_two`   the form at border 3

Limits. The step is a hypothesis: nothing here shows that the member accepts. Nothing on any
property. Full size, the format's second hash function.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.OpeningAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.HeldAtTwo
import Johnson.Desc.ProofFile.Honest.K1.Law.SaidAtTwo
import Johnson.Desc.K13.Law.MadeAtOpeningLook
import Johnson.Desc.K13.Law.MadeAtOpening
import Johnson.Desc.K13.Law.MadeAtOpeningSent
import Johnson.Desc.K1.Law.IndexBools
import Johnson.Desc.AtSeats.FrontG
import Johnson.Desc.AtSeats.MgGCAtBase
import Johnson.Desc.AtSeats.PlanGAtAll
import Johnson.Desc.AtSeats.PlanZeroAtAll
import Johnson.Desc.K1.Law.TiesAtAll2
import Johnson.IMR.ListsEnds
import Johnson.P1L20R.RoomFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.First (flatPlacesOf pubAll)
open VerifiableInference.Desc.Sound (MsgT linksFull moreAll mgBase)
open VerifiableInference.Desc.K13.Law (openAt StepG)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

set_option maxRecDepth 1000000 in
/-- **`unheard` and `noneSent` are open or tied at border 2.** -/
theorem front_two : ∀ q ∈ ([.unheard, .noneSent] : List First.Pub),
    q ∈ (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[2]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) 2) := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **EVERY PUBLIC ITEM THAT IS OPEN OR TIED AT THE BORDER PASSES.** -/
theorem pubs_thr {b : Nat} {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E) :
    ∀ q ∈ (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[b]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) b),
      pubAll h.𝔇.pubD (mgBase : First.Meaning ProofFile.InstPub WtF).pub q (μ.st.input.x.pub, s) =
        true := by
  intro q hq
  refine (ProofFile.Honest.Small.partsAt_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    hT).2.pub q ?_
  rw [show (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).MgP.more = moreAll from
    Sound.mgAll_more_base h.𝔇]
  exact hq

/-- **THE FORM BEHIND THE KIND K1's OPENING.** -/
theorem k1_form_two (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {blk : Block TS ProofFile.Cl} {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hblk : cF.blocksInOrder[2]? = some blk)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 2 k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (2 + 1) k s' y.2 := by
  have hT' := hT.1
  have hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form 2 k s m :=
    hT'.2.2.1
  have hlen : 2 ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hR := reach_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT'
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hP := pubs_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT'
  have hbk : First.bookAt h.𝔇.N (flatPlacesOf linksFull true)[2]? s = true :=
    (ProofFile.Honest.Small.partsAt_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      hT').2.book
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, nm, Xp, he, hX, hu⟩ := IM.first_under h.scope h.reads O
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hblk)
  obtain ⟨rs, cols', n, e'⟩ := hyes.under hu
  have hst : StepG ProofFile.Cl Bs.G₀.first (K1.gpOf Zp) nm Xp
      (Johnson.Desc.First.Walk.Seat.fvsOf Zp.p.built.links) Zp.first.lin.kCol
      (m.st.input.x.pub, s) (m.st.input.x.pub, s') := ⟨rfl, 0, rs, cols', n, e'⟩
  obtain ⟨r₁, r₂, gs, hd⟩ := hst.decide
  have es : s = ProofFile.startS Zp m.st.input.x.pub := P1L20.reach_two h.scope h.reads O hR
  have hU : First.unheardB s = true := hP .unheard (front_two _ (by simp))
  have hNS : VerifiableInference.Desc.K13.noneSentC h.𝔇.N s = true :=
    hP .noneSent (front_two _ (by simp))
  have hPl := K1.G_hPlG_atAll h hX (K1.planG_atAll h O)
  obtain ⟨pl, fo, a1, a2, a3, a4, a5, a6⟩ := hPl.place
  have hone : K1.noneSentB s = true := by
    rw [K13.Law.noneSentC_eq, Bool.and_eq_true, Bool.and_eq_true] at hNS
    exact hNS.1.1
  have hz : s.st.oracles.size = 0 := by
    have h1 := hone
    unfold K1.noneSentB at h1
    rw [Bool.and_eq_true] at h1
    exact Array.size_eq_zero_iff.2 (Array.isEmpty_iff.1 h1.1)
  obtain ⟨hsh0, hl0⟩ := frame_two_head h hR
  have hsh : s.check.frame.shape = h.𝔇.shape := by
    rw [hsh0, K1.hDsh_atAll h O (K1.pin1_atAll h)]
    show Zp.first.shape = _
    rw [← O.first]
    exact K1.hs_atAll h O (K1.pin1_atAll h)
  have hg := (Meaning.K2.recAll_reached h.scope h.reads O hR (le_refl 2)
      (by rw [Meaning.Carry.front_len h.scope h.reads O]; decide)).walk.groups
  rw [← hsh0] at hg
  have hk0 : s.check.frame.keptBefore = #[] := by
    rw [es]
    exact Meaning.K2.start_kept O.pub _
  obtain ⟨s₁, g₁, h1, -⟩ := K1.openingZero_mid hd
  obtain ⟨gg, mask, -, -, hlt⟩ := K1.firstAtS_frame Bs.G₀.first (K1.gpOf Zp) s s₁ r₁ r₂ g₁ h1
  obtain ⟨hb, hk, ho⟩ := HashBuild.frontG Bs.G₀.first (K1.gpOf Zp) h.𝔇.shape h.𝔇.N h.𝔇.links
    (flatPlacesOf h.𝔇.links true) h.𝔇.built s hz hsh hl0 hg hk0
    (K1.G_hb0_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h)) (Nat.le_of_lt hlt)
  obtain ⟨Y, hY, hYF⟩ := K1.G_hY_atAll h O Xp hX
  have hidx := K1.openingZero_makes hd hone
  have h6 : P1K2.EQ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP IM.linksW IM.placesW
      m.st.input.x.pub (2 + 1) s' = true := by
    refine six_of_nine _ (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _ s'
      (head_inOrder h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF s') ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · show First.unheardB s' = true
      unfold First.unheardB at hU ⊢
      rw [(K1.openingZero_rec hd).2.2.2.2.2.1]
      exact hU
    · exact K13.Law.openingZero_ledger hd
    · exact (First.pubAll_lookIn h.𝔇.pubD _ 0 2 false (K1.G_hdg_atAll h) _).trans
        (K13.Law.openingZero_lookIn hd _ false pl fo a1 a2 a3 a4 a5 a6 hPl.arrays)
    · exact K13.Law.openingZero_linkFresh hd _ hPl.unheard hPl.arrays
    · show (h.𝔇.pubD.nsOf 0).any (fun n => First.freeAboveB n s') = true
      rw [hPl.slots]
      exact K13.Law.openingZero_freeAbove hd
    · exact (HashBuild.sent_base h.𝔇 _).trans (K13.Law.openingZero_sentIs hd _ hb hk ho)
    · exact (HashBuild.trees_base h.𝔇 _).trans (K13.Law.openingZero_treesAre hd _
        (HashBuild.trees_zero _ _ _ _ _ Xp.X Xp.ns Y hY hYF))
    · show K13.indexIsC h.𝔇.N.indexNo s' = true
      have e4 : h.𝔇.N.indexNo = (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size - 1 := by
        rw [K1.indexNo_atAll h O (K1.pin1_atAll h) (K1.pin2_atAll h),
          K1.eG_atAll h O (K1.pin1_atAll h)]
        decide
      rw [e4]
      exact hidx.1
    · exact hidx.2
  have hxk := xk_opening_head h hblk
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
    (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _
    (head_pub_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) m.st.input.x.pub 0 hR hyes h0
    (by
      have := xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF
      rw [head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
        head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w]
      exact this)
    h6
  have hsm := samples_opening_head h hblk
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
    (head_held_smp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) m.st.input.x.pub 0 hR
    (by rw [IM.placesW_full, ← head_N_is h]; exact hbk) hyes
  rw [head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hxk hsm
  exact form_behind_of_xk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS
    (mark_opening_head h hblk 0 hyes) hxk hsm
    (pubP_three (P5J.At.X Zp) h.𝔇.sent h.𝔇.d1 h.𝔇.rw13 h.𝔇.A1 h.𝔇.cr1 _
      (head_pubP_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.front_two
#print axioms ProofFile.Honest.K1.pubs_thr
#print axioms ProofFile.Honest.K1.k1_form_two
