-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormBehindTwo.lean: THE FIRST SEGMENT's OPENING AND W's
SENDING, EACH AS THE WHOLE MEMBER OF THE FIRST CHAIN (in scope the numbers 2 and 356): WHAT STANDS
BEHIND ITS ACCEPTING STEP OF THE TABLE's PROMISE ON THE VERIFIER's STATE, AT ONE STATE IN FRONT. The
opening's member is the kind K1's sub-protocol with the frame's step joined behind it
(K1.openingZero, Johnson/Desc/K1/Law/OpeningZero.lean); W's is K1's sending with the kind K13's rows
behind it (K13.atM4, Johnson/Desc/K13/AtS.lean). No thread and no prover occurs. General in the
numbers N, the meaning Mg and the public part z. Statements and proofs.

  xk_step_pt: kind-free: what one sub-protocol owes at one state (IM.HandsPt,
    Johnson/IMR/HandsPoint.lean) gives the six tests at the next border behind an accepting step
    from that state.
  handsPt_G_pub, handsPt_M4_pub: IM.HandsPt, ALL SIX FIELDS, AT THE TEST EPub
    (Johnson/Desc/AtSeats/HandsMore.lean), at the two whole sub-protocols. The library has the like
    at every state in front (hands_G_pub, hands_M4_pub, the same file): there the table's letters
    are asked as the structures FillG and FillM4, whole (Johnson/Desc/K13/Law/AtTableFirst.lean,
    Johnson/Desc/K13/Law/AtTableW.lean): seven and eighteen fields, of which these proofs spend
    three and seven; the others speak of what a public item says beside its test, of strings, of a
    witness, of one sample. Here just the fields that are spent are taken, as arms at the one state
    in front. The proofs are the library's, with these letters turned.
  xk_opening_at: so the six tests at P1K2.EQ (Johnson/P1K2R/TieTwo.lean) at border 3 behind an
    accepting step of the WHOLE joined member at number 2, in the goals' scope: by joined_under
    (Johnson/Desc/AtSeats/BackAtThree.lean). xk_W_at: the like at 356 and 357, at whatever stands
    under the lot's own sub-protocol: by lot4_under (Johnson/Desc/K13/Law/LotSits.lean).
  held_W_at: the samples are held behind W's member: by the table's row (RowM4.two): behind, the
    index masks' and W's alone are sampled.

F, y₀: ANY FRAME WITH ANY STRING OF IT WILL DO: an idle argument of three lemmas of the library on
the kind K13's tests, which are stated with a string and read none. No statement's end names them.

Limits. NOT ONE PREMISE IS SHOWN AT ANY NUMBERS OR MEANING: the tests on the table's row (RowG,
RowM4) · at the opening the groups' count and the own seats' test at the state in front · the arms
on the meaning's public tests · hPl. On the samples behind the opening nothing is shown: no field of
RowG says which are sampled there. xk_opening_at stands in the goals' scope, at files that are read,
under IM.Open at the earlier hash OnBytes.secondHashFunction. That a member accepts anywhere is not shown.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormBehind
import Johnson.Desc.AtSeats.BackAtThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Seat (zeroAt fvsOf)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning samplesHeld)
open VerifiableInference.Desc.K13 (Where atM4)
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open IM (linksW placesW)
open ProofFile (Cl)
open HashBuild (EPub epub_of epub_parts handsPt_of_all hands_G hands_M4 tied_of_pin joined_under)

variable {Pp W : Type}

/-- **From what is owed at one state to the six tests at the next border.** -/
theorem xk_step_pt {N : Numbers} {links : List ModelPart} {ps : List Place} {E : ℕ → S → Bool}
    {ft k : ℕ} {b : Block S Cl} {s s' : S} (H : IM.HandsPt N links ps E ft k b s)
    (hy : IM.Yes ft b s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK N links ps E k s = true) : IM.XK N links ps E (k + 1) s' = true := by
  unfold IM.XK IM.BK
  rw [H.shape s' hy h0 h1 hx, H.rows s' hy h0 h1 hx, H.members s' hy h0 h1 hx,
    H.book s' hy h0 h1 hx, H.more s' hy h0 h1 hx]
  rfl

/-! ## 1 The first segment's opening -/

/-- **WHAT THE OPENING's WHOLE SUB-PROTOCOL OWES, AT ONE STATE IN FRONT, AT THE TEST WITH
"in order".** -/
theorem handsPt_G_pub (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (z : Pp) (ft k : ℕ) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) (mk : List First.Pub)
    (hT : RowG N Mg.more links ps k (K1.layOf (K1.firstPar q gp)).shapes.size
      (K1.firstPar q gp).sent.size mk)
    (s₀ : S)
    (hgroups : Mg.pub .noneSent (z, s₀) = true → N.groupAt 0 = s₀.st.groups.size)
    (hown : Mg.inOrder (z, s₀) = true → First.bookAt N ps[k]? s₀ = true →
      K1.ownSeatsB N (openAt links ps (k + 1)) (K1.firstPar q gp)
        (s₀.check.frame.atMoment 0).length s₀.book.trees.size = true)
    (aOrd : ∀ s', StepG Cl q gp nm X fvs kCol (z, s₀) (z, s') →
      Mg.inOrder (z, s₀) = true → Mg.inOrder (z, s') = true)
    (aMade : ∀ s' i, StepG Cl q gp nm X fvs kCol (z, s₀) (z, s') →
      (∀ q' ∈ (First.pubSets Mg.more links ps)[k]?.getD [], Mg.pub q' (z, s₀) = true) →
      First.bookAt N ps[k]? s₀ = true → Mg.inOrder (z, s₀) = true →
      (i ∈ mk ∨ i = .indexIs ∨ i = .indexThere) → Mg.pub i (z, s') = true)
    (aRide : ∀ s' i, StepG Cl q gp nm X fvs kCol (z, s₀) (z, s') →
      (∀ q' ∈ (First.pubSets Mg.more links ps)[k]?.getD [], Mg.pub q' (z, s₀) = true) →
      First.bookAt N ps[k]? s₀ = true →
      i ∈ (First.pubSets Mg.more links ps)[k]?.getD [] → i ≠ .noneSent → Mg.pub i (z, s') = true) :
    IM.HandsPt N links ps (EPub z Mg links ps) ft k
      (K1.openingZero q gp nm X fvs kCol : Block S Cl) s₀ :=
  handsPt_of_all s₀ fun E₀ h1 h2 =>
    hands_G N Mg.more links ps E₀ ft k q gp nm X fvs kCol mk hT
      (fun s hx => by
        obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        exact hgroups ((epub_parts he).2.1 _ hT.noneSent))
      (fun s hx => by
        obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        exact hown (epub_parts he).1 (IM.xk_parts hx).2.2.2.1)
      fun s s' hy _ _ hx => by
        obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        obtain ⟨hin, hQ, _⟩ := epub_parts he
        have hbk := (IM.xk_parts hx).2.2.2.1
        obtain ⟨rs, cols, n, e⟩ := hy
        have hst : StepG Cl q gp nm X fvs kCol (z, s) (z, s') := ⟨rfl, ft, rs, cols, n, e⟩
        rw [h2]
        refine epub_of (aOrd _ hst hin) (fun i hi => ?_) fun i hi => ?_
        · rcases hT.pubs i hi with hi' | ⟨hi', hne⟩
          · exact aMade _ i hst hQ hbk hin (Or.inl hi')
          · exact aRide _ i hst hQ hbk hi' hne
        · rcases hT.tied i hi with rfl | rfl
          · exact aMade _ _ hst hQ hbk hin (Or.inr (Or.inl rfl))
          · exact aMade _ _ hst hQ hbk hin (Or.inr (Or.inr rfl))

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Fd : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE SIX TESTS AT BORDER 3, BEHIND AN ACCEPTING STEP OF THE WHOLE JOINED MEMBER AT NUMBER 2**,
in the goals' scope: from the six at border 2 and facts at that one state. -/
theorem xk_opening_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL Fd Z Bs base c A B) (N : Numbers)
    (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (G₀ : ProofFile.Ground) (mk : List First.Pub)
    (hT : RowG N Mg.more linksW placesW 2
      (K1.layOf (K1.firstPar G₀.first (K1.gpOf Z))).shapes.size
      (K1.firstPar G₀.first (K1.gpOf Z)).sent.size mk)
    {b b' : Block S Cl} (hL : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := some 0, piece := 1, kind := .K1 })
    (hj : IM.Joined Z 0 b b' { chain := 1, link := some 0, piece := 1, kind := .K1 })
    (s s' : S)
    (hgroups : Mg.pub .noneSent (z, s) = true → N.groupAt 0 = s.st.groups.size)
    (hown : Mg.inOrder (z, s) = true → First.bookAt N placesW[2]? s = true →
      K1.ownSeatsB N (openAt linksW placesW (2 + 1)) (K1.firstPar G₀.first (K1.gpOf Z))
        (s.check.frame.atMoment 0).length s.book.trees.size = true)
    (arms : ∀ X : LayPar, zeroAt Z.p.built.links Z.p.X = some X →
      (∀ t, StepG Cl G₀.first (K1.gpOf Z) b.name X (fvsOf Z.p.built.links) Z.first.lin.kCol
          (z, s) (z, t) → Mg.inOrder (z, s) = true → Mg.inOrder (z, t) = true) ∧
      (∀ t i, StepG Cl G₀.first (K1.gpOf Z) b.name X (fvsOf Z.p.built.links) Z.first.lin.kCol
          (z, s) (z, t) →
        (∀ q' ∈ (First.pubSets Mg.more linksW placesW)[2]?.getD [], Mg.pub q' (z, s) = true) →
        First.bookAt N placesW[2]? s = true → Mg.inOrder (z, s) = true →
        (i ∈ mk ∨ i = .indexIs ∨ i = .indexThere) → Mg.pub i (z, t) = true) ∧
      ∀ t i, StepG Cl G₀.first (K1.gpOf Z) b.name X (fvsOf Z.p.built.links) Z.first.lin.kCol
          (z, s) (z, t) →
        (∀ q' ∈ (First.pubSets Mg.more linksW placesW)[2]?.getD [], Mg.pub q' (z, s) = true) →
        First.bookAt N placesW[2]? s = true →
        i ∈ (First.pubSets Mg.more linksW placesW)[2]?.getD [] → i ≠ .noneSent →
        Mg.pub i (z, t) = true)
    (hy : IM.Yes ft b s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK N linksW placesW (P1K2.EQ Mg linksW placesW z) 2 s = true) :
    IM.XK N linksW placesW (P1K2.EQ Mg linksW placesW z) (2 + 1) s' = true := by
  rw [← epub_eq] at hx ⊢
  obtain ⟨X, hX, hu⟩ := joined_under hS hR O hL hp hj
  obtain ⟨a1, a2, a3⟩ := arms X hX
  exact xk_step_pt ((handsPt_G_pub N Mg linksW placesW z ft 2 G₀.first (K1.gpOf Z) b.name X
    (fvsOf Z.p.built.links) Z.first.lin.kCol mk hT s hgroups hown a1 a2 a3).under hu) hy h0 h1 hx

end

/-! ## 2 W's sending -/

/-- **WHAT W's WHOLE SUB-PROTOCOL OWES, AT ONE STATE IN FRONT, AT THE TEST WITH "in order".** F, y₀:
any frame and any string of it: an idle argument. -/
theorem handsPt_M4_pub (F : Frame) (y₀ : F.E.Str) (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (z : Pp) (ft k : ℕ) (P : Where) (P' : K1.Par)
    (hT : RowM4 N Mg.more links ps k (K1.layOf P').shapes.size P'.sent.size)
    (hPl : wSitsItem ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
      planSitsB P P' = true ∧ planSeatB N ps[k]? P' = true)
    (s₀ : S)
    (fOk₀ : Mg.pub .frontOk (z, s₀) = true → frontOkB P s₀ = true)
    (fOk : ∀ s', frontOkB P s' = true → Mg.pub .frontOk (z, s') = true)
    (eL : ∀ s', evalLaidB P s' = true → Mg.pub .evalLaid (z, s') = true)
    (wS : ∀ s', wSitsB P'.codes P s' = true → wSeatB N.w s' = true →
      Mg.pub wSitsItem (z, s') = true)
    (iIs : ∀ s', StepM4 Cl P P' (z, s₀) (z, s') → Mg.pub .indexIs (z, s₀) = true →
      Mg.pub .indexIs (z, s') = true)
    (iTh : ∀ s', StepM4 Cl P P' (z, s₀) (z, s') → Mg.pub .indexThere (z, s₀) = true →
      Mg.pub .indexThere (z, s') = true)
    (aRide : ∀ s' q, StepM4 Cl P P' (z, s₀) (z, s') →
      (∀ q' ∈ (First.pubSets Mg.more links ps)[k]?.getD [], Mg.pub q' (z, s₀) = true) →
      First.bookAt N ps[k]? s₀ = true → q ∈ (First.pubSets Mg.more links ps)[k]?.getD [] →
      Mg.pub q (z, s') = true)
    (aOrd : ∀ s', StepM4 Cl P P' (z, s₀) (z, s') → Mg.inOrder (z, s₀) = true →
      Mg.inOrder (z, s') = true) :
    IM.HandsPt N links ps (EPub z Mg links ps) ft k (atM4 P (K1.sendAtS P') : Block S Cl) s₀ :=
  handsPt_of_all s₀ fun E₀ h1 h2 =>
    hands_M4 N Mg.more links ps E₀ ft k P P' hT fun s s' hy _ _ hx => by
      obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
      obtain ⟨hin, hQ, hTd⟩ := epub_parts he
      have hbk := (IM.xk_parts hx).2.2.2.1
      obtain ⟨rs, cols, n, e⟩ := hy
      have hst : StepM4 Cl P P' (z, s) (z, s') := ⟨rfl, ft, rs, cols, n, e⟩
      obtain ⟨r₁, r₂, gs, hd⟩ := hst.decide
      have hon := (frontOkB_iff P s y₀).1 (fOk₀ (hQ _ hT.frontIn))
      obtain ⟨hE, hFr⟩ := atM4_laid hd y₀ y₀ hon
      rw [h2]
      refine epub_of (aOrd _ hst hin) (fun q hq => ?_) fun q hq => ?_
      · rcases hT.pubs q hq with rfl | rfl | rfl | hq'
        · exact fOk _ ((frontOkB_iff P _ y₀).2 hFr)
        · exact eL _ ((evalLaidB_iff P s').2 hE)
        · have hbk' := hbk
          unfold First.bookAt at hbk'
          simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
          obtain ⟨⟨b1, b2⟩, _⟩ := hbk'
          have hp1 := (planSitsB_iff P P').1 (hPl hq).1
          have hp2 : N.w = _ := eq_of_beq (hPl hq).2
          have hs := atM4_seat hd b2 hp1.pos
          rw [b1, ← hp2] at hs
          exact wS _ (atM4_sits hd y₀ hon hp1) hs
        · exact aRide _ q hst hQ hbk hq'
      · rcases hT.tied q hq with rfl | rfl
        · exact iIs _ hst (hTd _ (tied_of_pin hT.pinIn _ (Or.inl rfl)))
        · exact iTh _ hst (hTd _ (tied_of_pin hT.pinIn _ (Or.inr rfl)))

/-- **THE SIX TESTS AT BORDER 357, BEHIND AN ACCEPTING STEP OF WHATEVER STANDS UNDER THE LOT's OWN
SUB-PROTOCOL AT W's PLACE**: from the six at border 356 and what handsPt_M4_pub ends in, at that
one state, at every message that the shape gives for W. -/
theorem xk_W_at (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (Z : ProofFile.Pub)
    (G₀ : ProofFile.Ground) {c b' : Block S Cl}
    (hL : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := none, piece := 4, kind := .K1 })
    (hc : c.UnderR b') (s s' : S)
    (all : ∀ msg, linMessageW Z.first.lin = some msg →
      IM.HandsPt N linksW placesW (EPub z Mg linksW placesW) ft 356
        (atM4 (K13.whereOf Z) (K1.sendAtS (K1.parW Z.first
          { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg)) : Block S Cl) s)
    (hy : IM.Yes ft c s s') (h0 : s.failed = none) (h1 : s'.failed = none)
    (hx : IM.XK N linksW placesW (P1K2.EQ Mg linksW placesW z) 356 s = true) :
    IM.XK N linksW placesW (P1K2.EQ Mg linksW placesW z) (356 + 1) s' = true := by
  rw [← epub_eq] at hx ⊢
  obtain ⟨L, hL, hb⟩ := hL
  obtain ⟨rfl, -⟩ := IM.lot_M4 hL hb (by rw [hp]) (by rw [hp])
  obtain ⟨msg, hm, hu⟩ := lot4_under Z G₀ b' hb
  exact xk_step_pt ((all msg hm).under (hc.trans hu)) hy h0 h1 hx

/-- **THE SAMPLES ARE HELD BEHIND W's MEMBER**, from: the index masks' and W's are held there. -/
theorem held_W_at (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (z : Pp)
    (k nT nM : ℕ) (hT : RowM4 N Mg.more links ps k nT nM) (s' : S)
    (hI : Mg.held N.index.1 N.index.2 (z, s') = true)
    (hW : Mg.held N.w.1 N.w.2 (z, s') = true) :
    samplesHeld N Mg (IM.openAt links ps (k + 1)) (z, s') = true := by
  unfold samplesHeld
  refine List.all_eq_true.2 fun u hu => ?_
  rcases hT.two u hu with rfl | rfl
  · exact hI
  · exact hW

end ProofFile.Honest.K1
