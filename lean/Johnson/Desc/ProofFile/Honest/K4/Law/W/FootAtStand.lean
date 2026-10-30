-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FootAtStand.lean: CONDITIONAL.

Not shown here. THAT FootRest HOLDS ANYWHERE: every field of it is a hypothesis HERE; no example is
known. Laws for some of them lie in other files; none of these is called here: ownBack's field merge
(Law/OwnAtStand.lean, under the start of the merge's sumcheck); ownBack's field stack (`stack_led`,
Law/StackLed.lean, under the start; of the start's four sentences, Law/StackStart.lean, the lookup's
join has no law but at the library's full size); idn and hot (Law/W/IdnHead.lean,
Law/W/HotStand.lean: AT THE LIBRARY's FULL SIZE ALONE AND AT THE FORMAT's EARLIER HASH ALONE); emb
(`emb_at`, Law/W/ItemRightOf.lean: AT THE LIBRARY's OWN SIZES ALONE, under a hypothesis on the
witness). K4Plan's FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES, routed
experts among them: AT EVERY OTHER SHAPE THESE STATEMENTS SAY NOTHING. K4Seated's field fits (the
public test k4Fits) is spent: at shapes that do not fit they say nothing. TWO HYPOTHESES TIE ONE
LETTER: K4CellsTieAt, with the equation hM, ties the matrices to the input's cells off the planes'
matrix; the field look ties the planes' matrix to what the lookup's side holds. The tie on the
tokens is asked by no hypothesis here by name: it stands inside emb and ownBack.
k4_own_share_of_foot HAS ELEVEN HYPOTHESES: the table's parameters; that the states meant are states
of the structure Thread's proposition Thr; K4Seated; K4Sits; K4MaskTieAt, K4LookTieAt and
K4CellsTieAt at each state; that the matrices are read off the data (hM); K4Front, with its open
sentences; K4Plan; K4FootRest. AT A THREAD NONE OF WHOSE STEPS ACCEPTS, K4FootRest AND THE
CONCLUSIONS HOLD EMPTILY. By a walk of import lines the closure holds seven modules under
Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), through Law/SlotsTrue.lean's
imports; none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none of the names
Honest…, Both…, PassH…. Nothing on soundness, on completeness or on any other property.
No property is claimed.

Of the ten fields of `RightFoot` (Law/W/ItemRightOf.lean) five are paid at a state behind the
member's step, and half of a sixth: cells by `cellsAre_at` (Law/CellsAt.lean); makers by
`makersNorms_at` (Law/W/MakersAt.lean), with the size of the norms' token point
(Law/W/StandHear.lean); rows by `rowFields_pub` (Johnson/Road/K4/C/RowFieldsPub.lean), with the
structure that the forms read by `env_is` (Law/ClaimsAre.lean); terms (the fields rt, sc, sel of
OpenedRight) by `right_terms_of` (Law/W/RightTermsOf.lean), its point by `terms_point`
(Law/W/TermsPt.lean), the honest side's two returns by `termsJob_foot` (Law/W/MakersReturn.lean);
own (the own claims of four sumchecks) by `own_at` (Law/W/OwnAtFoot.lean); of back the right half at
its two slots by `back_at` (Law/W/BackAtStand.lean), the honest side's two returns by `stackJob_at`
(Law/W/MakersReturn.lean). What is left is `FootRest`: four fields of RightFoot, to the letter, and
the two own claims behind "back". With it the share of the debt `Exchange` at the member's own item,
in one statement.

  `FootRest h D tl Q o F₀ F₁ mask Mm w hh ds`   what is left as a hypothesis at one state: five
      fields.
  `rightFoot_at`   RightFoot from FootRest, at a state behind the member's step.
  `K4FootRest T At b …`   FootRest at every such state.
  `k4Foot_of_rest`   K4Foot from K4FootRest.
  `k4_own_share_of_foot`   ShareAt T At b [iOwn] from K4FootRest and ten hypotheses more.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ItemRightOf
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MakersAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MakersReturn
import Johnson.Desc.ProofFile.Honest.K4.Law.W.StandHear
import Johnson.Desc.ProofFile.Honest.K4.Law.W.BackAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OwnAtFoot
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightTermsOf
import Johnson.Desc.ProofFile.Honest.K4.Law.W.TermsPt
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre
import Johnson.Desc.ProofFile.Honest.K4.Law.CellsAt
import Johnson.Road.K4.C.RowFieldsPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Tape paired)
open OnBytes.Road (sclOf cellsOf cellsAt pt)
open OnBytes.Road.K4 (kept_atS entryTrue LedG laySizes_of_layout)
open OnBytes.Road.K4.W (K4Plan K4Ground IdnHold HotPoint OwnBack LookLeft kept_ground uEOf)
open OnBytes.Road.K4.C (CellsAre rowFields_pub normsPlan_of_plan sides_fields)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsFrontWith)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim xS)
open VerifiableInference.Desc (Block Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ matsOfData)
open VerifiableInference.Desc.Plain.K04 (frontRun)

/-- **What is left as a hypothesis at one state.** The letters are ItemRight's. This defines a
hypothesis; the definition claims nothing. -/
structure FootRest (h : Layer.Shape) (D : Dim) (tl : HTailF2) (Q : K4Pub)
    (o : Own) (F₀ F₁ : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Road.Mats Cb.Gl.E) (w : K4In)
    (hh ds : List Fmt.Drawn) : Prop where
  /-- the field emb of OpenedRight, in its own text -/
  emb : o.v.g = 0 → Reading.gl.val (wEmb Q w hh ds) =
    ∑ kh ∈ Finset.range (o.v.y.h.d / o.v.y.S2),
      Reading.gl.val ((eqTab o.H.tkh).getD kh zeroE) *
        ∑ r ∈ Finset.range (2 ^ o.v.y.ls), Blocks.eqN o.v.y.ls 0 (pt Reading.gl o.H.ZE) r *
          Blocks.ext D.lT
            (fun p => xS D (cellsOf D (cellsAt o.v.y Mm)) 0 (kh * 2 ^ o.v.y.ls + r) p)
            (uEOf Reading.gl o.v o.H)
  /-- the norms' identities at the cells -/
  idn : IdnHold (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm))
  /-- the selector's identity, extended over the positions, at the lookup's token point -/
  hot : HotPoint D (cellsOf D (cellsAt o.v.y Mm)) (pt Reading.gl o.H.ztF)
  /-- what is left of what the lookup's three claims ask -/
  look : LookLeft tl o F₀ mask Mm
  /-- behind "back": the two own claims -/
  ownBack : ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
    OwnBack Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **RightFoot FROM FootRest, AT A STATE BEHIND THE MEMBER's STEP.** CONDITIONAL: on every
hypothesis named. -/
theorem rightFoot_at {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    {b : Nat} {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
    {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}
    {h : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true) (hLk : K4LookTieAt look Q s m)
    (AQ : K4Plan h pc Q.P Q.g tl D)
    {r : List Layer.TableAt × List (Layer.TableAsk × List (ℕ × ℕ)) × ℕ}
    {pts : List (String × Array OnBytes.E)}
    (Gr : K4Ground h pc o.v Q.P.rd r tl o.H o.hd o.hd2 pts o.funs D) {Mm : Road.Mats Cb.Gl.E}
    (C : CellsAre Q (k4Wit Q cells weights tokens (look Q) m.st.input) Mm)
    (ds' : List Fmt.Drawn) {rows : Bool} {P' : Layer.Pub} {g' : ℕ} {fs₁ : Array Aff} {F₁ : Fork}
    (hf : formsFrontWith rows P' g' o A.F = some (fs₁, F₁))
    (Fl : FootRest h D tl Q o A.F F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask Mm
      (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) :
    RightFoot h D tl Q.P Q o A.F F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask Mm
      (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds
      (m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g)))) := by
  have Ow := own_at Z hT hd hLk AQ Gr C ds' hf
  obtain ⟨SD, e4, data, ends, _⟩ :=
    stackJob_at Z hT (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q))
  have Bk4 := fun (Wd : World Cb.Gl.E) (hW : Wd.entry = entryTrue tl o Mm) =>
    back_at Z hT hLk AQ Gr C data ends hW
  obtain ⟨hd2, tT, ⟨F, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, eg,
    ey⟩ := stand_led Z
  have elt : Q.P.y.h.lt = D.lT := by rw [(laySizes_of_layout AQ.lay).shape, AQ.sized.lT]
  have l3 : k4StartAt Q 3 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have l2 : k4StartAt Q 2 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have l1 : k4StartAt Q 1 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have hmats : matsOf Q = Road.matsR o.v.y o.v.g := by rw [ey, eg]; exact AQ.tails
  obtain ⟨Fh, hH⟩ := stand_hear Z
  have hh := k4_heard_front Z.seat hT
  have e := stand_look Z
  obtain ⟨g, _, h2, hzx, hzk, _⟩ := hLk
  rw [h2] at e
  obtain rfl := Option.some.inj e
  have hvAt : ∀ n, OnBytes.Desc.First.K4.Honest.envOf Q
      (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (m.st.heard ++ ds.take n)) = some o.v := fun n =>
    env_is hH _ (by rw [at_look _ _ ds hh]; exact hzk)
  obtain ⟨S, J, hS, hJ⟩ := termsJob_foot Z hT
  obtain ⟨_, _, _, hvS, _⟩ := sides_fields hS
  have eSv : S.v = o.v := Option.some.inj (hvS.symm.trans (hvAt (rJ3 Q.P Q.g)))
  exact
    { cells := C
      makers := makersNorms_at Z hT hd ((PV_size L hD l1).trans elt) elt
      rows := rowFields_pub Gr (hvAt _) hmats rfl C (normsPlan_of_plan AQ).NI
        ((rtV_size L hD l2).trans elt)
      emb := Fl.emb
      terms := right_terms_of Gr hS hJ ey.symm eg.symm hmats
        ⟨by rw [eSv], by rw [eSv], by rw [eSv], by rw [eSv]⟩ L.kTT
        (terms_point L hD l3 hJ (by rw [eSv]; exact ey) _ L.kTT)
        (by
          show (ptsOf Q _ (m.st.heard ++ ds.take (rJ3 Q.P Q.g))).fo.zx = _
          rw [at_look _ _ ds hh]
          exact hzx)
        C rfl
      idn := Fl.idn
      hot := Fl.hot
      own := Ow
      look := Fl.look
      back := fun fs₂ F₂ hb => ⟨Bk4 _ rfl, Fl.ownBack fs₂ F₂ hb⟩ }

/-- **FootRest AT EVERY STATE BEHIND THE MEMBER's STEP**, at every continuation of the challenges.
The binders are K4Right's. This defines a hypothesis; the definition claims nothing. -/
def K4FootRest (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) (h : Layer.Shape) (D : Dim) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    FootRest h D tl Q o (seatS.fork s') F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
      (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
  {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}
  {M : First.S → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated}
  {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par}
  {h : Layer.Shape} {pc : List (List String)} {D : Dim} {names : Array (Nat × String)}

/-- **K4Foot FROM K4FootRest.** CONDITIONAL: on every hypothesis named. -/
theorem k4Foot_of_rest (hAt : ∀ k s m E, At k s m E → Thr T b k s m E)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, At k s m E → K4LookTieAt look Q s m)
    (hCells : ∀ k s m E, At k s m E →
      K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m)
    (hM : ∀ t Dt, M t Dt = matsOfData tl names Dt)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hR : K4FootRest T At b cells weights tokens look Q M own rdOf tl p h D) :
    K4Foot T At b cells weights tokens look Q M own rdOf tl p h D := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' Aq hseg o fs₁ F₁ ho hf
  have Se := hSeat blk hblk
  obtain ⟨eP, _, eg, _, _⟩ := Se.own
  obtain ⟨_, _, Ak⟩ := (hF blk hblk k s m E ds y cols s' hA hd hS ds').asks
  have Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' Aq o :=
    ⟨Se, hSit, Ak.sized, hMask k s m E hA, hS, hseg, ho⟩
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  obtain ⟨r, pts, Gr⟩ := kept_ground (kept_atS hdec) A ho
  have Fl := hR blk hblk k s m E ds y cols s' hA hd hS ds' Aq hseg o fs₁ F₁ ho hf
  have AQ : K4Plan h pc Q.P Q.g tl D := by rw [← eP, ← eg]; exact A
  have C := cellsAre_at Se hSit hS hseg ho (hCells k s m E hA) hM (AQ.tails.trans AQ.mats.symm)
    AQ.NM ds'
  rw [eP] at Gr ⊢
  rw [seg_fork hseg ho] at Fl hf ⊢
  exact rightFoot_at Z (hAt k s m E hA) hd (hLook k s m E hA) AQ Gr C ds' hf Fl

/-- **THE SHARE OF `Exchange` AT THE MEMBER's OWN ITEM, FROM K4FootRest.** CONDITIONAL: on every
hypothesis named. -/
theorem k4_own_share_of_foot {iOwn iPl iJo : T.ι} {rest : List T.ι}
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf)
    (hAt : ∀ k s m E, At k s m E → Thr T b k s m E)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hLook : ∀ k s m E, At k s m E → K4LookTieAt look Q s m)
    (hCells : ∀ k s m E, At k s m E →
      K4CellsTieAt T cells weights tokens look Q tl names own rdOf k s m)
    (hM : ∀ t Dt, M t Dt = matsOfData tl names Dt)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hR : K4FootRest T At b cells weights tokens look Q M own rdOf tl p h D) :
    ShareAt T At b [iOwn] :=
  k4_own_share_of_right Tb hSeat hSit hMask hF A
    (k4Right_of hAt hSeat hSit hMask hF A
      (k4Foot_of_rest hAt hSeat hSit hMask hLook hCells hM hF A hR))

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.rightFoot_at
#print axioms ProofFile.Honest.K4.W.k4Foot_of_rest
#print axioms ProofFile.Honest.K4.W.k4_own_share_of_foot
