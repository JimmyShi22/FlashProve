-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/SlotsOfStand.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: K4Right is a hypothesis. That it can hold: no
example is known. AT A THREAD NONE OF WHOSE STEPS ACCEPTS, K4Right AND THE THREE CONCLUSIONS HOLD
EMPTILY. IN THE FIRST GROUP, AT A PLAN THAT HAS NOT THE LIBRARY's OWN SIZES, NO EXAMPLE OF K4Right
CAN COME BY THE LAWS THAT LIE BESIDE THIS FILE: the one law for the field emb stands at these sizes
alone (Law/W/EmbRight.lean). THE LIKE HOLDS IN EVERY GROUP for idn, hot and back's second half (the
batched sumcheck's own claim): at which sizes the laws for these stand, and which shapes K4Plan's
field sw bars, says the head of Law/W/ItemRightOf.lean. The left half, `opened_left`
(Law/SlotsTrue.lean), is called here; it is proved, under K4Stand. What each field of ItemRight
rests on: the heads of Johnson/Road/K4/W/Item.lean and Law/W/Halves.lean. By a walk of import lines
the closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms,
Bcs), through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under
Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness
or on any other property. No property is claimed.

The hypothesis `K4Slots` (Law/W/ValuesOfPlan.lean), at any proposition At on the state in front of
the member, from the hypotheses of the left half (K4Seated, K4Sits, K4MaskTieAt at each state of
At), K4Front, nine public facts on the plan (K4Plan) and `K4Right`: at every state behind the
member's step, the right half of Opened and OpenedBack with the fields of ItemSlots that do not
speak of a slot's honest word. With it K4Values and the share of the debt `Exchange` at the member's
own item. No statement here reads the structure Thread's proposition Thr: who pays a hypothesis from
Thr asks "At gives Thr" by name. Where the names are defined: the head of Law/W/Values.lean;
K4Seated: Law/Seated.lean; K4MaskTieAt: Law/ScriptAt.lean; K4SizedAt: Law/RowBatch.lean.

  `ItemRight h D tl P Q o F₀ F₁ mask Mm w hh ds seen`   at one state: OpenedRight in the world
      behind "front"; idn, hot, own, look as in ItemSlots; behind "back": OpenedRightBack and
      OwnBack.
  `K4Right T At b …`   ItemRight at the table's data and the honest side's input, at every such
      state.
  `slots_of_right`   K4Slots T At b M own rdOf tl p h D.
  `values_of_right`   K4Values. CALLED BY NOBODY: it stays as one of the four statements that end in
      K4Values, which the head of Law/Kept.lean lists.
  `k4_own_share_of_right`   the share.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ValuesOfPlan
import Johnson.Desc.ProofFile.Honest.K4.Law.W.HalvesNums
import Johnson.Road.K4.W.KeptEnv
import Johnson.Desc.First.K4.LedgerKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later)
open OnBytes.Road (sclOf cellsOf cellsAt pt)
open OnBytes.Road.K4 (kept_atS entryTrue)
open OnBytes.Road.K4.W (K4Plan IdnHold HotPoint OwnFront OwnBack LookThree kept_env)
open OnBytes.Desc.First.K4 (Par seatS planesParts formsBack formsFrontWith_later formsBack_later)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ)
open VerifiableInference.Desc.Plain.K04 (frontRun)

/-- **The right half and the other fields, at one state.** w: the honest side's input; hh: the
challenges heard in front of the member; ds: the member's own; seen: the rounds shown in front of
the batched sumcheck. This defines a hypothesis; the definition claims nothing. -/
structure ItemRight (h : Layer.Shape) (D : Dim) (tl : HTailF2) (P : Layer.Pub) (Q : K4Pub)
    (o : Own)
    (F₀ F₁ : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Road.Mats Cb.Gl.E) (w : K4In)
    (hh ds : List Fmt.Drawn) (seen : Seen) : Prop where
  /-- the reading of each honest word is the right side of Opened's field, behind "front" -/
  right : OpenedRight (scl := sclOf h o.v.sc o.v.g o.v.y.Lam)
    (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) Q o w hh ds D (cellsOf D (cellsAt o.v.y Mm))
  /-- the norms' identities at the cells -/
  idn : IdnHold (scl := sclOf h o.v.sc o.v.g o.v.y.Lam) D (cellsOf D (cellsAt o.v.y Mm))
  /-- the selector's identity, extended over the positions, at the lookup's token point -/
  hot : HotPoint D (cellsOf D (cellsAt o.v.y Mm)) (pt Reading.gl o.H.ztF)
  /-- the own claims of four sumchecks -/
  own : ∀ sh, ((Array.range (4 * P.y.NI)).mapM fun i => F₀.shown (o.H.tV.sEnd + i)) = some sh →
    OwnFront Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) P o sh
  /-- the lookup's three claims -/
  look : ∀ pp, planesParts o.v o.H.fo = some pp →
    LookThree Reading.gl (F₁.worldOf Reading.gl mask (entryTrue tl o Mm)) o pp
  /-- behind "back": the right half at its two slots, and the two own claims -/
  back : ∀ fs₂ F₂, formsBack o F₁ = some (fs₂, F₂) →
    OpenedRightBack (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) Q o w hh ds seen ∧
      OwnBack Reading.gl (F₂.worldOf Reading.gl mask (entryTrue tl o Mm)) o

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}

/-- **ItemRight AT EVERY STATE BEHIND THE MEMBER's STEP**, at every continuation of the challenges.
At: which states in front of the member are meant. This defines a hypothesis; the definition claims
nothing. -/
def K4Right (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) (b : Nat)
    (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) (h : Layer.Shape) (D : Dim) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    ItemRight h D tl p.P Q o (seatS.fork s') F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))
      (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds
      (m.shown.plus (roundsOf (y.1.take (rJ4 Q.P Q.g))))

section
variable {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
  {At : Coins Bk → First.S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub}
  {M : First.S → Bound GQ → Road.Mats GQ} {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated}
  {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par}
  {h : Layer.Shape} {pc : List (List String)} {D : Dim}

/-- **K4Slots from the two halves.** CONDITIONAL: on the left half's hypotheses (hSeat, hSit, hMask;
K4SizedAt at the one state in front comes from hF's clause asks), on hF, on A and on hR. -/
theorem slots_of_right
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hR : K4Right T At b cells weights tokens look Q M own rdOf tl p h D) :
    K4Slots T At b M own rdOf tl p h D := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' Aq hseg o fs₁ F₁ ho hf
  have Se := hSeat blk hblk
  obtain ⟨eP, _, eg, _, _⟩ := Se.own
  obtain ⟨_, _, Ak⟩ := (hF blk hblk k s m E ds y cols s' hA hd hS ds').asks
  have Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' Aq o :=
    ⟨Se, hSit, Ak.sized, hMask k s m E hA, hS, hseg, ho⟩
  have R := hR blk hblk k s m E ds y cols s' hA hd hS ds' Aq hseg o fs₁ F₁ ho hf
  have L1 : Later Aq.F F₁ := by
    rw [← seg_fork hseg ho]
    exact formsFrontWith_later hf
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  obtain ⟨vg, vy⟩ := kept_env (kept_atS hdec) A ho
  have N : HalvesNums Q o D :=
    halvesNums_of_plan (hS := h) (pc := pc) (tl := tl) (by rw [← eP, ← eg]; exact A)
      (by rw [← eP]; exact vy) (by rw [← eg]; exact vg)
  exact
    { opened := by
        rw [eP]
        exact opened_of_halves (scl := sclOf h o.v.sc o.v.g o.v.y.Lam)
          (opened_left Z ds' F₁ L1 _) R.right N
      idn := R.idn
      hot := R.hot
      own := R.own
      look := R.look
      back := fun fs₂ F₂ hb =>
        ⟨openedBack_of_halves (opened_left Z ds' F₂ (L1.trans (formsBack_later hb)) _)
          (R.back fs₂ F₂ hb).1 N, (R.back fs₂ F₂ hb).2⟩ }

/-- **The values.** CONDITIONAL: as slots_of_right. -/
theorem values_of_right
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hR : K4Right T At b cells weights tokens look Q M own rdOf tl p h D) :
    K4Values T At b M own rdOf tl p :=
  values_of_slots hSit hF A (slots_of_right hSeat hSit hMask hF A hR)

/-- **THE SHARE OF `Exchange` AT THE MEMBER's OWN ITEM.** CONDITIONAL: as values_of_right, and on
the table's parameters. -/
theorem k4_own_share_of_right {iOwn iPl iJo : T.ι} {rest : List T.ι}
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf)
    (hSeat : ∀ blk, T.bs[b]? = some blk → K4Seated T b cells weights tokens look Q p blk)
    (hSit : K4Sits T b p) (hMask : ∀ k s m E, At k s m E →
      K4MaskTieAt T cells weights tokens look Q own rdOf k s m)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hR : K4Right T At b cells weights tokens look Q M own rdOf tl p h D) :
    ShareAt T At b [iOwn] :=
  k4_own_share_of_slots Tb hSit hF A (slots_of_right hSeat hSit hMask hF A hR)

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.slots_of_right
#print axioms ProofFile.Honest.K4.W.values_of_right
#print axioms ProofFile.Honest.K4.W.k4_own_share_of_right
