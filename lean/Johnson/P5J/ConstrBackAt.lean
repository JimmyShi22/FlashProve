-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ConstrBackAt.lean: THE FIFTH TIE's STATE SIDE: THE FIELD constr OF `FieldsBack`
(Johnson/Desc/Sound/ItemsRide.lean: "this part of segment m's relaxed relation holds of the witness"
goes back from the statement behind a step to the one in front), AT THE COMPOSED MEANING's CLOSED
CONSTANT `mgAtAll h`, AT EVERY SEGMENT AND EVERY PART: NO PART IS LEFT OUT. A join: calls alone.

WHAT THE SENTENCE READS OF THE STATEMENT, AT THE CONSTANT: four letters.
  the request's reader: the public part alone (`meantAt_all`,
    Johnson/Top/H0/Walk/FrameReadKeptAtAll.lean) · the decoder: the stored table's cells and not the
    verifier's state (the same; `At.noRec_decT`) · the digits' part: neither the state nor the
    strings (`digitsPartK3`'s text, Johnson/Desc/First/Look/K3FillDigits.lean) · the output head's
    parts: the request and, AT THE PART lookCallsHeard ALONE, the heard reply's token
    (`headPartK6_goesBack`, Johnson/Desc/Kinds/Law/HeadPartsGoBack.lean).
SO OF THE VERIFIER's STATE THE WHOLE FIELD READS ONE THING, AT ONE (SEGMENT, PART).

  `relC`: the public part is the same and the cells are the same. `relCH`: and the heard token.
  `req_public_at`, `dec_public_at`, `digits_back_at`, `head_back_at`, `head_back_heard_at`: a letter
    each.
  **`constr_back_at`**: over relC, at every (m, p) but (the head's segment, lookCallsHeard).
  **`constr_field_at`**: over relCH, at every (m, p): the field, at own := nothing.
  `relCH_of_relOut`, `constr_relOut_at`: so over `relOut base`
    (Johnson/Desc/Sound/RidesFields.lean).
By: `constrQAt_back` (Johnson/Desc/Sound/ConstrRides.lean), `constrQAt_back_any`
(Johnson/Desc/Sound/ConstrRidesHead.lean).

Limits. (1) THAT A STEP GIVES relC OR relCH IS NOT SHOWN HERE: it is each sub-protocol's own. The
sub-protocol that hears the reply does not give relCH; by a closed evaluation of the table's own
lists (no theorem) the item constr 24 lookCallsHeard is opened by that sub-protocol and rides past
the next one alone. (2) One field of eight. (3) It goes backward.
(4) The head h enters through the letters' types alone: none of its facts is spent. At the full size
alone. Nothing on soundness.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.TokTerms
import Johnson.Desc.Sound.ConstrRidesHead
import Johnson.Desc.Sound.RidesFields
import Johnson.Desc.Kinds.Law.HeadPartsGoBack
import Johnson.Top.H0.Walk.FrameReadKeptAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (MeantAt meantAt_all)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The public part is the same and the stored table's cells are the same. -/
def relC : ProofFile.InstPub × S → Strs → ProofFile.InstPub × S → Strs → Prop :=
  fun a y b y' => a.1 = b.1 ∧ y'.cell = y.cell

/-- And the heard reply's token is the same. -/
def relCH : ProofFile.InstPub × S → Strs → ProofFile.InstPub × S → Strs → Prop :=
  fun a y b y' => relC a y b y' ∧ a.2.heardTok? = b.2.heardTok?

/-- The constant's three parameters are the meant terms: another house's, at the head's letters. -/
theorem meant_at (h : AtMgA o Z D r Zp Np cF x) :
    ∃ rq : ProofFile.InstPub → TReq, MeantAt h.𝔇 (At.seats Zp) rq :=
  ⟨_, meantAt_all o Zp Np cF (At.EAt Z) h.plan.shape Z.lay h.plan.laid h.plan.hN h.plan.hG x
    (At.wt Zp cF Z.lay) (At.cr1 Zp Z.lay) OnBytes.Flat.numsFull.rows⟩

/-- The request's reader reads the public part alone. -/
theorem req_public_at (h : AtMgA o Z D r Zp Np cF x) :
    ∀ a b : ProofFile.InstPub × S, a.1 = b.1 → h.𝔇.H.req a = h.𝔇.H.req b := by
  obtain ⟨rq, M⟩ := meant_at h
  intro a b e
  rw [M.req, M.req, e]

/-- The decoder reads the public part and the cells alone. -/
theorem dec_public_at (h : AtMgA o Z D r Zp Np cF x) :
    ∀ (a b : ProofFile.InstPub × S) (y y' : Strs), a.1 = b.1 → y'.cell = y.cell →
      h.𝔇.decT y.cell a = h.𝔇.decT y'.cell b := by
  obtain ⟨rq, M⟩ := meant_at h
  intro a b y y' e ec
  obtain ⟨z, s⟩ := a
  obtain ⟨z', t⟩ := b
  obtain rfl : z = z' := e
  rw [ec]
  exact M.dec _ _ _ _

/-- The digits' part reads neither the state nor the strings: it goes back over every relation. -/
theorem digits_back_at (h : AtMgA o Z D r Zp Np cF x)
    (rel : ProofFile.InstPub × S → Strs → ProofFile.InstPub × S → Strs → Prop) (m : ℕ) :
    GoesBack rel (h.𝔇.digitsPart m) := fun _ _ _ _ _ _ k => k

/-- The heard token's reader, over relCH. -/
theorem tokH_same {a b : ProofFile.InstPub × S} (e : a.2.heardTok? = b.2.heardTok?) :
    tokHOf a = tokHOf b := by
  unfold tokHOf tokOfHeard
  rw [e]

/-- The output head's parts but lookCallsHeard go back over relC. -/
theorem head_back_at (h : AtMgA o Z D r Zp Np cF x) (p : TPart) (hp : p ≠ .lookCallsHeard)
    (i : Cm.Idx) : GoesBack relC (h.𝔇.headPart p i) :=
  VerifiableInference.Desc.Kinds.Head.Law.headPartK6_goesBack _ _ _ _ _ _ _ _ _ _ _ _ relC
    (fun a _ b _ hr => req_public_at h a b hr.1) p (fun e => absurd e hp) i

/-- All of them go back over relCH. -/
theorem head_back_heard_at (h : AtMgA o Z D r Zp Np cF x) (p : TPart) (i : Cm.Idx) :
    GoesBack relCH (h.𝔇.headPart p i) :=
  VerifiableInference.Desc.Kinds.Head.Law.headPartK6_goesBack _ _ _ _ _ _ _ _ _ _ _ _ relCH
    (fun a _ b _ hr => req_public_at h a b hr.1.1) p (fun _ _ _ _ _ hr => tokH_same hr.2) i

/-- **constr OVER relC, AT EVERY (m, p) BUT (THE HEAD's SEGMENT, lookCallsHeard).** -/
theorem constr_back_at (h : AtMgA o Z D r Zp Np cF x) (m : ℕ) (p : TPart)
    (hmp : ¬ (m = headLink (At.X Zp) ∧ p = .lookCallsHeard)) :
    GoesBack relC ((mgAtAll h).constr m p) := by
  show GoesBack relC ((mgAll h.𝔇 mgBase).constr m p)
  rw [mgAll_constr]
  by_cases hd : p = .lookDigits
  · subst hd
    intro a y b y' w hr k
    unfold constrQAt at k ⊢
    rw [if_pos rfl] at k ⊢
    exact digits_back_at h relC m a y b y' w hr k
  · have hreq : ∀ a y b y', relC a y b y' →
        (oneDec h.𝔇.decT h.𝔇.H).req a = (oneDec h.𝔇.decT h.𝔇.H).req b :=
      fun a _ b _ hr => req_public_at h a b hr.1
    have hdec : ∀ a y b y', relC a y b y' →
        (oneDec h.𝔇.decT h.𝔇.H).dec a y = (oneDec h.𝔇.decT h.𝔇.H).dec b y' :=
      fun a y b y' hr => dec_public_at h a b y y' hr.1 hr.2
    by_cases hm : m = headLink (At.X Zp)
    · exact constrQAt_back_any _ _ _ _ _ m p hd relC hreq hdec
        (head_back_at h p fun e => hmp ⟨hm, e⟩)
    · exact constrQAt_back _ _ _ _ _ m p hd hm relC hreq hdec

/-- **THE FIELD constr OF FieldsBack, AT own := NOTHING, OVER relCH.** -/
theorem constr_field_at (h : AtMgA o Z D r Zp Np cF x) (m : ℕ) (p : TPart) :
    GoesBack relCH ((mgAtAll h).constr m p) := by
  by_cases hmp : m = headLink (At.X Zp) ∧ p = .lookCallsHeard
  · obtain ⟨-, rfl⟩ := hmp
    show GoesBack relCH ((mgAll h.𝔇 mgBase).constr m .lookCallsHeard)
    rw [mgAll_constr]
    exact constrQAt_back_any _ _ _ _ _ m .lookCallsHeard (by decide) relCH
      (fun a _ b _ hr => req_public_at h a b hr.1.1)
      (fun a y b y' hr => dec_public_at h a b y y' hr.1.1 hr.1.2)
      (head_back_heard_at h .lookCallsHeard)
  · exact (constr_back_at h m p hmp).mono fun _ _ _ _ hr => hr.1

/-- relOut gives relCH. -/
theorem relCH_of_relOut (base : ℕ) (a : ProofFile.InstPub × S) (y : Strs) (b : ProofFile.InstPub × S)
    (y' : Strs) (hr : relOut base a y b y') : relCH a y b y' := by
  obtain ⟨e, hs, hy⟩ := hr
  refine ⟨⟨e, funext hy.1⟩, ?_⟩
  rw [← replyTok_is_heardTok, ← replyTok_is_heardTok]
  unfold VerifiableInference.Desc.First.S.replyTok?
  rw [hs.out]

/-- **So over relOut, at every base.** -/
theorem constr_relOut_at (h : AtMgA o Z D r Zp Np cF x) (base m : ℕ) (p : TPart) :
    GoesBack (relOut base) ((mgAtAll h).constr m p) :=
  (constr_field_at h m p).mono (relCH_of_relOut base)

end P5J

#print axioms P5J.meant_at
#print axioms P5J.req_public_at
#print axioms P5J.dec_public_at
#print axioms P5J.digits_back_at
#print axioms P5J.tokH_same
#print axioms P5J.head_back_at
#print axioms P5J.head_back_heard_at
#print axioms P5J.constr_back_at
#print axioms P5J.constr_field_at
#print axioms P5J.relCH_of_relOut
#print axioms P5J.constr_relOut_at
