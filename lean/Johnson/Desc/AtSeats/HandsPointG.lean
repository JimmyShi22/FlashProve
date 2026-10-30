--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
HandsPointG.lean: THE POINTWISE ROAD FOR OUR SHARE AT THE
FIRST SEGMENT's OPENING: its premises over all states in front ("in order" holds; the groups'
count; the own seats' test) ARE ASKED UNDER THE FENCE ALONE. Statements with their proofs.
  `handsPt_of_all`: KIND-FREE: a term of `IM.Hands` that is general in the further test gives
  `IM.HandsPt` (HandsPoint.lean: another house's: what one sub-protocol owes at ONE state in
    front): it is called at the test "E, and at border k the state is s₀". (Another house has the
     in a file that stands above its own law chain; this one imports the
    light file alone.)
  `handsR_of_wider_pt`: KIND-FREE: the bridge `handsR_of_wider` in pointwise form:
  `HandsPt` at the
    wider test at every fenced state gives `IM.HandsR Fk` at the narrower.
  `handsPt_G`: at the opening, at `EAt z Mg`: `HandsPt … s₀` FROM THREE FACTS AT s₀ ALONE.
  `handsR_G_plus13`: **`IM.HandsR Fk N links ps (EAt z Mg links ps) ft k` at the opening, at the
  narrower filling Mg**: from `RowG` and `FillG` at the wider filling `plus13 D d Mg`; the test on
    the two doors at k and k + 1; and a fence that gives, at every state without a mark:
    `FactsK13`, Mg's own "in order", and the two facts on the list of rounds' numbers.
What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.IMR.HandsPoint
import Johnson.Desc.AtSeats.HandsBridgeK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers More Pub Meaning)
open VerifiableInference.Desc.Sound (doorsFitB)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open ProofFile (Cl)

section
variable {N : Numbers} {links : List ModelPart} {ps : List Place} {E E' : ℕ → S → Bool} {ft k : ℕ}
  {b : Block S Cl}

open Classical in
/-- **From a term that is general in the further test to the pointwise form.** -/
theorem handsPt_of_all (s₀ : S)
    (H : ∀ E₀ : ℕ → S → Bool, (∀ t, E₀ k t = true → t = s₀ ∧ E k t = true) →
      (∀ t, E₀ (k + 1) t = E (k + 1) t) → IM.Hands N links ps E₀ ft k b) :
    IM.HandsPt N links ps E ft k b s₀ := by
  have h1 : ∀ t, (E k t && decide (k = k → t = s₀)) = true → t = s₀ ∧ E k t = true := fun t h => by
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.2 rfl, h.1⟩
  have h2 : ∀ t, (E (k + 1) t && decide (k + 1 = k → t = s₀)) = E (k + 1) t := fun t => by
    have : (k + 1 = k → t = s₀) := fun e => absurd e (by omega)
    rw [decide_eq_true this, Bool.and_true]
  have H₀ := H (fun j t => E j t && decide (j = k → t = s₀)) h1 h2
  have up : IM.XK N links ps E k s₀ = true →
      IM.XK N links ps (fun j t => E j t && decide (j = k → t = s₀)) k s₀ = true := fun hx =>
    xk_swap hx (by
      show (E k s₀ && decide (k = k → s₀ = s₀)) = true
      rw [(IM.xk_parts hx).2.2.2.2, decide_eq_true (fun _ => rfl)]
      rfl)
  exact ⟨fun s' hy => H₀.mark s₀ s' hy, fun s' hy a c hx => H₀.shape s₀ s' hy a c (up hx),
    fun s' hy a c hx => H₀.rows s₀ s' hy a c (up hx),
    fun s' hy a c hx => H₀.members s₀ s' hy a c (up hx),
    fun s' hy a c hx => H₀.book s₀ s' hy a c (up hx),
    fun s' hy a c hx => (h2 s').symm.trans (H₀.more s₀ s' hy a c (up hx))⟩

/-- **The bridge, pointwise.** -/
theorem handsR_of_wider_pt {Fk : ℕ → S → Prop}
    (hup : ∀ s, Fk k s → s.failed = none → IM.XK N links ps E k s = true → E' k s = true)
    (hdown : ∀ s, E' (k + 1) s = true → E (k + 1) s = true)
    (H : ∀ s, Fk k s → IM.HandsPt N links ps E' ft k b s) : IM.HandsR Fk N links ps E ft k b where
  mark := fun s s' f hy => (H s f).mark s' hy
  shape := fun s s' f hy h0 h1 hx => (H s f).shape s' hy h0 h1 (xk_swap hx (hup s f h0 hx))
  rows := fun s s' f hy h0 h1 hx => (H s f).rows s' hy h0 h1 (xk_swap hx (hup s f h0 hx))
  members := fun s s' f hy h0 h1 hx => (H s f).members s' hy h0 h1 (xk_swap hx (hup s f h0 hx))
  book := fun s s' f hy h0 h1 hx => (H s f).book s' hy h0 h1 (xk_swap hx (hup s f h0 hx))
  more := fun s s' f hy h0 h1 hx =>
    hdown s' ((H s f).more s' hy h0 h1 (xk_swap hx (hup s f h0 hx)))

end

variable {Pp W : Type}

/-- **The first segment's opening, at one state in front.** -/
theorem handsPt_G (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (z : Pp)
    (ft k : ℕ) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar) (fvs : List Bool)
    (kCol : ℕ) (mk : List Pub)
    (hT : RowG N Mg.more links ps k (K1.layOf (K1.firstPar q gp)).shapes.size
      (K1.firstPar q gp).sent.size mk)
    (hF : FillG Cl q gp nm X fvs kCol N Mg ((First.pubSets Mg.more links ps)[k]?.getD []) ps[k]?
      mk)
    (s₀ : S) (hio : Mg.inOrder (z, s₀) = true)
    (hgroups : Mg.pub .noneSent (z, s₀) = true → N.groupAt 0 = s₀.st.groups.size)
    (hown : First.bookAt N ps[k]? s₀ = true →
      K1.ownSeatsB N (openAt links ps (k + 1)) (K1.firstPar q gp)
        (s₀.check.frame.atMoment 0).length s₀.book.trees.size = true) :
    IM.HandsPt N links ps (EAt z Mg links ps) ft k
      (K1.openingZero q gp nm X fvs kCol : Block S Cl) s₀ :=
  handsPt_of_all s₀ fun E₀ h1 h2 =>
    hands_G N Mg.more links ps E₀ ft k q gp nm X fvs kCol mk hT
      (fun s hx => by
        obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        exact hgroups ((eAt_parts he).1 _ hT.noneSent))
      (fun s hx => by
        obtain ⟨rfl, _⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        exact hown (IM.xk_parts hx).2.2.2.1)
      fun s s' hy _ _ hx => by
        obtain ⟨rfl, he⟩ := h1 s (IM.xk_parts hx).2.2.2.2
        obtain ⟨hQ, _⟩ := eAt_parts he
        have hbk := (IM.xk_parts hx).2.2.2.1
        obtain ⟨rs, cols, n, e⟩ := hy
        have hst : StepG Cl q gp nm X fvs kCol (z, s) (z, s') := ⟨rfl, ft, rs, cols, n, e⟩
        rw [h2]
        refine eAt_of (fun i hi => ?_) fun i hi => ?_
        · rcases hT.pubs i hi with hi' | ⟨hi', hne⟩
          · exact hF.made _ _ i hst hQ hbk hio (Or.inl hi')
          · exact hF.pubRide _ _ i hst hQ hbk hi' hne
        · rcases hT.tied i hi with rfl | rfl
          · exact hF.made _ _ _ hst hQ hbk hio (Or.inr (Or.inl rfl))
          · exact hF.made _ _ _ hst hQ hbk hio (Or.inr (Or.inr rfl))

/-- **The opening's share in the second form, at the narrower filling.** -/
theorem handsR_G_plus13 {nR : ℕ} (N : Numbers) (D : DataK13 Pp W nR) (d : K12Data)
    (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (z : Pp) (ft k : ℕ)
    (q : Params.First) (gp : GPar) (nm : String) (X : LayPar) (fvs : List Bool) (kCol : ℕ)
    (mk : List Pub) (Fk : ℕ → S → Prop)
    (hT : RowG N (plus13 D d Mg).more links ps k (K1.layOf (K1.firstPar q gp)).shapes.size
      (K1.firstPar q gp).sent.size mk)
    (hF : FillG Cl q gp nm X fvs kCol N (plus13 D d Mg)
      ((First.pubSets (plus13 D d Mg).more links ps)[k]?.getD []) ps[k]? mk)
    (hD : doorsFitB Mg.more (plus13 D d Mg).more cA13 links ps k = true)
    (hD' : doorsFitB Mg.more (plus13 D d Mg).more cA13 links ps (k + 1) = true)
    (hFk : ∀ s, Fk k s → s.failed = none → FactsK13 D d Mg (z, s))
    (hio : ∀ s, Fk k s → (plus13 D d Mg).inOrder (z, s) = true)
    (hgroups : ∀ s, Fk k s → (plus13 D d Mg).pub .noneSent (z, s) = true →
      N.groupAt 0 = s.st.groups.size)
    (hown : ∀ s, Fk k s → First.bookAt N ps[k]? s = true →
      K1.ownSeatsB N (openAt links ps (k + 1)) (K1.firstPar q gp)
        (s.check.frame.atMoment 0).length s.book.trees.size = true) :
    IM.HandsR Fk N links ps (EAt z Mg links ps) ft k
      (K1.openingZero q gp nm X fvs kCol : Block S Cl) :=
  handsR_of_wider_pt (E' := EAt z (plus13 D d Mg) links ps)
    (fun s f h0 hx => eAt_up z Mg (plus13 D d Mg).more (plus13 D d Mg).pub (plus13 D d Mg).inOrder
      cA13 links ps k s (plus13_hand D d Mg) hD
      (fun i _ hc => plus13_class D d Mg _ (hFk s f h0) i hc) (IM.xk_parts hx).2.2.2.2)
    (fun s h => eAt_down z Mg (plus13 D d Mg).more (plus13 D d Mg).pub (plus13 D d Mg).inOrder cA13
      links ps (k + 1) s (plus13_hand D d Mg) hD' h)
    fun s f => handsPt_G N (plus13 D d Mg) links ps z ft k q gp nm X fvs kCol mk hT hF s (hio s f)
      (hgroups s f) (hown s f)

end HashBuild
