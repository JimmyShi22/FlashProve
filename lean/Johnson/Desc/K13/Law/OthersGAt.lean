-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OthersGAt.lean: WHAT STAYED AT THE FIRST SEGMENT's OPENING (`OthersG`,
Johnson/Desc/K13/Law/FillGFromSentences.lean) OUT OF WHAT THE LETTERS SAY AND TESTS ON THE PLAN.
Definitions, and a statement with its proof.
  `MgG`: what the letters say beside kind K13's own premises (`MgK13`): "nothing is sent yet" is
    our layer's test; the two items of the table's own layer; the three of the look-ups' layer;
    `pubP` says nothing beside the Bool at the five that come.
  `PlanG`: tests on the plan's values: the ledger's number of slots; the link's first state has
  heard nothing; the table of arrays; the look-up's place, its shape, that it is the one on the
    calls, its first number, its room, its link; the look-ups' shape and layout are our layer's.
  `othersG_at`: **`OthersG` at any list mk of items that come.** SHOWN: the five of `madeSix`
  (MadeAtOpeningLook.lean) are made; "decodes" rides; the committed table's pin goes back; "every
  pending row holds" goes back (in front no row is pending). PREMISES THAT STAY: the making of
  whatever else a filling of the door lets come at the row (hmore); what other layers say of "in
  order" rides; the constraints go back; the decoder reads the public part alone.
What is not claimed. A member of `MgG` or `PlanG`. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.MgK13
import Johnson.Desc.K13.Law.MadeAtOpeningLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.First (S)

/-- The first segment's sending leaves where the chain stands. -/
theorem firstAtS_here {Cl : Type} (q : Params.First) (gp : GPar) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s rs gs = .ok s') : s'.here = s.here := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, _, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  rfl

end VerifiableInference.Desc.K1

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker
open Desc.Plain
open Johnson.Pack (sigOf)
open Johnson.Desc.First.Walk (LayPar startFork)
open Johnson.Desc.First.Walk.Law (openLayZero_ok)
open VerifiableInference.Desc.First (S Pub Item Meaning Numbers ledgerB freeAboveB)
open VerifiableInference.Desc.First.Look (K3Data linkFreshC lookInC liveIsC placeAt)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)

/-- In front of a yes of the joined block the chain stands between two links: the rows on the table
are the pending ones. -/
theorem rows_front_G {Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (hp : s.out.pending = []) : s.rows = [] := by
  obtain ⟨s₁, g₁, h1, h2⟩ := K1.openingZero_mid h
  have hb := (openLayZero_ok h2).1
  have he := K1.firstAtS_here q gp s s₁ _ g₁ h1
  unfold S.atBetween at hb
  rw [he] at hb
  unfold S.rows
  cases hh : s.here with
  | between => exact hp
  | _ => rw [hh] at hb; cases hb

/-- **What the letters say at the first segment's opening**, beside `MgK13`. -/
structure MgG {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (nsOf : ℕ → Option ℕ) (d : K3Data)
    (dg : Bool) : Prop where
  noneSent : ∀ x, Mg.pub .noneSent x = noneSentC N x.2
  ledger : ∀ x, Mg.pub (.ledger 0) x = ledgerB x.2
  freeAbove : ∀ x, Mg.pub (.freeAbove 0) x = (nsOf 0).any fun n => freeAboveB n x.2
  linkFresh : ∀ x, Mg.pub (.linkFresh 0) x = linkFreshC d 0 x.2
  lookIn : ∀ x, Mg.pub (.lookIn 0 2) x = lookInC d 0 dg x.2
  liveIs : ∀ x, Mg.pub (.more (some 0) "frame.liveIs") x = liveIsC d x.2
  quiet : ∀ i ∈ madeSix, ∀ x, Mg.pubP i x

/-- **The tests on the plan's values.** -/
structure PlanG (X : LayPar) (nsOf : ℕ → Option ℕ) (d : K3Data) (dg : Bool)
    (sh : Params.ReqShape) (ly : Params.ReqLayout) : Prop where
  slots : nsOf 0 = some X.ns
  unheard : X.tl₀.heard = none
  arrays : d.arrayOf.getD 0 #[] = X.X.arrayOf
  place : ∃ p f, placeAt d.X 0 dg = some p ∧ p.shape = some f ∧ p.digits = false ∧
    (startFork X.X X.ns).next = p.first ∧ p.first + Forest.elems f ≤ X.ns ∧ p.link = 0
  shape : d.shape = sh
  layout : d.layout = ly

/-- **`OthersG` at any list of items that come.** -/
theorem othersG_at {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} {q : Params.First} {gp : GPar} {nm : String}
    {X : LayPar} {fvs : List Bool} {kCol : ℕ} {nsOf : ℕ → Option ℕ} {d : K3Data} {dg : Bool}
    (Q : List Pub) (p : Option Place) (mk : List Pub)
    (hMg : MgK13 P N Mg cs sh ly rest arr mat G smp ms decT M L) (hG : MgG N Mg nsOf d dg)
    (hPl : PlanG X nsOf d dg sh ly) (hm : Pub.noneSent ∈ Q) (hdec : DecBlind decT)
    (hmore : ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
      First.bookAt N p x.2 = true → Mg.inOrder x = true → i ∈ mk → i ∉ madeSix →
      Mg.pub i x' = true ∧ Mg.pubP i x')
    (hin : ∀ x x', StepG Cl q gp nm X fvs kCol x x' → Mg.inOrder x = true →
      Mg.inOrder x' = true)
    (hrest : ∀ x x', StepG Cl q gp nm X fvs kCol x x' → rest x = true → rest x' = true)
    (hconstr : ∀ x x' y y' w m c, StepG Cl q gp nm X fvs kCol x x' →
      (∀ q' ∈ Q, Mg.pub q' x = true) → First.bookAt N p x.2 = true → y'.cell = y.cell →
      Mg.constr m c x' y' w → Mg.constr m c x y w) :
    OthersG Cl q gp nm X fvs kCol N Mg rest Q p mk where
  made := fun x x' i h hQ hbk hio hi0 => by
    by_cases hi : i ∈ madeSix
    swap
    · exact hmore x x' i h hQ hbk hio hi0 hi
    obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
    refine ⟨?_, hG.quiet i hi x'⟩
    obtain ⟨pl, f, a1, a2, a3, a4, a5, a6⟩ := hPl.place
    simp only [madeSix, madeG, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · rw [hG.ledger]
      exact openingZero_ledger hd
    · rw [hG.lookIn]
      exact openingZero_lookIn hd d dg pl f a1 a2 a3 a4 a5 a6 hPl.arrays
    · rw [hG.linkFresh]
      exact openingZero_linkFresh hd d hPl.unheard hPl.arrays
    · rw [hG.freeAbove, hPl.slots]
      exact openingZero_freeAbove hd
    · rw [hG.liveIs]
      have h1 := hin x x' h hio
      rw [hMg.ours.inOrder, Bool.and_eq_true] at h1
      refine openingZero_liveIs hd d cs ?_
      rw [hPl.shape, hPl.layout]
      exact h1.2
  rest := hrest
  decodes := fun x x' y y' h hc h0 => by
    rw [hMg.sig.decodes] at h0 ⊢
    exact decodes_rides_blind hdec h.1 hc h0
  back := fun x x' y y' w i h hQ hbk hc hi h0 => by
    cases i with
    | pinW =>
      have h1 : Mg.pinW x' y' w := h0
      show Mg.pinW x y w
      rw [hMg.sig.pinW] at h1 ⊢
      exact pinW_back_blind hdec h.1 hc h1
    | pile =>
      show Mg.pile x y w
      refine (hMg.ours.pile x y w).2 fun r hr => ?_
      have hn := hQ _ hm
      rw [hG.noneSent, noneSentC_eq, Bool.and_eq_true] at hn
      have hp0 : x.2.out.pending = [] := List.isEmpty_iff.1 hn.2
      obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
      have hr0 : x.2.rows = [] := rows_front_G hd hp0
      rw [hr0] at hr
      cases hr
    | constr m c => exact hconstr x x' y y' w m c h hQ hbk hc h0
    | _ => cases hi

end VerifiableInference.Desc.K13.Law
