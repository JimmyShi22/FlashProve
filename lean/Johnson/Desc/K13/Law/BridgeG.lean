-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/BridgeG.lean: THE WIDER FILLING FOR THE TIE AT THE FIRST SEGMENT's OPENING,
AND ITS BRIDGE. That tie's premises on the letters (`MgG`, Johnson/Desc/K13/Law/OthersGAt.lean)
name, beside the eight names of `plus13` (Johnson/Desc/K13/Law/BridgeK13.lean), the look-ups' test
at "frame.liveIs" of segment 0, which has left the door too. Definitions, and statements with
their proofs. `liveItem0`; `pubLive0 dk f`: f, with the look-ups' own test `liveIsC dk` at that
  one item. `plusG D d dk Mg` := `plus13 D d` over Mg with `pubLive0`: THE DOOR IS `plus13`'s: the
  ninth name is answered, and stands
    open nowhere by this filling.
  `cAG`: the class: the nine names. `plusG_hand`, `plusG_io`, `plusG_more`. `FactsG D d dk Mg x`:
  `FactsK13`, the look-ups' test, and that `pubP` says nothing beside it. `tiedAtR_plusG`: **THE
  CALL**: a tie at `plusG D d dk Mg` is a tie in the second form at Mg. `MgGC`: the tie's premises
  on the letters AT THE NARROWER FILLING: five equations at items that stay, and `pubP`'s silence
    at five; `mgG_plus`: `MgG` at `plusG`. `fillsK13_plusG`: `FillsK13` at `plusG` out of
    `FillsK13C` at Mg.
`frontB s`: a test on the walk's copy of the frame that goes into the wider filling's
OWN "in order": what the tie reads of the state in front and no item of the table's promise pins;
`openingZero_front`: the opening leaves it; `FactsG` asks it of the reached states.
`frontB` says outright that the frame stands at link 0: the own seats' test reads how
many
messages the frame expects at moment 0, which hangs on the link.
What is not claimed. `FactsG` at any state; a member of `MgGC`. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillsK13C
import Johnson.Desc.K13.Law.OthersGAt
import Johnson.Desc.K13.Law.MadeAtOpeningSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers More ledgerB freeAboveB unheardB)
open VerifiableInference.Desc.First.Look (K3Data linkFreshC lookInC liveIsC)
open Desc.Plain
open OnBytes.Params
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Law (openLayZero_ok)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Sound (MsgT Sending Mem Frame Piece TiedAt TiedAtR HandsOn doorsFitB
  FactsAt tiedAtR_of_classA)

/-- The look-ups' name at segment 0. -/
def liveItem0 : Pub := .more (some 0) "frame.liveIs"

/-- f, with the look-ups' own test at that one item. -/
def pubLive0 {Pp : Type} (dk : K3Data) (f : Pub → Pp × S → Bool) : Pub → Pp × S → Bool :=
  fun q a => if q = liveItem0 then liveIsC dk a.2 else f q a

open Classical in
/-- **What the opening's tie reads of the walk's copy of the frame in front**, and nothing in the
table's promise pins: the groups are its own shape's; the frame stands at link 0; nothing
is kept. It holds in front of and behind the opening, not further on: the bridge asks it there
alone. With no code: the wider filling is run nowhere. -/
noncomputable def frontB (s : S) : Bool :=
  decide (s.check.frame.groups = reqGroups s.check.frame.shape) &&
    decide (s.check.frame.link = 0) && decide (s.check.frame.keptBefore = #[])

open Classical in
theorem frontB_iff (s : S) : frontB s = true ↔
    s.check.frame.groups = reqGroups s.check.frame.shape ∧ s.check.frame.link = 0 ∧
      s.check.frame.keptBefore = #[] := by
  unfold frontB
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    decide_eq_true_eq, and_assoc]

/-- It reads four fields of that copy. -/
theorem frontB_same {s t : S} (hg : t.check.frame.groups = s.check.frame.groups)
    (hs : t.check.frame.shape = s.check.frame.shape) (hl : t.check.frame.link = s.check.frame.link)
    (hk : t.check.frame.keptBefore = s.check.frame.keptBefore) : frontB t = frontB s := by
  unfold frontB
  rw [hg, hs, hl, hk]

/-- **The opening leaves it.** -/
theorem openingZero_front {Cl : Type} {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    frontB t = frontB s := by
  obtain ⟨s₁, g₁, h1, h2⟩ := K1.openingZero_mid h
  obtain ⟨_, _, _, _, _, _, _, hc, _, _⟩ := openLayZero_ok h2
  obtain ⟨g, mask, e, _, _⟩ := K1.firstAtS_frame q gp s s₁ r₁ r₂ g₁ h1
  refine frontB_same ?_ ?_ ?_ ?_ <;> rw [hc, e]

section
variable {Pp W : Type} {nR : ℕ}

/-- Mg with that test laid, and `frontB` beside its "in order". -/
noncomputable def withLive0 (dk : K3Data) (Mg : Meaning Pp W) : Meaning Pp W :=
  { Mg with pub := pubLive0 dk Mg.pub, inOrder := fun x => Mg.inOrder x && frontB x.2 }

/-- **The wider filling for the opening.** -/
noncomputable def plusG (D : DataK13 Pp W nR) (d : K12Data) (dk : K3Data) (Mg : Meaning Pp W) :
    Meaning Pp W :=
  plus13 D d (withLive0 dk Mg)

/-- **The class**: the nine names. -/
def cAG (q : Pub) : Bool := cA13 q || decide (q = liveItem0)

/-- **What the condition beside the promise is to give** at a state. -/
structure FactsG (D : DataK13 Pp W nR) (d : K12Data) (dk : K3Data) (Mg : Meaning Pp W)
    (x : Pp × S) : Prop where
  k13 : FactsK13 D d Mg x
  live : liveIsC dk x.2 = true
  front : frontB x.2 = true
  liveQuiet : Mg.pubP liveItem0 x

variable (D : DataK13 Pp W nR) (d : K12Data) (dk : K3Data) (Mg : Meaning Pp W)

theorem plusG_more : (plusG D d dk Mg).more = (plus13 D d Mg).more := rfl

theorem plusG_hand (q : Pub) (h : cAG q = false) (x : Pp × S) :
    (plusG D d dk Mg).pub q x = Mg.pub q x := by
  unfold cAG at h
  rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  unfold plusG
  rw [plus13_hand D d _ q h.1]
  show pubLive0 dk Mg.pub q x = _
  unfold pubLive0
  rw [if_neg h.2]

theorem plusG_both (x : Pp × S) (h : (plusG D d dk Mg).inOrder x = true) :
    Mg.inOrder x = true ∧ frontB x.2 = true := by
  have h1 : (Mg.inOrder x && frontB x.2) = true := plus13_io D d (withLive0 dk Mg) x h
  rwa [Bool.and_eq_true] at h1

theorem plusG_io (x : Pp × S) (h : (plusG D d dk Mg).inOrder x = true) : Mg.inOrder x = true :=
  (plusG_both D d dk Mg x h).1

/-- At the ninth name the wider filling answers with the look-ups' test. -/
theorem plusG_live (x : Pp × S) : (plusG D d dk Mg).pub liveItem0 x = liveIsC dk x.2 := by
  unfold plusG
  rw [plus13_hand D d _ liveItem0 rfl]
  show pubLive0 dk Mg.pub liveItem0 x = _
  unfold pubLive0
  rw [if_pos rfl]

theorem factsK13_live {x : Pp × S} (h : FactsK13 D d Mg x) : FactsK13 D d (withLive0 dk Mg) x :=
  ⟨h.order, h.masks, h.within, h.oneRow, h.weights, h.book, h.seats, h.shapes, h.fits, h.quiet⟩

variable {A Cl : Type} {C : CK} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place)
  (get : A → Pp × S)

/-- **THE CALL.** The facts are asked at the two borders of the sub-protocol alone. -/
theorem tiedAtR_plusG (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) (q : Piece C Fr A Cl W)
    (hD : doorsFitB Mg.more (plusG D d dk Mg).more cAG links ps k = true)
    (hD' : doorsFitB Mg.more (plusG D d dk Mg).more cAG links ps (k + 1) = true)
    (hF : ∀ j a, Rch j a → j = k ∨ j = k + 1 → (get a.1).2.failed = none →
      FactsG D d dk Mg (get a.1))
    (hs : HandsOn Rch k q) (h : TiedAt N (plusG D d dk Mg) links ps get k q) :
    TiedAtR N Mg links ps get Rch k q := by
  have h' : TiedAtR N Mg links ps get (fun j a => Rch j a ∧ (j = k ∨ j = k + 1)) k q :=
    tiedAtR_of_classA N Mg (plusG D d dk Mg).more (plusG D d dk Mg).pub (plusG D d dk Mg).inOrder
      cAG links ps get _ k q (plusG_hand D d dk Mg) (plusG_io D d dk Mg) hD hD'
      (fun j a hr hm =>
        ⟨fun h0 => by
          show ((Mg.inOrder (get a.1) && frontB (get a.1).2) &&
            inOrderK13 D.codes D.shape D.layout (get a.1).2) = true
          rw [h0, (hF j a hr.1 hr.2 hm).k13.order, (hF j a hr.1 hr.2 hm).front]
          rfl, fun i _ hc => by
          unfold cAG at hc
          rw [Bool.or_eq_true, decide_eq_true_eq] at hc
          rcases hc with hc | rfl
          · exact ⟨plus13_class D d _ _ (factsK13_live D d dk Mg (hF j a hr.1 hr.2 hm).k13) i hc,
              (hF j a hr.1 hr.2 hm).k13.quiet i hc⟩
          · exact ⟨(plusG_live D d dk Mg _).trans (hF j a hr.1 hr.2 hm).live,
              (hF j a hr.1 hr.2 hm).liveQuiet⟩⟩)
      (fun a τ b hr ho => ⟨hs a τ b hr.1 ho, Or.inr rfl⟩) h
  obtain ⟨o, o', R, R', hl, t1, t2, t3, t4, t5, hM, hDc⟩ := h'
  exact ⟨o, o', R, R', hl, fun a ha hr => t1 a ha ⟨hr, Or.inl rfl⟩,
    fun a τ b ha hr => t2 a τ b ha ⟨hr, Or.inl rfl⟩,
    fun a τ b w ha hr => t3 a τ b w ha ⟨hr, Or.inl rfl⟩,
    fun a τ b w ha hr => t4 a τ b w ha ⟨hr, Or.inl rfl⟩,
    fun a τ b w i ha hr => t5 a τ b w i ha ⟨hr, Or.inl rfl⟩, hM, hDc⟩

end

/-- **The tie's premises on the letters, at the narrower filling.** -/
structure MgGC {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (nsOf : ℕ → Option ℕ) (dk : K3Data)
    (dg : Bool) : Prop where
  noneSent : ∀ x, Mg.pub .noneSent x = noneSentC N x.2
  ledger : ∀ x, Mg.pub (.ledger 0) x = ledgerB x.2
  freeAbove : ∀ x, Mg.pub (.freeAbove 0) x = (nsOf 0).any fun n => freeAboveB n x.2
  linkFresh : ∀ x, Mg.pub (.linkFresh 0) x = linkFreshC dk 0 x.2
  lookIn : ∀ x, Mg.pub (.lookIn 0 2) x = lookInC dk 0 dg x.2
  quiet : ∀ i ∈ madeSix, ∀ x, Mg.pubP i x

/-- **`MgG` at the wider filling.** -/
theorem mgG_plus {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (d : K12Data) (dk : K3Data)
    {N : Numbers} {Mg : Meaning Pp W} {nsOf : ℕ → Option ℕ} {dg : Bool}
    (h : MgGC N Mg nsOf dk dg) : MgG N (plusG D d dk Mg) nsOf dk dg where
  noneSent := fun x => (plusG_hand D d dk Mg _ rfl x).trans (h.noneSent x)
  ledger := fun x => (plusG_hand D d dk Mg _ rfl x).trans (h.ledger x)
  freeAbove := fun x => (plusG_hand D d dk Mg _ rfl x).trans (h.freeAbove x)
  linkFresh := fun x => (plusG_hand D d dk Mg _ rfl x).trans (h.linkFresh x)
  lookIn := fun x => (plusG_hand D d dk Mg _ rfl x).trans (h.lookIn x)
  liveIs := plusG_live D d dk Mg
  quiet := h.quiet

/-- `FillsK13C` does not read the ninth name. -/
theorem fillsK13C_live {Pp Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    (dk : K3Data) (h : FillsK13C P N Mg cs arr mat G smp ms decT) :
    FillsK13C P N (withLive0 dk Mg) cs arr mat G smp ms decT where
  pile := h.pile
  pileOne := h.pileOne
  frontOk := h.frontOk
  evalLaid := h.evalLaid
  wSits := h.wSits
  indexIs := h.indexIs
  indexThere := h.indexThere
  held := h.held
  shown := h.shown
  noColl := h.noColl
  pin := h.pin
  pinW := h.pinW
  decodes := h.decodes
  quiet := h.quiet

end VerifiableInference.Desc.K13.Law
