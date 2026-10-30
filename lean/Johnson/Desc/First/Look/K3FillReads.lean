-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3FillReads.lean: the kind "lookup" (K3): ITS LAYER OF THE FILLING OF THE
TABLE OF JOINTS' MEANING: WHICH COMPONENTS OF THE WITNESS ITS SENTENCES READ, BY THEIR AUTHORS' OWN
WORD, AND THE LEMMA: readsK3 X D L : Item → List Comp; two witnesses that have every component of
readsK3 i in common give the sentence at i one truth value, at every state of the verifier and all
strings. Definitions, statements, proofs. NO SOUNDNESS IS CLAIMED.

Why. The kind-free fifth tie has one premise over all items: an item's sentence reads the witness
through the components that the table books for it (ReadsOkQ, Johnson/Desc/Sound/BordersSides.lean).
The form of that premise in the table's files asks each layer that fills a sentence to say what it
reads; a test with code then holds that against Item.reads.

Main names.
  seatsComps arr n seat: of the members number 0 … n - 1: each one's message and its pad.
  readsK3: THE COARSE, HONEST ONE: at worth m pc _ by the sort of the piece, and at constr m
    lookDigits: on the digits: every member of the link's own list (moments 0, 1, 2) · on the calls
    at attention: every member of the calls' list (the kept ones, then moment 0's) · at a layers'
    link: these AND THE CELLS (the committed table's message) · [] at every other item.
  msgsOf_congr: the reading of the witness's messages reads each member's message and pad alone.
  worthDig_reads, worthAtt_reads, worthLay_reads: the three arms. digitsPart_reads. worthK3_reads:
    THE FIELD.
OBJECT. No block's text: the sentences of worthK3 (K3FillWorth.lean) and digitsPartK3
(K3FillDigits.lean).
USER. Johnson/P5J/ReadsDigitsAt.lean calls digitsPart_reads and worthK3_reads.
LETTERS. X, D, L; f (whatever says worth elsewhere).
IS IT EMPTY? Implications between Props on two witnesses; hW is a premise on the letter L.msgW.

Compiled with the whole library.
Limits. hW (L.msgW reads the cells alone) is shown at no filling. That readsK3 i ⊆ Item.reads i is
left to a test in the files that fill the letters (Johnson/P5J/): it hangs on L.seat against the
numbers N: not said here. Where the field falls through to f the lemma asks f's own reading (hf).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3FillDigits
import Johnson.Desc.Sound.BordersSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Item Comp)
open VerifiableInference.Desc (Strs)

/-- Of the members number 0 … n - 1: each one's message and its pad. -/
def seatsComps (arr : ℕ → ℕ → ℕ) (n : ℕ) (seat : ℕ → ℕ × ℕ) : List Comp :=
  (List.range n).flatMap fun j =>
    [Comp.msg (arr (seat j).1 (seat j).2), Comp.pad (seat j).1 (seat j).2]

section
variable {Cells Tok : Type}

/-- **The reading of the witness's messages reads each member's message and pad alone.** -/
theorem msgsOf_congr (cs : Codes) (l : List (OracleShape × ℕ)) (seat : ℕ → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (w w' : Desc.Wit Cells Tok MsgT)
    (h : ∀ c ∈ seatsComps arr l.length seat, sameQ c w w') :
    msgsOf cs l (fun j : Fin l.length => seat j.1) arr w =
      msgsOf cs l (fun j : Fin l.length => seat j.1) arr w' := by
  funext i
  have hm : ∀ c ∈ [Comp.msg (arr (seat i.1).1 (seat i.1).2), Comp.pad (seat i.1).1 (seat i.1).2],
      c ∈ seatsComps arr l.length seat :=
    fun c hc => List.mem_flatMap.2 ⟨i.1, List.mem_range.2 i.2, hc⟩
  have h1 : w.msg (arr (seat i.1).1 (seat i.1).2) = w'.msg (arr (seat i.1).1 (seat i.1).2) :=
    h (.msg (arr (seat i.1).1 (seat i.1).2)) (hm _ (by simp))
  have h2 : w.pad (seat i.1).1 (seat i.1).2 = w'.pad (seat i.1).1 (seat i.1).2 :=
    h (.pad (seat i.1).1 (seat i.1).2) (hm _ (by simp))
  funext j
  cases j with
  | inl q =>
    show w.tab cs _ _ _ _ false _ _ = w'.tab cs _ _ _ _ false _ _
    unfold Desc.Wit.tab
    rw [h1, h2]
  | inr q =>
    show w.tab cs _ _ _ _ true _ _ = w'.tab cs _ _ _ _ true _ _
    unfold Desc.Wit.tab
    rw [h1, h2]

variable (X : Verify.Public) (D : Desc.First.Look.Sent) (L : K3Letters Cells Tok)

/-- The digits' members' components at segment m. -/
def readsDig (m : ℕ) : List Comp :=
  match digAt X m with
  | some v => seatsComps L.arr (digList v.1 D L.rad).length (L.seat v.1.link true)
  | none => []

/-- The calls' members' components at segment m; at a layers' link the cells too. -/
def readsCalls (m : ℕ) : List Comp :=
  match attAt X m with
  | some v => seatsComps L.arr (sigListCalls D L.rad v.1.link).length (L.seat v.1.link false)
  | none =>
    match layAt X m, tlAt X m with
    | some x, some _ =>
      .cells :: seatsComps L.arr (sigListCalls D L.rad x.link).length (L.seat x.link false)
    | _, _ => []

/-- **WHICH COMPONENTS OF THE WITNESS K3's SENTENCES READ.** -/
def readsK3 : Item → List Comp
  | .worth m pc _ =>
    match k3SortAt X m pc with
    | some true => readsDig X D L m
    | some false => readsCalls X D L m
    | none => []
  | .constr m .lookDigits => readsDig X D L m
  | _ => []

/-! ## The arms -/

theorem worthDig_reads (x : Desc.First.Look.Place) (tl : HTailF2) (r : String)
    (s : Desc.First.S) (w w' : Desc.Wit Cells Tok MsgT) (els els' : Prop) (he : els → els')
    (h : ∀ c ∈ seatsComps L.arr (digList x D L.rad).length (L.seat x.link true), sameQ c w w')
    (hw : worthDig D L x tl r s w els) : worthDig D L x tl r s w' els' := by
  have e : digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w =
      digMu x D L.rad (fun j => L.seat x.link true j.1) L.arr w' := by
    unfold digMu
    rw [msgsOf_congr D.codes (digList x D L.rad) (L.seat x.link true) L.arr w w' h]
  have e2 : digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr w =
      digNu x tl D L.rad (fun j => L.seat x.link true j.1) L.arr w' := by
    funext q
    unfold digNu
    rw [e]
  unfold worthDig at hw ⊢
  split
  · rename_i hr
    rw [if_pos hr] at hw
    unfold K3WorthPlanes at hw ⊢
    rw [← e2]
    exact hw
  · rename_i hr
    rw [if_neg hr] at hw
    split
    · rename_i hr2
      rw [if_pos hr2] at hw
      unfold K3WorthKeys at hw ⊢
      beta_reduce at hw ⊢
      rw [← e2, ← e]
      exact hw
    · rename_i hr2
      rw [if_neg hr2] at hw
      exact he hw

theorem digitsPart_reads {P : Type} (m : ℕ) (a : P × Desc.First.S) (y : Strs)
    (w w' : Desc.Wit Cells Tok MsgT) (h : ∀ c ∈ readsDig X D L m, sameQ c w w')
    (hw : digitsPartK3 X D L m a y w) : digitsPartK3 X D L m a y w' := by
  unfold digitsPartK3 at hw ⊢
  unfold readsDig at h
  cases hx : digAt X m with
  | none =>
    rw [hx] at hw
    exact hw
  | some v =>
    rw [hx] at hw h
    have e : digMu v.1 D L.rad (fun j => L.seat v.1.link true j.1) L.arr w =
        digMu v.1 D L.rad (fun j => L.seat v.1.link true j.1) L.arr w' := by
      unfold digMu
      rw [msgsOf_congr D.codes (digList v.1 D L.rad) (L.seat v.1.link true) L.arr w w' h]
    show DgP.DigIn v.2 (enOf v.1.arrays) _
    rw [← e]
    exact hw

theorem worthAtt_reads (x : Desc.First.Look.Place) (A : Attention.Shape) (tl : HTailF2)
    (r : String) (s : Desc.First.S) (w w' : Desc.Wit Cells Tok MsgT) (els els' : Prop)
    (he : els → els')
    (h : ∀ c ∈ seatsComps L.arr (sigListCalls D L.rad x.link).length (L.seat x.link false),
      sameQ c w w')
    (hw : worthAtt D L x A tl r s w els) : worthAtt D L x A tl r s w' els' := by
  have e0 : attMs x D L.rad (fun j => L.seat x.link false j.1) L.arr w =
      attMs x D L.rad (fun j => L.seat x.link false j.1) L.arr w' := by
    unfold attMs
    exact msgsOf_congr D.codes (sigListCalls D L.rad x.link) (L.seat x.link false) L.arr w w' h
  have e : attMu x tl D L.rad (fun j => L.seat x.link false j.1) L.arr w =
      attMu x tl D L.rad (fun j => L.seat x.link false j.1) L.arr w' := by
    unfold attMu
    rw [e0]
  have e2 : attNu x A tl D L.rad (fun j => L.seat x.link false j.1) L.arr w =
      attNu x A tl D L.rad (fun j => L.seat x.link false j.1) L.arr w' := by
    funext q
    unfold attNu
    rw [e]
  unfold worthAtt at hw ⊢
  split
  · rename_i hr
    rw [if_pos hr] at hw
    unfold attWorthPlanes K3WorthPlanes at hw ⊢
    rw [← e2]
    exact hw
  · rename_i hr
    rw [if_neg hr] at hw
    split
    · rename_i hr2
      rw [if_pos hr2] at hw
      unfold attWorthKeys K3WorthKeys at hw ⊢
      beta_reduce at hw ⊢
      rw [← e2, ← e]
      exact hw
    · rename_i hr2
      rw [if_neg hr2] at hw
      split
      · rename_i hr3
        rw [if_pos hr3] at hw
        unfold attWorthRider K3WorthRider at hw ⊢
        rw [← e0]
        exact hw
      · rename_i hr3
        rw [if_neg hr3] at hw
        exact he hw

theorem worthLay_reads (hW : ∀ w w' : Desc.Wit Cells Tok MsgT, w.cells = w'.cells →
      L.msgW w = L.msgW w')
    (x : Desc.First.Look.Place) (q : LayPub) (tl : HTailF2)
    (r : String) (s : Desc.First.S) (w w' : Desc.Wit Cells Tok MsgT) (els els' : Prop)
    (he : els → els')
    (h : ∀ c ∈ Comp.cells ::
      seatsComps L.arr (sigListCalls D L.rad x.link).length (L.seat x.link false), sameQ c w w')
    (hw : worthLay D L x q tl r s w els) : worthLay D L x q tl r s w' els' := by
  have hc : L.msgW w = L.msgW w' := hW w w' (h .cells (List.mem_cons_self ..))
  have hm := msgsOf_congr D.codes (sigListCalls D L.rad x.link) (L.seat x.link false) L.arr w w'
    fun c hcm => h c (List.mem_cons_of_mem _ hcm)
  have e0 : layMs x D L.rad L.oW (fun j => L.seat x.link false j.1) L.arr L.msgW w =
      layMs x D L.rad L.oW (fun j => L.seat x.link false j.1) L.arr L.msgW w' := by
    unfold layMs layWt
    rw [hc, hm]
  have e : layMu x tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
        L.msgW w =
      layMu x tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
        L.msgW w' := by
    unfold layMu
    rw [e0]
  have e2 : layNu x q tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
        L.msgW w =
      layNu x q tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
        L.msgW w' := by
    funext p
    unfold layNu
    rw [e]
  unfold worthLay at hw ⊢
  split
  · rename_i hr
    rw [if_pos hr] at hw
    unfold layWorthPlanes K3WorthPlanes at hw ⊢
    rw [← e2]
    exact hw
  · rename_i hr
    rw [if_neg hr] at hw
    split
    · rename_i hr2
      rw [if_pos hr2] at hw
      unfold layWorthKeys K3WorthKeys at hw ⊢
      beta_reduce at hw ⊢
      rw [← e2, ← e]
      exact hw
    · rename_i hr2
      rw [if_neg hr2] at hw
      split
      · rename_i hr3
        rw [if_pos hr3] at hw
        unfold layWorthRider K3WorthRider at hw ⊢
        rw [← e0]
        exact hw
      · rename_i hr3
        rw [if_neg hr3] at hw
        exact he hw

/-! ## The field -/

/-- **worthK3 READS THE WITNESS THROUGH readsK3**, where what says the field elsewhere (f) reads it
through whatever makes hf true. -/
theorem worthK3_reads {P : Type} (hW : ∀ w w' : Desc.Wit Cells Tok MsgT, w.cells = w'.cells →
      L.msgW w = L.msgW w')
    (f : ℕ → ℕ → String → P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop)
    (m pc : ℕ) (r : String) (a : P × Desc.First.S) (y : Strs) (w w' : Desc.Wit Cells Tok MsgT)
    (hf : f m pc r a y w → f m pc r a y w')
    (h : ∀ c ∈ readsK3 X D L (.worth m pc r), sameQ c w w')
    (hw : worthK3 X D L f m pc r a y w) : worthK3 X D L f m pc r a y w' := by
  unfold worthK3 at hw ⊢
  have h' : ∀ c ∈ (match k3SortAt X m pc with
      | some true => readsDig X D L m
      | some false => readsCalls X D L m
      | none => []), sameQ c w w' := h
  cases hs : k3SortAt X m pc with
  | none =>
    rw [hs] at hw
    exact hf hw
  | some dg =>
    rw [hs] at hw h'
    cases dg with
    | true =>
      have h2 : ∀ c ∈ readsDig X D L m, sameQ c w w' := h'
      unfold readsDig at h2
      cases hx : digAt X m with
      | none =>
        rw [hx] at hw
        exact hf hw
      | some v =>
        rw [hx] at hw h2
        exact worthDig_reads D L v.1 v.2 r a.2 w w' _ _ hf h2 hw
    | false =>
      have h2 : ∀ c ∈ readsCalls X D L m, sameQ c w w' := h'
      unfold readsCalls at h2
      cases hx : attAt X m with
      | some v =>
        rw [hx] at hw h2
        exact worthAtt_reads D L v.1 v.2.1 v.2.2 r a.2 w w' _ _ hf h2 hw
      | none =>
        rw [hx] at hw h2
        cases hl : layAt X m with
        | none =>
          rw [hl] at hw
          exact hf hw
        | some x =>
          cases ht : tlAt X m with
          | none =>
            rw [hl, ht] at hw
            exact hf hw
          | some tl =>
            rw [hl, ht] at hw h2
            exact worthLay_reads D L hW x _ tl r a.2 w w' _ _ hf h2 hw

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.msgsOf_congr
#print axioms VerifiableInference.OnPublicFiles.worthDig_reads
#print axioms VerifiableInference.OnPublicFiles.digitsPart_reads
#print axioms VerifiableInference.OnPublicFiles.worthAtt_reads
#print axioms VerifiableInference.OnPublicFiles.worthLay_reads
#print axioms VerifiableInference.OnPublicFiles.worthK3_reads
