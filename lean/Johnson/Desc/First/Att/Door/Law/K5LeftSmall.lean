-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5LeftSmall.lean: kind K5: SMALL PAYERS at the common letters of K5Left's assembly (Door/Law/K5AtEqsPlus.lean · K5GainsPlus.lean · K5LeftFitsB.lean): each pays one premise of a field's theorem from an equation on the filling (MgIs.pub · MgGains.formsT), the
table's own map of names, or a definition's make.
Main names:
  onAt_tied: under the promise and "no mark" the public tests TIED TO THE OPEN ITEMS hold (onAt_pub's twin half: Att/K05T2.lean speaks of the list Q; this of pubOfItems O).
  hlook_plus: the filling's Bool at the item look m, at an attention segment, is lookAttB (pubAll_look_att, Johnson/Desc/First/PubAllAt.lean).
  hTo_plus · hFrom_plus: the item formsT m 2 "objects" against the two sentences at its two runs (1, "objects") · (1, "guests") (MgGains.formsT; the name is not "weights").
  hIn_plus: the public test at (1, "objects") in front, from the promise (onAt_tied · pubAll_formsInT, Johnson/Desc/First/PubAllAt.lean).
  hMask_plus: the stated data keep the mask row (of_mask, Johnson/Desc/Sound/FormsT.lean).
  hms_plus: the lookup argument's files' reading of the witness's messages, at the pin's own seats and numbering of arrays, IS the filled pin's part: by the two definitions' make.
IS IT EMPTY HERE? Implications and two equations by rfl.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5GainsPlus
import Johnson.Desc.First.Att.K05BehindAtTable
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent sigListCalls)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.OnPublicFiles (attMs)
open VerifiableInference.Desc.First.Att.P

/-- **Under the promise and "no mark" the tests tied to the open items hold.** -/
theorem onAt_tied {P W : Type} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {p : VerifiableInference.Desc.Place} {O : List Item}
    {Q : List Pub} {a : P × S} {y : Strs} (h : onAt N Mg links (some p) O Q a y) (hu : a.2.failed = none) :
    ∀ q ∈ pubOfItems O, Mg.pub q a = true := by
  obtain ⟨_, hm | ⟨h1, _, _, _⟩⟩ := h
  · exact absurd hu hm
  simp only [Bool.and_eq_true] at h1
  have c5 := h1.1.2
  unfold pubHeld at c5
  exact fun q hq => List.all_eq_true.1 c5 q (List.mem_append_right _ hq)

section
variable {Pp Cells Tok : Type} {Mg : Meaning Pp (Wit Cells Tok MsgT)}

theorem hlook_plus {D : PubData} {base : Pub → Pp × S → Bool} (hpub : Mg.pub = pubAll D base) {m : ℕ} (hmH : (m == D.mH) = false)
    (hlay : FillK4.isLay D.links m = false) (hatt : D.d5.isAtt m = true) :
    ∀ (π : Pp) (s : S), Mg.pub (.look m) (π, s) = lookAttB s := by
  intro π s
  rw [hpub]
  exact pubAll_look_att D base m hmH hlay hatt (π, s)

section Gains
variable {cs : Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem} {Rd : ℕ → Readers} {runs : ℕ → ℕ → String → List (ℕ × String)} {St : Stated}
  {N : Numbers} {wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop} {m₀ : ℕ} {x : Look.Place} {A : Attention.Shape} {tl : HTailF2}
  {Dn : Sent} {rad : OracleShape → ℕ} {seatT : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ} {arrL : ℕ → ℕ → ℕ}
  (G : MgGains Mg cs arr ms Rd runs St N wt m₀ x A tl Dn rad seatT arrL) {m : ℕ}
  (hr : runs m 2 "objects" = [(1, "objects"), (1, "guests")])
include G hr

theorem hTo_plus : ∀ (π : Pp) t y w, Mg.formsT m 2 "objects" (π, t) y w →
    formsTQ (Rd m) St (N.sent m 0) 1 "objects" t (seatTab cs arr ms w) :=
  fun π t y w h => hfT_plus G m 2 "objects" (π, t) y w h (1, "objects") (by rw [hr]; simp)

theorem hFrom_plus : ∀ (π : Pp) t y w, formsTQ (Rd m) St (N.sent m 0) 1 "objects" t (seatTab cs arr ms w) →
    formsTQ (Rd m) St (N.sent m 0) 1 "guests" t (seatTab cs arr ms w) → Mg.formsT m 2 "objects" (π, t) y w := by
  intro π t y w h1 h2
  rw [G.formsT]
  refine ⟨fun p hp => ?_, fun h => absurd h (by decide)⟩
  rw [hr] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1
  · exact h2

end Gains

theorem hIn_plus {Fr : Frame} {D : PubData} {base : Pub → Pp × S → Bool} (hpub : Mg.pub = pubAll D base) {m : ℕ}
    (hr : D.runs m 2 "objects" = [(1, "objects"), (1, "guests")]) {links : List ModelPart} {pl : VerifiableInference.Desc.Place} {O : List Item}
    {Q : List Pub} (hO : Pub.formsInT m 2 "objects" ∈ pubOfItems O) :
    ∀ (π : Pp) s (y : Fr.E.Str), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      K9.formsInT (D.Rd m) (D.N.sent m 0) 1 "objects" s = true := by
  intro π s y hon hm
  have h := onAt_tied hon hm _ hO
  rw [hpub, pubAll_formsInT, hr] at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact h.1

end

theorem hMask_plus (u : S → VerifiableInference.Desc.K9L.Bound GQ → ℕ × String → ℕ → ℕ → GQ) : ∀ t Dt, ((Stated.of u).at1 t Dt).mask = Dt.mask := fun _ _ => rfl

/-- **The two readings of the witness's messages are one**, at the pin's own seats and numbering of arrays. -/
theorem hms_plus {Xi Cells Tok : Type} (G0 : FileDescription Xi) (x : Look.Place) (Dn : Sent) (rad : OracleShape → ℕ)
    (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)
    (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls Dn rad x.link).length) →
      Option ((Johnson.Pack.sigOf Dn.codes (sigListCalls Dn rad x.link)).om i).Smp)
    (arr : ℕ → ℕ → ℕ) (Fr : Frame) (bs : ℕ) (hlow : ∀ i, (seat i).1 < bs) :
    ∀ w, attMs x Dn rad seat arr w = (k5Pin (Cells := Cells) (Tok := Tok) G0 x Dn rad seat smpR arr Fr bs hlow).part w :=
  fun _ => rfl

end H2K5.Door

#print axioms H2K5.Door.onAt_tied
#print axioms H2K5.Door.hlook_plus
#print axioms H2K5.Door.hTo_plus
#print axioms H2K5.Door.hFrom_plus
#print axioms H2K5.Door.hIn_plus
#print axioms H2K5.Door.hMask_plus
#print axioms H2K5.Door.hms_plus
