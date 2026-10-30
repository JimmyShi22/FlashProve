-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsAtSem.lean: THE LAST JOIN OF THE LINE "forms": from forms_kept
(Johnson/Road/K4/FormsKept.lean), whose conclusion stands at semQ, a Sem that hangs on the
verifier's state, TO THE SENTENCE FormsT AT THE LAW's OWN Sem: QK.semOf part tl
(Johnson/Road/K4/CloseFill.lean), which is one for all states: the conclusion of the line
K4Lines.forms (Johnson/Road/K4/CloseAtTable.lean), to the letter, at tl := p.hp.tl.

  `runs_marks`: behind K4's two runs the ledgers' arrays of marks are at most as long as the number
    of slots of the ledger from which "front" started, where that ledger has arrays of the right
    sizes.
  `forms_at_sem`: THE JOIN.
No new argument: formsT_sem (Johnson/Road/K4/FormsOfItem.lean), entryTrue_cells
(Johnson/Road/K4/EntryCells.lean).
Limits. PREMISES of forms_at_sem: all nine of forms_kept, AND TWO EQUATIONS OF READERS OF ONE
WITNESS, each asked only where the sentence reads:
  hm: BELOW THE LEDGER's NUMBER OF SLOTS the value's mask row (QK.maskAt (part w)) is the table's
    data's. Its payer speaks below the mask row's length: so "the number of slots is at most that
    length" is owed beside it: a test on the public parameters.
  hM: INSIDE THE RANGES OF tl the value's matrices (QK.mats (part w)) are M at the table's data.
Neither is paid here. M and tl are letters. NOT HERE: that the forms are worth 0 anywhere. Met
through Lean at no member. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.


-/
import Johnson.Road.K4.FormsKept
import Johnson.Road.K4.EntryCells
import Johnson.Road.K4.CloseFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4.InT (StatesAt kept_open)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K9 (segAt? LinkHoles statesOfLink readersOfLink)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated second dataQ formsTQ)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)

/-- Behind K4's two runs the arrays of marks are at most as long as the first ledger's number of
slots, under sG. -/
theorem runs_marks {p : Par} {o : Own} {G F₁ F₂ : Fork} {fs₁ fs₂ : Array Aff}
    (sG : PscRun.Sized G) (h1 : frontRun p o G = some (fs₁, F₁))
    (h2 : formsBack o F₁ = some (fs₂, F₂)) : F₁.gotF.size ≤ G.ns ∧ F₂.gotF.size ≤ G.ns := by
  have L1 : Later G F₁ := OnBytes.Desc.First.K4.formsFrontWith_later h1
  have L2 : Later F₁ F₂ := OnBytes.Desc.First.K4.formsBack_later h2
  have s1 := L1.sized sG
  have s2 := L2.sized s1
  exact ⟨by rw [s1.2.2, L1.ns], by rw [s2.2.2, L2.ns, L1.ns]⟩

/-- **THE LAST JOIN**, under forms_kept's nine and hm, hM. -/
theorem forms_at_sem [scl : Inst.Model.Scl] {Wt Mm : Type} {St : Stated} (QK : Plan4K Mm S)
    (part : Wt → Mm)
    (M : S → Bound GQ → Mats GQ) (H : LinkHoles) (l : Link S Claim) (own : List (ℕ × ℕ))
    (rd : Wt → ℕ × ℕ → MsgQ) (w : Wt) {p : Par} {s s' : S} {P₀ : Pub} {o₀ : Own} {tl : HTailF2}
    (K : KeptAtS p s s') (A : KeptAsks p s s' P₀ o₀)
    (hN : ∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F)
    (hB : readsArrayB p.hp s' = true) (hs1 : StatesAt (statesOfLink l) 2 p "front" s')
    (hs2 : StatesAt (statesOfLink l) 2 p "back" s') (hk : p.k3Runs = true)
    (X : ∀ A' o c, segAt? s' = some A' → s'.own? = some o → A'.L.arrayOf[o.v.iU3]? = some c →
      second s' c = true → StatedAt St M s' tl o c (p.hp.nU.getD 2 0) (dataQ own A' (rd w)))
    (Item : ∀ q ∈ [(2, "front"), (2, "back")],
      formsTQ (readersOfLink H l) St own q.1 q.2 s' (rd w))
    (hm : ∀ A' G, segAt? s' = some A' → s'.fork? = some G → ∀ j, j < G.ns →
      QK.maskAt (part w) j = (dataQ own A' (rd w)).mask j)
    (hM : ∀ A', segAt? s' = some A' →
      InRange tl (QK.mats (part w)) (M s' (dataQ own A' (rd w)))) :
    FormsT seatS (QK.semOf part tl) (frontRun p) formsBack s' w := by
  obtain ⟨A', hA', hT⟩ := forms_kept M H l own rd w K A hN hB hs1 hs2 hk X Item
  obtain ⟨a, a', fo, o, G, t, u, ha, hfo, ha', eF, eo, ho', hG', hh⟩ := kept_open K
  have sG : PscRun.Sized G := (OnBytes.Desc.First.K4.hearFl_later hh).sized (A.sized a ha)
  have hfork : seatS.fork s' = G := by
    show (match s'.here with | .lay a => a.F | _ => {}) = _
    rw [ha']
    exact eF
  refine formsT_sem (Sm := semQ tl M s' fun w => dataQ own A' (rd w)) (Sm' := QK.semOf part tl)
    (n := G.ns) (hm A' G hA' hG') (fun o' _ => entryTrue_cells (hM A' hA') o')
    (fun o' fs₁ F₁ fs₂ F₂ h1 h2 => ?_) hT
  rw [hfork] at h1
  exact runs_marks sG h1 h2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.runs_marks
#print axioms OnBytes.Road.K4.forms_at_sem
