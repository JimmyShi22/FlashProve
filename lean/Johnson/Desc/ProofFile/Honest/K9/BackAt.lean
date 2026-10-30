-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BackAt.lean: FOR THE ITEM "totalB": THE NAMED SENTENCE `ItemBack`
(Honest/K9/TotalFront.lean) ITSELF, AT THE CALLERS' TEN ENTRIES, SORT BY SORT, FROM THE SEALED LIBRARY's GATHERING OF
A SORT's TIES AND LAWS. A definition, statements and proofs; no goal is stated.
  `zeros_lay`, `zeros_att`   at a state s with K9's part b and the promise at what is fixed at s: at (2, "front"), (2,
      "back") | (2, "first"), (2, "keys"), (2, "second"): the second hole silent at the entry and s, and the table's
      sentence "forms" there ⊢ every coefficient of the entry's terms is 0 (`eqs_layers`, `eqs_attention`,
      Honest/K9/EqAt.lean, with `zeros_of_eq`, `fx_self`, EqItem.lean)
  `itemBack_lay`, `itemBack_att`   so `ItemBack` at these entries, at every thread T and border b, at Front := fun s v
      => "the hole is silent at s" ∧ "forms" at s and the witness's tables
  `termsBack_mono`   `TermsBack` (so `ItemBack`) goes down in Front
  **`itemBack_lay_at`**, **`itemBack_att_at`**   AT THE TABLE's OWN HOLES (`K9.holesAt Xp mH m L`, m not the head's
      segment), AT Front := "forms" ALONE: silence there is the library's `H2K5.Door.silent_none`
  `RunAnswers`   A NAMED PREMISE AT THE STAND: at the head's five entries the run's own reader answers at the stand's
      state. IT HAS NO PAYER HERE. It is no clause of Front, which is fed from the open items' meanings alone, with no
      thread in hand; the library gets the like from "the tables are laid", and that from "reached"
      (`speaks_of_forms`, Johnson/Top/H0/MergeLaw/SpeaksOfTables.lean; Johnson/LPFE1R/HrunAnyAt.lean)
  **`itemBack_head`**   at the head's five: (3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge"), (3, "join"):
      under `RunAnswers`: at Front := "forms" ALONE, AT WHATEVER SECOND HOLE (`zeros_head`, Honest/K9/EqCarry.lean)
T, b, pw and, but for `RunAnswers`, the stand are not spent: these are sentences on the verifier's state and the
library's algebra. THE JOIN (`FrontShares.back`, TotalFront.lean) TAKES ONE Front OVER ALL OF THE LINK's ORDER: these
are its clauses at ten entries; the gathering over an order is not here. The letters are the sort's Take's own (u, ψ,
Ok, the sort's numbers, tm4, t3, l3); that Honest/K9/TotalFill.lean's filling is an instance (the Take there by the
library's `take_of_layersOwesC` and its sisters, as Honest/K9/TotalSeal.lean calls them): by reading, not typed. No
member; the three marked are called by no line.
WHAT IS NOT CLAIMED. The Take at any link. `RunAnswers` at any thread (at the frame's own thread at the library's
head: Honest/K9/RunAnswersAt.lean). Front at any state. What is left of the orders: the lookups' nine entries (objects
· planes · the attention's (2, "join")) and "K8.equations" (Honest/K9/TotalItems.lean, RestBack.lean); "guests" are
paid (TotalItems.lean). Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.EqCarry
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc

variable {β : Type}

/-- The zeros at a feed-forward segment's two entries. -/
theorem zeros_lay (H : Desc.K9.LinkHoles) {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {l3 : ℕ × String → Q β → ℕ} (A : LayersTake L u ψ Ok Fu p nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ))
    (rd : ℕ × ℕ → MsgQ) (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hOk : Ok (fixed9 (phiAll u ψ) s)) :
    ∀ o ∈ [(2, "front"), (2, "back")], H.silent o.1 o.2 s = none →
      formsQ (Desc.K9.readersOfLink H L) own o.1 o.2 s rd →
      ∀ n, ∀ c ∈ tmL p entUnit tm4 t3 o n (fixed9 (phiAll u ψ) s) (dataQ own b rd), c.2 = 0 :=
  fun o ho hsil hQ => zeros_of_eq _ _ _ own rd o s b hb
    (eqs_layers H A own rd s b hb (fx_self _ Ok s b hb hOk) o ho hsil (formsQ_in _ own o.1 o.2 s rd hQ)) hQ

/-- The zeros at an attention segment's three entries. -/
theorem zeros_att (H : Desc.K9.LinkHoles) {L : Link S Claim} {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {rdA : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rdA c nU entUnit tm4 t3 l3) (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (s : S)
    (b : Desc.K9.Part) (hb : atS.get? s = some b) (hOk : Ok (fixed9 (phiAll u ψ) s)) :
    ∀ o ∈ [(2, "first"), (2, "keys"), (2, "second")], H.silent o.1 o.2 s = none →
      formsQ (Desc.K9.readersOfLink H L) own o.1 o.2 s rd →
      ∀ n, ∀ x ∈ tmA rdA c entUnit tm4 t3 o n (fixed9 (phiAll u ψ) s) (dataQ own b rd), x.2 = 0 :=
  fun o ho hsil hQ => zeros_of_eq _ _ _ own rd o s b hb
    (eqs_attention H A own rd s b hb (fx_self _ Ok s b hb hOk) o ho hsil (formsQ_in _ own o.1 o.2 s rd hQ)) hQ

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ) (pw : Desc.K9.Where)
  (own : List (ℕ × ℕ)) (rdW : T.Wt → ℕ × ℕ → MsgQ) (H : Desc.K9.LinkHoles) {L : Link S Claim} {u : HTailF2}
  {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop} {nU : Array ℕ} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
  {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}

/-- **`ItemBack` at a feed-forward segment's two entries.** -/
theorem itemBack_lay {p : OnBytes.Desc.First.K4.Par} (A : LayersTake L u ψ Ok Fu p nU entUnit tm4 t3 l3) :
    ∀ o ∈ [(2, "front"), (2, "back")],
      ItemBack L pw (phiAll u ψ) Ok (tmL p entUnit tm4 t3) T b own rdW o fun s v =>
        H.silent o.1 o.2 s = none ∧ formsQ (Desc.K9.readersOfLink H L) own o.1 o.2 s (rdW v) :=
  fun o ho _ s _ _ _ _ _ _ _ _ _ _ a v ha hOk hF => zeros_lay H A own (rdW v) s a ha hOk o ho hF.1 hF.2

/-- **`ItemBack` at an attention segment's three entries.** -/
theorem itemBack_att {rdA : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    (A : AttTake L u ψ Ok Fu rdA c nU entUnit tm4 t3 l3) :
    ∀ o ∈ [(2, "first"), (2, "keys"), (2, "second")],
      ItemBack L pw (phiAll u ψ) Ok (tmA rdA c entUnit tm4 t3) T b own rdW o fun s v =>
        H.silent o.1 o.2 s = none ∧ formsQ (Desc.K9.readersOfLink H L) own o.1 o.2 s (rdW v) :=
  fun o ho _ s _ _ _ _ _ _ _ _ _ _ a v ha hOk hF => zeros_att H A own (rdW v) s a ha hOk o ho hF.1 hF.2

/-- `TermsBack` goes down in Front. -/
theorem termsBack_mono {α : Type} {φ : S → α} {Ok' : α × Option Pub9 → Prop}
    {tm : ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)} {F F' : S → T.Wt → Prop}
    (h : ∀ s v, F' s v → F s v) (B : TermsBack L pw φ Ok' T b own rdW tm F) :
    TermsBack L pw φ Ok' T b own rdW tm F' :=
  fun κ s m En ds y cols s' x z G hS a v ha hOk hF => B κ s m En ds y cols s' x z G hS a v ha hOk (h s v hF)

/-- **"The run's own reader answers at the stand's state", at the head's five entries.** A NAMED PREMISE: it is no
clause of Front, which is fed from the open items' meanings alone: it wants the thread (the tables are laid at a state
that is reached). -/
def RunAnswers : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand L pw T b κ s m En ds y cols s' x z G →
    ∀ o ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge"), (3, "join")],
      (Desc.K9.readerOf (Desc.K9.statesOfLink L) o.1 o.2 s).isSome = true

/-- **`ItemBack` at the head's five entries, at whatever second hole, at Front := "forms" alone.** -/
theorem itemBack_head {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Kinds.Head.Par}
    {kap : Phi β → Option Kinds.Head.Law.Seen}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU entUnit tm4 t3 l3) (hrun : RunAnswers T b pw (L := L)) :
    ∀ o ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (8, "the merge"), (3, "join")],
      ItemBack L pw (phiAll u ψ) Ok (tmH h iU3 p kap entUnit tm4 t3) T b own rdW o fun s v =>
        formsQ (Desc.K9.readersOfLink H L) own o.1 o.2 s (rdW v) :=
  fun o ho κ s m En ds y cols s' x z G hS a v ha hOk hF =>
    zeros_head H A own (rdW v) s a ha hOk o ho (hrun κ s m En ds y cols s' x z G hS o ho) hF

/-- **Off the head, at the table's own holes: Front := "forms" alone**: at a feed-forward segment. -/
theorem itemBack_lay_at (Xp : OnBytes.Model.Verify.Public) {mH m : ℕ} (hm : (m == mH) = false)
    {p : OnBytes.Desc.First.K4.Par} (A : LayersTake L u ψ Ok Fu p nU entUnit tm4 t3 l3) :
    ∀ o ∈ [(2, "front"), (2, "back")],
      ItemBack L pw (phiAll u ψ) Ok (tmL p entUnit tm4 t3) T b own rdW o fun s v =>
        formsQ (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH m L) L) own o.1 o.2 s (rdW v) :=
  fun o ho => termsBack_mono T b pw own rdW
    (fun s _ hF => ⟨by rw [H2K5.Door.silent_none Xp hm L], hF⟩)
    (itemBack_lay T b pw own rdW (Desc.K9.holesAt Xp mH m L) A o ho)

/-- The same at an attention segment. -/
theorem itemBack_att_at (Xp : OnBytes.Model.Verify.Public) {mH m : ℕ} (hm : (m == mH) = false)
    {rdA : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    (A : AttTake L u ψ Ok Fu rdA c nU entUnit tm4 t3 l3) :
    ∀ o ∈ [(2, "first"), (2, "keys"), (2, "second")],
      ItemBack L pw (phiAll u ψ) Ok (tmA rdA c entUnit tm4 t3) T b own rdW o fun s v =>
        formsQ (Desc.K9.readersOfLink (Desc.K9.holesAt Xp mH m L) L) own o.1 o.2 s (rdW v) :=
  fun o ho => termsBack_mono T b pw own rdW
    (fun s _ hF => ⟨by rw [H2K5.Door.silent_none Xp hm L], hF⟩)
    (itemBack_att T b pw own rdW (Desc.K9.holesAt Xp mH m L) A o ho)

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.zeros_lay
#print axioms ProofFile.Honest.K9.zeros_att
#print axioms ProofFile.Honest.K9.itemBack_lay
#print axioms ProofFile.Honest.K9.itemBack_att
#print axioms ProofFile.Honest.K9.termsBack_mono
#print axioms ProofFile.Honest.K9.itemBack_head
#print axioms ProofFile.Honest.K9.itemBack_lay_at
#print axioms ProofFile.Honest.K9.itemBack_att_at
