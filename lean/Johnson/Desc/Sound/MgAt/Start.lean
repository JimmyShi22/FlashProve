-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/Start.lean: WHAT THE FIRST BORDER's PROMISE READS OF THE COMPOSED MEANING "mgAll 𝔇 Mg" (WITH the small list of extra public tests; Johnson/Desc/Sound/MgAll.lean), AT A LAWFUL FIRST STATE OF THE VERIFIER: EVERY ITEM, WITH WHO ANSWERS IT, AT A CLOSED BASE, UNDER ONE PREMISE ON THE TABLE's NUMBERS.
The tests on every reached state stand off the table, booked apart. General in every letter of 𝔇.

THE LETTER OF THE TOPS' LAWS. By mgAll_is_tower the term at which the tops' laws are stated is meaningQ … (meaningSig … (withReq 𝔇.reqB ‹M›)) at M := mgLetter 𝔇 Mg₀: the runs' forms' layer over shut Mg₀ (mgBelow 𝔇 Mg₀). The facts on a start are asked at MS := meaningSig … M.
A LAWFUL FIRST STATE: (S.firstRecord codes shape layout).withReq req, AT ANY codes | shape | layout | words: no oracle message, no group, no reply heard.
WHAT IS READ THERE, AND WHO ANSWERS:
  inOrder: Mg₀'s own (ms_inOrder := rfl): the base: true.
  pub .unheard [the table's own layer: no reply has been heard] · pub .noneSent [three of the clauses of K13.noneSentC (Johnson/Desc/K13/PubK13.lean): none sent · none "at the start" · as many groups as the numbers' groupAt 0: noneSentC_first, UNDER 𝔇.N.groupAt 0 = 0].
  NO FURTHER ITEM IS OPEN AT THE START (start_list: mgMore_start := []).
  pubP at these two: no layer lays a sentence at either: the base's own.
start_order · start_items_at (for a caller that holds "s is the lawful first state") · start_says: AT Mg₀ WITH inOrder := fun _ => true · more := {} · AND ITS OWN SENTENCE HOLDING AT THE TWO ITEMS (its sentence is "the table saysNone (Johnson/Desc/First/AllSaid.lean) says that no sentence is meant at the item").

Limits. Values at one kind of state. That a first state of a description IS lawful is the caller's. Cheap, and rightly. Nothing says that any witness meets the items. NO MEMBER. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.FillStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (Meaning Numbers Pub pubStartM pubAll)

theorem noneSentC_first (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (layout : OnBytes.Params.ReqLayout) (req : Array UInt32) (N : Numbers) (h : N.groupAt 0 = 0) :
    K13.noneSentC N ((First.S.firstRecord codes shape layout).withReq req) = true := by
  simp [K13.noneSentC, First.S.firstRecord, First.S.withReq, h]

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The tops' laws' letter at the composed meaning.** -/
noncomputable def mgLetter : Meaning P (Wit (CellsQ rows cols) Tok MsgT) :=
  meaningForms 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.Rd 𝔇.runs 𝔇.St 𝔇.after 𝔇.N 𝔇.wt 𝔇.rw 𝔇.ah (shut Mg₀ (mgBelow 𝔇 Mg₀))

local notation "MS" => meaningSig 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.decT (mgLetter 𝔇 Mg₀)

theorem ms_pub : (MS).pub = pubAll 𝔇.pubD Mg₀.pub := rfl
theorem ms_more : (MS).more = (mgAll 𝔇 Mg₀).more := rfl
theorem ms_pubP : (MS).pubP = (mgAll 𝔇 Mg₀).pubP := rfl
theorem ms_inOrder (a : P × First.S) : (MS).inOrder a = Mg₀.inOrder a := rfl

/-- What is open at the chain's start, at a base that opens nothing: two items. -/
theorem start_list (h3 : Mg₀.more = {}) : pubStartM (MS).more = [.unheard, .noneSent] := by
  rw [ms_more, mgAll_more_closed 𝔇 Mg₀ h3]
  rfl

variable {𝔇 Mg₀}

/-- **"In order".** -/
theorem start_order (h1 : Mg₀.inOrder = fun _ => true) (a : P × First.S) : (MS).inOrder a = true := by
  rw [ms_inOrder, h1]

/-- **Every public item that is open at the chain's start holds at a lawful first state.** -/
theorem start_items_at (h3 : Mg₀.more = {}) (hG : 𝔇.N.groupAt 0 = 0) (p : P) (s : First.S)
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (layout : OnBytes.Params.ReqLayout)
    (req : Array UInt32) (hs : s = (First.S.firstRecord codes shape layout).withReq req) :
    ∀ q ∈ pubStartM (MS).more, (MS).pub q (p, s) = true := by
  subst hs
  intro q hq
  rw [start_list 𝔇 Mg₀ h3] at hq
  rw [ms_pub]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl
  · exact First.unheardB_first codes shape layout req
  · exact noneSentC_first codes shape layout req 𝔇.N hG

/-- **And its sentence**: no layer lays one at either. -/
theorem start_says (h2 : ∀ a, Mg₀.pubP .unheard a ∧ Mg₀.pubP .noneSent a) (h3 : Mg₀.more = {})
    (a : P × First.S) :
    ∀ q ∈ pubStartM (MS).more, (MS).pubP q a := by
  intro q hq
  rw [start_list 𝔇 Mg₀ h3] at hq
  rw [ms_pubP, mgAll_pubP]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl
  · exact (h2 a).1
  · exact (h2 a).2

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.noneSentC_first
#print axioms VerifiableInference.Desc.Sound.start_list
#print axioms VerifiableInference.Desc.Sound.start_order
#print axioms VerifiableInference.Desc.Sound.start_items_at
#print axioms VerifiableInference.Desc.Sound.start_says
