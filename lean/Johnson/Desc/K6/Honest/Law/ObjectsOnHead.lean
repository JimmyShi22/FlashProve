-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/ObjectsOnHead.lean: THE SENTENCE OF THE OPEN CLAIM formsT 24 3 "objects"
GOES FORWARD OVER A YES OF THE SUB-PROTOCOL "the output head's own rounds" (K6), AT THE CLOSED TERM
FOR THE COMPOSED MEANING, mgAtAll h (Johnson/P5J/MgAtAll.lean), UNDER ITS ONE HEAD AtMgA, at a state
that the first chain's first 341 sub-protocols reach. BOTH THEOREMS ARE CONDITIONAL: h (the head) ·
hr (the state in front is reached at border 341) · K (what a yes leaves of the state: `K6Keeps`,
Honest/Law/Keeps.lean) · the sentence in front. NO PROMISE OF THE TABLE IS ASKED.

  `objects_on_head_runs`  the sentence's first clause, at any reader rd of the witness's tables
  `objects_on_head`       THE SENTENCE at mgAtAll h

How: calls. Every premise of `objects_on_runs` (Honest/Law/ObjectsOnAll.lean) but K and the sentence
is a fact under the head or at a reached state: the two facts on link 24's list of rounds
(`P4.six_at_head`, Johnson/Desc/Kinds/Law/K6StateAtHead.lean) · the runs' readers and the sort of
segment 24 (`paid_at_const`, Johnson/Desc/Kinds/Law/K06AtConst.lean) · which runs stand under the
name (`runs_at_head`, Johnson/Desc/Kinds/Law/K6PubMore.lean) · a ledger is open with its sizes
(`P4.free_at_341`, Johnson/P4R/FreeAt341N.lean, with `sized_iff`,
Johnson/Desc/Kinds/Law/GrowsAt.lean) · no kept row names an entry (`P4.bare_341`,
Johnson/P4R/BareAt341.lean).

Limits. THAT AtMgA CAN BE MET: the library's own files under that head say "no example". That any
state is reached at border 341, or that a yes is said there: not shown here. NOTHING HERE SAYS THAT
A FORM IS WORTH 0 AT ANY STATE: the sentence in front is a premise. THE FULL SIZE ALONE, and the
format's second hash function alone. Modules under lean/Johnson/Goal/ are among what this file imports: it
imports no module of that folder by name and calls nothing that is declared there. Nothing on any
property.
-/
import Johnson.Desc.K6.Honest.Law.ObjectsOnAll
import Johnson.Desc.Kinds.Law.K06AtConst
import Johnson.Desc.Kinds.Law.K6StateAtHead
import Johnson.Desc.Kinds.Law.K6PubMore
import Johnson.P4R.FreeAt341N
import Johnson.P4R.BareAt341

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT MsgQ formsTQ)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)

/-- **At each run under the name the sentence goes forward.** CONDITIONAL: h; hr; K; hw: the
sentence's first clause in front. -/
theorem objects_on_head_runs {XP : Type} {start : XP → S} {π : XP} {s s' : S}
    (hr : Reach 0 cF.blocksInOrder start 341 (π, s)) (K : K6Keeps s s') (rd : ℕ × ℕ → MsgQ)
    (hw : ∀ p ∈ h.𝔇.runs 24 3 "objects",
      formsTQ (h.𝔇.Rd 24) h.𝔇.St (h.𝔇.N.sent 24 0) p.1 p.2 s rd) :
    ∀ p ∈ h.𝔇.runs 24 3 "objects",
      formsTQ (h.𝔇.Rd 24) h.𝔇.St (h.𝔇.N.sent 24 0) p.1 p.2 s' rd := by
  obtain ⟨Bs, base0, O⟩ := h.laid.opened
  obtain ⟨Lk, hl, six⟩ := P4.six_at_head h
  have Pd := Law.AtTable.paid_at_const h Lk hl
  obtain ⟨G, hG, hs, -⟩ :=
    P4.free_at_341 h.scope h.reads O (P4.plan_at O h.laid.planOk 340) hr
  have hG' : s.fork? = some G := hG
  exact objects_on_runs h.𝔇 24 Pd.readers (Law.AtTable.runs_at_head h.𝔇 Pd.sorts).1
    six.2.2.2.2.1 six.2.2.2.2.2 K ((Law.sized_iff hG').2 hs)
    (P4.bare_341 h.scope h.reads O h.laid.planOk hr) rd hw

/-- **THE SENTENCE OF THE OPEN CLAIM formsT 24 3 "objects" GOES FORWARD, AT THE CLOSED TERM.**
CONDITIONAL: h; hr; K; hw: the sentence in front. -/
theorem objects_on_head {XP : Type} {start : XP → S} {π : XP} {s s' : S}
    (hr : Reach 0 cF.blocksInOrder start 341 (π, s)) (K : K6Keeps s s') (z z' : ProofFile.InstPub)
    (y y' : Strs) (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hw : (mgAtAll h).formsT 24 3 "objects" (z, s) y w) :
    (mgAtAll h).formsT 24 3 "objects" (z', s') y' w :=
  ⟨objects_on_head_runs h hr K _ hw.1, fun e => absurd e (by decide)⟩

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.objects_on_head_runs
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.objects_on_head
