-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/InAtOfThr.lean: THE BRIDGE FROM THE THREADS' INVARIANT TO THE
FORM IN WHICH THE LIBRARY's LAWS OF THE KIND K1 TAKE THE PROMISE IN FRONT: WHEREVER THE FIRST
CHAIN's THREAD HOLDS (Thr, Honest/Thread/Thr.lean), K1.InAt (Johnson/Desc/K1/Law/KeepAtLater.lean:
"the promise in front of block k, whole, and no mark") HOLDS AT THE THREAD's OWN LETTERS, AT THE
MEANING ADAPTED TO THE HONEST SIDE (L.mgP), AT EVERY STRINGS y. Four theorems; no definition.

THIS LETTER IS FOR THE HONEST RUN's OWN FORMS ALONE: NO STATEMENT ON ANY OTHER PARTY MAY TAKE IT.
NEVER ON SOUNDNESS's ROAD. (A fence. WHY: L.mgP is
"honest" (Honest/Thread/First.lean) of a meaning: at it three fields that read the oracles' strings
are True by definition: so InAt at it ASKS LESS than InAt at the library's own meaning. THE FIRST
REVIEWER's OWN WORDS, QUOTED, NO WORD OF OURS ON ANY PROPERTY: "a meaning at which noColl, shown or
decodes is True by definition [...] may stand beneath completeness or zero-knowledge statements
only, NEVER beneath sound_of_verify_at or any front statement on soundness".)

  - inAt_of_thr   AT ANY LETTERS L, any border b, any strings y: Thr L.thread b k s m E gives
                  K1.InAt L.N L.mgP L.links L.ps b (L.pubOf m.st.input.x, s) y.
  - inAt_of_thrS  the same from ThrS (Honest/Thread/Said.lean): Thr and Said.
  - inAt_head     UNDER h (the library's head: A HYPOTHESIS), at ProofFile's lettersHead, WITH EVERY
                  LETTER SPELLED AS THE LIBRARY's LAWS SPELL IT: the numbers h.𝔇.N · the meaning
                  honest (mgAll h.𝔇 mgBase) ‹the letters' ans› test · the sorts linksFull · the
                  places flatPlacesOf linksFull true.
  - inAt_marked_fails   A NEGATIVE TEST ON THE FORM: at a state with a mark InAt is false, whatever
                  the other letters are: so the bridge says something of the state.

BY OTHER LAWS. formP_iff (the thread's clause on the promise IS the library's onAt at L.mgP, at
any strings: by rfl) and partsAt_of_thr (no mark) are in Honest/Small/FormParts.lean.
What is new here is the form alone: InAt's two halves in one, at K1's own name, and the head's
spelling. KIN (this file does not call them; THEIR STATEMENTS ARE NOT K1.InAt): from Thr, the
promise and no mark: onAt_of_thr, failed_of_thr (Honest/K3/Law/Thread/AtBorder.lean: general in
the first chain's letters); onAt_of_thr (Honest/K5/Law/Front.lean: at the kind's border).

Limits. IT PAYS NOTHING: Thr is a hypothesis: a definition of which nothing is claimed. y IS IDLE:
at L.mgP the three clauses that read the strings hold outright. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Small.FormParts
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.K1.Law.KeepAtLater
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (S Numbers Meaning ModelPart flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT linksFull mgAll mgBase)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.Small (formP_iff partsAt_of_thr)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- **WHEREVER THE THREAD HOLDS, THE PROMISE IN FRONT HOLDS IN K1's FORM**, at any letters, any
border, any strings. -/
theorem inAt_of_thr {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
    (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr L.thread b k s m E) (y : Strs) :
    K1.InAt L.N L.mgP L.links L.ps b (L.pubOf m.st.input.x, s) y :=
  ⟨(formP_iff L b (L.pubOf m.st.input.x, s) y).1 hT.2.2.1.2, (partsAt_of_thr L hT).1⟩

/-- The same from the invariant with Said. -/
theorem inAt_of_thrS {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}
    (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : ThrS L.thread Said b k s m E) (y : Strs) :
    K1.InAt L.N L.mgP L.links L.ps b (L.pubOf m.st.input.x, s) y :=
  inAt_of_thr L hT.1 y

/-- **AT lettersHead, EVERY LETTER SPELLED AS THE LIBRARY's LAWS SPELL IT.** -/
theorem inAt_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {b : Nat} {k : Coins Bk}
    {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s μ E)
    (y : Strs) :
    K1.InAt h.𝔇.N
      (honest (mgAll h.𝔇 mgBase) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ans test)
      linksFull (flatPlacesOf linksFull true) b (μ.st.input.x.pub, s) y :=
  inAt_of_thrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said hT y

/-- A negative test on the form: at a state with a mark InAt is false. -/
theorem inAt_marked_fails {P W : Type} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (a : P × S) (y : Strs) (t : String) (hm : a.2.failed = some t) :
    ¬ K1.InAt N Mg links ps k a y := by
  intro hI
  rw [hI.2] at hm
  cases hm

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.inAt_of_thr
#print axioms ProofFile.Honest.K1.inAt_of_thrS
#print axioms ProofFile.Honest.K1.inAt_head
#print axioms ProofFile.Honest.K1.inAt_marked_fails
