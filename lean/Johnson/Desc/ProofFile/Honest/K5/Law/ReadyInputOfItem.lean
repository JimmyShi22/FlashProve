-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReadyInputOfItem.lean: conditional: under the library's head and its test
protocolDataWellFormed, some input meets the condition "ReadyInput" (Honest/Thread/ReadyInput.lean) at the head's description and at
the prover that the frame's maker "onlineProverFromPublicFiles" returns at a filling with the full-size trace, if one sentence on the
public files holds: the clause on the request's item (E2E/StartAtFiles.lean, the field "item" of "StartHeld"), or
one of three lighter sentences. Calls of laws that stand in the library; no definition; nothing is evaluated.

"ReadyInput F H v" has three clauses. Each, with what gives it here:
  the instance passes the description's first test okStart
        okStart_of_item, okStart_of_one (E2E/StartInScope.lean): in scope, from the clause on the item, or from one
        accept: at what the library writes for every instance of the full size's type, at every OOD sample
  the index is in range
        at the full-size filling the range is in the index's type: "inRange" is constant (Honest/AtPureFullIn.lean)
  the prover's trace returns at the index and the instance
        servedTyped_exists (Johnson/FrontRoad/ServedExists.lean): there are an index and a typed request that the
        index serves; instOf_at_frame (ProofFile/InstOfTies.lean): what the library writes for it is read back;
        fullIn_trace_served (Honest/AtPureFullIn.lean): there the full-size trace returns; atPure_ok, atPure_trace
        (Honest/AtPureLaw.lean): the maker's prover has the filling's trace and range

  readyInput_of_start         the core: from "okStart accepts what the library writes for every instance of the type":
                              at every filling P whose trace is the full-size one and whose range is constant, and
                              every A that the maker returns at P with A.Z = Zp: there are an index i and a typed
                              request x' such that at every OOD sample and every value of the field rc the input is
                              ready
  readyInput_of_item          from the clause on the item
  item_of_one                 at the format's second hash function the clause on the item at one string of the request file's
                              length gives it at every such string (a call of item_free, E2E/StartAtFiles.lean)
  readyInput_of_item_at_one   from the clause on the item at one string of that length
  readyInput_of_okBy          from one accept of "ProofFile.okBy" at any instance whose request has that length
  readyInput_of_one           from one accept of okStart at what the library writes for one instance of the type
  item_of_readyInput          the other way: one ready input, at such a filling, gives the clause on the item back: so
                              under the head "some input is ready" asks no less than that clause
  readyInput_widerC_of_start, .._of_item, .._of_okBy, .._of_one   at the written filling
                              "widerFillAtC fullIn o' S O", with the maker's return (atPure_returns_widerC_fullIn,
                              ReturnsAtWiderCFullIn.lean, under its premise hB)

Limits. The sentence on the public files is a premise in each form. This file and the files that state it prove it at
no public files; AtFullSide/K5/ItemAtFull.lean, which this file does not import, proves it at VerifierAndGoals.storedPublicFiles alone.
It holds two readers of the parameter file against each other, and three digests of lists of
calls that are made twice. The head and protocolDataWellFormed are premises. The index and the request are the library's own member
(by the Limits of ServedExists.lean, by inspection: the all-zero weights, all tokens 0): nothing is said of any other.
The inputs that are shown ready bear what the library writes at every OOD sample: whether the key that a committer
makes is one of these is not said here.
"ReadyInput" is a condition on an input: a value of a thread's parameter "valid". Nothing here says that "ready"
(Honest/Frame.lean) returns at that input, that any part plays, that a thread's border is reached, or that a verifier
accepts. All limits of ReadyInput.lean hold: the condition reads the private input; its first clause bears tests on the
table's key; a law whose end states a distribution over rc or the seed may not lean on it without more.
No property of the protocol is claimed: nothing on soundness, completeness or what anything reveals.
-/
import E2E.StartInScope
import Johnson.FrontRoad.ServedExists
import Johnson.Desc.ProofFile.InstOfTies
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Desc.ProofFile.Honest.Thread.ReadyInput
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsAtWiderCFullIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.Flat (RecFull)
open LPFD.Full (XF)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA F0T TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 At a filling with the full-size trace -/

/-- **Some input is ready, if the description's first test accepts what the library writes for every instance of the
type.** Conditional: h: the head; hl: the library's test protocolDataWellFormed; hok: these accepts; ht, hr: the filling has the
full-size trace and a constant range; hA, hZ: the maker returns A at it, at the head's public part. -/
theorem readyInput_of_start (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hok : ∀ z : XF × RecFull, (F0T OnBytes.secondHashFunction Zp Np cF).okStart (LPFD.Full.instanceAsPlainRecord z) = true)
    {Rc X₀ X : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ X} (ht : P.trace = fullIn.trace)
    (hr : ∀ i, P.inRange i = true) {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hZ : A.Z = Zp) :
    ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : Rc),
      ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ := by
  obtain ⟨i, x', T⟩ := OnBytes.FrontRoad.servedTyped_exists Z Zp Np cF h.scope h.reads hl h.laid
  refine ⟨i, x', fun rec rc => ⟨hok (x', rec), ?_, ?_⟩⟩
  · show A.H.inRange i = true
    rw [(atPure_ok hA).2.2.2.2.2.1]
    exact hr i
  · show A.H.trace i (LPFD.Full.instanceAsPlainRecord (x', rec)) = some _
    rw [atPure_trace hA, hZ, ht]
    exact fullIn_trace_served (ProofFile.instOf_at_frame (x', rec)) T

/-- **From the clause on the request's item.** -/
theorem readyInput_of_item (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (item : ∀ req : ByteArray, req.size = 4 * (Zp.p.X.T + 2) →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction Zp.pol Zp.KL req = some it ∧
        OnBytes.Model.Verify.statementHeld Zp.p.X it = .ok ())
    {Rc X₀ X : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ X} (ht : P.trace = fullIn.trace)
    (hr : ∀ i, P.inRange i = true) {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hZ : A.Z = Zp) :
    ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : Rc),
      ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ :=
  readyInput_of_start h hl (AtPublicFiles.Start.okStart_of_item h.scope h.laid item) ht hr hA hZ

/-- At the format's second hash function the clause on the item hangs on the request's length alone: at one string of a
length it gives the clause at every string of that length. -/
theorem item_of_one {X : OnBytes.Model.Verify.Public} {pol KL req₀ : ByteArray} {n : Nat}
    (hs : req₀.size = n)
    (h₁ : ∃ it, Fmt.requestItem OnBytes.secondHashFunction pol KL req₀ = some it ∧
      OnBytes.Model.Verify.statementHeld X it = .ok ()) :
    ∀ req : ByteArray, req.size = n →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction pol KL req = some it ∧
        OnBytes.Model.Verify.statementHeld X it = .ok () :=
  fun _ hq => AtPublicFiles.Start.item_free (hs.trans hq.symm) h₁

/-- **From the clause on the item at one string of the request file's length.** -/
theorem readyInput_of_item_at_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {req₀ : ByteArray} (hs : req₀.size = 4 * (Zp.p.X.T + 2))
    (h₁ : ∃ it, Fmt.requestItem OnBytes.secondHashFunction Zp.pol Zp.KL req₀ = some it ∧
      OnBytes.Model.Verify.statementHeld Zp.p.X it = .ok ())
    {Rc X₀ X : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ X} (ht : P.trace = fullIn.trace)
    (hr : ∀ i, P.inRange i = true) {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hZ : A.Z = Zp) :
    ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : Rc),
      ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ :=
  readyInput_of_item h hl (item_of_one hs h₁) ht hr hA hZ

/-- **From one accept of the seven tests on an instance, at any instance whose request has that length.** By the
test's own text hs follows from h₀; it is kept as a premise to spare a lemma. -/
theorem readyInput_of_okBy (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {ξ₀ : ProofFile.Inst} (hs : ξ₀.pub.request.size = 4 * (Zp.p.X.T + 2))
    (h₀ : ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp ξ₀ = true)
    {Rc X₀ X : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ X} (ht : P.trace = fullIn.trace)
    (hr : ∀ i, P.inRange i = true) {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hZ : A.Z = Zp) :
    ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : Rc),
      ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ :=
  readyInput_of_item_at_one h hl hs (AtPublicFiles.Start.item_of_okBy h₀) ht hr hA hZ

/-- **From one accept of the description's first test, at what the library writes for one instance of the type.** -/
theorem readyInput_of_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    {z₀ : XF × RecFull}
    (h₀ : (F0T OnBytes.secondHashFunction Zp Np cF).okStart (LPFD.Full.instanceAsPlainRecord z₀) = true)
    {Rc X₀ X : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ X} (ht : P.trace = fullIn.trace)
    (hr : ∀ i, P.inRange i = true) {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hZ : A.Z = Zp) :
    ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : Rc),
      ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ :=
  readyInput_of_start h hl (AtPublicFiles.Start.okStart_of_one h.scope h.laid h₀) ht hr hA hZ

/-- **The other way: one ready input gives the clause on the request's item back.** Its first clause gives the clause
at the input's own request; its third, at the full-size trace, that this request has the request file's length.
Conditional: h: the head; ht, hA, hZ as above; hv: the input is ready. protocolDataWellFormed is not asked. -/
theorem item_of_readyInput (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {Rc X₀ X : Type} {P : OnlineProverParts Cm.Idx Rc Cells X₀ X} (ht : P.trace = fullIn.trace)
    {A : OnlineProverWithDescription Cm.Idx Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hZ : A.Z = Zp)
    {v : Local Cm.Idx Rc ProofFile.Inst Cells} (hv : ReadyInput (F0T OnBytes.secondHashFunction Zp Np cF) A.H v) :
    ∀ req : ByteArray, req.size = 4 * (Zp.p.X.T + 2) →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction Zp.pol Zp.KL req = some it ∧
        OnBytes.Model.Verify.statementHeld Zp.p.X it = .ok () := by
  obtain ⟨h1, -, h3⟩ := hv
  rw [atPure_trace hA, hZ, ht] at h3
  obtain ⟨x₁, hx, -, -⟩ := fullIn_trace_some h3
  have hs : v.x.pub.request.size = 4 * (Zp.p.X.T + 2) := by
    rw [← (ProofFile.instOf_bytes hx).1, (AtPublicFiles.Start.numbers_of_laid h.scope h.laid).1]
    unfold OnBytes.Flat.requestBytesOf
    rw [AtPublicFiles.Start.size_bytesOfWords, OnBytes.Flat.size_requestWordsOf]
  rw [AtPublicFiles.Start.okStart_eq, Bool.and_eq_true] at h1
  exact item_of_one hs (AtPublicFiles.Start.item_of_okBy h1.1)

/-! ## 2 At the written filling, with the maker's return -/

/-- **The core at the written filling.** Conditional: h, hl, hok; hB: the closed sentence on the written book that the
maker's return takes. -/
theorem readyInput_widerC_of_start (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (hok : ∀ z : XF × RecFull, (F0T OnBytes.secondHashFunction Zp Np cF).okStart (LPFD.Full.instanceAsPlainRecord z) = true)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAtC fullIn o' S O) = .ok A ∧
      A.F = F0T OnBytes.secondHashFunction Zp Np cF ∧
      ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : IndexCommitterCoins),
        ReadyInput A.F A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ := by
  obtain ⟨A, hA, hZ, hF, -⟩ := atPure_returns_widerC_fullIn h hl hB o' S O
  refine ⟨A, hA, hF, ?_⟩
  rw [hF]
  exact readyInput_of_start h hl hok rfl (fun _ => rfl) hA hZ

/-- **From the clause on the request's item, at the written filling.** -/
theorem readyInput_widerC_of_item (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (item : ∀ req : ByteArray, req.size = 4 * (Zp.p.X.T + 2) →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction Zp.pol Zp.KL req = some it ∧
        OnBytes.Model.Verify.statementHeld Zp.p.X it = .ok ())
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAtC fullIn o' S O) = .ok A ∧
      A.F = F0T OnBytes.secondHashFunction Zp Np cF ∧
      ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : IndexCommitterCoins),
        ReadyInput A.F A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ :=
  readyInput_widerC_of_start h hl hB (AtPublicFiles.Start.okStart_of_item h.scope h.laid item) o' S O

/-- **From one accept of the seven tests on an instance, at the written filling.** -/
theorem readyInput_widerC_of_okBy (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    {ξ₀ : ProofFile.Inst} (hs : ξ₀.pub.request.size = 4 * (Zp.p.X.T + 2))
    (h₀ : ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp ξ₀ = true)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAtC fullIn o' S O) = .ok A ∧
      A.F = F0T OnBytes.secondHashFunction Zp Np cF ∧
      ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : IndexCommitterCoins),
        ReadyInput A.F A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ :=
  readyInput_widerC_of_item h hl hB (item_of_one hs (AtPublicFiles.Start.item_of_okBy h₀)) o' S O

/-- **From one accept of the description's first test, at the written filling.** -/
theorem readyInput_widerC_of_one (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    {z₀ : XF × RecFull}
    (h₀ : (F0T OnBytes.secondHashFunction Zp Np cF).okStart (LPFD.Full.instanceAsPlainRecord z₀) = true)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAtC fullIn o' S O) = .ok A ∧
      A.F = F0T OnBytes.secondHashFunction Zp Np cF ∧
      ∃ (i : Cm.Idx) (x' : XF), ∀ (rec : RecFull) (rc : IndexCommitterCoins),
        ReadyInput A.F A.H
        ⟨i, rc, LPFD.Full.instanceAsPlainRecord (x', rec),
          ⟨OnBytes.HonestTrace.cellOf Zp.p.X (OnBytes.HonestTrace.theTrace Zp.p.X i x'.val)⟩⟩ :=
  readyInput_widerC_of_start h hl hB (AtPublicFiles.Start.okStart_of_one h.scope h.laid h₀) o' S O

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.readyInput_of_start
#print axioms ProofFile.Honest.K5.readyInput_of_item
#print axioms ProofFile.Honest.K5.item_of_one
#print axioms ProofFile.Honest.K5.readyInput_of_item_at_one
#print axioms ProofFile.Honest.K5.readyInput_of_okBy
#print axioms ProofFile.Honest.K5.readyInput_of_one
#print axioms ProofFile.Honest.K5.item_of_readyInput
#print axioms ProofFile.Honest.K5.readyInput_widerC_of_start
#print axioms ProofFile.Honest.K5.readyInput_widerC_of_item
#print axioms ProofFile.Honest.K5.readyInput_widerC_of_okBy
#print axioms ProofFile.Honest.K5.readyInput_widerC_of_one
