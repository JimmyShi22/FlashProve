-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/LettersAtHead.lean: THE TWO STRUCTURES OF LETTERS K6KeysLetters
(Honest/K6/Law/KeysAtThread.lean) AND K6IdnLetters (Honest/K6/Law/IdnAtThread.lean), WHOLE, AT THE
FIRST CHAIN'S LETTERS AT THE LIBRARY'S OWN (Honest/Thread/FirstAt.lean: lettersAt): sisters of
LettersFull.lean's k6_letters_full.
WHAT IT IS NOT. FACTS ON LETTERS, DATA AND PUBLIC NUMBERS: no state of a run stands in them, and no
item is shown true. CONDITIONAL on that file's one hypothesis h, AND ON ONE PREMISE EACH, WHICH IS
NOT SHOWN HERE: hIn: at a valid input the Script's cells are those of an index. The full size and
the format's second hash function alone, as h. THE NUMBERS ARE FIXED HERE AS IN k6_letters_full: lay6 :=
At.layout Zp, num := At.num Zp, n := At.num Zp 24 0, rb := 0, b := 341, toP := id, toW := id, the
data with the decoder and the carried word's sentence turned. Nothing on any property.
WHAT IS TYPED ANEW, AND WHY: calls_at_head's proof FOLLOWS, LINE BY LINE, the lines by which the
library's dueAt_of_mg (Johnson/Desc/Kinds/Law/K6LawAtMgAll.lean) derives, inside its own proof,
these facts on the place of the lookup on the head's calls: they are no lemmas there.
  calls_at_head        on that place x: its number of slots is the one that the public parameters
                       fix; the test on its public numbers accepts; it has six calls.
  meets_at_head        the library's CallerMeets, at h's data with two fields turned into any
                       others: built as dueAt_of_mg builds it.
  open_at_341          the two items are open at border 341, by the thread's own reckoning
                       (fwdOpen): by Lean's kernel on the written lists P5J.At.links and P5J.At.ps
                       (measured in two builds: between half a minute and two and a half minutes of
                       compile time).
  keysLetters_at_head, idnLetters_at_head   THE TWO TOPS.
WHO PAYS WHAT. means: MeansIn.lean, hMg by unfolding lettersAt. meets: paid_at_const (seg, place,
lay), callsC_at_head_all with calls_of_C, maskC_at_head with mask_of_C, calls_at_head. named:
h.plan.hN. inRange: hIn; the Script's witness has the Script's cells at all coins and lists.
ranges, inFour, d, V: the library's lemmas in the goals' scope. laid: h.plan.laid. fits:
LettersFull.lean's fits_turned. put: putReq_keeps. dec: by unfolding.
OF THE FOLDER Johnson/Goal/ it calls InScope.numbers_in_scope (Goal/Meaning/HeadCondScope.lean), as
the library's kindTied_K6_mgAll does; nothing else of that folder is called.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.KeysAtThread
import Johnson.Desc.ProofFile.Honest.K6.Law.IdnAtThread
import Johnson.Desc.ProofFile.Honest.K6.Law.MeansIn
import Johnson.Desc.ProofFile.Honest.K6.Law.LettersFull
import Johnson.Desc.Kinds.Law.K6LawAtMgAll
import Johnson.Desc.Kinds.Law.DAtConst
import Johnson.HB.LLHARD.K6CallsAtHeadAll
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable
open VerifiableInference.Desc (Chain Strs Wit Link Claim)
open VerifiableInference.Desc.First (Item S)
open VerifiableInference.Desc.Sound (mgAll mgBase MsgT namedOnce)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open ProofFile.Honest (ProverCoinCounts Local Placed FirstRows.rows)
open ProofFile.Honest.FirstThread (Script WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **On the place of the lookup on the head's calls.** -/
theorem calls_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    x.ns = (At.X Zp).H.ns ∧ FoNums.ok x.fs = true ∧ x.fs.NC = 6 := by
  obtain ⟨Lk, hlk⟩ := P4.link24_at_head h
  have A := paid_at_const h Lk hlk
  have hsh : (First.Look.P.ofPlace (OnBytes.Params.settingOf (At.X Zp).P.frame) false x).shape =
      some x.fs := by
    have hx := A.place
    unfold headAt at hx
    obtain ⟨x', -, hx⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨h', hh, hx⟩ := Option.map_eq_some_iff.1 hx
    subst hx
    exact hh
  have hpl3 : First.Look.placeAt (At.X Zp) 24 false =
      some (First.Look.P.ofPlace (OnBytes.Params.settingOf (At.X Zp).P.frame) false x) := by
    letI := (parOf (At.X Zp).hS 0).sizes
    letI := (parOf (At.X Zp).hS 0).policy
    letI : Request := ⟨fun _ => 0, 0, 0⟩
    have e5 := VerifiableInference.OnPublicFiles.placeAt_headAt A.place
    rw [A.seg] at e5
    exact e5
  obtain ⟨pc, ec, _, _, nc⟩ := InScope.calls_place h.scope h.pubOne
  obtain rfl := Option.some.inj (hpl3.symm.trans ec)
  refine ⟨nc, ?_, ?_⟩
  · obtain ⟨h0, hs0, hp0, e0⟩ := First.Look.P.shape_made hsh
    rw [e0]
    exact Cb.Fo.shape_ok hs0 hp0
  · obtain ⟨_, _, _, _, hp5, _⟩ :=
      k6Pub_says (At.X Zp) (InScope.k6Pub_in_scope h.scope h.reads h.pubOne)
    exact (hp5 _ _ hpl3 hsh).1

/-- **The caller's reading of the witness is tied to the law's, AT THE DATA WITH TWO FIELDS
TURNED**: decT', cr1': any. -/
theorem meets_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (decT' : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S →
      Option (CellsM OnBytes.Flat.numsFull))
    (cr1' : ℕ → ProofFile.InstPub × S → Strs → WtF → Prop) :
    CallerMeets { dAt h with decT := decT', cr1 := cr1' } (At.layout Zp) (At.num Zp)
      (At.num Zp 24 0) x := by
  obtain ⟨Lk, hlk⟩ := P4.link24_at_head h
  have A := paid_at_const h Lk hlk
  exact ⟨⟨A.seg, A.place⟩, A.lay,
    AtFold.calls_of_C (callsC_at_head_all h)
      (ColFour (At.X Zp).hS (At.X Zp).HLy (OnBytes.Model.Verify.borderOf (At.X Zp).y))
      (fun a c hc => by
        have e := OffPad.four_matrix hc
        omega), (calls_at_head h).1, AtFold.mask_of_C (maskC_at_head h)⟩

/-- **The two items are open at border 341**, by the thread's own reckoning: one evaluation, by
Lean's kernel, on the first chain's written lists of links and places. No premise. -/
theorem open_at_341 :
    Item.worth 24 3 "keys" ∈ ProofFile.Honest.fwdOpen (First.start P5J.At.links)
        (FirstRows.rows P5J.At.links P5J.At.ps) 341 ∧
      Item.constr 24 .idn ∈ ProofFile.Honest.fwdOpen (First.start P5J.At.links)
        (FirstRows.rows P5J.At.links P5J.At.ps) 341 := by
  decide +kernel

/-- **K6KeysLetters, WHOLE.** -/
theorem keysLetters_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop)
    (hIn : ∀ w, valid w → VerifiableInference.OnPublicFiles.Flat.InRange (Q.cells w)) :
    K6KeysLetters
      (ProofFile.Honest.FirstThread.lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides
        keeps).thread 341 (Item.worth 24 3 "keys") id id
      (fun w => { dAt h with decT := fun _ _ => some (Q.cells w), cr1 := carryX }) mgBase
      (At.layout Zp) (At.num Zp) (At.num Zp 24 0) x :=
  { opened := open_at_341.1
    means := k6_means_worth _ (fun _ => rfl) 24 3 "keys"
    meets := fun _ _ => meets_at_head h _ _
    named := fun _ _ μ r c hr hc _ => h.plan.hN 24 μ r c hr hc
    inRange := fun _ w _ hv => hIn w hv
    ranges := Came.inRanges_in_scope h.scope h.reads h.pubOne _
    inFour := fun a r c => Came.inSizes_in_scope h.scope h.reads h.pubOne a r c
    laid := h.plan.laid
    d := (InScope.numbers_in_scope h.scope h.reads h.pubOne).d
    V := (InScope.numbers_in_scope h.scope h.reads h.pubOne).V
    nums := (calls_at_head h).2.1
    calls := (calls_at_head h).2.2 }

/-- **K6IdnLetters, WHOLE.** -/
theorem idnLetters_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop)
    (hIn : ∀ w, valid w → VerifiableInference.OnPublicFiles.Flat.InRange (Q.cells w)) :
    K6IdnLetters
      (ProofFile.Honest.FirstThread.lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides
        keeps).thread 341 (Item.constr 24 .idn) id id
      (fun w => { dAt h with decT := fun _ _ => some (Q.cells w), cr1 := carryX }) mgBase
      (At.layout Zp) (At.num Zp) (At.num Zp 24 0) 0 :=
  { opened := open_at_341.2
    means := k6_means_constr _ (fun _ => rfl) 24 .idn
    fits := fun _ _ => ⟨_, _, _, _, _, _, _, fits_turned h _ _⟩
    put := fun _ _ => Came.putReq_keeps
    dec := fun _ _ _ _ _ _ => rfl
    inRange := fun _ w _ hv => hIn w hv }

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.calls_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.meets_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.open_at_341
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.keysLetters_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.idnLetters_at_head
