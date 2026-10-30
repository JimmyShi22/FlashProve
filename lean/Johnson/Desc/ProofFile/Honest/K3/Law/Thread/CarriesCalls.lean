-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CarriesCalls.lean: the kind "lookup" (K3): the cut of a
member's acceptance into structure and values (Honest/Thread/Shape.lean), at the member of the
description's first chain at a lookup on the calls: the member's guards on the first chain's shape,
written as one Boolean test and one update, both definitions with code; and `Carries` for these
guards: where the member's own step accepts and the guards return at the state's shape, they return
the shape behind. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the shape of a state is `chainSh`
(Johnson/Desc/First/Shape/Chain.lean), of nineteen components. The guards of a member are the field
g of `Shape` (Honest/Thread/Shape.lean) at its border: a function on shapes that returns a shape or
a rejection. A filling of the cut's letters is a value of `Shape`. `Carries` and `Returns` are
definitions of Shape.lean (there labelled (B1) and (B2)).

What is shown.
  `callsB`, `callsU`, `callsG`: the test; the update; the guards, which are "if the test passes then
    the update, else a rejection".
  `callsHere_readers`: what each reader of the state answers at the state behind, from `CallsHere`
    (Honest/K3/Law/KeepsDefs.lean).
  `callsU_at`, `chainSh_calls`: hence the shape behind is the update of the shape in front.
  `carriesR_calls`: the sentence of `Carries` at the member's step (helper: `sized_of_callsB`).
  `carries_calls`: `Carries bs ft Z b`, at every filling Z of the cut's letters whose sh is the
    first chain's shape and whose g at b is `callsG`.
The update changes three of the nineteen components: led (`lookUpd` of the face,
Honest/K3/Shape/Ops.lean), lookHeard (`lookHeardSh`, Honest/K3/Shape/HeardOps.lean, at the count and
the number of owed claims of the ledger's shape), and, where the link is not the head's, look (the
same value). The test asks: no mark; no row waits; nothing is heard yet; a ledger is there, its
count is the lookup's first slot, its three arrays have their size, and the lookup's slots are there
and free.
The proof of `Carries` uses one clause of the test: the arrays have their size. The other clauses
are there for `Returns`, which is not shown in this file: nothing here says that the member's step
accepts.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the calls.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk). In `carries_calls` the one hypothesis `hm` says the
    three of the entry of bs at b.
  `h`, `hg`: (in `carriesR_calls`) the member's step accepts from sj to sj'; the guards return at
    the shape of sj.
  `hg`: (in `carries_calls`) g at b is `callsG s.shape s.p.first`.
  In the helpers: `hC`: `CallsHere`; `hF`, `hl`: a ledger is open, or the shape holds a ledger's
    shape; `e1`, `e2`: the two shapes behind, as code on those in front; `hB`: `callsB` accepts.

Imported: Johnson/Desc/First/Shape/Chain.lean and Honest/Thread/Shape.lean.

How the proof goes. `chainSh_calls` goes component by component, by rewriting with
`callsHere_readers`.

Users. `carries_calls_link` (Honest/K3/Law/Thread/AtLink.lean) calls `carries_calls` at the first
chain's flat list and the border. `returns_calls` (Honest/K3/Law/Thread/ReturnsLook.lean) is
`Returns` at the same guards; it assumes two public tests besides (`hok`, `hT2`).
Honest/K3/Law/Thread/CarriesGuards.lean [not in this library] evaluates `callsB` and
`callsG`.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
No filling Z is constructed here: `carries_calls` is stated for an arbitrary one. With another
version of Johnson/Desc/First/Shape/Chain.lean the shape is another.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.ProofFile.Honest.Thread.Shape
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CallsParts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LedNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh LedSh ledSh heardAll sizedB freeB hereNo
  endSh attOf finOf)
open ProofFile.Honest.K3.Shape (lookUpd lookHeardSh)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "FShape" => OnBytes.Model.Forest.Shape
local notation "headShOf" => VerifiableInference.Desc.First.Shape.headOf

/-- **The Boolean test.** Here h is the lookup's shape and first is its first slot. -/
def callsB (h : FShape) (first : Nat) (a : ChainSh) : Bool :=
  !a.marked && VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits a.rowsOwed &&
    a.lookHeard.isNone &&
    a.led.any fun Ld =>
      Ld.next == first && sizedB Ld && freeB Ld first (OnBytes.Model.Forest.elems h)

/-- **The update**, written out component by component: sixteen components stay as they are, three
are set. The number 3 of the component here is the head's link, opened (`hereNo`,
Johnson/Desc/First/Shape/Chain.lean). Where the shape holds no ledger's shape nothing is changed;
`callsB` rejects there. -/
def callsU (h : FShape) (a : ChainSh) : ChainSh :=
  match a.led with
  | some Ld =>
    ChainSh.mk a.marked a.here a.tl (some (lookUpd (faceOf h) Ld)) a.tables a.rowsOwed a.core
      a.reply a.indexMasks a.pile a.atEnd a.check a.link
      (if a.here == 3 then a.look else some (lookHeardSh h Ld.next Ld.owed.length))
      (some (lookHeardSh h Ld.next Ld.owed.length)) a.own a.head a.att a.fin
  | none => a

/-- **The guards.** -/
def callsG (h : FShape) (first : Nat) (a : ChainSh) : Except String ChainSh :=
  if callsB h first a then .ok (callsU h a) else .error "K3: the lookup on the calls"

/-- What each reader of the state answers at the state behind, from the three cases of `CallsHere`.
-/
theorem callsHere_readers {sj sj' : FS} {G : Fork} {H : OnBytes.Model.Forest.Heard}
    (hC : CallsHere sj sj' H G) :
    sj'.failed = sj.failed ∧ hereNo sj'.here = hereNo sj.here ∧ sj'.tl? = sj.tl? ∧
      sj'.fork? = some G ∧ sj'.funs? = sj.funs? ∧ sj'.rowsOwed = sj.rowsOwed ∧ sj'.st = sj.st ∧
      sj'.out = sj.out ∧ endSh sj'.here = endSh sj.here ∧ sj'.check = sj.check ∧
      sj'.link? = sj.link? ∧ sj'.book = sj.book ∧ sj'.roots = sj.roots ∧
      sj'.look? = (if hereNo sj.here == 3 then sj.look? else some H) ∧
      sj'.lookHeard? = some H ∧ sj'.own? = sj.own? ∧ headShOf sj'.here = headShOf sj.here ∧
      attOf sj'.here = attOf sj.here ∧ finOf sj'.here = finOf sj.here := by
  rcases hC with ⟨a, hh, rfl⟩ | ⟨a, hh, rfl⟩ | ⟨a, hh, ho, rfl⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hereNo, hh]
    · simp [S.tl?, hh]
    · simp [S.fork?]
    · simp [S.funs?, hh]
    · simp [endSh, hh]
    · simp [S.link?, hh]
    · simp [S.look?, hereNo, hh]
    · simp [S.lookHeard?]
    · simp [S.own?, hh]
    · rw [hh]
      rfl
    · rw [hh]
      rfl
    · rw [hh]
      rfl
  · refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hereNo, hh]
    · simp [S.tl?, hh]
    · simp [S.fork?]
    · simp [S.funs?, hh]
    · simp [endSh, hh]
    · simp [S.link?, hh]
    · simp [S.look?, hereNo, hh]
    · simp [S.lookHeard?]
    · simp [S.own?, hh]
    · rw [hh]
      rfl
    · rw [hh]
      rfl
    · rw [hh]
      rfl
  · refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hereNo, hh, ho]
    · simp [S.tl?, hh, ho]
    · simp [S.fork?, ho]
    · simp [S.funs?, hh, ho]
    · simp [endSh, hh]
    · simp [S.link?, hh, ho]
    · simp [S.look?, hereNo, hh, ho]
    · simp [S.lookHeard?, ho]
    · simp [S.own?, hh]
    · rw [hh]
      simp [VerifiableInference.Desc.First.Shape.headOf,
        VerifiableInference.Desc.First.Shape.headSh, ho]
    · rw [hh]
      rfl
    · rw [hh]
      rfl

/-- The update, where a ledger's shape is there. -/
theorem callsU_at {h : FShape} {a : ChainSh} {Ld : LedSh} (hl : a.led = some Ld) :
    callsU h a = ChainSh.mk a.marked a.here a.tl (some (lookUpd (faceOf h) Ld)) a.tables a.rowsOwed
      a.core a.reply a.indexMasks a.pile a.atEnd a.check a.link
      (if a.here == 3 then a.look else some (lookHeardSh h Ld.next Ld.owed.length))
      (some (lookHeardSh h Ld.next Ld.owed.length)) a.own a.head a.att a.fin := by
  unfold callsU
  rw [hl]

/-- **The shape behind is the update of the shape in front.** The hypotheses `e1` and `e2` give the
shape of the ledger behind and the shape of what was heard as values of `lookUpd` and `lookHeardSh`.
-/
theorem chainSh_calls {h : FShape} {sj sj' : FS} {F G : Fork} {H : OnBytes.Model.Forest.Heard}
    (hF : sj.fork? = some F) (hC : CallsHere sj sj' H G)
    (e1 : ledSh G = lookUpd (faceOf h) (ledSh F))
    (e2 : heardAll H = lookHeardSh h (ledSh F).next (ledSh F).owed.length) :
    chainSh sj' = callsU h (chainSh sj) := by
  have hl : (chainSh sj).led = some (ledSh F) := by
    show sj.fork?.map ledSh = _
    rw [hF]
    rfl
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17,
    r18, r19⟩ :=
    callsHere_readers hC
  rw [callsU_at hl, ← e1, ← e2]
  unfold chainSh
  rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    r19]
  cases hq : hereNo sj.here == 3 with
  | true =>
    show ChainSh.mk _ _ _ _ _ _ _ _ _ _ _ _ _ ((if true = true then sj.look? else some H).map
      heardAll) _ _ _ _ _ = ChainSh.mk _ _ _ _ _ _ _ _ _ _ _ _ _
      (if (hereNo sj.here == 3) = true then _ else _) _ _ _ _ _
    rw [hq]
    rfl
  | false =>
    show ChainSh.mk _ _ _ _ _ _ _ _ _ _ _ _ _ ((if false = true then sj.look? else some H).map
      heardAll) _ _ _ _ _ = ChainSh.mk _ _ _ _ _ _ _ _ _ _ _ _ _
      (if (hereNo sj.here == 3) = true then _ else _) _ _ _ _ _
    rw [hq]
    rfl

/-- The Boolean test contains the test on the ledger's arrays, at the ledger that the state holds.
-/
theorem sized_of_callsB {h : FShape} {first : Nat} {sj : FS}
    (hB : callsB h first (chainSh sj) = true) (F : Fork) (hF : sj.fork? = some F) :
    sizedB (ledSh F) = true := by
  have hl : (chainSh sj).led = some (ledSh F) := by
    show sj.fork?.map ledSh = _
    rw [hF]
    rfl
  unfold callsB at hB
  rw [hl] at hB
  simp only [Bool.and_eq_true, Option.any_some] at hB
  exact hB.2.1.2

/-- **The sentence of `Carries` at the member's step.** Conditional on the hypotheses that this
file's head lists. No instance of these hypotheses is exhibited in this file. -/
theorem carriesR_calls (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (t : ChainSh) (h : m.step ft sj rs c = .ok (sj', n))
    (hg : callsG s.shape s.p.first (chainSh sj) = .ok t) : t = chainSh sj' := by
  unfold callsG at hg
  cases hB : callsB s.shape s.p.first (chainSh sj) with
  | false =>
    rw [hB] at hg
    exact nomatch hg
  | true =>
    rw [hB] at hg
    have ht : callsU s.shape (chainSh sj) = t := Except.ok.inj hg
    obtain ⟨F, H, G, a1, _, a5, hC, _⟩ := calls_here o pol lay KL Fd Z Bs base ch A B O s hs hd lot
      m hb hbs hm hmp hpk ft sj sj' n rs c h
    have hs' := hs
    unfold lookSites at hs'
    obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
    obtain ⟨_, f2, _⟩ := site_facts _ _ x s hsx
    have hS := VerifiableInference.Desc.First.Shape.sized_of_B (sized_of_callsB hB F a1)
    rw [← ht]
    exact (chainSh_calls a1 hC (ProofFile.Honest.K3.Shape.hearVia_sh hS f2 a5).2
      ((ProofFile.Honest.K3.Shape.hearVia_heard hS f2 a5).trans (heardSh_led s.shape F))).symm

/-- **`Carries` in the form of its definition**, at every filling of the cut's letters whose shape
is the first chain's and whose guards at b are `callsG`. The filling is arbitrary: none is
constructed here. -/
theorem carries_calls (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place)
    (bs : List (Block FS ProofFile.Cl)) (ft b : Nat)
    (hm : ∀ blk, bs[b]? = some blk → blk ∈ ch.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → FS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g b = callsG s.shape s.p.first) :
    Carries bs ft ⟨ChainSh, chainSh, g, vals⟩ b := by
  intro blk hblk sj rs cols sj' n t hst hgt
  obtain ⟨h1, h2, h3⟩ := hm blk hblk
  have hgt' : g b (chainSh sj) = .ok t := hgt
  rw [hg] at hgt'
  exact carriesR_calls o pol lay KL Fd Z Bs base ch A B O s hs hd lot blk hb hbs h1 h2 h3 ft sj sj'
    n rs cols t hst hgt'

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.callsHere_readers
#print axioms ProofFile.Honest.K3.Law.AtThr.callsU_at
#print axioms ProofFile.Honest.K3.Law.AtThr.chainSh_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.sized_of_callsB
#print axioms ProofFile.Honest.K3.Law.AtThr.carriesR_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.carries_calls
