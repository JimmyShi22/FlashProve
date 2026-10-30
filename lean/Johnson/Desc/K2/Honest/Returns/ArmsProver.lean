-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ArmsProver.lean: THE CODE SWITCH's RETURNS LAW, WHOLE, AT THE OUTPUT
HEAD's SWITCH AND BEHIND THE LAST SEGMENT, AT A REACHED STATE, UNDER THE ONE HEAD `P5J.AtMgA`, FROM
SEVEN CLAUSES THAT NAME THE PROVER's TWO ROUNDS OR THE COLUMNS (`HeadSeven`, `FinSeven`) AND "THE
ROUNDS FIT". What Returns/LinkProver.lean has at the links. A join of Returns/LeftAtReached.lean,
Returns/OwnReached.lean and Returns/OwnFinish.lean with a file of another house. Statements with
their proofs: calls.

  `CallFive p x B roots r₁ r₂ cols c` `CallLast` (Returns/LeftAtReached.lean) without plan, trees,
                    inRange and readsOwn, field for field: fits₁ · vals · answers · loc · readsOpens
  `HeadSeven`, `FinSeven` `HeadLast`, `FinLast` with `CallFive` in the place of `CallLast`: beside
                    the five: noneLeft · groups
  `headLast_of_seven`, `finLast_of_seven` under the head, the rounds that fit and the state's own
                    look-ups: the seven give `HeadLast` | `FinLast`, and the entry's test at the
                    plan's own list holds
  `head_behind_seven`, `head_returns_seven`, `fin_behind_seven`, `fin_returns_seven` `HeadBehind` |
                    `FinBehind`; the kind's own decision's yes

THE COUNT. Of `HeadBehind`'s 60 clauses and `FinBehind`'s 59, SEVEN are left at each, beside the
premises on the state that the tops of Returns/LeftAtReached.lean take (`here` and the group's
look-up; the quiet front's yes, `here` and the group that is laid). The entry's test is a premise no
more.

ANOTHER HOUSE's, CALLED: `head_four_reached`, `fin_four_reached`
(Johnson/AtFull/Shape/ArmsLeftNums.lean): plan · trees · the entry's test · inRange. BY THAT HOUSE's
OWN PAPERS: the file called and the three of that house beneath it
(Johnson/AtFull/Shape/LinkPlanNums.lean, LinkLeftNums.lean, LinkLeftPlan.lean) have that house's
ride of record at the bytes that it has lined for the next sealed library; each of the four was read
whole, proofs too, once, at other bytes, by one reader of that house who is not its pen, and
since by difference (comments, and in one an import line, have turned): none whole at the lined
bytes; the file called decides six closed facts by Lean's kernel (four of them under a raised
recursion limit), the three beneath it ten more; of its controls that house's own reader says that
they stand at one row and at no notice alone; they stand over two more files of that house
(PlansAtHead.lean, AtSwitchReached.lean), lined too. NONE OF THE SIX IS IN A SEALED LIBRARY YET;
four of them strike the instance `Inst.Model.Scl.ref`. This folder's: `head_behind_last`,
`head_returns_last`, `fin_behind_last`, `fin_returns_last` (Returns/LeftAtReached.lean) ·
`head_own_reached` (Returns/OwnReached.lean), `fin_own_reached` (Returns/OwnFinish.lean) ·
`head_draws_plan`, `finish_draws_plan` (Returns/LinkReached.lean): the range of the positions drawn
· `h25_of_hy` (Returns/FinAtReached.lean), `tests_at_head` (Returns/UnderHead.lean). The library's
`frontAt_of` (Johnson/Top/H0/Tw/K2C/HeldAtYes.lean).

Limits. THE HEAD IS SHOWN MET BY NOBODY HERE: NO MEMBER. THE HEAD IS `P5J.AtMgA`, WHICH ASKS MORE
THAN THE `P5J.AtMg` OF THIS FOLDER's OTHER TOPS. The seven and the rounds that fit stay premises.
THE SEVEN ARE NOT ON THE ROUNDS AND THE COLUMNS ALONE: readsOpens asks four facts a tree of the
verifier's state; answers and loc hold three ties of the plan's numbers. The opening is a premise in
the head's own letters. At the format's second hash function alone. The full size alone. This file's imports
are heavy. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.LeftAtReached
import Johnson.Desc.K2.Honest.Returns.OwnFinish
import Johnson.AtFull.Shape.ArmsLeftNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (roundsFit Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (P2 decideWith rounds par9 flat locOk behindArgs headFrontOf
  finFrontOf finishFrontQ frontAt_of)
open VerifiableInference.Desc.First.Send (planOk1)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.AtFull.Shape (head_four_reached fin_four_reached)
open P1K2 (Prep Nums numsAt prepOf)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open IM (k2P)
open _root_.Tw.K2 (Front Col sendByL8)
open ProofFile (Cl)

/-- **The five of the call that name the prover's two rounds or the columns.** c: the old main
code. -/
structure CallFive (p : P2) (x : Front) (B : TreeBook) (roots : Nat) (r₁ r₂ : Fmt.RoundView)
    (cols : List OpenedColumn) (c : Code) : Prop where
  fits₁ : _root_.Desc.Plain.fits (par9 p).eSeed r₁ = true
  vals : r₁.vals = []
  answers : (K1.answersIn (K1.cutTo (sendingAt p x) r₂)).length = (sendingAt p x).answers
  loc : locOk (behindArgs (par9 p) x (sentAt (sendingAt p x) x.st B roots r₁ r₂) r₂ cols) c.logN =
    true
  readsOpens : AllOpen (callIn p x B roots r₁ r₂ cols).st (callIn p x B roots r₁ r₂ cols).firstTree
    (Positions.ofDraws c.logN r₂.drawn.poss) (callIn p x B roots r₁ r₂ cols).book
    (treesOf (callIn p x B roots r₁ r₂ cols)) (callIn p x B roots r₁ r₂ cols).opened

/-- **The seven at the output head's switch.** c: the old main code. -/
structure HeadSeven (p : P2) (s : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : HeadOwn) (Q : ReqGroup) (c : Code) : Prop where
  call : CallFive p (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs) c
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) s.book
    (treesOf (callIn p (headFrontOf s a Q.target) s.book s.roots r₁ r₂ (flat p gs)))
    (flat p gs) = []
  groups : gs.length = p.read.length

/-- **The seven behind the last segment.** c: the old main code. -/
structure FinSeven (p : P2) (t : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (a : FinOwn) (Q : ReqGroup) (c : Code) : Prop where
  call : CallFive p (finFrontOf t a Q) t.book t.roots r₁ r₂ (flat p gs) c
  noneLeft : leftAfter (Positions.ofDraws c.logN r₂.drawn.poss) t.book
    (treesOf (callIn p (finFrontOf t a Q) t.book t.roots r₁ r₂ (flat p gs))) (flat p gs) = []
  groups : gs.length = p.read.length

variable {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {z : ProofFile.InstPub}
  {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **`HeadSeven` gives `HeadLast`, and the entry's test holds.** -/
theorem headLast_of_seven (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a' nm .head n)) [r₁, r₂] = true)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code}
    (E : HeadSeven (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀) :
    planOk1 none n.sent (par9 (k2P Zp a' nm .head n)).eSeed = true ∧
      HeadLast (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀ := by
  obtain ⟨p1, p2, he, p4⟩ := head_four_reached h O hP hn hr a' nm here group
  obtain ⟨d1, -⟩ := head_draws_plan h.scope h.reads O h.laid.value h.laid.planOk hP hn hr a' nm
    (frontAt_of (Or.inr (Or.inl ⟨rfl, a, Q, here, group, rfl⟩))) r₁ r₂ he hrf
  exact ⟨he,
      { call :=
          { fits₁ := E.call.fits₁
            plan := p1
            vals := E.call.vals
            answers := E.call.answers
            trees := p2
            loc := E.call.loc
            readsOwn := head_own_reached h.scope h.reads O hr here group _ _ _ _ _
            readsOpens := E.call.readsOpens
            inRange := p4 r₂ c₀ d1 }
        noneLeft := E.noneLeft
        groups := E.groups }⟩

theorem head_behind_seven (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a' nm .head n)) [r₁, r₂] = true)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : HeadSeven (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀) :
    HeadBehind (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀ := by
  obtain ⟨he, E'⟩ := headLast_of_seven h O hP hn hr a' nm r₁ r₂ gs hrf here group E
  exact head_behind_last h.toAtMg O hP hn hr a' nm r₁ r₂ gs he hrf here group hc E'

theorem head_returns_seven (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 339 (z, s))
    (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a' nm .head n)) [r₁, r₂] = true)
    {a : HeadOwn} {Q : ReqGroup} (here : s.here = .head a)
    (group : s.check.frame.groups[s.check.frame.link]? = some Q)
    {c₀ : Code} (hc : s.st.codes.base[s.check.frame.shape.code]? = some c₀)
    (E : HeadSeven (k2P Zp a' nm .head n) s r₁ r₂ gs a Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .head n) s [r₁, r₂] gs = .ok s' := by
  obtain ⟨he, E'⟩ := headLast_of_seven h O hP hn hr a' nm r₁ r₂ gs hrf here group E
  exact head_returns_last h.toAtMg O hP hn hr a' nm r₁ r₂ gs he hrf here group hc E'

/-- **`FinSeven` gives `FinLast`, and the entry's test holds.** -/
theorem finLast_of_seven (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a' nm .finish n)) [r₁, r₂] = true)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code}
    (E : FinSeven (k2P Zp a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    planOk1 none n.sent (par9 (k2P Zp a' nm .finish n)).eSeed = true ∧
      FinLast (k2P Zp a' nm .finish n) t r₁ r₂ gs a Q c₀ := by
  obtain ⟨p1, p2, he, p4⟩ := fin_four_reached h O hP hn hr hq a' nm here laid
  have h25 := h25_of_hy h.scope O (tests_at_head h.toAtMg O).1
  obtain ⟨d1, -⟩ := finish_draws_plan h.scope h.reads O h.laid.value h.laid.planOk h25 hP hn hr hq
    a' nm (frontAt_of (Or.inr (Or.inr ⟨rfl, a, Q, here, laid, rfl⟩))) r₁ r₂ he hrf
  exact ⟨he,
      { call :=
          { fits₁ := E.call.fits₁
            plan := p1
            vals := E.call.vals
            answers := E.call.answers
            trees := p2
            loc := E.call.loc
            readsOwn := fin_own_reached h.scope h.reads O hr hq here Q _ _ _ _
            readsOpens := E.call.readsOpens
            inRange := p4 r₂ c₀ d1 }
        noneLeft := E.noneLeft
        groups := E.groups }⟩

theorem fin_behind_seven (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a' nm .finish n)) [r₁, r₂] = true)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀)
    (E : FinSeven (k2P Zp a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    FinBehind (k2P Zp a' nm .finish n) s t r₁ r₂ gs a Q c₀ := by
  obtain ⟨he, E'⟩ := finLast_of_seven h O hP hn hr hq a' nm r₁ r₂ gs hrf here laid E
  exact fin_behind_last h.toAtMg O hP hn hr hq a' nm r₁ r₂ gs he hrf here laid hc E'

theorem fin_returns_seven (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : Prep} {n : Nums} (hP : prepOf Zp Bs.G₀ = some Pp)
    (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 353 (z, s))
    (hq : finishFrontQ s = .ok t) (a' : Place) (nm : String) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hrf : roundsFit (rounds (k2P Zp a' nm .finish n)) [r₁, r₂] = true)
    {a : FinOwn} {Q : ReqGroup} (here : t.here = .fin a) (laid : a.G = some Q)
    {c₀ : Code} (hc : t.st.codes.base[t.check.frame.shape.code]? = some c₀)
    (E : FinSeven (k2P Zp a' nm .finish n) t r₁ r₂ gs a Q c₀) :
    ∃ s', decideWith sendByL8 (k2P Zp a' nm .finish n) t [r₁, r₂] gs = .ok s' := by
  obtain ⟨he, E'⟩ := finLast_of_seven h O hP hn hr hq a' nm r₁ r₂ gs hrf here laid E
  exact fin_returns_last h.toAtMg O hP hn hr hq a' nm r₁ r₂ gs he hrf here laid hc E'

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.headLast_of_seven
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_behind_seven
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_returns_seven
#print axioms VerifiableInference.Desc.K2.Honest.Returns.finLast_of_seven
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_behind_seven
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_returns_seven
