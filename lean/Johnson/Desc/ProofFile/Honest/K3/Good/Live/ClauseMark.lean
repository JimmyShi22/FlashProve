-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/ClauseMark.lean: the kind "lookup" (K3): the condition of
Honest/K3/Good/Live/Clause.lean follows where the lookup's mark says nothing on the samples of the
lookup's own rounds and the state holds what the lookup heard on these rounds. Theorems.

Terms. Honest/K3/GLOSSARY.md ("mark", "good samples", "sample"). In this file: the marks are
`markK3` and `markOut` (Honest/K3/Good/Mark.lean); a mark says nothing if its test returns none. The
lookups' form of a sub-protocol is `FormAt` (Honest/K3/Law/MemberOne.lean). The two seats of the
first chain are `seatOf claim d` (Honest/K3/Law/Stated.lean).

What is shown.
  `clauseBy_behind`: at any test T: the condition at the state behind an accepting step of a
    sub-protocol of the lookups' form: that the state holds what was heard on the step's own rounds,
    from a ledger whose next slot is the place's first, is shown by `form_state`
    (Honest/K3/Law/Thread/StateBehind.lean) and `form_back` (Honest/K3/Law/Thread/MemberBack.lean).
  `clauseBy_member`: the same at the description's own member at a lookup of a public part.
  `silent_iff`, `silentOut_iff`, `silent_both`: `markK3` says nothing just where `goodK3` accepts;
    `markOut` just where `goodK3Out` accepts; where both say nothing both tests accept.
  `clause_of_silent`, `clause_behind`, `clause_member`: the condition at `goodK3` where `markK3`
    says nothing: at a return of the seated hearing; behind a step; at the description's member.
  `clauseOut_behind`, `clauseBoth_behind`, `clauseBoth_member`: the like at `markOut`; at both
    marks.

Hypotheses that remain.
  `hp`: the place's parameters make a shape.
  `hm`, `hm'`, `hk`, `hk'` (in `silent_both`: `h1`, `h2`): the mark says nothing, at the samples of
    the lookup's rounds. The mark's place a and the samples in front fr are read by nothing: the
    tests of these marks read the second list alone.
  `hT`: (in the two theorems at any test) the test accepts these samples.
  `hc`: these samples are such as the rounds can sample (`canDraw`). An accepting step does not give
    this: the step does not ask that the words of a sampled element are below the prime. At a kit of
    challenges it is `canAll_of_kit` (Honest/K3/Good/MarkKit.lean).
  `clause_of_silent`: the hearing's return (`hv`), the ledger's next slot (`hn`), that the second
    list is the rounds' samples (`ho`), and that o holds what was heard (`hs`).
  The theorems whose names end in `_behind`: the form (`Fm`) and the step's acceptance (`hst`).
    Those whose names end in `_member`: the hypotheses of `member_back` (MemberBack.lean), word for
    word: `O`, `hs`, `hb`, `hbs`, `hm` (there: m is a member of the first chain's flat list), `hmp`,
    `hpk`, `hst`.


Limits. The state is the one right behind the lookup's own step. That a later state still holds what
was heard is not shown here. That the second argument of a mark's test is handed the samples of the
member's own rounds is for the files that call the marks to say.
No instance of the hypotheses of `clause_member` together is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Clause
import Johnson.Desc.ProofFile.Honest.K3.Good.Mark
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes.Model (Aff Fork)
open OnBytes.Model.Forest (Shape Heard)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn Place)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.K3.Law (hearVia)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr (form_state form_back)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## At any test -/

/-- **The condition at the state behind an accepting step of a sub-protocol of the lookups' form.**
Conditional on the form, the acceptance and the two tests. -/
theorem clauseBy_behind {T : LFace → List Fmt.Drawn → Bool} {Cl : Type} {claim : Aff → Cl}
    {X : OnBytes.Model.Verify.Public} {i : Nat} {d : Bool} {p : P} {b : Block FS Cl}
    (Fm : FormAt claim X i d p b) {h : Shape} (hp : p.shape = some h) (ft : Nat) (s t : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (hst : b.step ft s rs c = .ok (t, n))
    (hT : T (faceOf h) (rs.map (·.drawn)) = true)
    (hc : canDraw (faceOf h) (rs.map (·.drawn)) = true) :
    ClauseBy T p ((seatOf claim d).heard t) := by
  obtain ⟨F, H, G, a1, _, _, a4, a5, _⟩ := form_state Fm ft s t n rs c hst
  obtain ⟨F', H', G', b1, b2, b3⟩ := form_back Fm ft s t n rs c hst
  obtain rfl : F = F' := Option.some.inj (a1.symm.trans b1)
  obtain rfl : H = H' := congrArg (·.1) (Option.some.inj (a5.symm.trans b2))
  exact clauseBy_of hp (beq_iff_eq.1 a4) a5 hc hT b3

/-- **The same at the description's own member at a lookup of a public part.** Conditional on the
hypotheses that the head of this file lists. No instance of these hypotheses is exhibited in this
file. -/
theorem clauseBy_member {T : LFace → List Fmt.Drawn → Bool} (o : SecondHashFunctionArgument)
    (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place)
    (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView)
    (c : List OpenedColumn) (hst : m.step ft sj rs c = .ok (sj', n)) {h : Shape}
    (hp : s.p.shape = some h) (hT : T (faceOf h) (rs.map (·.drawn)) = true)
    (hc : canDraw (faceOf h) (rs.map (·.drawn)) = true) :
    ClauseBy T s.p ((seatOf K3Lot.ofForm s.digits).heard sj') := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  obtain ⟨_, _, _, _, hst'⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  exact clauseBy_behind Fm hp ft sj sj' n rs c ((hst' ft sj sj' n rs c).1 hst).1 hT hc

/-! ## At the marks -/

/-- The mark says nothing just where the test accepts. -/
theorem silent_iff (a : Place) (f : LFace) (fr own : List Fmt.Drawn) :
    (markK3 a f).test fr own = none ↔ goodK3 f own = true := by
  show (if goodK3 f own then none else some _ : Option String) = none ↔ _
  cases goodK3 f own <;> simp

/-- The like of the mark for other kinds' slots and entries. -/
theorem silentOut_iff (a : Place) (f : LFace) (fr own : List Fmt.Drawn) :
    (markOut a f).test fr own = none ↔ goodK3Out f own = true := by
  show (if goodK3Out f own then none else some _ : Option String) = none ↔ _
  cases goodK3Out f own <;> simp

/-- Where both marks say nothing both tests accept. -/
theorem silent_both {a a' : Place} {f : LFace} {fr fr' own : List Fmt.Drawn}
    (h1 : (markK3 a f).test fr own = none) (h2 : (markOut a' f).test fr' own = none) :
    (goodK3 f own && goodK3Out f own) = true :=
  Bool.and_eq_true_iff.2 ⟨(silent_iff _ _ _ _).1 h1, (silentOut_iff _ _ _ _).1 h2⟩

/-- **The condition, where the mark says nothing, at a return of the seated hearing.** -/
theorem clause_of_silent {p : P} {h : Shape} (hp : p.shape = some h) (a : Place)
    (fr own : List Fmt.Drawn) (hm : (markK3 a (faceOf h)).test fr own = none)
    (hc : canDraw (faceOf h) own = true) {F G : Fork} {rs : List Fmt.RoundView} {H : Heard}
    (hn : F.next = p.first) (hv : hearVia p F rs = some (H, G)) (ho : rs.map (·.drawn) = own)
    {o : Option Heard} (hs : o = some H) : Clause p o := by
  subst ho
  exact clauseBy_of hp hn hv hc ((silent_iff _ _ _ _).1 hm) hs

/-- **The condition at the state behind an accepting step of a sub-protocol of the lookups' form.**
Conditional on the form, the acceptance, the mark's silence and `canDraw`. -/
theorem clause_behind {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} {p : P} {b : Block FS Cl} (Fm : FormAt claim X i d p b) {h : Shape}
    (hp : p.shape = some h) (a : Place) (fr : List Fmt.Drawn) (ft : Nat) (s t : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (hst : b.step ft s rs c = .ok (t, n))
    (hm : (markK3 a (faceOf h)).test fr (rs.map (·.drawn)) = none)
    (hc : canDraw (faceOf h) (rs.map (·.drawn)) = true) :
    Clause p ((seatOf claim d).heard t) :=
  clauseBy_behind Fm hp ft s t n rs c hst ((silent_iff _ _ _ _).1 hm) hc

/-- The like at the mark for other kinds' slots and entries. -/
theorem clauseOut_behind {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public} {i : Nat}
    {d : Bool} {p : P} {b : Block FS Cl} (Fm : FormAt claim X i d p b) {h : Shape}
    (hp : p.shape = some h) (a : Place) (fr : List Fmt.Drawn) (ft : Nat) (s t : FS) (n : Nat)
    (rs : List Fmt.RoundView) (c : List OpenedColumn) (hst : b.step ft s rs c = .ok (t, n))
    (hm : (markOut a (faceOf h)).test fr (rs.map (·.drawn)) = none)
    (hc : canDraw (faceOf h) (rs.map (·.drawn)) = true) :
    ClauseOut p ((seatOf claim d).heard t) :=
  clauseBy_behind Fm hp ft s t n rs c hst ((silentOut_iff _ _ _ _).1 hm) hc

/-- The like where both marks say nothing: both tests, on the same rounds. -/
theorem clauseBoth_behind {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public}
    {i : Nat} {d : Bool} {p : P} {b : Block FS Cl} (Fm : FormAt claim X i d p b) {h : Shape}
    (hp : p.shape = some h) (a a' : Place) (fr fr' : List Fmt.Drawn) (ft : Nat) (s t : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (hst : b.step ft s rs c = .ok (t, n))
    (hm : (markK3 a (faceOf h)).test fr (rs.map (·.drawn)) = none)
    (hm' : (markOut a' (faceOf h)).test fr' (rs.map (·.drawn)) = none)
    (hc : canDraw (faceOf h) (rs.map (·.drawn)) = true) :
    ClauseBoth p ((seatOf claim d).heard t) :=
  clauseBy_behind Fm hp ft s t n rs c hst (silent_both hm hm') hc

/-- **The same at the description's own member at a lookup of a public part.** Conditional on the
hypotheses that the head of this file lists. No instance of these hypotheses is exhibited in this
file. -/
theorem clause_member (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place)
    (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView)
    (c : List OpenedColumn) (hst : m.step ft sj rs c = .ok (sj', n)) {h : Shape}
    (hp : s.p.shape = some h) (a : Place) (fr : List Fmt.Drawn)
    (hk : (markK3 a (faceOf h)).test fr (rs.map (·.drawn)) = none)
    (hc : canDraw (faceOf h) (rs.map (·.drawn)) = true) :
    Clause s.p ((seatOf K3Lot.ofForm s.digits).heard sj') :=
  clauseBy_member o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk ft sj sj' n rs c
    hst hp ((silent_iff _ _ _ _).1 hk) hc

/-- The like where both marks say nothing. Conditional on the hypotheses that the head of this file
lists. No instance of these hypotheses is exhibited in this file. -/
theorem clauseBoth_member (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (lot m : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder) (hmp : m.place = lot.place)
    (hpk : m.planOk = true) (ft : Nat) (sj sj' : FS) (n : Nat) (rs : List Fmt.RoundView)
    (c : List OpenedColumn) (hst : m.step ft sj rs c = .ok (sj', n)) {h : Shape}
    (hp : s.p.shape = some h) (a a' : Place) (fr fr' : List Fmt.Drawn)
    (hk : (markK3 a (faceOf h)).test fr (rs.map (·.drawn)) = none)
    (hk' : (markOut a' (faceOf h)).test fr' (rs.map (·.drawn)) = none)
    (hc : canDraw (faceOf h) (rs.map (·.drawn)) = true) :
    ClauseBoth s.p ((seatOf K3Lot.ofForm s.digits).heard sj') :=
  clauseBy_member o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk ft sj sj' n rs c
    hst hp (silent_both hk hk') hc

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.clauseBy_behind
#print axioms ProofFile.Honest.K3.Good.Live.clauseBy_member
#print axioms ProofFile.Honest.K3.Good.Live.silent_iff
#print axioms ProofFile.Honest.K3.Good.Live.silentOut_iff
#print axioms ProofFile.Honest.K3.Good.Live.silent_both
#print axioms ProofFile.Honest.K3.Good.Live.clause_of_silent
#print axioms ProofFile.Honest.K3.Good.Live.clause_behind
#print axioms ProofFile.Honest.K3.Good.Live.clauseOut_behind
#print axioms ProofFile.Honest.K3.Good.Live.clauseBoth_behind
#print axioms ProofFile.Honest.K3.Good.Live.clause_member
#print axioms ProofFile.Honest.K3.Good.Live.clauseBoth_member
