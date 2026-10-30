-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/RidesPast.lean: the honest side of the kind "lookup"
(K3). Conditional: the sentence `RidesPast` (Honest/Thread/Pays.lean, which lists it as owed at a
member) at a lookup's sub-protocol in the first chain: an item that is open in front, and that the
sub-protocol's row of the table neither shuts nor owes, says behind, of any witness, what it says in
front. General in the first chain's letters. Theorems; one definition.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: L is the structure of the first chain's letters (`Letters`,
Honest/Thread/First.lean), and b is a border's number. `SameBut` is the library's relation between
the states in front of and behind a lookup (Johnson/Desc/First/Look/K3CallsTurns.lean).

What is shown.
  `sameBut_symm`, `stays_symm`, `relOf_symm`: the relation is symmetric.
  `GoesOn`, `goesOn_of_back`: "what it says in front, it says behind"; from the library's sentence.
  `strs_stay`, `stays_mono`: the first chain's strings stay below the number of trees sent, whatever
    rounds are set behind.
  `unmarked_back`: the item "no mark of failure".
  `ridesPast_of_sameBut`: `RidesPast`, at every number b at which the letter keeps gives `SameBut`:
    nothing of a lookup is in the statement but that relation.

Hypotheses that remain, and whose each is.
  `hKeep`: the letter keeps gives `SameBut` at this sub-protocol: it is for the thread's letters. It
    bounds that letter from above; the sentence `Behind` (Pays.lean) bounds it from below (an
    acceptance of the step gives keeps). Both hold where keeps is `SameBut` at a lookup's number:
    Honest/K3/Law/Thread/BehindStep.lean (`step_digits`, `step_calls`) then shows it behind an
    acceptance by the step of the stated sub-protocol, where that one's test on the plan accepts; at
    the calls on rounds whose words are below the prime.
  `hbase`: base is at most the number of trees that the sub-protocols in front send: a line on
    numbers. A smaller base makes `hBack` the stronger hypothesis (more pairs of strings are
    related): the weakest is base := that number itself.
  `hBack`: for each item that is carried past: the library's sentence `GoesBack`, at the items'
    meaning at the honest letters: it is for whoever fills the item. The honest letters change two
    of the fields that items read: pin and totalB. At every other item the sentence is the library's
    own. The library shows it at its composed meaning in part
    (Johnson/Desc/Sound/MgAt/K3Rides.lean): of five fields: row and pile outright; pinW, pin and
    constr under named hypotheses on that meaning's letters; at the lookup on the calls alone; and
    by that file's own head no parameters are shown there that meet these hypotheses. At the items
    on pins and at totalB it speaks of the honest side's two letters: that is not shown in this
    file; it is for whoever sets these two letters to show: they must read of the state nothing that
    a lookup sets.
  `h`: (in `sameBut_symm`, `stays_symm`, `relOf_symm`, `stays_mono`, `goesOn_of_back`) the relation,
    or the library's sentence, that is turned round. `hb`: (in `stays_mono`) base' ≤ base.

Imported. Files under Honest/Thread/.

How the proof goes. The library has the mirror of this sentence on the verifier's side: its rule for
what is carried past a lookup's seat (`rides_at_seat_rel`, Johnson/Desc/First/Look/K3RidesR.lean)
asks of each such item `GoesBack (relOf SameBut base)`: what it says behind, it says in front. The
relation is symmetric: `SameBut` is made of equations and of a clause on the state's sort that reads
the same both ways; "the strings stay below base" is made of equations. So each such sentence goes
forward as well. The proof of `ridesPast_of_sameBut` takes one clause out of the thread's sentence
by its position: a clause more in that sentence, in another file, would break it.

Users. Honest/K3/Law/Thread/ToyLetters.lean [not in this library] calls `ridesPast_of_sameBut` and
`unmarked_back`.

Limits. An implication, conditional on the three. No instance of these hypotheses is exhibited in
this file.
Where an item "forms" is carried past, `hBack` may have no instance: `SameBut` relates two states
whose open layers' link holds any two ledgers, and that item's sentence reads the ledger. At the
lookups on the digits the sentence is had another way, without `hBack`:
`lookupOpenItemsRidePastTheDigits` (Honest/K3/Term/LookupOpenItemsRidePastTheDigits.lean),
conditional on what that file's head lists.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3RidesR
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Item Numbers Meaning)
open VerifiableInference.Desc.Sound (MsgT GoesBack)
open VerifiableInference.OnPublicFiles (SameBut relOf)
open Johnson.Desc.First.Walk.Tied (Stays)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## The relation is symmetric -/

theorem sameBut_symm {s t : FS} (h : SameBut s t) : SameBut t s where
  st := h.st.symm
  book := h.book.symm
  roots := h.roots.symm
  rowsOwed := h.rowsOwed.symm
  failed := h.failed.symm
  check := h.check.symm
  out := h.out.symm
  req := h.req.symm
  link := h.link.symm
  sort := by
    rcases h.sort with ⟨a, a', e, e'⟩ | ⟨a, a', e, e'⟩ | ⟨a, a', e, e', o, o'⟩
    · exact Or.inl ⟨a', a, e', e⟩
    · exact Or.inr (Or.inl ⟨a', a, e', e⟩)
    · exact Or.inr (Or.inr ⟨a', a, e', e, o', o⟩)

theorem stays_symm {base : Nat} {y y' : Strs} (h : Stays base y y') : Stays base y' y :=
  ⟨fun x => (h.1 x).symm, fun j x hj => (h.2 j x hj).symm⟩

theorem relOf_symm {Pp : Type} {base : Nat} {a b : Pp × FS} {y y' : Strs}
    (h : relOf SameBut base a y b y') : relOf SameBut base b y' a y :=
  ⟨h.1.symm, sameBut_symm h.2.1, stays_symm h.2.2⟩

/-! ## Forward -/

/-- What the sentence says at the state in front, it says at the state behind, wherever the two are
related. The library's `GoesBack`, read the other way. -/
def GoesOn {Pp Wt : Type} (rel : Pp × FS → Strs → Pp × FS → Strs → Prop)
    (φ : Pp × FS → Strs → Wt → Prop) : Prop :=
  ∀ a y b y' w, rel a y b y' → φ a y w → φ b y' w

/-- **Over the lookups' relation the library's sentence goes forward as well.** -/
theorem goesOn_of_back {Pp Wt : Type} {base : Nat} {φ : Pp × FS → Strs → Wt → Prop}
    (h : GoesBack (relOf SameBut base) φ) : GoesOn (relOf SameBut base) φ :=
  fun a y b y' w hr hφ => h b y' a y w (relOf_symm hr) hφ

/-- The item "no mark of failure": the library's sentence holds of it at every meaning. -/
theorem unmarked_back {Pp Wt : Type} (N : Numbers) (Mg : Meaning Pp Wt) (base : Nat) :
    GoesBack (relOf SameBut base) (Item.unmarked.holds N Mg) := by
  intro a y b y' w hr h
  have h' : b.2.failed = none := h
  show a.2.failed = none
  rw [← hr.2.1.failed]
  exact h'

/-! ## The first chain's strings -/

/-- **The first chain's strings stay below the number of trees sent**, whatever rounds are set
behind. -/
theorem strs_stay (item n₁ n₂ : Nat) (E : Env) (ps : List Played) :
    Stays E.sent (Env.strs item (srcAt 0 n₁ n₂) E)
      (Env.strs item (srcAt 0 n₁ n₂) (E.add ps)) := by
  refine ⟨fun _ => rfl, fun j x hj => ?_⟩
  show (match (srcAt 0 n₁ n₂ j).bind (E.add ps).tree with
      | some u => if x < 2 ^ u.2.logLength then u.2.col x else []
      | none => []) =
    (match (srcAt 0 n₁ n₂ j).bind E.tree with
      | some u => if x < 2 ^ u.2.logLength then u.2.col x else []
      | none => [])
  have e : (srcAt 0 n₁ n₂ j).bind (E.add ps).tree = (srcAt 0 n₁ n₂ j).bind E.tree := by
    unfold srcAt
    by_cases h1 : j < n₁
    · simp [h1, Env.add, hj]
    · simp [h1]
  rw [e]

theorem stays_mono {base base' : Nat} {y y' : Strs} (h : Stays base y y') (hb : base' ≤ base) :
    Stays base' y y' := ⟨h.1, fun j x hj => h.2 j x (Nat.lt_of_lt_of_le hj hb)⟩

/-! ## `RidesPast` -/

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT)

/-- **`RidesPast` at sub-protocol number b of the first chain.** Conditional on what this file's
head lists. No instance of these hypotheses is exhibited in this file. -/
theorem ridesPast_of_sameBut (b base : Nat) (hKeep : ∀ s s', L.keeps b s s' → SameBut s s')
    (hbase : base ≤ treesTo L.bs b)
    (hBack : ∀ w i, i ∈ L.thread.opened b → i ∉ (L.thread.row b).shuts →
      i ∉ (L.thread.row b).owes → GoesBack (relOf SameBut base) (i.holds L.N (L.mg w))) :
    RidesPast L.thread b := by
  intro k s m E s' ps i v hA hk hi h1 h2 hm
  have hsent : E.sent = treesTo L.bs b := hA.2.2.2.2.1.2.2.1
  have hst : Stays base (Env.strs L.item (srcAt 0 L.n₁ L.n₂) E)
      (Env.strs L.item (srcAt 0 L.n₁ L.n₂) (E.add ps)) :=
    stays_mono (strs_stay L.item L.n₁ L.n₂ E ps) (by rw [hsent]; exact hbase)
  exact goesOn_of_back (hBack m.st.input i hi h1 h2) (L.thread.seat k m s) _ (L.thread.seat k m s')
    _ v ⟨rfl, hKeep s s' hk, hst⟩ hm

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.sameBut_symm
#print axioms ProofFile.Honest.K3.Law.AtThr.stays_symm
#print axioms ProofFile.Honest.K3.Law.AtThr.relOf_symm
#print axioms ProofFile.Honest.K3.Law.AtThr.goesOn_of_back
#print axioms ProofFile.Honest.K3.Law.AtThr.unmarked_back
#print axioms ProofFile.Honest.K3.Law.AtThr.strs_stay
#print axioms ProofFile.Honest.K3.Law.AtThr.stays_mono
#print axioms ProofFile.Honest.K3.Law.AtThr.ridesPast_of_sameBut
