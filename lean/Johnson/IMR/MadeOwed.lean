--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/MadeOwed.lean (over PubFoot.lean:
madeAtK takes D; more_of_owed asks that base is alike): WHAT EACH OF THE SIX KINDS THAT SEND NOTHING
INSIDE A LINK (K3, K4,
K5, K6, K8, K11) OWES FOR THE SIXTH FIELD "more" OF HandsR AT THE PROMISE's
PUBLIC TEST: ONE FORM FOR ALL; and the rule that draws the field from it. Definitions and one
theorem, proved.




  EAt D base links ps z   the promise's public test as the letter E of HandsR: fun k s => ePubAt
    (pubAll D base) moreAll links ps k (z, s).
  keepsAt p   the readers of the verifier's state that the sub-protocol at the place p leaves: the
    five of keepsT; the four of keepsQ at K8 and at K3's lookup on the digits (piece 7 or more),
    which write the approximate range proof's parameters.
  MadeOwed Fk N links ps D base z ft k b p   THE DEBT: at every fenced state s in front and every
    accepting step of b from s to s', neither bearing a mark, with XK at k and s: every item of
    madeAtK D (keepsAt p) moreAll links ps k p is true at s'.
  ridesK_mono, madeAtK_sub, keepsQ_sub, owed_of_Q   more readers kept: less owed: whoever shows the
    items of madeAtQ (at the five readers) has paid MadeOwed.
  more_of_owed   ps[k]? = some p, "every accepting step of b leaves keepsAt p", MadeOwed: then
    HandsR's field "more" at E := EAt.

OBJECT: HandsR's sixth field. USER: none in Lean yet. LETTERS: Fk, N, links, ps, D, base, z, ft, k,
b, p: free.

What is not claimed. MadeOwed at any sub-protocol. That a sub-protocol leaves keepsAt p
(Johnson/IMR/RideAt.lean, Johnson/IMR/TlLot.lean; K4: its own authors'). No soundness.
-/
import Johnson.IMR.HandsFence
import Johnson.Goal.Meaning.QuietRide

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData Rdr More SameOn pubAll ePubAt)
open Meaning.Ride (keepsQ keepsT ridesK frontAt madeAtK madeAtQ more_keeps)
open ProofFile (Cl)

/-- The promise's public test, as HandsR's letter E. -/
def EAt {Q : Type} (D : PubData) (base : Pub → Q × S → Bool) (links : List ModelPart) (ps : List Place)
    (z : Q) : Nat → S → Bool :=
  fun k s => ePubAt (pubAll D base) moreAll links ps k (z, s)

/-- The readers that the sub-protocol at the place leaves. -/
def keepsAt (p : Place) : List Rdr :=
  if p.kind == .K8 || (p.kind == .K3 && decide (7 ≤ p.piece)) then keepsQ else keepsT

/-- **THE DEBT OF A KIND's AUTHORS AT ONE OF ITS PLACES.** -/
def MadeOwed {Q : Type} (Fk : Nat → S → Prop) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (D : PubData) (base : Pub → Q × S → Bool) (z : Q) (ft k : Nat) (b : Block S Cl) (p : Place) :
    Prop :=
  ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
    XK N links ps (EAt D base links ps z) k s = true →
    ∀ q ∈ madeAtK D (keepsAt p) moreAll links ps k p, pubAll D base q (z, s') = true

/-- More readers kept: more rides. -/
theorem ridesK_mono {D : PubData} {keeps keeps' : List Rdr} (h : ∀ r ∈ keeps, r ∈ keeps')
    {A : List Pub} {q : Pub} (hr : ridesK D keeps A q = true) : ridesK D keeps' A q = true := by
  unfold ridesK at hr ⊢
  rw [Bool.and_eq_true] at hr ⊢
  refine ⟨hr.1, ?_⟩
  cases hf : VerifiableInference.Desc.First.footOf D q with
  | none => simp [hf] at hr
  | some R =>
    have h2 := hr.2
    rw [hf] at h2
    have h3 : R.all keeps.contains = true := h2
    show R.all keeps'.contains = true
    rw [List.all_eq_true] at h3 ⊢
    intro r hr'
    have := h3 r hr'
    simpa using h r (by simpa using this)

/-- … and less is owed. -/
theorem madeAtK_sub {D : PubData} {keeps keeps' : List Rdr} (h : ∀ r ∈ keeps, r ∈ keeps')
    {M : More} {links : List ModelPart} {ps : List Place} {k : Nat} {p : Place} {q : Pub}
    (hq : q ∈ madeAtK D keeps' M links ps k p) : q ∈ madeAtK D keeps M links ps k p := by
  unfold madeAtK at hq ⊢
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hq
  refine List.mem_filter.2 ⟨h1, ?_⟩
  cases hr : ridesK D keeps (frontAt M links ps k) q with
  | false => rfl
  | true => rw [ridesK_mono h hr] at h2; exact h2

theorem keepsQ_sub (p : Place) : ∀ r ∈ keepsQ, r ∈ keepsAt p := by
  intro r hr
  unfold keepsAt
  split
  · exact hr
  · simp only [keepsQ, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [keepsT, List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

/-- **Whoever shows the items of madeAtQ (the five readers) has paid the debt.** -/
theorem owed_of_Q {Q : Type} {Fk : Nat → S → Prop} {N : Numbers} {links : List ModelPart}
    {ps : List Place} {D : PubData} {base : Pub → Q × S → Bool} {z : Q} {ft k : Nat}
    {b : Block S Cl} {p : Place}
    (h : ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps (EAt D base links ps z) k s = true →
      ∀ q ∈ madeAtQ D moreAll links ps k p, pubAll D base q (z, s') = true) :
    MadeOwed Fk N links ps D base z ft k b p :=
  fun s s' f hy h0 h1 hx q hq => h s s' f hy h0 h1 hx q (madeAtK_sub (keepsQ_sub p) hq)

/-- **THE FIELD "more" FROM THE DEBT.** -/
theorem more_of_owed {Q : Type} {Fk : Nat → S → Prop} {N : Numbers} {links : List ModelPart}
    {ps : List Place} {D : PubData} {base : Pub → Q × S → Bool} {z : Q} {ft k : Nat}
    {b : Block S Cl} {p : Place} (hp : ps[k]? = some p)
    (hK : ∀ s s', Yes ft b s s' → SameOn D (keepsAt p) s s')
    (alike : ∀ q s s', base q (z, s') = base q (z, s))
    (M : MadeOwed Fk N links ps D base z ft k b p) :
    ∀ s s', Fk k s → Yes ft b s s' → s.failed = none → s'.failed = none →
      XK N links ps (EAt D base links ps z) k s = true →
      EAt D base links ps z (k + 1) s' = true :=
  fun s s' f hy h0 h1 hx =>
    more_keeps D base links ps z k p (keepsAt p) hp s s' (hK s s' hy) (fun q => alike q s s')
      (M s s' f hy h0 h1 hx)
      (xk_parts hx).2.2.2.2

end IM

#print axioms IM.owed_of_Q
#print axioms IM.more_of_owed
