-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/RiderLaw.lean: one draw, many riders: the law of the rounds of a block that hears,
stated of the text that runs, and proved from named premises.

The setting. In a segment of the protocol (Johnson/Desc/Block.lean) most blocks only hear: they take
the prover's messages and the verifier's challenges into the state and test nothing at once. One
such block (a host) draws a point, coordinate by coordinate, and several identities are tested at
that point: its own and those of other blocks (its guests). Each identity is a polynomial in the
coordinate drawn, fixed before the draw.

ONE DRAW, MANY RIDERS (Johnson/Desc/RiderAlg.lean: pure algebra, over Mathlib alone). A RIDER is a
polynomial in the element x that is drawn. If each rider has degree at most δ, the BAD values of x
are the roots of the FIRST rider that is not the zero polynomial: at most δ values: the largest
degree, NOT the sum over the riders. At every other x: if all riders vanish at x, all riders are the
zero polynomial (`riders_back`). The maximum is right for this state alone: "some equation that is
alive is false at the one datum to which the prover is bound". It is not right over several events
that each rescue the same false equation, nor over several candidates for the datum. No basis is
fixed: `eqk a b`, the pair (1 - x, x) of an equality kernel, is one form of a rider; a list of
powers (`termsPoly`, Johnson/Desc/LinkLaw2.lean) is another.

THE LAW OF A HEARING BLOCK (sections 2, 3). A meaning X (`HearSem`) is laid beside a block: a
relation in front (`In`), a relation on the state behind (`Out`: meant: the equations behind the
block's claims hold), a relation `At` behind each round of the block's stretch, a relation `Mid`
behind each element that a round draws (a round may draw several: they are taken one by one), and
for each drawn element its riders, which see the state in front, the earlier rounds, the round's own
message, the elements drawn before in the round and the prover's data, but not that element.
  `HearSem.Sound`: for each drawn element at most `deg` values are bad, named by what stands
    before its draw and by the prover's data; and wherever the block's own step says yes on a
    stretch none of whose drawn elements is bad: `Out` at the state behind gives `In` at the
    state in front.
  `HearSem.Premises.sound`: PROVED from: `start`, `close`, `enter`, `leave` and, for each
    drawn element: `degs`: the riders' degrees; `vanish`: the relation behind it makes all riders
    vanish at it; `back`: that relation, with all riders the zero polynomial, gives the relation
    in front of it.
  `HearSem.Answers`, `HearSem.Worth`: companions, for a run to show of a block: a yes at data
    at which `In` holds; a yes at data at which `In` fails; a yes behind which `Out` holds.
  An element without riders, or a round without a drawn element, is one whose relation is carried
  backward outright.
Host and guests: the host's own identity and each guest's are riders of the same draw. A guest is a
family: behind s of its k borrowed coordinates it is 2 ^ (k - s) values, each pair of them a rider
at the next. A guest that borrows only some coordinates rides at these draws and is part of `At` and
`Mid` at the others. A RIDER IS THE TRUE IDENTITY, a function of the data to which the prover is
bound, NOT the form that the verifier's text types: that form may read what is sent behind the
point; that the two agree is a claim of its own, tested in no file of this library.

AGAINST THE LIBRARY. Blocks/StageBoth.lean has the rider as a law of the library's typed blocks
(`Vanishes`, `doomed_rider`, `Block.clean_rider`; the maximum: `Block.Clean.both`). A kind that
carries a proved block of the library has its riders there and needs nothing of this file. This file
is for a kind whose lemma is proved outright on views, and for what that file's own Limits shut out:
a verifier message that is a whole point.

THE SILLY MEMBERS (section 4), as theorems at one meaning over the field of 5 elements: a host with
a table of four hidden values, tested at a point of two coordinates drawn in two rounds, and a guest
with two hidden values that borrows the second coordinate alone; all riders in the pair (1 - x, x).
The block as it is meant meets all premises at the degree 1, and the companions. A block that lays
the first drawn element twice does not meet `Sound`. A meaning that forgets the guest behind the
first round does not meet the premise `back`. A block that says no to all meets `Sound` and does
not meet `Answers`. And the same host and guest with BOTH COORDINATES DRAWN IN ONE ROUND: the block
as it is meant meets all premises and the companions; the block that lays the first drawn element
twice does not meet `Sound`.

LIMITS. (1) X is letters: a hollow filling gives a hollow law (In always true; Out never): `Worth`
guards these two. It cannot guard a relation behind that does not look at the state (Out saying what
In says): no companion can: the guard is that In and Out are the relations which a table of what
each block hands to the next fixes for this block. NO BLOCK OF THE PROTOCOL IS SHOWN TO MEET THE
PREMISES: the law of one link, host and guests composed, is stated by this file as a predicate on
what runs, and is not paid. (2) Where a round
draws k elements at once, the law names bad VALUES of each element, given the earlier ones. How many
of the round's challenges (tuples) are then bad, at most the sum over j of deg j times the field's
size to the power k - 1, is not counted here: it is part of the carriage to raw challenges. A draw
from the field without 0 is the like. (3) The prover's data y are one letter for the whole block,
and in `Sound` they stand under "for all": "named before the draw" is true of a bad set only once y
is pinned in front of the block (Johnson/Desc/LinkLaw4.lean: `huniq`). A block in whose stretch the
prover sends an oracle of which that block's own riders speak is not covered. (4) The count is of
field elements that a view shows as drawn. (5) Which degrees occur is each kind's to say. (6)
Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.LinkLaw2
import Johnson.Desc.RiderAlg

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc
open Polynomial

/-! ## 1 One draw, many riders: Johnson/Desc/RiderAlg.lean -/

/-! ## 2 The meaning beside a block that hears -/

section Hear
variable {S Cl Y K : Type} [Field K]

/-- **The meaning that is laid beside a hearing block's text.** Nothing here is code of the
verifier. S: the state. Y: the data to which the prover is bound. K: the field. "The earlier rounds"
of a round of the block's stretch are the rounds of the stretch before it, with their draws. A round
may draw several elements: they are taken one by one, in the order in which a view shows them. -/
structure HearSem (K S Y : Type) [Field K] where
  /-- a drawn element, as a view shows it, as an element of the field -/
  rd : Fmt.Ext → K
  /-- the condition on the state in front of the block -/
  ready : S → Prop
  /-- the relation in front of the block -/
  In : S → Y → Prop
  /-- the relation on the state behind the block -/
  Out : S → Y → Prop
  /-- the relation behind some first rounds of the stretch: it sees the state in front and these
  rounds -/
  At : S → List Fmt.RoundView → Y → Prop
  /-- the relation inside a round, behind its message and the first of its drawn elements: it sees
  the state in front, the earlier rounds, the round's message and these elements -/
  Mid : S → List Fmt.RoundView → List Fmt.ItemValue → List Fmt.Ext → Y → Prop
  /-- the riders of a round's next drawn element: they see the state in front, the earlier rounds,
  the round's own message, the elements that the round has drawn before and the prover's data, NOT
  that element -/
  riders : S → List Fmt.RoundView → List Fmt.ItemValue → List Fmt.Ext → Y → List K[X]
  /-- the largest degree at the element number j of the round number i -/
  deg : ℕ → ℕ → ℕ

variable (X : HearSem K S Y)

/-- No drawn element of the stretch is bad: for every round, with the rounds before it, and every
element that it has drawn, with those drawn before it in the round. -/
def HearSem.CleanAt (s : S) (y : Y) (rs : List Fmt.RoundView) : Prop :=
  ∀ pre r post, rs = pre ++ r :: post → ∀ xs x ys, r.drawn.elems = xs ++ x :: ys →
    X.rd x ∉ badRiders K (X.riders s pre r.vals xs y)

/-- **THE LAW OF A HEARING BLOCK, the half on soundness.** For each drawn element at most `deg`
values are bad, named by what stands before its draw and by the prover's data. Wherever the block's
own step says yes (from a ready state; all words below the prime) on a stretch without a bad
element, the relation on the state behind gives the relation in front. -/
def HearSem.Sound (b : Block S Cl) (ft : ℕ) : Prop :=
  (∀ s pre vals xs y, X.ready s →
    (badRiders K (X.riders s pre vals xs y)).card ≤ X.deg pre.length xs.length) ∧
  ∀ s rs cols s' k y, X.ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true → b.step ft s rs cols = .ok (s', k) →
    X.CleanAt s y rs → X.Out s' y → X.In s y

/-- **The companion**: the step says yes somewhere, at data at which the relation in front holds. -/
def HearSem.Answers (b : Block S Cl) (ft : ℕ) : Prop :=
  ∃ s rs cols s' k y, X.ready s ∧ viewWordsBelowPrime ⟨rs, cols⟩ = true ∧ b.step ft s rs cols = .ok (s', k) ∧
    X.In s y

/-- **A filling is worth something only if**, beside that, the step says yes somewhere at data at
which the relation in front FAILS, and somewhere with the relation behind holding. A relation in
front that always holds fails the first; a relation behind that never holds fails the second. -/
def HearSem.Worth (b : Block S Cl) (ft : ℕ) : Prop :=
  X.Answers b ft ∧
  (∃ s rs cols s' k y, X.ready s ∧ viewWordsBelowPrime ⟨rs, cols⟩ = true ∧
    b.step ft s rs cols = .ok (s', k) ∧ ¬ X.In s y) ∧
  ∃ s rs cols s' k y, X.ready s ∧ viewWordsBelowPrime ⟨rs, cols⟩ = true ∧
    b.step ft s rs cols = .ok (s', k) ∧ X.Out s' y

/-- The premises of the law. -/
structure HearSem.Premises (b : Block S Cl) (ft : ℕ) : Prop where
  /-- the relation behind no round gives the relation in front of the block -/
  start : ∀ s y, X.ready s → X.At s [] y → X.In s y
  /-- at a yes, the relation on the state behind gives the relation behind the last round -/
  close : ∀ s rs cols s' k y, X.ready s → viewWordsBelowPrime ⟨rs, cols⟩ = true →
    b.step ft s rs cols = .ok (s', k) → X.Out s' y → X.At s rs y
  /-- the relation behind a round gives the relation behind the last of its drawn elements -/
  enter : ∀ s pre r y, X.ready s → X.At s (pre ++ [r]) y → X.Mid s pre r.vals r.drawn.elems y
  /-- the relation behind a round's message, in front of its draws, gives the relation in front of
  the round -/
  leave : ∀ s pre vals y, X.ready s → X.Mid s pre vals [] y → X.At s pre y
  /-- the riders' degrees -/
  degs : ∀ s pre vals xs y, X.ready s →
    ∀ q ∈ X.riders s pre vals xs y, q.natDegree ≤ X.deg pre.length xs.length
  /-- the relation behind a drawn element makes its riders vanish at it -/
  vanish : ∀ s pre vals xs x y, X.ready s → X.Mid s pre vals (xs ++ [x]) y →
    ∀ q ∈ X.riders s pre vals xs y, q.eval (X.rd x) = 0
  /-- the relation behind a drawn element, with all its riders the zero polynomial, gives the
  relation in front of it -/
  back : ∀ s pre vals xs x y, X.ready s → X.Mid s pre vals (xs ++ [x]) y →
    (∀ q ∈ X.riders s pre vals xs y, q = 0) → X.Mid s pre vals xs y

/-! ## 3 The law, proved from the premises -/

/-- Backward along the elements that one round has drawn. -/
theorem HearSem.Premises.alongElems {X : HearSem K S Y} {b : Block S Cl} {ft : ℕ}
    (H : X.Premises b ft) (s : S) (y : Y) (hr : X.ready s) (pre : List Fmt.RoundView)
    (vals : List Fmt.ItemValue) :
    ∀ es : List Fmt.Ext,
      (∀ xs x ys, es = xs ++ x :: ys → X.rd x ∉ badRiders K (X.riders s pre vals xs y)) →
      X.Mid s pre vals es y → X.Mid s pre vals [] y := by
  intro es
  induction es using List.reverseRecOn with
  | nil => exact fun _ h => h
  | append_singleton xs x ih =>
    intro hclean hmid
    refine ih (fun xs' x' ys' h => hclean xs' x' (ys' ++ [x]) (by rw [h]; simp)) ?_
    exact H.back s pre vals xs x y hr hmid
      (riders_back K _ (X.rd x) (hclean xs x [] rfl) (H.vanish s pre vals xs x y hr hmid))

/-- Backward along a stretch without a bad element. -/
theorem HearSem.Premises.along {X : HearSem K S Y} {b : Block S Cl} {ft : ℕ}
    (H : X.Premises b ft) (s : S) (y : Y) (hr : X.ready s) :
    ∀ rs : List Fmt.RoundView, X.CleanAt s y rs → X.At s rs y → X.At s [] y := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => exact fun _ h => h
  | append_singleton pre r ih =>
    intro hclean hat
    refine ih (fun p q post hpq => hclean p q (post ++ [r]) (by rw [hpq]; simp)) ?_
    exact H.leave s pre r.vals y hr
      (H.alongElems s y hr pre r.vals r.drawn.elems (hclean pre r [] rfl)
        (H.enter s pre r y hr hat))

/-- **THE LAW, PROVED FROM THE PREMISES.** -/
theorem HearSem.Premises.sound {X : HearSem K S Y} {b : Block S Cl} {ft : ℕ}
    (H : X.Premises b ft) : X.Sound b ft :=
  ⟨fun s pre vals xs y hr => badRiders_card_le K _ _ (H.degs s pre vals xs y hr),
    fun s rs cols s' k y hr hw hs hclean hout =>
      H.start s y hr (H.along s y hr rs hclean (H.close s rs cols s' k y hr hw hs hout))⟩

end Hear

/-! ## 4 The silly members: the law tried on toys, as theorems -/

/-- A stretch that passes a block's test on the rounds has as many rounds as the block declares. -/
theorem roundsFit_count : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds rs = true → rs.length = ds.length
  | [], [], _ => rfl
  | d :: ds, r :: rs, h => by
    simp only [roundsFit, Bool.and_eq_true] at h
    simp [roundsFit_count ds rs h.2]
  | [], _ :: _, h => by simp [roundsFit] at h
  | _ :: _, [], h => by simp [roundsFit] at h

theorem step_fits {S Cl : Type} {ft : ℕ} {b : Block S Cl} {s s' : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {k : ℕ} (h : b.step ft s rs cols = .ok (s', k)) :
    roundsFit b.rounds rs = true := by
  rw [Block.step_eq] at h
  split at h
  · next hf => exact hf
  · cases h

/-- The first round of a stretch that passes has drawn as many elements as its entry says. -/
theorem roundsFit_elems {d : Fmt.DeclaredRound} {ds : List Fmt.DeclaredRound} {r : Fmt.RoundView}
    {rs : List Fmt.RoundView} (h : roundsFit (d :: ds) (r :: rs) = true) :
    r.drawn.elems.length = d.entry.drawE ∧ roundsFit ds rs = true := by
  simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨by tauto, h.2⟩

namespace RiderToy
open LinkToy

/-- The toy's state: the two elements laid. -/
abbrev Pt : Type := F5 × F5

/-- The prover's data: a host's table of four hidden values (at 00, 01, 10, 11) and a guest's of
two. All are claimed to be 0. -/
structure Dat where
  h00 : F5
  h01 : F5
  h10 : F5
  h11 : F5
  g0 : F5
  g1 : F5

/-- All six are 0. -/
def Dat.zero (y : Dat) : Prop :=
  y.h00 = 0 ∧ y.h01 = 0 ∧ y.h10 = 0 ∧ y.h11 = 0 ∧ y.g0 = 0 ∧ y.g1 = 0

/-- The host's table with its first coordinate at a. -/
def Dat.row (y : Dat) (a : F5) : F5 × F5 :=
  ((1 - a) * y.h00 + a * y.h10, (1 - a) * y.h01 + a * y.h11)

/-- Behind the first coordinate: the host's two values at a are 0, and THE GUEST IS CARRIED. -/
def Dat.half (y : Dat) (a : F5) : Prop :=
  (y.row a).1 = 0 ∧ (y.row a).2 = 0 ∧ y.g0 = 0 ∧ y.g1 = 0

/-- Behind both: the host's value at (a, b) and the guest's at b are 0. -/
def Dat.full (y : Dat) (a b : F5) : Prop :=
  (1 - b) * (y.row a).1 + b * (y.row a).2 = 0 ∧ (1 - b) * y.g0 + b * y.g1 = 0

/-- The meaning, but for what is carried behind the first coordinate. -/
def semWith (half : Dat → F5 → Prop) : HearSem F5 Pt Dat :=
  { rd := rd, ready := fun _ => True
    In := fun _ y => y.zero
    Out := fun s y => y.full s.1 s.2
    At := fun _ rs y =>
      match rs with
      | [] => y.zero
      | [r] => ∃ a, r.drawn.elems = [a] ∧ half y (rd a)
      | [r, r'] => ∃ a b, r.drawn.elems = [a] ∧ r'.drawn.elems = [b] ∧ y.full (rd a) (rd b)
      | _ => False
    Mid := fun _ pre _ xs y =>
      match pre, xs with
      | [], [] => y.zero
      | [], [a] => half y (rd a)
      | [r], [] => ∃ a, r.drawn.elems = [a] ∧ half y (rd a)
      | [r], [b] => ∃ a, r.drawn.elems = [a] ∧ y.full (rd a) (rd b)
      | _, _ => False
    riders := fun _ pre _ xs y =>
      match pre, xs with
      | [], [] => [eqk F5 y.h00 y.h10, eqk F5 y.h01 y.h11]
      | [r], [] =>
        match r.drawn.elems with
        | [a] => [eqk F5 (y.row (rd a)).1 (y.row (rd a)).2, eqk F5 y.g0 y.g1]
        | _ => []
      | _, _ => []
    deg := fun _ _ => 1 }

/-- THE MEANING. -/
def sem : HearSem F5 Pt Dat := semWith Dat.half

/-- SILLY: a meaning that forgets the guest behind the first coordinate. -/
def semForgets : HearSem F5 Pt Dat := semWith fun y a => (y.row a).1 = 0 ∧ (y.row a).2 = 0

/-- A block with two rounds, each of which draws one element, and a given decision. -/
def block2 (dec : Pt → List Fmt.RoundView → Except String Pt) : Block Pt Bool :=
  { name := "host", place := ⟨1, some 0, 1, .K4⟩, planOk := true, rounds := [round, round]
    oracles := [[], []], before := [], decide := fun s rs _ => dec s rs, claims := [], after := [] }

/-- THE BLOCK AS IT IS MEANT: it lays the two elements drawn into the state. -/
def meant : Block Pt Bool :=
  block2 fun _ rs =>
    match rs.flatMap (·.drawn.elems) with
    | [a, b] => .ok (rd a, rd b)
    | _ => .error "two elements"

/-- SILLY: it lays the first element drawn twice. -/
def twice : Block Pt Bool :=
  block2 fun _ rs =>
    match rs.flatMap (·.drawn.elems) with
    | [a, _] => .ok (rd a, rd a)
    | _ => .error "two elements"

/-- SILLY: it says no to all. -/
def noToAll : Block Pt Bool := block2 fun _ _ => .error "no"

theorem block2_step (dec : Pt → List Fmt.RoundView → Except String Pt) (s : Pt) (a b : Fmt.Ext) :
    (block2 dec).step 0 s [rv a, rv b] [] = (dec s [rv a, rv b]).map fun s' => (s', 0) := by
  have h1 : roundsFit (block2 dec).rounds [rv a, rv b] = true := rfl
  have h2 : groupsOf 0 (block2 dec).rounds ([rv a, rv b].map (·.drawn)) = [] := rfl
  have h3 : [rv a, rv b].map noDigest = [rv a, rv b] := rfl
  rw [Block.step_eq, h1, h2, h3]
  cases h : dec s [rv a, rv b] <;>
    simp [block2, h, Except.map, bind, Except.bind, pure, Except.pure]

theorem block2_yes {dec : Pt → List Fmt.RoundView → Except String Pt} {s s' : Pt} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {k : ℕ} (h : (block2 dec).step 0 s rs cols = .ok (s', k)) :
    dec s (rs.map noDigest) = .ok s' := by
  rw [Block.step_eq] at h
  split at h
  · split at h
    · simp only [block2] at h
      cases hd : dec s (rs.map noDigest) with
      | error e => simp [hd, bind, Except.bind] at h
      | ok z =>
        simp only [hd, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [h.1]
    · cases h
  · cases h

/-- A stretch on which such a block says yes: two rounds, one element each. -/
theorem block2_shape {dec : Pt → List Fmt.RoundView → Except String Pt} {s s' : Pt} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {k : ℕ} (h : (block2 dec).step 0 s rs cols = .ok (s', k)) :
    ∃ r r' a b, rs = [r, r'] ∧ r.drawn.elems = [a] ∧ r'.drawn.elems = [b] := by
  have hf : roundsFit [round, round] rs = true := step_fits h
  have hlen : rs.length = 2 := roundsFit_count _ _ hf
  match rs, hlen with
  | [r, r'], _ =>
    obtain ⟨h1, hf'⟩ := roundsFit_elems hf
    obtain ⟨h2, _⟩ := roundsFit_elems hf'
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 h1
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 h2
    exact ⟨r, r', a, b, rfl, ha, hb⟩

theorem toy_degs (half : Dat → F5 → Prop) (s : Pt) (pre : List Fmt.RoundView) (vals : List Fmt.ItemValue)
    (xs : List Fmt.Ext) (y : Dat) :
    ∀ q ∈ (semWith half).riders s pre vals xs y, q.natDegree ≤ 1 := by
  intro q hq
  simp only [semWith] at hq
  split at hq
  · rcases List.mem_cons.1 hq with rfl | hq
    · exact eqk_natDegree_le _ _ _
    · rw [List.mem_singleton.1 hq]; exact eqk_natDegree_le _ _ _
  · split at hq
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact eqk_natDegree_le _ _ _
      · rw [List.mem_singleton.1 hq]; exact eqk_natDegree_le _ _ _
    · cases hq
  · cases hq

/-- THE MEANT BLOCK MEETS ALL PREMISES OF THE LAW: at each draw two riders, at the degree 1. -/
theorem meant_premises : sem.Premises meant 0 where
  start := fun _ _ _ h => h
  close := fun s rs cols s' k y _ _ h hout => by
    obtain ⟨r, r', a, b, rfl, ha, hb⟩ := block2_shape h
    have hd := block2_yes h
    simp only [elems_noDigest, List.flatMap_cons, List.flatMap_nil, ha, hb, List.append_nil,
      List.cons_append, List.nil_append, Except.ok.injEq] at hd
    subst hd
    exact ⟨a, b, ha, hb, hout⟩
  enter := fun s pre r y _ hat => by
    match pre, hat with
    | [], ⟨a, ha, h⟩ => rw [ha]; exact h
    | [r₀], ⟨a, b, ha, hb, h⟩ => rw [hb]; exact ⟨a, ha, h⟩
    | _ :: _ :: pre, hat => cases pre <;> exact hat.elim
  leave := fun s pre vals y _ hm => by
    match pre, hm with
    | [], h => exact h
    | [_], h => exact h
    | _ :: _ :: _, h => exact h.elim
  degs := fun s pre vals xs y _ => toy_degs _ s pre vals xs y
  vanish := fun s pre vals xs x y _ hm q hq => by
    match pre, xs, hm with
    | [], [], ⟨h1, h2, _, _⟩ =>
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [eqk_eval]; exact h1
      · rw [List.mem_singleton.1 hq, eqk_eval]; exact h2
    | [r], [], ⟨a, ha, h1, h2⟩ =>
      have hq' : q ∈ [eqk F5 (y.row (rd a)).1 (y.row (rd a)).2, eqk F5 y.g0 y.g1] := by
        simpa [sem, semWith, ha] using hq
      rcases List.mem_cons.1 hq' with rfl | hq'
      · rw [eqk_eval]; exact h1
      · rw [List.mem_singleton.1 hq', eqk_eval]; exact h2
  back := fun s pre vals xs x y _ hm hz => by
    match pre, xs, hm with
    | [], [], ⟨_, _, hg0, hg1⟩ =>
      obtain ⟨a1, a2⟩ := eqk_eq_zero F5 (hz (eqk F5 y.h00 y.h10) (by simp [sem, semWith]))
      obtain ⟨b1, b2⟩ := eqk_eq_zero F5 (hz (eqk F5 y.h01 y.h11) (by simp [sem, semWith]))
      exact ⟨a1, b1, a2, b2, hg0, hg1⟩
    | [r], [], ⟨a, ha, _⟩ =>
      obtain ⟨a1, a2⟩ := eqk_eq_zero F5
        (hz (eqk F5 (y.row (rd a)).1 (y.row (rd a)).2) (by simp [sem, semWith, ha]))
      obtain ⟨b1, b2⟩ := eqk_eq_zero F5 (hz (eqk F5 y.g0 y.g1) (by simp [sem, semWith, ha]))
      exact ⟨a, ha, a1, a2, b1, b2⟩
    | [], _ :: xs, hm => cases xs <;> exact hm.elim
    | [_], _ :: xs, hm => cases xs <;> exact hm.elim

theorem meant_sound : sem.Sound meant 0 := meant_premises.sound

/-- The state from which the toys start. -/
def s0 : Pt := (0, 0)

theorem meant_step (a b : Fmt.Ext) :
    meant.step 0 s0 [rv a, rv b] [] = .ok ((rd a, rd b), 0) := by
  rw [meant, block2_step]; rfl

theorem meant_answers : sem.Answers meant 0 :=
  ⟨s0, [rv (0, 0, 0), rv (0, 0, 0)], [], _, 0, ⟨0, 0, 0, 0, 0, 0⟩, trivial, by decide,
    meant_step _ _, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Data at which the guest's first value is not 0. -/
def yG : Dat := ⟨0, 0, 0, 0, 1, 0⟩

theorem yG_not_zero : ¬ yG.zero := fun h => absurd h.2.2.2.2.1 (by decide)

/-- The toy's filling is worth something. -/
theorem meant_worth : sem.Worth meant 0 :=
  ⟨meant_answers,
    ⟨s0, [rv (0, 0, 0), rv (0, 0, 0)], [], _, 0, yG, trivial, by decide, meant_step _ _,
      yG_not_zero⟩,
    ⟨s0, [rv (0, 0, 0), rv (0, 0, 0)], [], _, 0, ⟨0, 0, 0, 0, 0, 0⟩, trivial, by decide,
      meant_step _ _, by constructor <;> simp [Dat.row]⟩⟩

/-- The stretch that draws 1, then 0, has no bad element at these data: the host's riders are all
the zero polynomial, and the guest's rider, 1 - x, does not vanish at 0. -/
theorem clean_yG (s : Pt) : sem.CleanAt s yG [rv (1, 0, 0), rv (0, 0, 0)] := by
  intro pre r post h xs x ys hx hbad
  obtain ⟨q, hq, hne, hev⟩ := mem_badRiders F5 hbad
  match pre, h with
  | [], h =>
    obtain ⟨rfl, _⟩ := List.cons.inj h
    match xs, hx with
    | [], _ =>
      have hq' : q ∈ [eqk F5 (0 : F5) 0, eqk F5 (0 : F5) 0] := hq
      have : q = eqk F5 (0 : F5) 0 := by simpa using hq'
      exact hne (by rw [this]; simp [eqk])
    | _ :: xs, hx => exact absurd (List.cons.inj hx).2 (by simp)
  | [r₀], h =>
    obtain ⟨rfl, h'⟩ := List.cons.inj h
    obtain ⟨rfl, _⟩ := List.cons.inj h'
    match xs, hx with
    | [], hx =>
      obtain ⟨rfl, _⟩ := List.cons.inj hx
      have hq' : q ∈ [eqk F5 (yG.row (rd (1, 0, 0))).1 (yG.row (rd (1, 0, 0))).2,
        eqk F5 (1 : F5) 0] := hq
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact hne (by simp [eqk, Dat.row, yG])
      · rw [List.mem_singleton.1 hq', eqk_eval] at hev
        exact absurd hev (by decide)
    | _ :: xs, hx => exact absurd (List.cons.inj hx).2 (by simp)
  | _ :: _ :: pre, h =>
    exact absurd (List.cons.inj (List.cons.inj h).2).2 (by simp)

/-- At (1, 1) the host's value and the guest's are 0 at these data. -/
theorem yG_full : yG.full (rd (1, 0, 0)) (rd (1, 0, 0)) := by
  unfold Dat.full Dat.row yG
  decide

/-- **A BLOCK THAT LAYS THE FIRST DRAWN ELEMENT TWICE DOES NOT MEET THE LAW.** -/
theorem twice_not_sound : ¬ sem.Sound twice 0 := by
  rintro ⟨_, h⟩
  have := h s0 [rv (1, 0, 0), rv (0, 0, 0)] [] (rd (1, 0, 0), rd (1, 0, 0)) 0 yG trivial
    (by decide) (by rw [twice, block2_step]; rfl) (clean_yG _) yG_full
  exact yG_not_zero this

/-- **A MEANING THAT FORGETS THE GUEST BEHIND THE FIRST COORDINATE DOES NOT MEET THE PREMISES**: its
`back` fails at the first draw. -/
theorem forgets_not_premises : ¬ semForgets.Premises meant 0 := by
  intro H
  have := H.back s0 [] [] [] (0, 0, 0) yG trivial
    (show (yG.row (rd (0, 0, 0))).1 = 0 ∧ (yG.row (rd (0, 0, 0))).2 = 0 by
      constructor <;> simp [Dat.row, yG])
    (fun q hq => by
      have hq' : q ∈ [eqk F5 (0 : F5) 0, eqk F5 (0 : F5) 0] := hq
      have : q = eqk F5 (0 : F5) 0 := by simpa using hq'
      rw [this]; simp [eqk])
  exact yG_not_zero this

/-- NO TO ALL meets the half on soundness, as every verifier that refuses all does … -/
theorem noToAll_sound : sem.Sound noToAll 0 :=
  ⟨fun s pre vals xs y _ => badRiders_card_le F5 _ _ (toy_degs _ s pre vals xs y),
    fun _ _ _ _ _ _ _ _ h => by cases block2_yes (dec := fun _ _ => .error "no") h⟩

/-- … AND **DOES NOT MEET THE COMPANION.** -/
theorem noToAll_not_answers : ¬ sem.Answers noToAll 0 := by
  rintro ⟨_, _, _, _, _, _, _, _, h, _⟩
  cases block2_yes (dec := fun _ _ => .error "no") h

/-! ### The same host and guest, with both coordinates drawn in ONE round -/

/-- The meaning where one round draws both coordinates: `Mid` stands behind no element, behind the
first, behind both; the second element's riders see the first. -/
def semOne : HearSem F5 Pt Dat :=
  { rd := rd, ready := fun _ => True
    In := fun _ y => y.zero
    Out := fun s y => y.full s.1 s.2
    At := fun _ rs y =>
      match rs with
      | [] => y.zero
      | [r] => ∃ a b, r.drawn.elems = [a, b] ∧ y.full (rd a) (rd b)
      | _ => False
    Mid := fun _ pre _ xs y =>
      match pre, xs with
      | [], [] => y.zero
      | [], [a] => y.half (rd a)
      | [], [a, b] => y.full (rd a) (rd b)
      | _, _ => False
    riders := fun _ pre _ xs y =>
      match pre, xs with
      | [], [] => [eqk F5 y.h00 y.h10, eqk F5 y.h01 y.h11]
      | [], [a] => [eqk F5 (y.row (rd a)).1 (y.row (rd a)).2, eqk F5 y.g0 y.g1]
      | _, _ => []
    deg := fun _ _ => 1 }

/-- A round in which nothing is sent and two elements are drawn. -/
def roundTwo : Fmt.DeclaredRound := { entry := { name := "ZERO", drawE := 2 } }

/-- A block with that one round and a given decision. -/
def block1 (dec : Pt → List Fmt.RoundView → Except String Pt) : Block Pt Bool :=
  { name := "host", place := ⟨1, some 0, 1, .K4⟩, planOk := true, rounds := [roundTwo]
    oracles := [[]], before := [], decide := fun s rs _ => dec s rs, claims := [], after := [] }

/-- THE BLOCK AS IT IS MEANT. -/
def meantOne : Block Pt Bool :=
  block1 fun _ rs =>
    match rs.flatMap (·.drawn.elems) with
    | [a, b] => .ok (rd a, rd b)
    | _ => .error "two elements"

/-- SILLY: it lays the first element drawn twice. -/
def twiceOne : Block Pt Bool :=
  block1 fun _ rs =>
    match rs.flatMap (·.drawn.elems) with
    | [a, _] => .ok (rd a, rd a)
    | _ => .error "two elements"

/-- A round in which nothing is sent and a, then b, are drawn. -/
def rv2 (a b : Fmt.Ext) : Fmt.RoundView := ⟨[], ⟨[a, b], [], [], none⟩⟩

theorem block1_step (dec : Pt → List Fmt.RoundView → Except String Pt) (s : Pt) (a b : Fmt.Ext) :
    (block1 dec).step 0 s [rv2 a b] [] = (dec s [rv2 a b]).map fun s' => (s', 0) := by
  have h1 : roundsFit (block1 dec).rounds [rv2 a b] = true := rfl
  have h2 : groupsOf 0 (block1 dec).rounds ([rv2 a b].map (·.drawn)) = [] := rfl
  have h3 : [rv2 a b].map noDigest = [rv2 a b] := rfl
  rw [Block.step_eq, h1, h2, h3]
  cases h : dec s [rv2 a b] <;>
    simp [block1, h, Except.map, bind, Except.bind, pure, Except.pure]

theorem block1_yes {dec : Pt → List Fmt.RoundView → Except String Pt} {s s' : Pt} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {k : ℕ} (h : (block1 dec).step 0 s rs cols = .ok (s', k)) :
    dec s (rs.map noDigest) = .ok s' := by
  rw [Block.step_eq] at h
  split at h
  · split at h
    · simp only [block1] at h
      cases hd : dec s (rs.map noDigest) with
      | error e => simp [hd, bind, Except.bind] at h
      | ok z =>
        simp only [hd, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [h.1]
    · cases h
  · cases h

/-- A stretch on which such a block says yes: one round, two elements. -/
theorem block1_shape {dec : Pt → List Fmt.RoundView → Except String Pt} {s s' : Pt} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {k : ℕ} (h : (block1 dec).step 0 s rs cols = .ok (s', k)) :
    ∃ r a b, rs = [r] ∧ r.drawn.elems = [a, b] := by
  have hf : roundsFit [roundTwo] rs = true := step_fits h
  have hlen : rs.length = 1 := roundsFit_count _ _ hf
  match rs, hlen with
  | [r], _ =>
    obtain ⟨h1, _⟩ := roundsFit_elems hf
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 h1
    exact ⟨r, a, b, rfl, hab⟩

theorem one_degs (s : Pt) (pre : List Fmt.RoundView) (vals : List Fmt.ItemValue) (xs : List Fmt.Ext) (y : Dat) :
    ∀ q ∈ semOne.riders s pre vals xs y, q.natDegree ≤ 1 := by
  intro q hq
  simp only [semOne] at hq
  split at hq
  · rcases List.mem_cons.1 hq with rfl | hq
    · exact eqk_natDegree_le _ _ _
    · rw [List.mem_singleton.1 hq]; exact eqk_natDegree_le _ _ _
  · rcases List.mem_cons.1 hq with rfl | hq
    · exact eqk_natDegree_le _ _ _
    · rw [List.mem_singleton.1 hq]; exact eqk_natDegree_le _ _ _
  · cases hq

/-- THE MEANT BLOCK MEETS ALL PREMISES OF THE LAW WHERE ONE ROUND DRAWS BOTH COORDINATES. -/
theorem meantOne_premises : semOne.Premises meantOne 0 where
  start := fun _ _ _ h => h
  close := fun s rs cols s' k y _ _ h hout => by
    obtain ⟨r, a, b, rfl, hab⟩ := block1_shape h
    have hd := block1_yes h
    simp only [elems_noDigest, List.flatMap_cons, List.flatMap_nil, hab, List.append_nil,
      Except.ok.injEq] at hd
    subst hd
    exact ⟨a, b, hab, hout⟩
  enter := fun s pre r y _ hat => by
    match pre, hat with
    | [], ⟨a, b, hab, h⟩ => rw [hab]; exact h
    | _ :: pre, hat => cases pre <;> exact hat.elim
  leave := fun s pre vals y _ hm => by
    match pre, hm with
    | [], h => exact h
    | _ :: _, h => exact h.elim
  degs := fun s pre vals xs y _ => one_degs s pre vals xs y
  vanish := fun s pre vals xs x y _ hm q hq => by
    match pre, xs, hm with
    | [], [], ⟨h1, h2, _, _⟩ =>
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [eqk_eval]; exact h1
      · rw [List.mem_singleton.1 hq, eqk_eval]; exact h2
    | [], [a], ⟨h1, h2⟩ =>
      rcases List.mem_cons.1 hq with rfl | hq
      · rw [eqk_eval]; exact h1
      · rw [List.mem_singleton.1 hq, eqk_eval]; exact h2
    | [], _ :: _ :: xs, hm => cases xs <;> exact hm.elim
    | _ :: _, _, hm => exact hm.elim
  back := fun s pre vals xs x y _ hm hz => by
    match pre, xs, hm with
    | [], [], ⟨_, _, hg0, hg1⟩ =>
      obtain ⟨a1, a2⟩ := eqk_eq_zero F5 (hz (eqk F5 y.h00 y.h10) (by simp [semOne]))
      obtain ⟨b1, b2⟩ := eqk_eq_zero F5 (hz (eqk F5 y.h01 y.h11) (by simp [semOne]))
      exact ⟨a1, b1, a2, b2, hg0, hg1⟩
    | [], [a], _ =>
      obtain ⟨a1, a2⟩ := eqk_eq_zero F5
        (hz (eqk F5 (y.row (rd a)).1 (y.row (rd a)).2) (by simp [semOne]))
      obtain ⟨b1, b2⟩ := eqk_eq_zero F5 (hz (eqk F5 y.g0 y.g1) (by simp [semOne]))
      exact ⟨a1, a2, b1, b2⟩
    | [], _ :: _ :: xs, hm => cases xs <;> exact hm.elim
    | _ :: _, _, hm => exact hm.elim

theorem meantOne_sound : semOne.Sound meantOne 0 := meantOne_premises.sound

theorem meantOne_step (a b : Fmt.Ext) :
    meantOne.step 0 s0 [rv2 a b] [] = .ok ((rd a, rd b), 0) := by
  rw [meantOne, block1_step]; rfl

theorem meantOne_worth : semOne.Worth meantOne 0 :=
  ⟨⟨s0, [rv2 (0, 0, 0) (0, 0, 0)], [], _, 0, ⟨0, 0, 0, 0, 0, 0⟩, trivial, by decide,
      meantOne_step _ _, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩,
    ⟨s0, [rv2 (0, 0, 0) (0, 0, 0)], [], _, 0, yG, trivial, by decide, meantOne_step _ _,
      yG_not_zero⟩,
    ⟨s0, [rv2 (0, 0, 0) (0, 0, 0)], [], _, 0, ⟨0, 0, 0, 0, 0, 0⟩, trivial, by decide,
      meantOne_step _ _, by constructor <;> simp [Dat.row]⟩⟩

/-- The round that draws 1, then 0, has no bad element at the data `yG`. -/
theorem cleanOne_yG (s : Pt) : semOne.CleanAt s yG [rv2 (1, 0, 0) (0, 0, 0)] := by
  intro pre r post h xs x ys hx hbad
  obtain ⟨q, hq, hne, hev⟩ := mem_badRiders F5 hbad
  match pre, h with
  | [], h =>
    obtain ⟨rfl, _⟩ := List.cons.inj h
    match xs, hx with
    | [], _ =>
      have hq' : q ∈ [eqk F5 (0 : F5) 0, eqk F5 (0 : F5) 0] := hq
      have : q = eqk F5 (0 : F5) 0 := by simpa using hq'
      exact hne (by rw [this]; simp [eqk])
    | [a], hx =>
      obtain ⟨rfl, hx'⟩ := List.cons.inj hx
      obtain ⟨rfl, _⟩ := List.cons.inj hx'
      have hq' : q ∈ [eqk F5 (yG.row (rd (1, 0, 0))).1 (yG.row (rd (1, 0, 0))).2,
        eqk F5 (1 : F5) 0] := hq
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact hne (by simp [eqk, Dat.row, yG])
      · rw [List.mem_singleton.1 hq', eqk_eval] at hev
        exact absurd hev (by decide)
    | _ :: _ :: xs, hx => exact absurd (List.cons.inj (List.cons.inj hx).2).2 (by simp)
  | _ :: pre, h => exact absurd (List.cons.inj h).2 (by simp)

/-- **THERE TOO A BLOCK THAT LAYS THE FIRST DRAWN ELEMENT TWICE DOES NOT MEET THE LAW.** -/
theorem twiceOne_not_sound : ¬ semOne.Sound twiceOne 0 := by
  rintro ⟨_, h⟩
  have := h s0 [rv2 (1, 0, 0) (0, 0, 0)] [] (rd (1, 0, 0), rd (1, 0, 0)) 0 yG trivial
    (by decide) (by rw [twiceOne, block1_step]; rfl) (cleanOne_yG _) yG_full
  exact yG_not_zero this

end RiderToy

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.HearSem.Premises.alongElems
#print axioms VerifiableInference.Desc.HearSem.Premises.along
#print axioms VerifiableInference.Desc.HearSem.Premises.sound
#print axioms VerifiableInference.Desc.roundsFit_count
#print axioms VerifiableInference.Desc.step_fits
#print axioms VerifiableInference.Desc.roundsFit_elems
#print axioms VerifiableInference.Desc.RiderToy.block2_step
#print axioms VerifiableInference.Desc.RiderToy.block2_yes
#print axioms VerifiableInference.Desc.RiderToy.block2_shape
#print axioms VerifiableInference.Desc.RiderToy.toy_degs
#print axioms VerifiableInference.Desc.RiderToy.meant_premises
#print axioms VerifiableInference.Desc.RiderToy.meant_sound
#print axioms VerifiableInference.Desc.RiderToy.meant_step
#print axioms VerifiableInference.Desc.RiderToy.meant_answers
#print axioms VerifiableInference.Desc.RiderToy.yG_not_zero
#print axioms VerifiableInference.Desc.RiderToy.meant_worth
#print axioms VerifiableInference.Desc.RiderToy.clean_yG
#print axioms VerifiableInference.Desc.RiderToy.yG_full
#print axioms VerifiableInference.Desc.RiderToy.twice_not_sound
#print axioms VerifiableInference.Desc.RiderToy.forgets_not_premises
#print axioms VerifiableInference.Desc.RiderToy.noToAll_sound
#print axioms VerifiableInference.Desc.RiderToy.noToAll_not_answers
#print axioms VerifiableInference.Desc.RiderToy.block1_step
#print axioms VerifiableInference.Desc.RiderToy.block1_yes
#print axioms VerifiableInference.Desc.RiderToy.block1_shape
#print axioms VerifiableInference.Desc.RiderToy.one_degs
#print axioms VerifiableInference.Desc.RiderToy.meantOne_premises
#print axioms VerifiableInference.Desc.RiderToy.meantOne_sound
#print axioms VerifiableInference.Desc.RiderToy.meantOne_step
#print axioms VerifiableInference.Desc.RiderToy.meantOne_worth
#print axioms VerifiableInference.Desc.RiderToy.cleanOne_yG
#print axioms VerifiableInference.Desc.RiderToy.twiceOne_not_sound
