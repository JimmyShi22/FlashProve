-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Rider/ForB.lean: a second zero test on the challenges of the lookup of a
sub-proof: the bundle for the term `forB`, and the rule at `KnowAt`.

Definitions, statements and proofs. No protocol of its own: the reduction, its counts, its two
joints and its extractor are those of OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean, taken as they stand.

The term is `Cb.Fo.forB E h L V₀ V₀C`: the draw of the shift if the forest has several calls, then
the whole chain of the lookup at the letters `forA E h L`, over the named short sumcheck. The
explicit part x of its output statement holds the caller's state (`x.1.1`), the shift (`x.1.2`) and
the claim on the keys (`x.2.1`), whose point `x.2.1.pt` has v' + 1 places, v' = `FoNums.v' h`. Place
0 belongs to the top bit of a key's number. In the theorems b is the whole output statement
(explicit part, oracles): there these are `b.1.1.1`, `b.1.1.2`, `b.1.2.1`. Two numberings occur: the
names k that the rounds bind (k is coordinate k of the point that the last key level hands down) and
the places of pt; the name k stands at place v' - k.

Main names:
  `lkKB`, `lkK_carries`, `lkK_passes`: the shift's round binds nothing; a bundle `Carries`
    (Cb/G6/Rider/Carrier.lean) of the block behind it is a bundle of the two; so for the state.
  `forBB`, `forB_carries`: the bundle for forB. By forBB's definition only the rounds of the last
    key level bind (`forBB_vars`: the list of the names bound is that level's); whatever the
    verifier outputs, `pt (v' - k)` is the challenge bound to the name k ≤ v'; the rider's list lies
    below forB's own list of counts. No premise on h.
  `forB_passes`: whatever the verifier outputs holds the caller's state.
  `forB_ride`: the rule, for any two joints between which forB has `KnowAt`, with any extractor; it
    applies to its own result. The same reduction, extractor and counts, from (the joint before and
    "every array of the family is 0 on its cube") to (the joint behind and "the multilinear
    extension of every array is 0 at its chosen places of pt"). The arrays read the caller's state
    and the tuple of messages. The family, each member's cube and each member's choice are free; a
    choice is any list of different places among 0, .., v', place 0 (the line's challenge) among
    them.
  `forB_rider`: the rule at the block's own joints `forIn`, `forOut`; the block's knowledge
    soundness is a premise, used as a black box. `forB_rider₀`, `forB_rider_gl`: the premise filled
    by `holeC₀`, `holeCgl` (OnBytes/Tie/Pv/Lookup/Forest/FoAt.lean).
  `forIn_in`, `forB_rider_in`, `forB_rider_in_gl`: the source laid inside R0 at the input alone.
  `forB_rider_know`: that form with round-by-round knowledge soundness alone as premise and
    conclusion.
  `forB_hollow`, `forB_hollow_R0`: empty uses.

The rider is an outer clause of the two joints (`withRider`, Cb/G6/Rider/Both.lean). It is no part
of the relation R0 that rides along: R0 is read at the caller's state, before the shift's draw.

An empty use. R0 is a free letter, and the out-joint hands R0 out as it came in. If R0 gives the
source on both sides, or the in-joint's own claim ("each call's keys lie in that call's table")
gives it, the statement with the rider follows from the premise alone, for any choice, and says
nothing (`forB_hollow`, `forB_hollow_R0`). A use should prove two sentences: (i) at a statement
with the condition `on`, the in-joint's relaxed relation without the rider holds and the source
fails; (ii) from that statement the verifier puts out a statement at which the whole out-joint with
the rider holds. Both sentences are owed at this term: neither is proved here for any value of h, L,
R0.

`forB_rider_in` is `forB_rider` with the conjunction at the input bracketed anew. It guards against
one trap alone: that the source comes out again inside R0. At the same R0 it is as safe as
`forB_rider`, and no safer.

Limits: the arrays read the caller's state and the tuple of messages alone: not the shift, no later
challenge, no message of the block's own transcript, nothing that an extractor makes: by type.
`KnowAt` speaks for each fixed tuple of messages. It is on a use that the parts of the tuple which
its arrays read are sent before the lookup's first challenge: for a part that is sent later the
statement is true and of no worth. Nothing on whether a later stage takes the target up; nothing on
an honest prover; nothing on the lookups of the key file, which are another term. Nothing here is
computed by a verifier.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.Tie.Pv.Lookup.Forest.FoAt
import Cb.G6.Rider.LookupK
import Cb.G6.Rider.UsesK

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks Cb.LdLkp Cb.LdLkp.Kn TWhole Cb.Fo

/-! ## 1. The shift before a block -/

section Shift
variable {E St J Xo : Type} [Field E] [Fintype E] {Ex : ExtSpec} (P : ShiftQ E St (J → E))

/-- The shift's round, if there is one, binds nothing; the block behind it binds by β. -/
noncomputable def lkKB : (several : Bool) → (b : BkK (St × E) Xo Ex) → Binds ℕ E b.R.shape →
    Binds ℕ E (P.lkK several b).R.shape
  | true, b, β => Binds.app (s := (P.bkK Ex).R.shape) (t := b.R.shape) (idle _) β
  | false, _, β => β

theorem lkK_carries : ∀ (several : Bool) (b : BkK (St × E) Xo Ex) {β : Binds ℕ E b.R.shape}
    {T : ℕ → Prop} {r : Xo → ℕ → E}, Carries b.R β b.e T r →
    Carries (P.lkK several b).R (lkKB P several b β) (P.lkK several b).e T r
  | true, _, _, _, _, C => Carries.seqR (P.bkK Ex).R (P.bkK Ex).e C
  | false, _, _, _, _, C => C.pre _ _

theorem lkKB_vars : ∀ (several : Bool) (b : BkK (St × E) Xo Ex) (β : Binds ℕ E b.R.shape),
    (lkKB P several b β).vars = β.vars
  | true, b, β => by
    refine (Binds.vars_app (s := (P.bkK Ex).R.shape) (t := b.R.shape) (idle _) β).trans ?_
    rw [idle_vars]
    rfl
  | false, _, _ => rfl

/-- What the block behind the shift hands on of the caller's state, the two hand on. -/
theorem lkK_passes {Rc : Type} (r : St → Rc) : ∀ (several : Bool) (b : BkK (St × E) Xo Ex)
    {r' : Xo → Rc}, b.R.Passes (fun x => r x.1) r' → (P.lkK several b).R.Passes r r'
  | true, _, _, hp => (IOR.Passes.draw E Prod.mk Ex r (fun x => r x.1) fun _ _ => rfl).seq hp
  | false, _, _, hp => hp.pre _ _ fun x x' e => by
      obtain rfl := Option.some.inj e
      rfl

end Shift

/-! ## 2. The bundle for the lookup of a sub-proof -/

section For
variable (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  (h : Sh) (L : Lay E St₀ J₀) (Ex : ExtSpec)

/-- The Binds of forB, along its own make: the shift's round binds nothing; in the chain only the
last key level binds. -/
noncomputable def forBB : Binds ℕ E (forB E h L V₀ V₀C (Ex := Ex)).R.shape :=
  lkKB (forP E h L) (FoNums.several h) ((forA E h L).baseK V₀ V₀C)
    (chnKB (letterCar₀ E Ex) (forA E h L))

/-- The bundle for forB. The name k ≤ v' stands at place v' - k of the point in the output
statement's claim on the keys. No premise on h. -/
theorem forB_carries :
    Carries (forB E h L V₀ V₀C (Ex := Ex)).R (forBB E h L Ex) (forB E h L V₀ V₀C (Ex := Ex)).e
      (fun k => k ≤ FoNums.v' h) (fun b k => b.2.1.pt (FoNums.v' h - k)) :=
  lkK_carries (forP E h L) (FoNums.several h) _ (baseK₀_carries (forA E h L))

/-- The names that forB's rounds bind are those that the last key level's rounds bind. -/
theorem forBB_vars : (forBB E h L Ex).vars =
    (levKB (letterCar₀ E Ex) (DKh (forA E h L)) (FoNums.v' h)).vars :=
  (lkKB_vars _ _ _ _).trans (chnKB_vars _ _)

/-- Whatever forB's verifier outputs holds the caller's state. -/
theorem forB_passes :
    (forB E h L V₀ V₀C (Ex := Ex)).R.Passes (fun st : St₀ => st) fun b => b.1.1 :=
  lkK_passes (forP E h L) (fun st : St₀ => st) (FoNums.several h) _
    (passes_map (baseK₀_passes (forA E h L)) Prod.fst)

end For

/-! ## 3. The rule -/

section Rule
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  {h : Sh} {L : Lay E St₀ J₀} {Ex : ExtSpec} {Kc M Wp : Type}

/-- forB has the rule, between any two joints between which it has KnowAt, with any extractor. -/
theorem forB_rides {JA : IOR.Rels Kc St₀ Ex (M × Wp)}
    {JB : IOR.Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp)}
    {xt : M → St₀ × Ex.Str → Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape → Wp → Wp}
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R JA JB xt (forB E h L V₀ V₀C (Ex := Ex)).e) :
    RidesAt (forB E h L V₀ V₀C (Ex := Ex)).R JA JB xt (forB E h L V₀ V₀C (Ex := Ex)).e
      (FoNums.v' h) (fun st : St₀ => st) (fun b => b.1.1) (fun b => b.2.1.pt) :=
  ridesAt_of_carries (forB_carries E h L Ex) (forB_passes E h L Ex) hK

/-- The rule at forB, for any two joints between which it has KnowAt; it applies to its own result.
The same reduction, extractor and counts. Source: every f i is 0 at every vertex of its cube, of
dimension g i. Target: the multilinear extension of every f i is 0 at the places sel i 0, .., sel i
(g i - 1) of the point pt of the claim on the keys in the output statement. ι is free; cube and
choice are per member; sel i is any injection into 0, .., v'; place 0, the line's challenge, is
allowed. The arrays read the caller's state and the tuple of messages alone. Warning:
JA and JB are free. Wherever JA's relaxed relation or JB's already gives the source, this says
nothing (knowAt_hollow_own, knowAt_hollow_out, Cb/G6/Rider/KnowAt.lean). -/
theorem forB_ride {JA : IOR.Rels Kc St₀ Ex (M × Wp)}
    {JB : IOR.Rels Kc (TX (St₀ × E) E (Option J₀)) Ex (M × Wp)}
    {xt : M → St₀ × Ex.Str → Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape → Wp → Wp}
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R JA JB xt (forB E h L V₀ V₀C (Ex := Ex)).e)
    {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ) (hsel : SelIn (FoNums.v' h) g sel)
    (f : ι → St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider JA fun m a => OnCubes g f a.1 m)
      (withRider JB fun m b => AtCoords g sel f b.1.1.1 b.1.2.1.pt m) xt
      (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forB_rides hK ι g sel hsel f

variable {R0 : IOR.Rels Kc St₀ Ex (M × Wp)} {msg₀ : M → J₀ → E}

/-- The rule at the block's own joints. hK, the block's own knowledge soundness, is a premise and is
used as a black box. Both clauses are outer clauses; R0 is not touched. Warning: R0 is free and
comes out as it went in. Where R0, or the in-joint's own claim, gives the source, this says nothing
(forB_hollow); the two sentences of the head are owed by a use. -/
theorem forB_rider
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ) (hsel : SelIn (FoNums.v' h) g sel)
    (f : ι → St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a => OnCubes g f a.1 m)
      (withRider (forOut E h L R0 msg₀) fun m b => AtCoords g sel f b.1.1.1 b.1.2.1.pt m)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forB_ride hK g sel hsel f

omit [Fintype E] [Fintype J₀] [DecidableEq J₀] in
/-- A clause beside the in-joint may be laid inside the relation R0 that rides along, at the input
alone: the conjunction is bracketed anew; whatever stands behind the block stays. By this each
statement with a rider beside forIn gets the form in which the source comes in inside R0. -/
theorem forIn_in {Xo : Type} {R : IOR St₀ Ex Xo Ex} {S : M → St₀ × Ex.Str → Prop}
    {B : IOR.Rels Kc Xo Ex (M × Wp)} {xt : M → St₀ × Ex.Str → Tr R.shape → Wp → Wp}
    {ε : Err R.shape} (G : KnowAt R (withRider (forIn E h L R0 msg₀) S) B xt ε) :
    KnowAt R (forIn E h L (withRider R0 S) msg₀) B xt ε :=
  ⟨G.point, G.isLocal, G.onOut, fun m a ha =>
    Doomed.mono _ _ (fun _ hτ b w hb hw =>
      ⟨⟨(hτ b w hb hw).1.1, (hτ b w hb hw).2⟩, (hτ b w hb hw).1.2⟩) (G.know m a ha)⟩

/-- The source laid inside R0 at the input alone: the out-joint rides over R0 without it and has the
target. It is forB_rider with the conjunction bracketed anew: it guards against the source coming
out again inside R0, and against nothing else: if R0 itself, or the in-joint's own claim, gives the
source, it says nothing. -/
theorem forB_rider_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ) (hsel : SelIn (FoNums.v' h) g sel)
    (f : ι → St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b => AtCoords g sel f b.1.1.1 b.1.2.1.pt m)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (forB_rider hK g sel hsel f)

/-- The form of forB_rider_in with round-by-round knowledge soundness alone as premise and
conclusion: for a statement in which the block's knowledge soundness is a hypothesis by itself,
apart from the three facts on the verifier. Warning: R0 is free, as in forB_rider. -/
theorem forB_rider_know
    (hK : ∀ m, (forB E h L V₀ V₀C (Ex := Ex)).R.red.Know (forIn E h L R0 msg₀).on
      (fun a wp => (forIn E h L R0 msg₀).relR a (m, wp))
      (fun b wp => (forOut E h L R0 msg₀).relR b (m, wp)) (fun _ _ wp => wp)
      (forB E h L V₀ V₀C (Ex := Ex)).e)
    {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ) (hsel : SelIn (FoNums.v' h) g sel)
    (f : ι → St₀ → M → ℕ → E) (m : M) :
    (forB E h L V₀ V₀C (Ex := Ex)).R.red.Know
      (forIn E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀).on
      (fun a wp => (forIn E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀).relR a (m, wp))
      (fun b wp => (withRider (forOut E h L R0 msg₀)
        fun m b => AtCoords g sel f b.1.1.1 b.1.2.1.pt m).relR b (m, wp))
      (fun _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  (know_of_carries (xt := fun _ _ _ wp => wp) (forB_carries E h L Ex) (forB_passes E h L Ex) hK g
    sel hsel f m).conseq (fun _ ha => ha) (fun _ _ _ hw => ⟨⟨hw.1.1, hw.2⟩, hw.1.2⟩)
    (fun _ _ hw => hw)

/-- An empty use. If the in-joint's relaxed relation gives the source at the statements with the
condition on, the statement with the rider holds whatever the target says: SB is any clause. -/
theorem forB_hollow
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {ι : Type} (g : ι → ℕ) (f : ι → St₀ → M → ℕ → E)
    (SB : M → TX (St₀ × E) E (Option J₀) × Ex.Str → Prop)
    (h0 : ∀ a w, (forIn E h L R0 msg₀).on a → (forIn E h L R0 msg₀).relR a w →
      OnCubes g f a.1 w.1) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a => OnCubes g f a.1 m)
      (withRider (forOut E h L R0 msg₀) SB) (fun _ _ _ wp => wp)
      (forB E h L V₀ V₀C (Ex := Ex)).e :=
  knowAt_hollow_own hK _ SB h0

/-- An empty use, at the natural mistake. With the source inside R0 on both sides, the conclusion of
forB_rider follows from the block's own knowledge soundness alone, for any choice sel (the places
need not be different, nor in range): the in-joint gives the source, and the out-joint still holds
it. -/
theorem forB_hollow_R0 {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ) (f : ι → St₀ → M → ℕ → E)
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀)
      (forOut E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀)
        fun m a => OnCubes g f a.1 m)
      (withRider (forOut E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀)
        fun m b => AtCoords g sel f b.1.1.1 b.1.2.1.pt m)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forB_hollow hK g f _ fun _ _ _ hw => hw.1.2

/-- The rule, the block's knowledge soundness taken from holeC₀. -/
theorem forB_rider₀ (p : ℕ) [CharP E p] (H : FoNums.ok h = true)
    (hp : 2 ^ h.d * (2 ^ 32 - 1) < p) {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ)
    (hsel : SelIn (FoNums.v' h) g sel) (f : ι → St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a => OnCubes g f a.1 m)
      (withRider (forOut E h L R0 msg₀) fun m b => AtCoords g sel f b.1.1.1 b.1.2.1.pt m)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forB_rider (holeC₀ E p St₀ J₀ h L Ex Kc M Wp R0 msg₀ H hp) g sel hsel f

end Rule

/-! ## 4. At the challenge field -/

section Gl
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh) (L : Lay Cb.Gl.E St₀ J₀)
  (Ex : ExtSpec) (Kc M Wp : Type) (R0 : IOR.Rels Kc St₀ Ex (M × Wp)) (msg₀ : M → J₀ → Cb.Gl.E)

/-- The rule at the challenge field, from holeCgl: the one premise left is the test on the forest's
public numbers. Warning: R0 is free, as in forB_rider. -/
theorem forB_rider_gl (H : FoNums.ok h = true) {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ)
    (hsel : SelIn (FoNums.v' h) g sel) (f : ι → St₀ → M → ℕ → Cb.Gl.E) :
    KnowAt (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn Cb.Gl.E h L R0 msg₀) fun m a => OnCubes g f a.1 m)
      (withRider (forOut Cb.Gl.E h L R0 msg₀) fun m b => AtCoords g sel f b.1.1.1 b.1.2.1.pt m)
      (fun _ _ _ wp => wp) (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e :=
  forB_rider (holeCgl St₀ J₀ h L Ex Kc M Wp R0 msg₀ H) g sel hsel f

/-- The source laid inside R0 at the input alone, at the challenge field. -/
theorem forB_rider_in_gl (H : FoNums.ok h = true) {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ)
    (hsel : SelIn (FoNums.v' h) g sel) (f : ι → St₀ → M → ℕ → Cb.Gl.E) :
    KnowAt (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R
      (forIn Cb.Gl.E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀)
      (withRider (forOut Cb.Gl.E h L R0 msg₀) fun m b => AtCoords g sel f b.1.1.1 b.1.2.1.pt m)
      (fun _ _ _ wp => wp) (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e :=
  forB_rider_in (holeCgl St₀ J₀ h L Ex Kc M Wp R0 msg₀ H) g sel hsel f

end Gl

end Cb.Rider

#print axioms Cb.Rider.forB_carries
#print axioms Cb.Rider.forBB_vars
#print axioms Cb.Rider.forB_passes
#print axioms Cb.Rider.forB_ride
#print axioms Cb.Rider.forB_rider
#print axioms Cb.Rider.forIn_in
#print axioms Cb.Rider.forB_rider_in
#print axioms Cb.Rider.forB_rider_know
#print axioms Cb.Rider.forB_hollow
#print axioms Cb.Rider.forB_hollow_R0
#print axioms Cb.Rider.forB_rider₀
#print axioms Cb.Rider.forB_rider_gl
#print axioms Cb.Rider.forB_rider_in_gl
