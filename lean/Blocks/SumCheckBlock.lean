-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/SumCheckBlock.lean: the masked sumcheck as a block, with soundness, completeness and masked
form (`Hon.Masked`, Blocks/BlockHon.lean).

The claim is that an affine form in the committed entries (Blocks/RelForm.lean) has as its value the
weighted sum of a polynomial Φ over the Boolean hypercube. In the round that binds the variable i
the prover sends e i + 1 scalars, each masked by a pad (a uniform field element added to it); with
the round's equation Λ_i(ĝ_i) = val(f), f the running form, they determine the round polynomial ĝ_i,
of degree at most e i + 1. The verifier sends ζ_i, checks no equation, and computes the next running
form ĝ_i(ζ_i) (`SC.nextForm`). The format `SC` fixes the weights (for instance all 1, or those of a
factor eq(ϱ, ·)), which scalars are sent, and which pads mask them (words of this library:
lean/GLOSSARY.md).

Main results, for a block in the sense of Blocks/Block.lean:
  `SC.clean_sc`: soundness (`Block.Clean`) from the running claim `SC.Rsum` before the rounds to the
      one after them, with at most e i + 1 bad values of ζ_i. Once all variables are bound this is
      the end claim `SC.Reval`: the end form has the value of Φ at the point of the challenges. It
      assumes `SC.OK`, above all that Φ has degree at most e i + 1 in the variable i.
  `SC.Prover.accOn_sc`: completeness, for all pads and at every challenge outside the withheld set
      (`Hon.withheld`, Blocks/BlockHon.lean). Among the hypotheses: 0, ..., e i + 1 are distinct in
      E, and the statement has the prover's weights and pads.
  `SC.Prover.masked_sc_on`: if no pad is used twice and no variable is bound twice, and outside the
      withheld set: Each scalar is a value plus a pad of its own, the values read no pad, so the
      plain parts are uniform.

With a factor eq(ϱ, ·) a round divides by ϱ_i. So the relations assume that no weight by which a
later round divides is 0, and the flag `SC.nzv` marks the variables by whose challenge a later block
divides: there the verifier rejects the challenge 0, which is in the withheld set, and the later
relations may assume that the challenge is not 0.

Notation: `sumOutL`: sums out the variables of a list, each variable v with its weights wt v;
`BadRound`: the challenge r of the round that binds i is bad: the running claim c before the round
is false, and the running claim next r after it is true; `node e`: the nodes 0, 1, ..., e + 1 as
elements of the field (these: Alg/SumCheck.lean); `Rho`: the verifier's randomness of a whole
execution; `Plains`: the plain parts of all prover messages (Iop/Shape.lean); in
`Hon.Masked V U D Sim` (Blocks/BlockHon.lean) V is validity of the honest state; for U, D see that
record.
Limits: `Rsum` and `Reval` assume that no stored challenge at a flagged variable outside the list of
unbound variables is 0. If a variable that is never bound is flagged and the start point is 0 there,
both relations hold vacuously and the honest relation `Hsum` is false. Nothing in this file forbids
such a format; a caller could prove neither its backward nor its forward step with it.
Sources: the block follows the masked sumcheck of a write-up of ours (lean/CREDITS.md). The sumcheck
goes back to (LFKN92). To mask each scalar by a pad out of a vector that was sent before is as in
(DHRR26) and (FS24). Not to send the scalar that the round's equation fixes, and to keep a factor
eq(ϱ, ·) in the round's equation, is as in (Gru24).
-/
import Blocks.BlockLib
import Blocks.RelForm
import Alg.SumCheck
import Alg.RoundValues
import Alg.RoundBasis
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob Alg

/-- The format of a masked sumcheck: the data of the protocol. ι is the set of variables, Ξ the type
of the public data on which the weights and the polynomial may depend (for instance the point ϱ of
an equality factor), Y the type of implicit parts, P the set of pads. The true polynomial Φ : Ξ → Y
→ (ι → E) → E is not part of the format: the verifier never computes it. It is an argument of the
relations (`Rsum`, `Reval`) and of `OK`. So a block names only what the protocol uses, and an object
of a relation (which may be defined by a case distinction that no program decides) does not occur in
a scheme's definition. -/
structure SC (E Y P Ξ ι : Type) [Field E] where
  forms : Forms E Y P
  /-- the weights of the round's equation: Λ_i(q) = wt ξ i false · q(0) + wt ξ i true · q(1) -/
  wt : Ξ → ι → Bool → E
  /-- the round that binds the variable i has e i + 1 masked scalars -/
  e : ι → ℕ
  /-- their pads -/
  idx : (i : ι) → Fin (e i + 1) → P
  /-- does a later block divide by the challenge of the round that binds i? Then the verifier
  rejects if that challenge is 0 -/
  nzv : ι → Bool
  /-- in which scalars the polynomial of the round that binds i is sent (Alg/RoundBasis.lean). By
  default the value at 0 and the coefficients of X², ..., X^(e i + 1) -/
  bas : (i : ι) → Basis E (e i) := fun i => Basis.coeff E (e i)

namespace SC

variable {E Y P Ξ ι : Type} [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] (S : SC E Y P Ξ ι)

/-- What the format and the true polynomial have to satisfy for soundness: the constant form has the
value 1; Φ has degree at most e i + 1 in the variable i; and whatever scalars are sent in a round,
they and the round's equation determine a polynomial of degree at most e i + 1, if the weight by
which the round divides is not 0. For the default scalars the last clause holds in every field, and
its proof is filled in. -/
structure OK (Φ : Ξ → Y → (ι → E) → E) : Prop where
  forms : S.forms.OK
  deg : ∀ ξ y, DegLE (fun i => S.e i + 1) (Φ ξ y)
  bas : ∀ ξ i, S.wt ξ i true ≠ 0 → (S.bas i).Sound (S.wt ξ i) := by
    exact fun _ _ h => Alg.Basis.sound_coeff h

/-- The explicit part of a statement: the running form, the point so far (each challenge is at the
coordinate of its variable), the public data. -/
abbrev X : Type := S.forms.Fm × (ι → E) × Ξ

/-- The round that binds the variable i: e i + 1 scalars, then a challenge in E. -/
abbrev rd (i : ι) : Round :=
  vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) (Fin (S.e i + 1)) E

/-- The next running form f_i = ĝ_i(ζ_i): a combination of the running form and of the forms of the
masked scalars, with coefficients that the verifier computes from the challenge and the weights. -/
def nextForm (i : ι) (ξ : Ξ) (f : S.forms.Fm) (m : Fin (S.e i + 1) → E) (r : E) :
    S.forms.Fm :=
  (S.bas i).cClaim (S.wt ξ i) r • f +
    ∑ j, (S.bas i).cMsg (S.wt ξ i) r j • S.forms.scalar (m j) (S.idx i j)

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
/-- Under `Forms.OK`: the value of the next running form is the verifier's recurrence on the values.
-/
theorem val_nextForm (h : S.forms.OK) (y : Y) (i : ι) (ξ : Ξ) (f : S.forms.Fm)
    (m : Fin (S.e i + 1) → E) (r : E) :
    S.forms.val y (S.nextForm i ξ f m r) =
      (S.bas i).next (S.wt ξ i) (S.forms.val y f)
        (fun j => m j - S.forms.val y (S.forms.pad (S.idx i j))) r := by
  unfold nextForm Basis.next
  simp only [map_add, map_smul, map_sum, smul_eq_mul, S.forms.val_scalar h]

/-- What the verifier computes in the round that binds i. It tests no equation: it computes the next
running form and stores the challenge. It rejects on its own randomness only: if a later block
divides by the challenge and the challenge is 0. -/
def pb (i : ι) (x : S.X) (r : E) (m : Fin (S.e i + 1) → E) : Option S.X :=
  if S.nzv i = true ∧ r = 0 then none
  else some (S.nextForm i x.2.2 x.1 m r, Function.update x.2.1 i r, x.2.2)

/-- One round. -/
@[reducible] def round (i : ι) : Block S.X Y S.X Y :=
  Block.one (S.rd i) (S.pb i) (fun y _ _ => y)

/-- The masked sumcheck that binds the variables of the list, in this order. -/
def sc : List ι → Block S.X Y S.X Y
  | [] => Block.pure some id
  | i :: l => (S.round i).seq (sc l)

/-- Its errors: e i + 1 bad values in the round that binds i. -/
def scErr : (l : List ι) → Err (S.sc l).shape
  | [] => ()
  | i :: l => Err.app (s := (S.round i).shape) (S.e i + 1, ()) (scErr l)

/-- The challenges that are stored already (those of the variables outside l) and by which a later
block divides are not 0. -/
def NZ (l : List ι) (z : ι → E) : Prop := ∀ v, S.nzv v = true → v ∉ l → z v ≠ 0

variable {Φ : Ξ → Y → (ι → E) → E}

variable (Φ) in
/-- The running claim when the variables of the list l are not yet bound: the value of the running
form is the weighted sum of the true polynomial over these variables, at the point so far. It has
two premises: no weight by which a round of l divides is 0; and no stored challenge by which a later
block divides is 0. -/
def Rsum (l : List ι) (x : S.X) (y : Y) : Prop :=
  (∀ v ∈ l, S.wt x.2.2 v true ≠ 0) → S.NZ l x.2.1 →
  S.forms.val y x.1 = sumOutL (S.wt x.2.2) l (Φ x.2.2 y) x.2.1

variable (Φ) in
/-- The end claim: the value of the end form is the true polynomial at the end point. The premise:
no coordinate of the end point by which a later block divides is 0. -/
def Reval (x : S.X) (y : Y) : Prop :=
  (∀ v, S.nzv v = true → x.2.1 v ≠ 0) → S.forms.val y x.1 = Φ x.2.2 y x.2.1

omit [Fintype E] [DecidableEq E] in
theorem rsum_nil (x : S.X) (y : Y) : S.Rsum Φ [] x y ↔ S.Reval Φ x y :=
  ⟨fun h hz => h (fun _ hv => absurd hv List.not_mem_nil) fun v hv _ => hz v hv,
    fun h _ hz => h fun v hv => hz v hv List.not_mem_nil⟩

/-! ## Soundness -/

variable (Φ) in
/-- The bad values of the challenge of the round that binds i, when the variables of l are bound
later. -/
def badSet (i : ι) (l : List ι) (x : S.X) (y : Y) (m : (S.rd i).Msg) : Set E :=
  {r | S.wt x.2.2 i true ≠ 0 ∧
    BadRound (S.wt x.2.2) (Φ x.2.2 y) i l x.2.1 (S.forms.val y x.1)
      ((S.bas i).next (S.wt x.2.2 i) (S.forms.val y x.1) fun j =>
        m.2 j - S.forms.val y (S.forms.pad (S.idx i j))) r}

omit [Fintype E] [DecidableEq E] in
/-- After a round whose challenge has passed the verifier's test, the stored challenges by which a
later block divides are still not 0. -/
theorem NZ.update {i : ι} {l : List ι} {z : ι → E} (h : S.NZ (i :: l) z)
    {r : E} (hr : ¬ (S.nzv i = true ∧ r = 0)) :
    S.NZ l (Function.update z i r) := by
  intro v hv hvl
  by_cases hvi : v = i
  · subst hvi
    rw [Function.update_self]
    exact fun h0 => hr ⟨hv, h0⟩
  · rw [Function.update_of_ne hvi]
    exact h v hv fun hm => (List.mem_cons.1 hm).elim hvi hvl

/-- Under `SC.OK`: soundness of one round. A value of the challenge is bad if the weight by which
the round divides is not 0, the equation of the running claim before the round is false and that of
the running claim after it is true. There are at most e i + 1 bad values. -/
theorem clean_round (h : S.OK Φ) (i : ι) (l : List ι) :
    (S.round i).Clean (S.Rsum Φ (i :: l)) (S.Rsum Φ l) (S.e i + 1, ()) := by
  refine Block.clean_one (r := S.rd i) (S.badSet Φ i l) (S.e i + 1)
    (fun x y m => ?_) fun x y m c xo hc hxo hRo hnz hz => ?_
  · exact Basis.count_bad_le (h.deg x.2.2 y) (S.wt x.2.2) i l x.2.1 le_rfl
      (S.bas i) (h.bas x.2.2 i) _ _
  · have hxo' : S.pb i x c m.2 = some xo := hxo
    unfold pb at hxo'
    by_cases hr : S.nzv i = true ∧ c = 0
    · rw [if_pos hr] at hxo'
      exact absurd hxo' (by simp)
    · rw [if_neg hr] at hxo'
      obtain rfl := Option.some.inj hxo'
      have h2 : S.forms.val y (S.nextForm i x.2.2 x.1 m.2 c) =
          sumOutL (S.wt x.2.2) l (Φ x.2.2 y) (Function.update x.2.1 i c) :=
        hRo (fun v hv => hnz v (List.mem_cons_of_mem _ hv)) (hz.update S hr)
      rw [S.val_nextForm h.forms] at h2
      by_contra hne
      exact hc ⟨hnz i List.mem_cons_self, hne, h2⟩

/-- Under `SC.OK`: soundness of the masked sumcheck, from the running claim with the variables l ++
l' unbound to that with l' unbound. -/
theorem clean_sc (h : S.OK Φ) :
    ∀ l l' : List ι, (S.sc l).Clean (S.Rsum Φ (l ++ l')) (S.Rsum Φ l') (S.scErr l)
  | [], _ => Block.clean_pure_iff.2 fun x y xo hxo hR => by
      rw [Option.some.inj hxo]
      exact hR
  | i :: l, l' => (S.clean_round h i (l ++ l')).comp (clean_sc h l l')

/-- Under `SC.OK`, when all variables of the list are bound: soundness from the start claim to the
end claim. -/
theorem clean_sc_eval (h : S.OK Φ) (l : List ι) :
    (S.sc l).Clean (S.Rsum Φ l) (S.Reval Φ) (S.scErr l) := by
  have h1 := S.clean_sc h l []
  rw [List.append_nil] at h1
  exact h1.conseq (fun _ _ hx => hx) fun x y hx => (S.rsum_nil x y).2 hx

/-! ## The start claim in its two forms -/

section Start

variable [Fintype ι]

omit [Fintype E] [DecidableEq E] in
/-- Plain form: if all weights are 1 and the list holds every variable once, the start claim says
that the value of the start form is the sum of Φ over the hypercube. -/
theorem rsum_plain (hw : ∀ ξ, S.wt ξ = plainW) {l : List ι} (hl : l.Nodup)
    (hall : ∀ v, v ∈ l) (x : S.X) (y : Y) :
    S.Rsum Φ l x y ↔ S.forms.val y x.1 = ∑ b : ι → Bool, Φ x.2.2 y (corner b) := by
  unfold Rsum
  rw [hw, sumOutL_plain l hl hall]
  exact ⟨fun h => h (fun _ _ => one_ne_zero) fun v _ hv => absurd (hall v) hv, fun h _ _ => h⟩

omit [Fintype E] [DecidableEq E] in
/-- With the weights of an equality factor eq(ϱ, ·) and a list that holds every variable once, the
start claim says: if no coordinate of ϱ is 0, the value of the start form is the sum of eq(ϱ, b)
Φ(b) over the hypercube. -/
theorem rsum_eq (ϱ : Ξ → ι → E) (hw : ∀ ξ, S.wt ξ = eqW (ϱ ξ)) {l : List ι} (hl : l.Nodup)
    (hall : ∀ v, v ∈ l) (x : S.X) (y : Y) :
    S.Rsum Φ l x y ↔
    ((∀ v, ϱ x.2.2 v ≠ 0) →
      S.forms.val y x.1 = ∑ b : ι → Bool, eqk (ϱ x.2.2) b * Φ x.2.2 y (corner b)) := by
  unfold Rsum
  rw [hw, sumOutL_eq _ l hl hall]
  exact ⟨fun h hv => h (fun v _ => hv v) fun v _ hv' => absurd (hall v) hv',
    fun h hv _ => h fun v => hv v (hall v)⟩

end Start

/-! ## The honest prover -/

/-- What the honest prover knows: its state is a pair of some a : A (index, instance, earlier
challenges) and the point so far. From a it computes the weights and its polynomial, which has the
degrees of the format. That this is the polynomial of the statement is stated separately
(`Prover.reval_of_hsum`). The last clause is a law of the format's scalars, which completeness uses:
from the honest scalars the verifier's recurrence gives the value of the round polynomial, if the
nodes 0, ..., e i + 1 are distinct in E and the weight by which the round divides is not 0. For the
default scalars its proof is filled in. -/
structure Prover (A : Type) where
  wt : A → ι → Bool → E
  Φ : A → (ι → E) → E
  deg : ∀ a, DegLE (fun i => S.e i + 1) (Φ a)
  cmp : ∀ i, Function.Injective (node (S.e i) : Fin (S.e i + 2) → E) →
      ∀ w : Bool → E, w true ≠ 0 → (S.bas i).Complete w := by
    exact fun _ hn _ hw => Alg.Basis.complete_coeff hn hw

variable {S} {A : Type} (H : S.Prover A)

namespace Prover

/-- The scalars of the true round polynomial of the round that binds i, when the variables of l are
bound later, by the explicit formulas of the format's scalars in values of that polynomial, which
are sums of the prover's polynomial (Alg/RoundBasis.lean, Alg/RoundValues.lean). So the honest
prover's definition uses no choice. -/
def scalars (i : ι) (l : List ι) (s : A × (ι → E)) : Fin (S.e i + 1) → E :=
  (S.bas i).scal fun t => sumOutL (H.wt s.1) l (H.Φ s.1) (Function.update s.2 i t)

/-- The honest message of the round that binds i, when the variables of l are bound later: the
scalars of the true round polynomial, each plus its pad. -/
def msg (i : ι) (l : List ι) (s : A × (ι → E)) (π : P → E) : (S.rd i).Msg :=
  (fun a => Empty.elim a, fun j => H.scalars i l s j + π (S.idx i j))

/-- The honest prover of one round. Its withheld set holds the challenge 0, if a later block divides
by the challenge, and nothing else. -/
@[reducible] def round (i : ι) (l : List ι) :
    Hon (S.round i) P E (A × (ι → E)) (A × (ι → E)) :=
  Hon.one (H.msg i l) (fun s r => (s.1, Function.update s.2 i r))
    {r | S.nzv i = true ∧ r = 0} fun _ => ∅

/-- The honest prover of the masked sumcheck that binds the variables of l, when those of l' are
bound later. -/
def sc : (l l' : List ι) → Hon (S.sc l) P E (A × (ι → E)) (A × (ι → E))
  | [], _ => Hon.pure some id id
  | i :: l, l' => (H.round i (l ++ l')).seq (sc l l')

/-- The honest running claim. Link a π ξ y says that the public data ξ and the implicit part y
belong to the state a and the pads π. The point of the statement is that of the state, no weight by
which a later round divides is 0, no stored challenge by which a later block divides is 0, and the
running claim is true for the prover's polynomial. -/
def Hsum (Link : A → (P → E) → Ξ → Y → Prop) (l : List ι) (s : A × (ι → E))
    (π : P → E) (x : S.X) (y : Y) : Prop :=
  Link s.1 π x.2.2 y ∧ x.2.1 = s.2 ∧ (∀ v ∈ l, H.wt s.1 v true ≠ 0) ∧ S.NZ l s.2 ∧
    S.forms.val y x.1 = sumOutL (H.wt s.1) l (H.Φ s.1) s.2

variable {Link : A → (P → E) → Ξ → Y → Prop}

/-- Completeness of one round, at every challenge outside the withheld set and for all pads, under
`Forms.OK` and if the nodes 0, ..., e i + 1 are distinct in E. Of Link it is used that the weights
of the statement are the prover's, and that the pads of this round are in the implicit part. -/
theorem accOn_round (hok : S.forms.OK) (i : ι)
    (hnode : Function.Injective (node (S.e i) : Fin (S.e i + 2) → E)) (l : List ι)
    (hLink : ∀ a π ξ y, Link a π ξ y →
      S.wt ξ = H.wt a ∧ ∀ j, S.forms.val y (S.forms.pad (S.idx i j)) = π (S.idx i j)) :
    (H.round i l).AccOn (H.Hsum Link (i :: l)) (H.Hsum Link l) :=
  Hon.accOn_one fun s π x y c hi hc _ => by
    obtain ⟨hL, hz, hnz, hst, hv⟩ := hi
    obtain ⟨hwt, hpad⟩ := hLink _ _ _ _ hL
    refine ⟨_, if_neg hc, hL, ?_,
      fun v hv => hnz v (List.mem_cons_of_mem _ hv), hst.update S hc, ?_⟩
    · show Function.update x.2.1 i c = Function.update s.2 i c
      rw [hz]
    · show S.forms.val y (S.nextForm i x.2.2 x.1 (H.msg i l s π).2 c) = _
      rw [S.val_nextForm hok, hwt, hv]
      have hsc : (fun j => (H.msg i l s π).2 j - S.forms.val y (S.forms.pad (S.idx i j))) =
          H.scalars i l s := by
        funext j
        rw [hpad]
        exact add_sub_cancel_right _ _
      rw [hsc]
      exact Basis.next_roundPoly (H.deg s.1) (H.wt s.1) i l s.2 le_rfl (S.bas i)
        (H.cmp i hnode _ (hnz i List.mem_cons_self)) c

end Prover

/-! ## Masked form -/

variable (S) in
/-- The pads of the rounds that bind the variables of the list. -/
def padsOf : List ι → Set P
  | [] => ∅
  | i :: l => Set.range (S.idx i) ∪ padsOf l

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
theorem mem_padsOf {p : P} : ∀ {l : List ι}, p ∈ S.padsOf l ↔ ∃ v ∈ l, p ∈ Set.range (S.idx v)
  | [] => by simp [padsOf]
  | i :: l => by
      show p ∈ Set.range (S.idx i) ∪ S.padsOf l ↔ _
      rw [Set.mem_union, mem_padsOf (l := l)]
      simp

/-- Completeness of the masked sumcheck, under `Forms.OK` and if the nodes are distinct in E: if the
running claim before the rounds of l is true, so is the one after them, at every ρ outside the
withheld set. Of Link it is used that the weights of the statement are the prover's, and that the
pads of this sumcheck are in the implicit part. -/
theorem Prover.accOn_sc (H : S.Prover A) {Link : A → (P → E) → Ξ → Y → Prop} (hok : S.forms.OK)
    (hnode : ∀ i, Function.Injective (node (S.e i) : Fin (S.e i + 2) → E)) :
    ∀ l l' : List ι,
      (∀ a π ξ y,
        Link a π ξ y → S.wt ξ = H.wt a ∧ ∀ p ∈ S.padsOf l, S.forms.val y (S.forms.pad p) = π p) →
      (H.sc l l').AccOn (H.Hsum Link (l ++ l')) (H.Hsum Link l')
  | [], _, _ => Hon.accOn_pure fun _ _ x _ hi => ⟨x, rfl, hi⟩
  | i :: l, l', hLink =>
      (H.accOn_round hok i (hnode i) (l ++ l') fun a π ξ y hL =>
          ⟨(hLink a π ξ y hL).1, fun j => (hLink a π ξ y hL).2 _ (Or.inl ⟨j, rfl⟩)⟩).comp
        (Prover.accOn_sc H hok hnode l l' fun a π ξ y hL =>
          ⟨(hLink a π ξ y hL).1, fun p hp => (hLink a π ξ y hL).2 p (Or.inr hp)⟩)

omit [Fintype E] [DecidableEq E] in
/-- Where soundness and completeness meet: if Link says that the polynomial of the statement is the
prover's, the honest end claim implies the end claim of soundness. -/
theorem Prover.reval_of_hsum (H : S.Prover A) {Link : A → (P → E) → Ξ → Y → Prop}
    (hΦ : ∀ a π ξ y, Link a π ξ y → Φ ξ y = H.Φ a) {s : A × (ι → E)} {π : P → E} {x : S.X}
    {y : Y} (h : H.Hsum Link [] s π x y) : S.Reval Φ x y := by
  obtain ⟨hL, hz, -, -, hv⟩ := h
  intro _
  rw [hv, hΦ _ _ _ _ hL, hz]
  rfl

variable (S) in
/-- Every pad is used for one masked scalar only. -/
def PlacesOnce : Prop := Function.Injective fun p : (Σ i, Fin (S.e i + 1)) => S.idx p.1 p.2

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
theorem PlacesOnce.injective (h : S.PlacesOnce) (i : ι) :
    Function.Injective (S.idx i) := fun j j' hj => by
  have h1 := h (a₁ := ⟨i, j⟩) (a₂ := ⟨i, j'⟩) hj
  exact eq_of_heq (Sigma.mk.inj_iff.mp h1).2

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
theorem PlacesOnce.disjoint (h : S.PlacesOnce) {i : ι} {l : List ι} (hi : i ∉ l) :
    Disjoint (Set.range (S.idx i)) (S.padsOf l) := by
  refine Set.disjoint_left.2 fun p hp hp' => ?_
  obtain ⟨j, rfl⟩ := hp
  obtain ⟨v, hv, j', hj'⟩ := mem_padsOf.1 hp'
  have h1 := h (a₁ := ⟨v, j'⟩) (a₂ := ⟨i, j⟩) hj'
  exact hi ((Sigma.mk.inj_iff.mp h1).1 ▸ hv)

variable (S) in
/-- `PlacesOnce` for the rounds that bind the variables of a list only. (If there are infinitely
many variables and finitely many pads, only this can hold.) -/
def PlacesOnceOn (l : List ι) : Prop :=
  Set.InjOn (fun p : (Σ i, Fin (S.e i + 1)) => S.idx p.1 p.2) {p | p.1 ∈ l}

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
theorem PlacesOnce.on (h : S.PlacesOnce) (l : List ι) : S.PlacesOnceOn l := h.injOn

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
theorem PlacesOnceOn.injective {l : List ι} (h : S.PlacesOnceOn l) {i : ι} (hi : i ∈ l) :
    Function.Injective (S.idx i) := fun j j' hj => by
  have h1 := h (x₁ := ⟨i, j⟩) (x₂ := ⟨i, j'⟩) hi hi hj
  exact eq_of_heq (Sigma.mk.inj_iff.mp h1).2

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
theorem PlacesOnceOn.tail {i : ι} {l : List ι} (h : S.PlacesOnceOn (i :: l)) : S.PlacesOnceOn l :=
  h.mono fun _ hp => List.mem_cons_of_mem _ hp

omit [Fintype E] [DecidableEq E] [DecidableEq ι] in
theorem PlacesOnceOn.disjoint {i : ι} {l : List ι} (h : S.PlacesOnceOn (i :: l)) (hi : i ∉ l) :
    Disjoint (Set.range (S.idx i)) (S.padsOf l) := by
  refine Set.disjoint_left.2 fun p hp hp' => ?_
  obtain ⟨j, rfl⟩ := hp
  obtain ⟨v, hv, j', hj'⟩ := mem_padsOf.1 hp'
  have h1 := h (x₁ := ⟨v, j'⟩) (x₂ := ⟨i, j⟩) (List.mem_cons_of_mem _ hv) List.mem_cons_self hj'
  exact hi ((Sigma.mk.inj_iff.mp h1).1 ▸ hv)

variable [Fintype P] [DecidableEq P]

variable (S) in
/-- The simulator of the plain parts: independent uniform scalars. -/
def simSc : (l : List ι) → Rho (S.sc l).shape → PMF (Plains (S.sc l).shape)
  | [] => fun _ => PMF.pure ()
  | i :: l => Hon.simSeq (s := (S.round i).shape) (Hon.simOne (r := S.rd i) E id) (simSc l)

namespace Prover

/-- If the pads of the round are distinct, it is in masked form: each scalar is a value plus its own
pad, and the values read no pad. -/
theorem masked_round_of_injective
    (V : A × (ι → E) → Prop) (i : ι) (hinj : Function.Injective (S.idx i)) (l : List ι) :
    (H.round i l).Masked V (Set.range (S.idx i))
      (Set.range (S.idx i)) (Hon.simOne (r := S.rd i) E id) := by
  have h := Hon.masked_one (r := S.rd i) (pb := S.pb i) (im := fun (y : Y) _ _ => y)
    (msg := H.msg i l) (nx := fun s r => (s.1, Function.update s.2 i r))
    (Bd := {r | S.nzv i = true ∧ r = 0}) (Wn := fun _ => ∅) (enc := id) V (S.idx i)
    hinj (fun s _ j => H.scalars i l s j) ∅ (fun _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl) (Set.empty_disjoint _)
  rwa [Set.empty_union] at h

theorem masked_round (hp : S.PlacesOnce) (V : A × (ι → E) → Prop) (i : ι) (l : List ι) :
    (H.round i l).Masked V (Set.range (S.idx i))
      (Set.range (S.idx i)) (Hon.simOne (r := S.rd i) E id) :=
  H.masked_round_of_injective V i (hp.injective i) l

/-- If no pad of these rounds is used twice and the list has no repetition, the masked sumcheck is
in masked form: it masks with its own pads and reads no other pad; its plain parts are uniform
outside the withheld set. -/
theorem masked_sc_on (V : A → Prop) :
    ∀ l l' : List ι, S.PlacesOnceOn l → l.Nodup →
      (H.sc l l').Masked (fun s => V s.1) (S.padsOf l) (S.padsOf l) (S.simSc l)
  | [], _, _, _ => Hon.masked_pure some id id _
  | i :: l, l', hp, hl =>
      (H.masked_round_of_injective
          (fun s => V s.1) i (hp.injective List.mem_cons_self) (l ++ l')).comp
        (masked_sc_on V l l' hp.tail (List.nodup_cons.1 hl).2) (fun _ _ ha _ => ha)
        (hp.disjoint (List.nodup_cons.1 hl).1) (hp.disjoint (List.nodup_cons.1 hl).1)

/-- `masked_sc_on` if every pad is used once, for all variables (and the list has no repetition). -/
theorem masked_sc (hp : S.PlacesOnce) (V : A → Prop) (l l' : List ι) (hl : l.Nodup) :
    (H.sc l l').Masked (fun s => V s.1) (S.padsOf l) (S.padsOf l) (S.simSc l) :=
  H.masked_sc_on V l l' (hp.on l) hl

end Prover

end SC

end Blocks
