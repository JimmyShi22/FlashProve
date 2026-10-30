-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupSeamsKey.lean: behind a sub-proof's lookup, the masked claim on the joint
shifted keys is one row on the entries, where each key of the layout is one entry or 0.

The seam between a lookup and the batching of rows (Johnson/Top/H/LookupSeamsBat.lean) asks, in
Members.key, for a member of the batched family whose claim gives the masked claim on the joint
shifted keys. That claim reads the keys through the caller's layout, by type an arbitrary function
of the entries.

What the file states.
 - affRow cl k kAt kc: from a masked claim cl (point, mask form, target): the row whose coefficient
   at entry j is the mask form's plus the sum of the point's equality weights over the numbers X
   below 2^k with kAt X = some j, and whose target is cl's less the sum of the weights times kc X.
   affRow_holds: if a vector's entry X is kc X plus the entry kAt X (0 if there is none), the row
   holds of the entries if and only if the masked claim holds of the vector.
 - KeysAre L kp: each key of the layout L is the entry kp c i, or 0 if there is none.
 - keyAt, keyConst, forA_key_aff: then each joint shifted key is one entry or none, plus a constant
   made of the public numbers and the shift.
 - keyRow c kp x: the row, made from the explicit part x that the lookup puts out: its point, mask
   form and target, and the shift x.1.2. keyRow_holds: it holds of the entries if and only if the
   masked claim on the joint shifted keys does. For every x, not only one that a run puts out.
 - key_member: so the member rowSl at the state keyRow c kp x, with that row's target, gives the
   claim: the clause Members.key can be met.
 - rowOf, layRows c kp n g: a map of states: of a family of n + 1 members rowSl, member 0 is the
   keys' row and member i + 1 is row number i that the lookup puts out, each at its own target; the
   carried state is g of the caller's state and the shift. It refuses an x that does not hold n
   rows. members_lay, seamBat_lay_ok: Members holds of it, and the seam is in order, if the carried
   joint A₀ at g gives the caller's own joint back. So Members is met in all four clauses.
 - keysAre_dig5: KeysAre holds of the layout digL5 of the lookup on the digits.

Limits. KeysAre is shown of digL5 alone; of the layouts of the calls' lookups nothing is shown, and
no caller with the layout digL5 is given here. That the batching's own family and map of states are
these is not shown. n is a parameter: that the lookup puts out n rows is not used (for another
number layRows refuses, and the seam says nothing). pos and the two clauses on A₀ are hypotheses.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupSeamsBat
import OnBytes.Tie.Pv.Lookup.Digits.PortEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp Finset

/-! ### a masked claim on a vector of single entries -/

section
variable {E N : Type} [Field E] [Fintype N] [DecidableEq N]

/-- The row of a masked claim on a vector whose entry X is kc X plus the entry kAt X. -/
def affRow (cl : MCl E N) (k : ℕ) (kAt : ℕ → Option N) (kc : ℕ → E) : Row E N where
  cf := fun j => cl.mf j +
    ∑ X ∈ range (2 ^ k), if kAt X = some j then Blocks.eqN k 0 cl.pt X else 0
  tg := cl.tg - ∑ X ∈ range (2 ^ k), Blocks.eqN k 0 cl.pt X * kc X

/-- The entry kAt X, or 0. -/
def atOr (μ : N → E) : Option N → E
  | some j => μ j
  | none => 0

theorem atOr_sum (μ : N → E) (o : Option N) (a : E) :
    ∑ j, (if o = some j then a else 0) * μ j = a * atOr μ o := by
  cases o with
  | none => simp [atOr]
  | some i =>
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
      rfl
    · intro j _ hj
      rw [if_neg (fun e => hj (Option.some.inj e).symm), zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h

theorem affRow_holds (cl : MCl E N) (k : ℕ) (kAt : ℕ → Option N) (kc : ℕ → E) (f : ℕ → E)
    (μ : N → E) (hf : ∀ X < 2 ^ k, f X = kc X + atOr μ (kAt X)) :
    (affRow cl k kAt kc).Holds μ ↔ cl.Holds k f μ := by
  have e1 : Blocks.ext k f cl.pt = ∑ X ∈ range (2 ^ k), Blocks.eqN k 0 cl.pt X * kc X +
      ∑ X ∈ range (2 ^ k), Blocks.eqN k 0 cl.pt X * atOr μ (kAt X) := by
    unfold Blocks.ext
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun X hX => ?_
    rw [hf X (Finset.mem_range.mp hX)]
    ring
  have e2 : ∑ j, (affRow cl k kAt kc).cf j * μ j = ∑ j, cl.mf j * μ j +
      ∑ X ∈ range (2 ^ k), Blocks.eqN k 0 cl.pt X * atOr μ (kAt X) := by
    unfold affRow
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun X _ => atOr_sum μ (kAt X) _
  unfold Row.Holds MCl.Holds
  rw [e1, e2]
  show _ = cl.tg - _ ↔ _
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

end
/-! ### the joint shifted keys of a layout whose keys are single entries -/

section
variable {E St₀ J₀ : Type} [Field E]

/-- Each key of the layout is one entry, or 0. -/
def KeysAre (L : Lay E St₀ J₀) (kp : ℕ → ℕ → Option J₀) : Prop :=
  ∀ st μ k i, L.K st μ k i = atOr μ (kp k i)

/-- The entry of joint key number X, if there is one. -/
def keyAt (h : Sh) (kp : ℕ → ℕ → Option J₀) (X : ℕ) : Option (Option J₀) :=
  if X % 2 ^ h.rK < h.NT then
    (kp (Port.co h (X % 2 ^ h.rK)) (X / 2 ^ h.rK + 2 ^ h.dT *
      (X % 2 ^ h.rK % 2 ^ Port.io h (Port.co h (X % 2 ^ h.rK))))).map some
  else none

/-- What joint shifted key number X holds beside its entry. x: the caller's state and the shift. -/
def keyConst (h : Sh) (x : St₀ × E) (X : ℕ) : E :=
  (if X % 2 ^ h.rK < h.NT then 0 else forT E h x.1 0 (Port.t0Of h 0)) +
    ((Port.fK h X : ℕ) : E) * x.2

theorem atOr_map (μ : Option J₀ → E) (o : Option J₀) :
    atOr (fun j => μ (some j)) o = atOr μ (o.map some) := by
  cases o <;> rfl

variable [Fintype E] [Fintype J₀] [DecidableEq J₀]

theorem forA_key_aff (h : Sh) (L : Lay E St₀ J₀) (kp : ℕ → ℕ → Option J₀) (hL : KeysAre L kp)
    (x : St₀ × E) (μ : Option J₀ → E) (X : ℕ) :
    (forA E h L).key x μ X = keyConst h x X + atOr μ (keyAt h kp X) := by
  show Port.key h (forT E h x.1) (forK E L x.1 μ) X + ((Port.fK h X : ℕ) : E) * x.2 = _
  unfold Port.key keyConst keyAt
  by_cases hX : X % 2 ^ h.rK < h.NT
  · rw [if_pos hX, if_pos hX, if_pos hX]
    show L.K x.1 (fun j => μ (some j)) _ _ + _ = _
    rw [hL, atOr_map]
    ring
  · rw [if_neg hX, if_neg hX, if_neg hX]
    show _ = _ + _ + 0
    ring

end

/-! ### the row -/

section
variable (c : LookupCCaller) (kp : ℕ → ℕ → Option c.J₀)

/-- The masked claim on the joint shifted keys, as a row, made from the explicit part x. -/
noncomputable def keyRow (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) :
    Row Cb.Gl.E (Option c.J₀) :=
  affRow x.2.1 ((forA Cb.Gl.E c.h c.L).v' + 1) (keyAt c.h kp) (keyConst c.h x.1)

theorem keyRow_holds (hL : KeysAre c.L kp) (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀))
    (μ : Option c.J₀ → Cb.Gl.E) :
    (keyRow c kp x).Holds μ ↔
      x.2.1.Holds ((forA Cb.Gl.E c.h c.L).v' + 1) ((forA Cb.Gl.E c.h c.L).key x.1 μ) μ :=
  affRow_holds x.2.1 _ _ _ _ μ fun X _ => forA_key_aff c.h c.L kp hL x.1 μ X

variable [DecidableEq c.Sg.Ent] (pos : c.J₀ → c.Sg.Ent)

/-- The member of the family that gives the keys' claim. -/
theorem key_member (hL : KeysAre c.L kp) (hpos : ∀ m j, c.msg₀ m j = c.Sg.ents m (pos j))
    (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (m : c.Sg.Msg) :
    (rowSl c pos).Holds ((keyRow c kp x).tg, keyRow c kp x) (c.Sg.ents m) ↔
      x.2.1.Holds ((forA Cb.Gl.E c.h c.L).v' + 1)
        ((forA Cb.Gl.E c.h c.L).key x.1 (zext (c.msg₀ m))) (zext (c.msg₀ m)) :=
  (rowSl_holds c pos hpos _ m).trans (keyRow_holds c kp hL x _)

end

/-! ### a map of states under which Members holds -/

section
variable (c : LookupCCaller) (kp : ℕ → ℕ → Option c.J₀) [DecidableEq c.Sg.Ent]
  (pos : c.J₀ → c.Sg.Ent) (n : ℕ) {Kc' St₀' : Type} (g : c.St₀ × Cb.Gl.E → St₀')
  (A₀ : IOR.Rels Kc' St₀' c.Ex (c.Sg.Msg × c.Wp))

/-- Member 0: the keys' row. Member i + 1: row number i that the lookup puts out. -/
noncomputable def rowOf (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) (b : Fin (n + 1)) :
    Row Cb.Gl.E (Option c.J₀) :=
  Fin.cases (keyRow c kp x) (fun i => x.2.2.getD i.val ⟨fun _ => 0, 0⟩) b

/-- The map of states: each row with its own target. It refuses unless x holds n rows. -/
noncomputable def layRows (x : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)) :
    Option (((Fin (n + 1) → Cb.Gl.E) × (Fin (n + 1) → Row Cb.Gl.E (Option c.J₀))) × St₀') :=
  if x.2.2.length = n then
    some ((fun b => (rowOf c kp n x b).tg, fun b => rowOf c kp n x b), g x.1)
  else none

/-- Members holds of that map, over the family whose every member is rowSl. -/
theorem members_lay (hL : KeysAre c.L kp) (hpos : ∀ m j, c.msg₀ m j = c.Sg.ents m (pos j))
    (hon : ∀ x y, c.R0.on (x.1, y) → A₀.on (g x, y))
    (hrd : ∀ x y w, c.R0.on (x.1, y) → A₀.relR (g x, y) w → c.R0.relR (x.1, y) w) :
    Members c (fun _ : Fin (n + 1) => Row Cb.Gl.E (Option c.J₀)) (fun _ => rowSl c pos) A₀
      (layRows c kp n g) where
  on := fun x y s' ho hf => by
    unfold layRows at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      exact hon x.1 y ho
    · cases hf
  rider := fun x y s' w ho hf hw => by
    unfold layRows at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      exact hrd x.1 y w ho hw
    · cases hf
  rows := fun x s' hf r hr => by
    unfold layRows at hf
    split at hf
    · rename_i hn
      obtain rfl := Option.some.inj hf
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem hr
      refine ⟨Fin.succ ⟨i, hn ▸ hi⟩, fun m hm => ?_⟩
      have e2 : rowOf c kp n x (Fin.succ ⟨i, hn ▸ hi⟩) = r := by
        show x.2.2.getD i _ = r
        rw [List.getD_eq_getElem _ _ hi, e]
      have hm' : (rowSl c pos).Holds ((rowOf c kp n x (Fin.succ ⟨i, hn ▸ hi⟩)).tg,
        rowOf c kp n x (Fin.succ ⟨i, hn ▸ hi⟩)) (c.Sg.ents m) := hm
      rw [e2] at hm'
      exact (rowSl_holds c pos hpos r m).1 hm'
    · cases hf
  key := fun x s' hf => by
    unfold layRows at hf
    split at hf
    · obtain rfl := Option.some.inj hf
      exact ⟨0, fun m hm => (key_member c kp pos hL hpos x m).1 hm⟩
    · cases hf

/-- The seam between the lookup and the batching of rows is in order under that map. -/
theorem seamBat_lay_ok (hL : KeysAre c.L kp) (hpos : ∀ m j, c.msg₀ m j = c.Sg.ents m (pos j))
    (hon : ∀ x y, c.R0.on (x.1, y) → A₀.on (g x, y))
    (hrd : ∀ x y w, c.R0.on (x.1, y) → A₀.relR (g x, y) w → c.R0.relR (x.1, y) w) :
    (seamOut c (batIn c (fun _ : Fin (n + 1) => Row Cb.Gl.E (Option c.J₀))
      (fun _ => rowSl c pos) A₀) (layRows c kp n g)).OK :=
  seamBat_ok c _ _ A₀ _ (members_lay c kp pos n g A₀ hL hpos hon hrd)

end

/-! ### the digits -/

section
open OnBytes OnBytes.Model OnBytes.DgP
variable {E J₀ : Type} [Field E]

/-- The entry of key number kn of call q of the lookup on the digits. -/
def digKp (tl : HTailF2) (en : Ent3 → J₀) (q kn : ℕ) : Option J₀ :=
  (digInCall tl q kn).map fun t => en (tl.ix.ZZ, t.2.2, q * tl.mz + t.2.1)

theorem keysAre_dig5 (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type) :
    KeysAre (digL5 E tl en mk jLK St₀) (digKp tl en) := by
  intro st μ k i
  show Kp tl (fun n => μ (en n)) k i = _
  unfold Kp digKp
  cases digInCall tl k i <;> rfl

end

#print axioms VerifiableInference.OnPublicFiles.affRow_holds
#print axioms VerifiableInference.OnPublicFiles.forA_key_aff
#print axioms VerifiableInference.OnPublicFiles.keyRow_holds
#print axioms VerifiableInference.OnPublicFiles.key_member
#print axioms VerifiableInference.OnPublicFiles.members_lay
#print axioms VerifiableInference.OnPublicFiles.seamBat_lay_ok
#print axioms VerifiableInference.OnPublicFiles.keysAre_dig5

end VerifiableInference.OnPublicFiles
