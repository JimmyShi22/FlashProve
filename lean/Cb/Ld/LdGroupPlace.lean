-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupPlace.lean: this file says where the entries of the folded complex go at the switch of
a closing: the carried message, and the kept messages encoded anew.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdGroupPlaceProofs.lean
(`GNew.toNew_injective` is stated and proved here). Many statements of this library are written
twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same name
outside that namespace proves it (lean/GLOSSARY.md).

In standard terms: `N.place` is a bijection from the coordinates of (message, encoding randomness)
of the folded code, together with fresh coordinates, onto the coordinates of the messages of the new
codewords; `N.cut` reads the old (message, randomness) back off the new messages.

After the fold of a closing the prover sends new oracle messages which together hold (message,
randomness) of the folded complex `Sh.Cf`, and fresh entries. A code switch asks for a bijection
"place" between [entries of message and randomness of the old code, fresh entries] and the entries
of the new messages.
`GNew Hd`: the data.
  `ag`: which of the held messages get a new oracle message of their own (those that will be kept
    again at the next closing need one: they must be in kept slots with a sample of their own once
    more); the others ride in the carried message, under its sample.
  `pad k` (k with `ag k`): the places of the pad of such a message (the entries that mask the
    answers of its old sample).
  `Qc`: the fresh entries of the carried message (its own pad; free room).
  `N.Qo`: all fresh entries: one for each pad place of each message that is encoded anew, and Qc.
The rule. An entry of a message that is encoded anew which is no pad place (a cell) goes to the same
place of the new message. At a pad place the new message has a fresh entry. The old pad goes into
the carried message, with all encoding randomness (that of the kept slots too), the ordinary slot,
the two masks, and all entries of the held messages that ride.

Why: the new message is sampled again. Its entries, the old pad among them, fill it exactly: there
is no room for a second pad; and one pad entry must not mask two answers that are shown.

Main names:
  `Spec.ldGroup_place_cell`, `Spec.ldGroup_place_fresh`, `Spec.ldGroup_place_rest`: where place
    sends a cell; a fresh pad entry; everything else.
  `Spec.ldGroup_place_cells`: for all new messages m (`N.N₀.Msg`): the slot of the cut that holds
    the kept message k has, at every cell, the entry of m (some k) at the same place.
  `Spec.ldGroup_place_pads`: and at a pad place it has an entry of the carried message: the old
    sample's row on the slot of the cut is a row on (the new message, the carried message).
  `Spec.ldGroup_place_old`, `Spec.ldGroup_place_ride`: what goes into the carried message: see their
    doc comments.

Limits: this file says nothing on any protocol or relation. It says nothing on the sizes of codes
(eC says that the carried message has exactly the room). The held messages that are encoded anew and
those that ride are both held (in `cl` of Cb/Ld/LdGroupSeg.lean): for both kinds the carried
predicates read the decoding until the locations, and the old sample's row is read on the slots of
the cut.
The rule for pads follows this protocol's technical report; the paper that this protocol builds on
has a like rule for one stack, and the pad of a sample goes back in part to advice.  The switch
follows that paper (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupSeg
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

section
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} {Sh : GShape G}
  {kp : S.O → Prop} (Hd : GHeld Sh kp)

/-- all entries of all held messages -/
abbrev GHeld.Ent : Type := Σ k : {a // Hd.cl a}, (S.om k.1.1).C.J

variable (ag : {a // Hd.cl a} → Prop)

/-- all entries of the held messages that are encoded anew -/
abbrev GHeld.EntA : Type := Σ k : {k // ag k}, (S.om k.1.1.1).C.J

/-- the fresh entries; the entries that are placed -/
abbrev GHeld.Fresh (pad : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J → Prop) (Qc : Type) : Type :=
  (Σ k : {k // ag k}, {j // pad k j}) ⊕ Qc
abbrev GHeld.All (pad : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J → Prop) (Qc : Type) : Type :=
  (Sh.Cf.J ⊕ Sh.Cf.Q) ⊕ Hd.Fresh ag pad Qc

/-- what is at a place of a message encoded anew: the old entry at a cell, a fresh entry at a pad
place -/
def GHeld.toNew (pad : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J → Prop) [∀ k, DecidablePred (pad k)]
    (Qc : Type) (n : Hd.EntA ag) : Hd.All ag pad Qc :=
  if h : pad n.1 n.2 then .inr (.inl ⟨n.1, ⟨n.2, h⟩⟩) else .inl (.inl (Hd.sJ n.1.1 n.2))

/-- an entry that goes to a message encoded anew -/
def GHeld.InNew (pad : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J → Prop) [∀ k, DecidablePred (pad k)]
    (Qc : Type) (u : Hd.All ag pad Qc) : Prop :=
  ∃ n, Hd.toNew ag pad Qc n = u

end

/-- The new messages of a closing: the data. -/
structure GNew {E : Type} [Field E] {S : Sig E} {G : Grp S} {Sh : GShape G}
    {kp : S.O → Prop} (Hd : GHeld Sh kp) where
  /-- the carried message -/
  oc   : OMsg E
  /-- which held messages get a new oracle message of their own; the others ride in the carried
  message -/
  ag   : {a // Hd.cl a} → Prop
  [decAg : DecidablePred ag]
  /-- these, encoded anew (any code; a sample of its own), with the same entries -/
  on   : {k // ag k} → OMsg E
  same : ∀ k, (S.om k.1.1.1).C.J ≃ (on k).C.J
  /-- the places of the old pads -/
  pad  : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J → Prop
  [decPad : ∀ k, DecidablePred (pad k)]
  /-- the fresh entries of the carried message -/
  Qc   : Type
  /-- the carried message holds exactly what goes nowhere else -/
  eC   : {u : Hd.All ag pad Qc // ¬ Hd.InNew ag pad Qc u} ≃ oc.C.J
  /-- different entries of kept messages are in different entries of the folded complex -/
  inj  : ∀ n n' : Hd.Ent, Hd.sJ n.1 n.2 = Hd.sJ n'.1 n'.2 → n = n'

attribute [instance] GNew.decAg GNew.decPad

namespace GNew
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] {Hd : GHeld Sh kp} (N : GNew Hd)

/-- The signature of the new messages. -/
@[reducible] def N₀ : Sig E := { O := Option {k // N.ag k}, om := fun a => a.elim N.oc N.on }

abbrev Qo : Type := Hd.Fresh N.ag N.pad N.Qc
abbrev U : Type := Hd.All N.ag N.pad N.Qc

/-- the entries of the held messages that are encoded anew and of the carried one, as the entries of
the new signature -/
def toEnt : Hd.EntA N.ag ⊕ N.oc.C.J ≃ N.N₀.Ent where
  toFun := fun n => match n with
    | .inl n => ⟨some n.1, N.same n.1 n.2⟩
    | .inr j => ⟨none, j⟩
  invFun := fun n => match n with
    | ⟨none, j⟩ => .inr j
    | ⟨some k, j⟩ => .inl ⟨k, (N.same k).symm j⟩
  left_inv := fun n => by
    rcases n with ⟨k, j⟩ | j
    · simp
    · rfl
  right_inv := fun n => by
    rcases n with ⟨_ | k, j⟩
    · rfl
    · simp

omit [DecidablePred kp] in
theorem toNew_injective : Function.Injective (Hd.toNew N.ag N.pad N.Qc) := by
  intro n n' h
  unfold GHeld.toNew at h
  by_cases h1 : N.pad n.1 n.2 <;> by_cases h2 : N.pad n'.1 n'.2
  · rw [dif_pos h1, dif_pos h2] at h
    have h3 := Sum.inl.inj (Sum.inr.inj h)
    obtain ⟨k, j⟩ := n
    obtain ⟨k', j'⟩ := n'
    obtain rfl : k = k' := congrArg Sigma.fst h3
    have h4 := eq_of_heq (Sigma.mk.inj h3).2
    exact congrArg (Sigma.mk k) (congrArg Subtype.val h4)
  · rw [dif_pos h1, dif_neg h2] at h
    cases h
  · rw [dif_neg h1, dif_pos h2] at h
    cases h
  · rw [dif_neg h1, dif_neg h2] at h
    have h3 := N.inj ⟨n.1.1, n.2⟩ ⟨n'.1.1, n'.2⟩ (Sum.inl.inj (Sum.inl.inj h))
    obtain ⟨⟨k, hk⟩, j⟩ := n
    obtain ⟨⟨k', hk'⟩, j'⟩ := n'
    obtain rfl : k = k' := congrArg Sigma.fst h3
    exact congrArg (Sigma.mk (⟨k, hk⟩ : {k // N.ag k})) (eq_of_heq (Sigma.mk.inj h3).2)

/-- the entries of the held messages that are encoded anew, as the entries that go to the messages
encoded anew -/
def eNew : Hd.EntA N.ag ≃ {u : N.U // Hd.InNew N.ag N.pad N.Qc u} :=
  Equiv.ofBijective (fun n => ⟨Hd.toNew N.ag N.pad N.Qc n, n, rfl⟩) ⟨fun _ _ h =>
      N.toNew_injective (congrArg Subtype.val h),
    fun u => ⟨u.2.choose, Subtype.ext u.2.choose_spec⟩⟩

open Classical in
/-- Where each entry goes. -/
def place : (Sh.Cf.J ⊕ Sh.Cf.Q) ⊕ N.Qo ≃ N.N₀.Ent :=
  ((Equiv.sumCompl (Hd.InNew N.ag N.pad N.Qc)).symm.trans
    (Equiv.sumCongr N.eNew.symm N.eC)).trans N.toEnt

/-- (message, randomness) of the folded complex, as the new messages hold them. -/
def cut (m : N.N₀.Msg) : (Sh.Cf.J → E) × (Sh.Cf.Q → E) :=
  (fun j => N.N₀.ents m (N.place (.inl (.inl j))), fun q => N.N₀.ents m (N.place (.inl (.inr q))))

end GNew

namespace Spec

def ldGroup_place_cell : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G)
      (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (N : GNew Hd)
      (k : {k // N.ag k}) (j : (S.om k.1.1.1).C.J),
    ¬ N.pad k j → N.place (.inl (.inl (Hd.sJ k.1 j))) = ⟨some k, N.same k j⟩

def ldGroup_place_fresh : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G) (kp : S.O → Prop)
      [DecidablePred kp] (Hd : GHeld Sh kp) (N : GNew Hd) (k : {k // N.ag k})
      (j : (S.om k.1.1.1).C.J) (h : N.pad k j),
    N.place (.inr (.inl ⟨k, ⟨j, h⟩⟩)) = ⟨some k, N.same k j⟩

def ldGroup_place_rest : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G)
      (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (N : GNew Hd)
      (u : N.U) (h : ¬ Hd.InNew N.ag N.pad N.Qc u),
    N.place u = ⟨none, N.eC ⟨u, h⟩⟩

/-- What goes into the carried message: the old pads; all randomness; the ordinary slot; the masks;
its own fresh entries. -/
def ldGroup_place_old : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G) (kp : S.O → Prop)
      [DecidablePred kp] (Hd : GHeld Sh kp) (N : GNew Hd),
    (∀ k j, N.pad k j → (N.place (.inl (.inl (Hd.sJ k.1 j)))).1 = none) ∧
    (∀ q : Sh.Cf.Q, (N.place (.inl (.inr q))).1 = none) ∧
    (∀ c : Sh.Cb.J, (N.place (.inl (.inl (.inl (none, c))))).1 = none) ∧
    (∀ c : Sh.Zb.J ⊕ Sh.Zb.J, (N.place (.inl (.inl (.inr c)))).1 = none) ∧
    (∀ q : N.Qc, (N.place (.inr (.inr q))).1 = none)

/-- What reads cells reads the same cells before and after. -/
def ldGroup_place_cells : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G) (kp : S.O → Prop)
      [DecidablePred kp] (Hd : GHeld Sh kp) (N : GNew Hd) (m : N.N₀.Msg)
      (k : {k // N.ag k}) (j : (S.om k.1.1.1).C.J),
    ¬ N.pad k j → (N.cut m).1 (Hd.sJ k.1 j) = m (some k) (N.same k j)

/-- At a pad place the slot of the cut has an entry of the carried message. -/
def ldGroup_place_pads : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G)
      (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (N : GNew Hd)
      (k : {k // N.ag k}) (j : (S.om k.1.1.1).C.J),
    N.pad k j → ∃ c : N.oc.C.J, ∀ m : N.N₀.Msg, (N.cut m).1 (Hd.sJ k.1 j) = m none c

/-- Every entry of a held message that rides is an entry of the carried message. -/
def ldGroup_place_ride : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (G : Grp S) (Sh : GShape G)
      (kp : S.O → Prop) [DecidablePred kp] (Hd : GHeld Sh kp) (N : GNew Hd)
      (k : {a // Hd.cl a}) (j : (S.om k.1.1).C.J),
    ¬ N.ag k → ∃ c : N.oc.C.J, ∀ m : N.N₀.Msg, (N.cut m).1 (Hd.sJ k j) = m none c

end Spec
end Cb
