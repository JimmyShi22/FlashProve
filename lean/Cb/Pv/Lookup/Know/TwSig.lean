-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Know/TwSig.lean.
Knowledge soundness for each fixed vector of entries, carried over every signature that has three
oracle messages with given entries.

Definitions, statements and proofs. General in the field E and in the three types of entries
J0, J1, J2. Only Cb/Ld/LdSigLiftProofs.lean and Cb/Ld/LdSigProofs.lean are imported.
Main names:
  `Sig3 S J0 J1 J2`: what "S has three oracle messages with these entries" is: the names of S's
    oracle messages are three (`nm : Fin 3 ≃ S.O`), and the entries of the message named `nm i` are
    J_i (an equivalence each). Data on the shape of S alone: its fields' types name `S.O` and
    `(S.om _).C.J` and nothing else of S: no message, word, sample, witness or transcript.
  `Sig3.msg`: the reading `S.Msg → (J0 ⊕ J1 ⊕ J2 → E)`; `Sig3.msgEquiv`: it is an equivalence.
  `jn Ex msg P`: the base joint over `M × Unit` with `on := fun _ => True` and
    `relR a (m, ()) := P a.1 (msg m)`. (The exact side `rel`, which knowledge soundness does not
    read, is the same P; the core is Unit.)
  `sig3_at`: knowledge soundness (round by round: `Reduction.Know`, Ior/Know.lean) of a reduction R
    between such joints for each tuple `m : S.Msg`. Its premise `hi`: at every fixed vector of
    entries μ, R is knowledge sound from RA · μ to RB · μ, on all statements, with Unit for the
    witnesses and the errors ε. The conclusion is `hi` at `h.msg m`.
  `sig3_know`: under the same premise, knowledge soundness with the errors ε of
    `R.keep S.Smp S.ext` (R with the words and samples of S copied; R reads none of them) between
    the joints over S, by `sigLift_know`. The condition, both relations and the extractor are those
    of `sigLift_know`: the examples behind it say so by rfl.
  `sigId`, `sigId3`, `sig3Id`, `sig3Id_source`: the statements range over something: for finite J0,
    J1, J2 a signature with `Sig3` exists (the word is the message; radius 0; one seed, no answer),
    and over it every vector of entries μ has a collision-free statement and a witness with the
    entries μ at which the relaxed relation holds if and only if P x μ.
Limits: `sig3_know` speaks of collision-free statements alone (the condition of `S.over`). Nothing
here shows that a statement over a given S is collision-free, but for the plain signature `sigId`.
Not claimed: anything on completeness or hiding.

-/
import Cb.Ld.LdSigLiftProofs
import Cb.Ld.LdSigProofs

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR

/-- S has three oracle messages, whose entries are J0, J1, J2, in this order. Data on the shape of S
alone. -/
structure Sig3 {E : Type} (S : Sig E) (J0 J1 J2 : Type) where
  nm : Fin 3 ≃ S.O
  e0 : J0 ≃ (S.om (nm 0)).C.J
  e1 : J1 ≃ (S.om (nm 1)).C.J
  e2 : J2 ≃ (S.om (nm 2)).C.J

namespace Sig3
variable {E : Type} {S : Sig E} {J0 J1 J2 : Type} (h : Sig3 S J0 J1 J2)

/-- the reading: entry j of message i -/
def msg (m : S.Msg) : J0 ⊕ J1 ⊕ J2 → E
  | .inl j => m (h.nm 0) (h.e0 j)
  | .inr (.inl j) => m (h.nm 1) (h.e1 j)
  | .inr (.inr j) => m (h.nm 2) (h.e2 j)

/-- a vector of entries, as the three messages by number -/
def fam (μ : J0 ⊕ J1 ⊕ J2 → E) : ∀ i : Fin 3, (S.om (h.nm i)).C.J → E
  | 0 => fun j => μ (.inl (h.e0.symm j))
  | 1 => fun j => μ (.inr (.inl (h.e1.symm j)))
  | 2 => fun j => μ (.inr (.inr (h.e2.symm j)))

/-- the same vector, as a tuple of messages by name -/
def back (μ : J0 ⊕ J1 ⊕ J2 → E) : S.Msg := Equiv.piCongrLeft (fun a => (S.om a).C.J → E) h.nm (h.fam
    μ)

theorem back_nm (μ : J0 ⊕ J1 ⊕ J2 → E) (i : Fin 3) : h.back μ (h.nm i) = h.fam μ i :=
  Equiv.piCongrLeft_apply_apply (fun a => (S.om a).C.J → E) h.nm (h.fam μ) i

theorem msg_back (μ : J0 ⊕ J1 ⊕ J2 → E) : h.msg (h.back μ) = μ := by
  funext j
  rcases j with j | j | j
  · show h.back μ (h.nm 0) (h.e0 j) = _
    rw [back_nm]; show μ (.inl (h.e0.symm (h.e0 j))) = _; rw [Equiv.symm_apply_apply]
  · show h.back μ (h.nm 1) (h.e1 j) = _
    rw [back_nm]; show μ (.inr (.inl (h.e1.symm (h.e1 j)))) = _; rw [Equiv.symm_apply_apply]
  · show h.back μ (h.nm 2) (h.e2 j) = _
    rw [back_nm]; show μ (.inr (.inr (h.e2.symm (h.e2 j)))) = _; rw [Equiv.symm_apply_apply]

theorem back_msg (m : S.Msg) : h.back (h.msg m) = m := by
  funext a
  obtain ⟨i, rfl⟩ := h.nm.surjective a
  rw [back_nm]
  funext j
  match i with
  | 0 => show m (h.nm 0) (h.e0 (h.e0.symm j)) = _; rw [Equiv.apply_symm_apply]
  | 1 => show m (h.nm 1) (h.e1 (h.e1.symm j)) = _; rw [Equiv.apply_symm_apply]
  | 2 => show m (h.nm 2) (h.e2 (h.e2.symm j)) = _; rw [Equiv.apply_symm_apply]

/-- The reading loses nothing and adds nothing. -/
def msgEquiv : S.Msg ≃ (J0 ⊕ J1 ⊕ J2 → E) := ⟨h.msg, h.back, h.back_msg, h.msg_back⟩

end Sig3

/-- The base joint of a predicate P on the explicit part and the entries, claimed of the messages
read by msg. No further witness; every statement. -/
def jn {M X J E : Type} (Ex : ExtSpec) (msg : M → J → E) (P : X → (J → E) → Prop) : Rels Unit X Ex
    (M × Unit) where
  rel := fun x _ w => P x (msg w.1)
  relR := fun a w => P a.1 (msg w.1)
  on := fun _ => True
  core := fun _ => ()

section
variable {E : Type} [Field E] {J0 J1 J2 X X' : Type} {Ex Ex' : ExtSpec}

omit [Field E] in
/-- Knowledge soundness between the joints `jn` at each fixed tuple m : S.Msg, from knowledge
soundness at every fixed vector of entries (the premise hi, taken at h.msg m). -/
theorem sig3_at (S : Sig E) (h : Sig3 S J0 J1 J2) (R : IOR X Ex X' Ex') (RA : X → (J0 ⊕ J1 ⊕ J2 → E)
    → Prop)
    (RB : X' → (J0 ⊕ J1 ⊕ J2 → E) → Prop) (ε : Err R.shape)
    (hi : ∀ μ : J0 ⊕ J1 ⊕ J2 → E,
      R.red.Know (fun _ => True) (fun a (_ : Unit) => RA a.1 μ) (fun b (_ : Unit) => RB b.1 μ) (fun
          _ _ wp => wp) ε)
    (m : S.Msg) :
    R.red.Know (jn Ex h.msg RA).on (fun a wp => (jn Ex h.msg RA).relR a (m, wp))
      (fun b wp => (jn Ex' h.msg RB).relR b (m, wp)) (fun _ _ wp => wp) ε :=
  hi (h.msg m)

/-- Over every signature with three messages of these entries, by `sigLift_know`. -/
theorem sig3_know (S : Sig E) (h : Sig3 S J0 J1 J2) (R : IOR X Ex X' Ex') (RA : X → (J0 ⊕ J1 ⊕ J2 →
    E) → Prop)
    (RB : X' → (J0 ⊕ J1 ⊕ J2 → E) → Prop) (ε : Err R.shape)
    (hi : ∀ μ : J0 ⊕ J1 ⊕ J2 → E,
      R.red.Know (fun _ => True) (fun a (_ : Unit) => RA a.1 μ) (fun b (_ : Unit) => RB b.1 μ) (fun
          _ _ wp => wp) ε) :
    (R.keep S.Smp S.ext).red.Know (S.over (jn Ex h.msg RA)).on (S.over (jn Ex h.msg RA)).relR
      (S.over (jn Ex' h.msg RB)).relR (fun _ _ w => w) ε :=
  sigLift_know E S Unit X X' Unit Unit Ex Ex' R (jn Ex h.msg RA) (jn Ex' h.msg RB) (fun _ _ _ wp =>
      wp) ε
    (sig3_at S h R RA RB ε hi)

/-! In `sig3_know` nothing is chosen: what the four places are, by rfl. -/
example (S : Sig E) (h : Sig3 S J0 J1 J2) (RA : X → (J0 ⊕ J1 ⊕ J2 → E) → Prop) :
    (jn Ex h.msg RA).on = fun _ => True := rfl
example (S : Sig E) (h : Sig3 S J0 J1 J2) (RA : X → (J0 ⊕ J1 ⊕ J2 → E) → Prop) :
    (S.over (jn Ex h.msg RA)).on = fun a => S.CF a.1.2 a.2.2 ∧ True := rfl
example (S : Sig E) (h : Sig3 S J0 J1 J2) (RA : X → (J0 ⊕ J1 ⊕ J2 → E) → Prop) :
    (S.over (jn Ex h.msg RA)).relR =
      fun a w => (∀ i, S.decs a.1.2 a.2.2 i = some (w.1 i).1) ∧ RA a.1.1 (h.msg (S.msgs w.1)) := rfl
/-- the extractor is that of `sigLift_know` at the identity -/
example (S : Sig E) (R : IOR X Ex X' Ex') :
    (fun (a : (X × S.Smp) × (Ex.prod S.ext).Str) (τ : Tr R.shape) (w : S.Wit × Unit) =>
      (w.1, (fun (_ : S.Msg) (_ : X × Ex.Str) (_ : Tr R.shape) (wp : Unit) => wp) (S.msgs w.1)
          (a.1.1, a.2.1) τ w.2)) =
    fun _ _ w => w := rfl

end

/-! ### "For every S" ranges over something, and the in-relation holds somewhere -/

/-- the plainest code: the word is the message -/
@[reducible] def idCode (E J : Type) [Fintype J] [DecidableEq J] : LdCode E J where
  NP := J
  NS := fun _ => Unit
  J := J
  Q := Empty
  enc := fun m _ p _ => m p
  Aa := Unit
  T := fun f x _ => f x ()
  src := fun x => {x}

/-- the plainest oracle message: radius 0, no sample -/
@[reducible] def idMsg (E J : Type) [Zero E] [Fintype J] [DecidableEq J] : OMsg E :=
  OMsg.plain (idCode E J) (Ood.Sample.nil E J) 0 fun _ => 0

/-- a signature all of whose oracle messages are such -/
@[reducible] def sigId (E O : Type) [Zero E] [Fintype O] [DecidableEq O] (J : O → Type) [∀ a,
    Fintype (J a)]
    [∀ a, DecidableEq (J a)] : Sig E := { O := O, om := fun a => idMsg E (J a) }

section
variable (E : Type) [Field E] (J : Type) [Fintype J] [DecidableEq J]

theorem idCode_laws : (idCode E J).Laws where
  encLin := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  tLin := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  inj := fun m r hh => ⟨funext fun p => congrFun (congrFun hh p) (), Subsingleton.elim _ _⟩
  loc := fun f g x hh => funext fun _ => by
    show f x () = g x ()
    rw [hh x (Finset.mem_singleton_self x)]

theorem idCode_dist : (idCode E J).Dist 1 := by
  intro m r hne
  have hm : m ≠ 0 := fun h0 => hne ⟨h0, Subsingleton.elim _ _⟩
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hm
  have : Nonempty {x : J // (idCode E J).T ((idCode E J).enc m r) x ≠ 0} :=
    ⟨⟨x, fun h0 => hx (congrFun h0 ())⟩⟩
  exact Nat.succ_le_of_lt (Nat.card_pos)

end

section
variable (E O : Type) [Field E] [Fintype O] [DecidableEq O] (J : O → Type) [∀ a, Fintype (J a)] [∀
    a, DecidableEq (J a)]

/-- the statement of a tuple of messages: the words are the messages; the one seed, no answer -/
def idSmp : (sigId E O J).Smp := fun _ => ((), fun s => s.elim)
def idStr (m : (sigId E O J).Msg) : (sigId E O J).ext.Str := fun a p _ => m a p
def idWit (m : (sigId E O J).Msg) : (sigId E O J).Wit := fun a => (m a, fun q => q.elim)

theorem sigId_cf (y : (sigId E O J).ext.Str) : (sigId E O J).CF (idSmp E O J) y := fun a =>
  sig_no_clash_unique E (idMsg E (J a)) 1 (idCode_laws E (J a)) (idCode_dist E (J a)) (show 2 * 0 <
      1 by decide) (y a) _

theorem sigId_decs (m : (sigId E O J).Msg) (a : O) :
    (sigId E O J).decs (idSmp E O J) (idStr E O J m) a = some (m a) := by
  have := sig_dec_enc E (idMsg E (J a)) (idCode_laws E (J a)) (idCode_dist E (J a)) (idStr E O J m
      a)
    (idWit E O J m a) () rfl
  have e : (idSmp E O J a) = (((), (idMsg E (J a)).Z.val () (idWit E O J m a).1) : (idMsg E (J
      a)).Smp) :=
    Prod.ext rfl (Subsingleton.elim _ _)
  show (idMsg E (J a)).dec (idStr E O J m a) (idSmp E O J a) = _
  rw [e]
  exact this

end

/-- three types by number -/
def J3 (J0 J1 J2 : Type) : Fin 3 → Type
  | 0 => J0
  | 1 => J1
  | 2 => J2
instance (J0 J1 J2 : Type) [Fintype J0] [Fintype J1] [Fintype J2] : ∀ a, Fintype (J3 J0 J1 J2 a)
  | 0 => inferInstanceAs (Fintype J0)
  | 1 => inferInstanceAs (Fintype J1)
  | 2 => inferInstanceAs (Fintype J2)
instance (J0 J1 J2 : Type) [DecidableEq J0] [DecidableEq J1] [DecidableEq J2] : ∀ a, DecidableEq (J3
    J0 J1 J2 a)
  | 0 => inferInstanceAs (DecidableEq J0)
  | 1 => inferInstanceAs (DecidableEq J1)
  | 2 => inferInstanceAs (DecidableEq J2)

section
variable (E : Type) [Field E] (J0 J1 J2 : Type) [Fintype J0] [Fintype J1] [Fintype J2] [DecidableEq
    J0] [DecidableEq J1]
  [DecidableEq J2]

/-- the plain signature with three messages -/
@[reducible] def sigId3 : Sig E := sigId E (Fin 3) (J3 J0 J1 J2)

/-- "For every S with Sig3" ranges over something. -/
def sig3Id : Sig3 (sigId3 E J0 J1 J2) J0 J1 J2 := ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _,
    Equiv.refl _⟩

/-- For every vector of entries μ and every explicit part x there is a statement over the plain
signature that is collision-free, and a witness whose entries are μ, at which the relaxed relation
over the signature is P x μ. -/
theorem sig3Id_source {X : Type} (Ex : ExtSpec) (P : X → (J0 ⊕ J1 ⊕ J2 → E) → Prop) (x : X) (y :
    Ex.Str)
    (μ : J0 ⊕ J1 ⊕ J2 → E) :
    ∃ (a : (X × (sigId3 E J0 J1 J2).Smp) × (Ex.prod (sigId3 E J0 J1 J2).ext).Str) (w : (sigId3 E J0
        J1 J2).Wit × Unit),
      a.1.1 = x ∧ (sig3Id E J0 J1 J2).msg ((sigId3 E J0 J1 J2).msgs w.1) = μ ∧
      ((sigId3 E J0 J1 J2).over (jn Ex (sig3Id E J0 J1 J2).msg P)).on a ∧
      (((sigId3 E J0 J1 J2).over (jn Ex (sig3Id E J0 J1 J2).msg P)).relR a w ↔ P x μ) := by
  let m := (sig3Id E J0 J1 J2).back μ
  refine ⟨((x, idSmp E (Fin 3) (J3 J0 J1 J2)), (y, idStr E (Fin 3) (J3 J0 J1 J2) m)),
    (idWit E (Fin 3) (J3 J0 J1 J2) m, ()), rfl, (sig3Id E J0 J1 J2).msg_back μ,
    ⟨sigId_cf E (Fin 3) (J3 J0 J1 J2) _, trivial⟩, ?_⟩
  constructor
  · intro hh
    have h2 : P x ((sig3Id E J0 J1 J2).msg ((sig3Id E J0 J1 J2).back μ)) := hh.2
    rwa [(sig3Id E J0 J1 J2).msg_back μ] at h2
  · intro hh
    refine ⟨fun i => sigId_decs E (Fin 3) (J3 J0 J1 J2) m i, ?_⟩
    show P x ((sig3Id E J0 J1 J2).msg ((sig3Id E J0 J1 J2).back μ))
    rwa [(sig3Id E J0 J1 J2).msg_back μ]

end
end Cb.Tw
#print axioms Cb.Tw.Sig3.msgEquiv
#print axioms Cb.Tw.sig3_at
#print axioms Cb.Tw.sig3_know
#print axioms Cb.Tw.sig3Id
#print axioms Cb.Tw.sig3Id_source
