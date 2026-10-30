-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Ride.lean: the masked sumcheck with short messages and with n further scalars in its
first message, as a block with knowledge soundness, for all parameters of the general sumcheck
(PscPar).

Why. In the programs a group of scalars that the prover sends has no round of its own: the scalars
stand in the message of the next round that is closed (OnBytes/Params/Planner.lean, planScalars).
In an attention sub-proof that round is mostly the first round of a sumcheck. The scalars are sent
before the sumcheck's first challenge is drawn, and the sumcheck's claim (its target and its
public state) may depend on them.

Main names:
  rRoundN, shapeRN: the rounds: a first message of n + 1 scalars (the n further scalars, then the
    sum of the hiding polynomial) and a challenge; one short round for each variable; the values.
  rideNR Y n F cl Ex: the block. At the statement x and the further scalars r it is the short
    sumcheck (Cb/G6/Carried.lean, shortR) at the claim cl x r. It puts out x, r and the short
    sumcheck's output.
  rideNIn, rideNOut: its joints, with two parameters: A0, a joint on the caller's statements that
    is carried along, and Θ x r m, what the caller says of the further scalars. Before the block:
    A0, and there are scalars r with Θ x r m for which the sum claim cl x r holds of m. Behind it:
    A0, Θ x r m and the sumcheck's output claims, where r are the scalars that were sent.
  rideN_doomed: for each fixed tuple of entries m, whichever scalars the prover sends, either the
    sum claim at them holds of m, or whatever the verifier puts out is false of m, but for the
    errors of the long sumcheck.
  rideN_knowAt: knowledge soundness in the form KnowAt, under the three conditions of the general
    sumcheck (VarsOK, DegOK, ValInj). There is no condition on F, Θ or cl.
  rideN_nums: the list of its errors. The numbers are counts of challenge values.
  rideN_out: at a lawful choice F (HFixs.OK) the verifier rejects nothing, and what it puts out.

The proof of rideN_doomed follows the case of one further scalar, the target itself, in
Cb/G6/Johnson/Layers/Ride.lean.

Limits. The entries m are fixed before the block's first message. A map that reads a message sent
behind the block is not covered: such a map must first be written as a function of entries fixed
before. At a choice F that is not lawful the verifier may reject, and knowledge soundness then
says the less. The block tests nothing of the further scalars: Θ x r m stands in the joint behind
the block as a claim that whoever follows must discharge. In the programs the target of a sumcheck
with further scalars is the public part of a form in them. The chain's conclusion then has content
only through Θ: Θ x r m must say of each further scalar what every other claim that names it says
(of the value r j less its factor times its mask entry). With Θ always true and a target that is
itself one of the further scalars, the relation before the block adds nothing to A0. Nothing is
said on an honest prover or on hiding. The file does not say which coefficient the programs leave
out, nor that the port's routine computes this block's output.

-/
import Cb.G6.Pick
import Cb.G6.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole Johnson.L5.Layers Johnson.L5.Door

variable {E : Type} [Field E] [Fintype E]

/-- round 0 with n scalars riding before μ; then ε from all of E -/
@[reducible] def rRoundN (E : Type) [Field E] [Fintype E] (n : ℕ) : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim,
    Plain := (Fin n → E) × E, Chal := E, dOrc := (), dPlain := (0, 0) }

def rRoundN_point (n : ℕ) : (rRoundN E n).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

variable (Y : PscPar E) (n : ℕ)

abbrev shapeRN : Shape := rRoundN E n :: (sRounds Y.fmt ++ [pRoundV E Y.A])

def riders (t : Tr (shapeRN Y n)) : Fin n → E := t.1.2.1
def unrideN (t : Tr (shapeRN Y n)) : Tr (shapeS Y) := (((), t.1.2.2), t.2.1, t.2.2)

theorem noOrc_RN : NoOrc (shapeRN Y n) :=
  ⟨inferInstanceAs (Subsingleton Unit),
    noOrc_s Y.fmt _ ⟨inferInstanceAs (Subsingleton Unit), trivial⟩⟩

variable (F : ∀ st, HFixs (Y.vars st)) {X : Type} (cl : X → (Fin n → E) → E × Y.St) (Ex : ExtSpec)

/-- The block as a term. -/
noncomputable def rideNR : IOR X Ex ((X × (Fin n → E)) × Y.Out) Ex where
  shape := shapeRN Y n
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x y τ =>
    ((shortR Y F Ex).out (cl x (riders Y n τ)) y (unrideN Y n τ)).map fun o =>
      ((x, riders Y n τ), o)
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- its errors: the short block's, number for number -/
noncomputable def rideNE : Err (shapeRN Y n) := shortE Y Ex

theorem rideN_nums : errList (rideNE Y n Ex) = 1 :: (Y.fmt.map PFmt.n ++ [0]) := shortE_nums Y Ex

/-- At a lawful choice the verifier rejects nothing. -/
theorem rideN_out (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (x : X) (y : Ex.Str)
    (τ : Tr (shapeRN Y n)) :
    (rideNR Y n F cl Ex).out x y τ =
      some ((x, riders Y n τ), shortV Y F (cl x (riders Y n τ)) (unrideN Y n τ)) := by
  show ((shortR Y F Ex).out _ y _).map _ = _
  rw [short_out Y F Ex hF]
  rfl

theorem rideN_doomed (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) (x : X) (y : Ex.Str)
    (m : Y.J → E) :
    Doomed (shapeRN Y n) (rideNE Y n Ex) fun t =>
      ¬ Y.SumHolds (cl x (riders Y n t)) m →
        ∀ o, (shortR Y F Ex).out (cl x (riders Y n t)) y (unrideN Y n t) = some o →
          ¬ Y.OutHolds o m :=
  fun msg => by
    by_cases h : Y.SumHolds (cl x msg.2.1) m
    · rw [cnt_false fun c hc => hc (Doomed.of_forall _ _ fun t hn => absurd h hn)]
      exact Nat.zero_le _
    · exact le_trans (cnt_mono fun c hc hd => hc (Doomed.mono _ _ (fun t ht _ => ht) hd))
        (short_doomed Y Ex hV hD hI (cl x msg.2.1) (F (cl x msg.2.1).2) y m h ((), msg.2.2))

variable {M Wp Kc : Type} (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → Y.J → E)
  (Θ : X → (Fin n → E) → (Y.J → E) → Prop)

/-- Its two joints. -/
def rideNIn : IOR.Rels Kc X Ex (M × Wp) :=
  ⟨fun x y w => A0.rel x y w ∧ ∃ r, Θ x r (msg w.1) ∧ Y.SumHolds (cl x r) (msg w.1),
    fun a w => A0.relR a w ∧ ∃ r, Θ a.1 r (msg w.1) ∧ Y.SumHolds (cl a.1 r) (msg w.1),
    A0.on, A0.core⟩
def rideNOut : IOR.Rels Kc ((X × (Fin n → E)) × Y.Out) Ex (M × Wp) :=
  ⟨fun b y w => A0.rel b.1.1 y w ∧ Θ b.1.1 b.1.2 (msg w.1) ∧ Y.OutHolds b.2 (msg w.1),
    fun a w => A0.relR (a.1.1.1, a.2) w ∧ Θ a.1.1.1 a.1.1.2 (msg w.1) ∧ Y.OutHolds a.1.2 (msg w.1),
    fun a => A0.on (a.1.1.1, a.2), A0.core⟩

/-- Knowledge soundness. -/
theorem rideN_knowAt (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj) :
    KnowAt (rideNR Y n F cl Ex) (rideNIn Y n cl Ex A0 msg Θ) (rideNOut Y n Ex A0 msg Θ)
      (fun _ _ _ wp => wp) (rideNE Y n Ex) where
  point := ⟨(rRoundN_point n, sRounds_point Y.fmt _ (pRoundV_point Y.A, ()))⟩
  isLocal :=
    { out := fun x y y' τ τ' h1 h2 _ _ => by
        rw [tr_ext (noOrc_RN Y n) τ τ' h1 h2]
        show ((shortR Y F Ex).out _ y _).map _ = ((shortR Y F Ex).out _ y' _).map _
        rw [(short_local Y F Ex).out _ y y' _ _ rfl rfl (fun p hp => absurd hp (by
          show p ∉ (∅ : Finset _)
          simp)) fun _ _ => rfl]
      imp := fun y y' _ _ q _ _ h _ => h q (Finset.mem_singleton_self q) }
  onOut := fun a τ b ha hb => by
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 hxo
    exact ha
  know := fun m a _ => by
    refine Doomed.mono _ _ ?_ (rideN_doomed Y n F cl Ex hV hD hI a.1 a.2 (msg m))
    intro τ hτ b wp hb hB
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hxo
    have hs : Y.SumHolds (cl a.1 (riders Y n τ)) (msg m) := by
      by_contra hn
      exact hτ hn o ho hB.2.2
    exact ⟨hB.1, riders Y n τ, hB.2.1, hs⟩

end Cb.Pv.Att
