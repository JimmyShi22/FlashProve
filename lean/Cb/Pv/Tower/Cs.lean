-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/Cs.lean: the code switch inside a proximity test (the two rounds "SEND seed" and "CS" of
a plan) whose first prover message bears a rider: an oracle that a later block would send (the next
fold's fresh mask, the last step's masking word) lies in the same string of columns as the new word.
A typed reduction of two rounds; the statement that it is round-by-round knowledge sound, proved
under conditions on codes and numbers that no file here shows of any setting.

The block holds both rounds: the sending of the new word, answered by the seed of the sample; then
the answers in the clear, answered in one verifier message by t long positions of the old word and
the seed of the batching. These are the library's own two rounds (`LdSw.sh`, Cb/Ld/LdSwitch.lean),
but that the first round's oracle is a string of columns (`LdSw.shC`, Cb/Ent/FoldRide.lean;
`ColLay`, Cb/Ent/ColRound.lean). The verifier is the library's own (`ldSwitch D`) on the transcript
in which the new word is cut out of the columns. The new implicit instance is the pair (new word,
rider); the output joint is the library's joint of the new word read on the first component
(`IOR.Rels.keepE`, Ior/Frame.lean): it asks nothing of the rider. The last step takes that joint as
its input joint (`cs_base_seam`); the next fold does so behind the cut of the form, which hands the
rider on (`cs_stage_seam`, Cb/Pv/Tower/Stage.lean).

A rider here is an oracle without a sample; Cb/Ld/LdGroupNewRide.lean uses the word for sampled
oracle messages of a next part.

Main names (D : `LdSw E P P' St`; Cw: the rider's code; Pt, lf, lfW: the leaves, and in which leaf a
native position of the new word, of the rider, lies: all letters):
  `csRide D Cw Pt lf lfW`: the reduction. `csOut D Cw e'`: its output joint,
    `(D.jOut e').rels.keepE Cw.nat`; its input joint is `(D.jIn e).rels`. `csErr`: the library's two
    error counts. The extractor is the library's (`D.back`).
  `CsKnow D Cw Pt lf lfW e e' L`: round-by-round knowledge soundness of `csRide`, and nothing else.
  `cs_know`: it holds under `D.HypK e' L` (Cb/Ent/TowerKnow.lean: the old code's laws, lists of the
    new code at the radius e' at most L, the laws of sample and batching).
  `cs_point` (finitely many leaves), `cs_isLocal` (under `D.Cout.Reads`), `cs_onOut`, `cs_errList`.
  `CsKnow₁`, `cs_know₁`: the same clause for the library's own block, without a rider.
  `cs_base_seam`: with the last step's masking word as the rider, the output joint is the last
    step's input joint.
  `cs_out`: the verifier in closed form: it never rejects. `cs_imp`: the new implicit instance: the
    new word and the rider, cut out of the columns. `cs_rounds`, `cs_vals`: two rounds; the numbers
    of values of the verifier's messages.
  `CsSize E`, `s.H`, `s.H₁`, `s.OK`, `s.h`, `s.h₁`: what is public of a code switch as one record;
    the two statements at a size; the conditions; the statements hold under them. `s.OKLocal`,
    `s.isLocal`: the condition for locality, which is no part of `s.OK`. In `s.H₁` the rider's code
    and the leaves are idle.

Limits: knowledge soundness and the verifier's format alone: nothing on an honest prover. No tree,
no hash: how a string of columns is committed to is the compiler's matter. Nothing says that L and
the two error counts are small. The errors are bare counts for one instance: nothing on proof of
work, nothing on several instances. lf and lfW are any maps: that they are the layout of a program's
leaves is not said here. One new word and one sample: a switch that sends further oracle messages
anew, each with its own sample, is not treated.

-/
import Cb.Ent.FoldRide
import Cb.Ent.TowerKnowProofs
import Cb.Ld.LdSwitchProofs
import Cb.Pv.Tower.Base
import Cb.Pv.Rider

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Cb.Pv.Tower
open Iop Prob IOR Blocks

variable {E P P' Pw St : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
  [Nonempty P'] (D : LdSw E P P' St) (Cw : LdCode E Pw) (Pt : Type) (lf : D.Cout.NP → Pt)
  (lfW : Cw.NP → Pt)

/-- The transcript of the library's switch: the new word cut out of the columns. -/
def csUp (τ : Tr (D.shC Cw Pt lf lfW)) : Tr D.sh :=
  (D.colL Cw Pt lf lfW).up (D.Cout.sendPoint _ _ _) τ

open Classical in
/-- The code switch whose first message bears a rider. -/
def csRide : IOR (E × St) D.Cin.ext (E × D.St') (D.Cout.ext.prod Cw.nat) where
  shape := D.shC Cw Pt lf lfW
  blinded _ := true
  extReads ρ := Finset.univ.image ρ.2.1.1
  reads _ := ∅
  out x y τ := (ldSwitch D).out x y (csUp D Cw Pt lf lfW τ)
  imp y τ := ((ldSwitch D).imp y (csUp D Cw Pt lf lfW τ), D.riderC Cw Pt lf lfW τ)
  srcE _ _ := ∅
  srcO _ q := match q with
    | .inl q => (D.Cout.src q).image fun n => Sum.inl (lf n)
    | .inr p => {Sum.inl (lfW p)}
  tie _ _ := ∅

/-- The output joint: the joint of the new word; nothing is asked of the rider. -/
def csOut (e' : ℕ) : IOR.Rels Unit (E × D.St') (D.Cout.ext.prod Cw.nat) (D.jOut e').W :=
  (D.jOut e').rels.keepE Cw.nat

/-- The library's two error counts. -/
def csErr (e L : ℕ) : Err (D.shC Cw Pt lf lfW) := (D.W.err1 L, (D.W.err2 e L, ()))

/-- Round-by-round knowledge soundness of the code switch that bears a rider. -/
def CsKnow (e e' L : ℕ) : Prop :=
  (csRide D Cw Pt lf lfW).red.Know (D.jIn e).rels.on (D.jIn e).rels.relR (csOut D Cw e').relR
    (fun _ _ w' => D.back w') (csErr D Cw Pt lf lfW e L)

/-- The same clause for the library's own block, without a rider. -/
def CsKnow₁ (e e' L t' : ℕ) : Prop := (ldSwBlock D e e' L t').KnowT

theorem cs_know₁ (e e' L t' : ℕ) (h : D.HypK e' L) : CsKnow₁ D e e' L t' :=
  ldEnt_switch_know E P P' St D e e' L t' h

theorem cs_know (e e' L : ℕ) (h : D.HypK e' L) : CsKnow D Cw Pt lf lfW e e' L := by
  intro a ha
  refine Doomed.mono _ _ ?_
    (doomed_col (D.colL Cw Pt lf lfW) (D.Cout.sendPoint _ _ _) _ _ _ _
      (ldEnt_switch_know E P P' St D e e' L 0 h a ha))
  intro τ hτ b w hb hw
  obtain rfl := Option.some.inj hb
  exact hτ _ w rfl hw

omit [Fintype E] [Fintype P'] [Nonempty P'] in
theorem cs_point [Fintype Pt] [DecidableEq Pt] :
    Nonempty (csRide D Cw Pt lf lfW).shape.IsPoint :=
  ⟨(@colPoint _ _ (D.colL Cw Pt lf lfW) (inferInstanceAs (Fintype Pt))
      (inferInstanceAs (DecidableEq Pt)), plainPoint _ _ _, ())⟩

theorem cs_onOut (e e' : ℕ) : ∀ a τ b, (D.jIn e).rels.on a →
    (csRide D Cw Pt lf lfW).red.out a τ = some b → (csOut D Cw e').on b :=
  fun _ _ _ _ _ => trivial

omit [Fintype E] [Fintype P'] [Nonempty P'] in
theorem cs_isLocal (hR : D.Cout.Reads) : (csRide D Cw Pt lf lfW).IsLocal where
  out := by
    intro x y y' τ τ' hρ hpl hy _
    exact (ldSwitch_isLocal D hR).out x y y' (csUp D Cw Pt lf lfW τ) (csUp D Cw Pt lf lfW τ') hρ
      hpl hy fun p hp => absurd hp (Finset.notMem_empty p)
  imp := by
    classical
    intro y y' τ τ' q _ _ _ hτ
    rcases q with q | p
    · refine congrArg Sum.inl (hR _ _ q fun n hn => ?_)
      have h := hτ (Sum.inl (lf n)) (Finset.mem_image.2 ⟨n, hn, rfl⟩)
      exact congrFun (congrArg Prod.fst h) ⟨n, rfl⟩
    · have h := hτ (Sum.inl (lfW p)) (Finset.mem_singleton.2 rfl)
      exact congrArg (fun z => Sum.inr (⟨p, z⟩ : Σ p, Cw.NS p → E))
        (congrFun (congrArg Prod.snd h) ⟨p, rfl⟩)

omit [Fintype E] [Fintype P'] [Nonempty P'] in
theorem cs_errList (e L : ℕ) :
    (csErr D Cw Pt lf lfW e L).toList = [D.W.err1 L, D.W.err2 e L] := rfl

omit [Fintype P] [Nonempty P] in
/-- The seam to the last step: its masking word as the rider. -/
theorem cs_base_seam (e' : ℕ) : csOut D D.Cout e' = baseIn (D.jOut e') := rfl

omit [Fintype E] [Fintype P'] [Nonempty P'] in
/-- The verifier in closed form: the library's new target and new state. It never rejects. -/
theorem cs_out (x : E × St) (y : D.Cin.Word) (τ : Tr (D.shC Cw Pt lf lfW)) :
    (csRide D Cw Pt lf lfW).out x y τ =
      some (D.W.tgt' x.1 τ.2.2.1.2 (D.Cin.T y) τ.2.2.2.1,
        (D.stOf x.2 τ.2.1 τ.2.2.2.1.1, τ.2.2.2.1.2)) := rfl

omit [Fintype E] [Fintype P'] [Nonempty P'] in
/-- The new implicit instance: the new word and the rider, cut out of the columns. -/
theorem cs_imp (y : D.Cin.Word) (τ : Tr (D.shC Cw Pt lf lfW)) :
    (csRide D Cw Pt lf lfW).imp y τ =
      ((D.colL Cw Pt lf lfW).main (D.Cout.sendPoint _ _ _) τ.1.1, D.riderC Cw Pt lf lfW τ) := rfl

omit [Fintype E] [Fintype P'] [Nonempty P'] in
theorem cs_rounds : (csRide D Cw Pt lf lfW).shape.length = 2 := rfl

omit [Fintype E] [Fintype P'] [Nonempty P'] in
theorem cs_vals : (csRide D Cw Pt lf lfW).shape.chalList =
    [Fintype.card D.Zo.D, Fintype.card ((Fin D.t → P) × D.Zb.D)] := rfl

/-! ### the statement at a size -/

/-- What is public of a code switch: the library's data D, the rider's code, the leaves (finitely
many), and the numbers of the statement: the radii e before and e' after, the list size L. -/
structure CsSize (E : Type) where
  P : Type
  P' : Type
  Pw : Type
  St : Type
  [finP : Fintype P]
  [neP : Nonempty P]
  [finP' : Fintype P']
  [neP' : Nonempty P']
  D : LdSw E P P' St
  Cw : LdCode E Pw
  Pt : Type
  [finPt : Fintype Pt]
  [decPt : DecidableEq Pt]
  lf : D.Cout.NP → Pt
  lfW : Cw.NP → Pt
  e : ℕ
  e' : ℕ
  L : ℕ

attribute [instance] CsSize.finP CsSize.neP CsSize.finP' CsSize.neP' CsSize.finPt CsSize.decPt

variable (s : CsSize E)

/-- The statement that CS that bears a rider, at the size s, is knowledge sound. -/
def CsSize.H : Prop := CsKnow s.D s.Cw s.Pt s.lf s.lfW s.e s.e' s.L

/-- The statement that CS without a rider, at the size s, is knowledge sound. -/
def CsSize.H₁ : Prop := CsKnow₁ s.D s.e s.e' s.L 0

/-- Conditions, as in the library's theorem on the switch, on public data alone. -/
def CsSize.OK : Prop := s.D.HypK s.e' s.L

/-- The condition for locality: the new code's transformation reads what it declares. -/
def CsSize.OKLocal : Prop := s.D.Cout.Reads

theorem CsSize.h (h : s.OK) : s.H := cs_know s.D s.Cw s.Pt s.lf s.lfW s.e s.e' s.L h

theorem CsSize.h₁ (h : s.OK) : s.H₁ := cs_know₁ s.D s.e s.e' s.L 0 h

omit [Fintype E] in
theorem CsSize.isLocal (h : s.OKLocal) : (csRide s.D s.Cw s.Pt s.lf s.lfW).IsLocal :=
  cs_isLocal s.D s.Cw s.Pt s.lf s.lfW h

#print axioms CsSize.h
#print axioms CsSize.h₁
#print axioms cs_isLocal

end Cb.Pv.Tower
