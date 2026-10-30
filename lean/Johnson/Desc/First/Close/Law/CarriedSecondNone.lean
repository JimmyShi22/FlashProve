-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/CarriedSecondNone.lean (kind K10): WHERE NO MESSAGE OF THE LIST IS
CARRIED PAST THE BATCHING, THE SECOND CONJUNCT OF `CarriedAt` (Leads.lean, beside this file) ASKS
NOTHING BUT THE JOINT's SHARE; AND AT WHICH WRITTEN LISTS THAT CAN BE SO. Definitions with code,
statements and proofs.

Why. kp o := "o is no member of the group, or o is marked keep" (Cb/Pv/Bat.lean). keep is a letter
of the
law (which messages the batching's joint hands on): by a reading, not shown here, it stands in no
frozen condition. At keep := nobody, kp holds of the messages that are no members alone. The group's
members are the list's messages with a main row (memMain).

What is said.
  `carried_second_none`: no message has kp (hnone) · any seed · v₂ with hA (the joint A₀'s relaxed
    relation at x's letters, of the family over the empty set of names, and v₂): the conjunct.
  `kp_none`: at keep := fun _ => False, where every message of the signature is a member of the
    group: no message has kp.
  `allMainB ls`: every message of every list of ls has a main row. `allMain_later`: **BY THE KERNEL:
    yes at all written lists but the first.** `allMain_first`: THE NEGATIVE LINE: at the first
    written list: no (it holds a message without a main row).

SO, by these: at the links 1 and on, at keep := nobody, the conjunct is the joint's share alone. AT
THE FIRST LINK IT IS NOT: the message without a main row has kp WHATEVER keep IS, and must decode at
what fa lays.

Limits. THAT keep MAY BE CHOSEN SO WHERE THE LAW IS SPENT, AND WHAT THE LAW's END THEN STILL GIVES,
IS NOT SHOWN HERE: it is held only when who composes the law has built it at that choice. hA is a
premise. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.CarriedSecond
import Johnson.G.SwitchKeptLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj OnBytes.Flat
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H

section
variable {S : Sig GE} (R : RowsK S) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **Where no message is carried past the batching.** -/
theorem carried_second_none (L : List (BatFoldCaller GE))
    (x : ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (hnone : ∀ o, ¬ (R.sizeB keep Sb sl Z).kp o) (z₀ : Z.D) (v₂ : Wp)
    (hA : A₀.relR (x.1.1.2, x.2.1.1) (fun i => absurd i.2 (hnone i.1), v₂)) :
    ∃ (z : Z.D) (v : (S.sub (R.sizeB keep Sb sl Z).kp).Wit × Wp),
      ((S.sub (R.sizeB keep Sb sl Z).kp).over A₀).relR
        ((batX (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) x.1 z).2,
          ((ldBrG R.G (R.sizeB keep Sb sl Z).kp E₀).map x.2.1).2) v :=
  carried_second_of_decs R keep Sb sl Z fx A₀ bC bZ w₀ w₁ L x z₀
    (fun i => absurd i.2 (hnone i.1)) (fun i => absurd i.2 (hnone i.1)) v₂ hA

end

/-- At keep := nobody, where every message is a member: no message has kp. -/
theorem kp_none {S : Sig GE} (R : RowsK S) {B : Type} [Fintype B] (Sb : B → Type)
    (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) (hall : ∀ o, R.G.mem o) :
    ∀ o, ¬ (R.sizeB (fun _ => False) Sb sl Z).kp o := by
  intro o h
  rcases h with h | h
  · exact h (hall o)
  · exact h

/-- Every message of every list has a main row. -/
def allMainB (ls : List (List (OracleShape × ℕ))) : Bool :=
  ls.all fun lo => lo.all fun y => y.1.mainRows != 0

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL: at all written lists but the first.** -/
theorem allMain_later : allMainB (Johnson.G.linksFullLit.drop 1) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line: the first written list holds a message without a main row. -/
theorem allMain_first : allMainB (Johnson.G.linksFullLit.take 1) = false := by decide +kernel

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.carried_second_none
#print axioms VerifiableInference.Desc.First.Close.kp_none
#print axioms VerifiableInference.Desc.First.Close.allMain_later
#print axioms VerifiableInference.Desc.First.Close.allMain_first
