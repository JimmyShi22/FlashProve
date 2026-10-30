-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Tidy.lean: every text of the lookup's hearing
(Johnson/Desc/First/Look/Via/Rounds.lean), wherever it returns from a ledger whose arrays have their
size, has changed no slot's mark at or above the count of slots that it leaves. Theorems, with
one class and one structure.

Terms. Honest/K3/GLOSSARY.md ("hearing", "ledger", "slot").

What is shown.
  `Tidy x`: the class: wherever x returns from a ledger whose arrays have their size, its ledger is
    later (Honest/K3/Law/GoesOn.lean), and from its count of slots on every slot is filled just if
    it was filled in front.
  Instances of the class: as in GoesOn.lean, text by text.
  `Reach F G`, `Reach.refl`, `Tidy.step`: the two clauses as one sentence on two ledgers, and how a
    walk through a "do" text carries it from piece to piece.
  `hear_low`, `whole_low`: the masked sumcheck's two texts.
  `hearV_reach`: the same for `hearV`.
Helpers: `Reach.trans`, `tidy_of_same`, `Tidy.bind`, `tidy_foldlM`, `level_low`, `turn_low`,
`fold_low`, `tidy_partsV`, `tidy_keysV`. A local tactic macro "tidy" is used in proofs alone.

Hypotheses that remain. The return of the text in question (`e` in `Tidy.step`, `hh` in `hear_low`,
`hw` in `whole_low`, `h` in `hearV_reach`, `level_low` and `turn_low`). `hS`: the first ledger's
arrays have their size (`Sized`). In `Tidy.step`: `P`: the sentence `Reach` holds from the first
ledger to the one in front of the piece. In `Reach.trans`: `h`, `h'`: the two sentences that are
joined. In `tidy_of_same`: `h`: wherever the text returns, it returns the ledger that it was given.
In `Tidy.bind` and `tidy_foldlM`: `hx`, `hf`: the texts that are composed are in the class. In
`fold_low` the size of the first ledger's arrays and the return stand without a name, in front of
arrows.

Why. A ledger's slots are dealt in the order of sending. So what is free above the count in front
of a text stays free above the count behind it, however far that freedom reaches: no hypothesis on
the whole ledger above the count is needed.

Users. This file is imported by Honest/K3/Law/LeavesFree.lean.

Limits. "If it returns": nothing here says that a text returns.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.GoesOn
import Johnson.Desc.Part.MaskedSumFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV)
open VerifiableInference.Desc.First.ProdV (LevelOut level turn Carried)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)

variable {α β γ : Type}

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run
local notation "VFace" => VerifiableInference.Desc.K3.Face

/-- **G is later than F, and from G's count of slots on a slot is filled in G just if it
is in F.** The library's `Reach` (Johnson/Top/H0/Walk/Reach.lean) is another thing: a relation
between a border of a list of sub-protocols and a state; other files of this folder (for one,
Law/Total/DigitsFormsNew.lean) use that short name for the library's. -/
structure Reach (F G : Fork) : Prop where
  later : Later F G
  low : ∀ j, G.next ≤ j → (Filled G j ↔ Filled F j)

theorem Reach.refl (F : Fork) : Reach F F := ⟨Later.refl F, fun _ _ => Iff.rfl⟩

theorem Reach.trans {F G H : Fork} (h : Reach F G) (h' : Reach G H) : Reach F H :=
  ⟨h.later.trans h'.later, fun j hj =>
    (h'.low j hj).trans (h.low j (Nat.le_trans h'.later.next hj))⟩

/-- **Wherever x returns from a ledger whose arrays have their size, it reaches its ledger.** -/
class Tidy (x : Hr α) : Prop where
  reach : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) → Sized F →
    Reach F G

/-- A walk's step: from the first ledger to the one behind the next piece. -/
theorem Tidy.step {x : Hr α} [Tidy x] {F F' G : Fork} {rs rest : List Fmt.RoundView} {a : α}
    (e : x F' rs = some (a, G, rest)) (hS : Sized F) (P : Reach F F') : Reach F G :=
  P.trans (Tidy.reach e (P.later.sized hS))

/-! ## "do" -/

/-- A text that leaves the ledger as it is. -/
theorem tidy_of_same {x : Hr α}
    (h : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) → G = F) :
    Tidy x := ⟨fun e _ => by rw [h e]; exact Reach.refl _⟩

instance tidy_pure (a : α) : Tidy (pure a : Hr α) :=
  tidy_of_same fun {F G rs rest b} e => by
    have e' : some (a, F, rs) = some (b, G, rest) := e
    cases e'
    rfl

theorem Tidy.bind {x : Hr α} {f : α → Hr β} (hx : Tidy x) (hf : ∀ a, Tidy (f a)) :
    Tidy (x >>= f) :=
  ⟨fun e hS => by
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some e
    have r1 := hx.reach h1 hS
    exact r1.trans ((hf a).reach h2 (r1.later.sized hS))⟩

instance tidy_bind (x : Hr α) (f : α → Hr β) [Tidy x] [∀ a, Tidy (f a)] : Tidy (x >>= f) :=
  Tidy.bind inferInstance inferInstance

instance tidy_ite (p : Prop) [Decidable p] (x y : Hr α) [Tidy x] [Tidy y] :
    Tidy (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each "if" and each pattern. -/
local macro "tidy" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Tidy.bind ?_ ?_
    | intro _
    | split)

theorem tidy_foldlM {f : β → γ → Hr β} (hf : ∀ s a, Tidy (f s a)) :
    ∀ (l : List γ) (s : β), Tidy (l.foldlM f s)
  | [], s => by
    show Tidy (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show Tidy (f s a >>= fun s' => l.foldlM f s')
    exact Tidy.bind (hf s a) fun s' => tidy_foldlM hf l s'

/-! ## The small texts -/

instance tidy_slot : Tidy Hr.slot := tidy_of_same fun e => (slot_spec e).2

instance tidy_must (b : Bool) : Tidy (Hr.must b) := tidy_of_same fun e => (must_spec e).2

instance tidy_owe (what : String) : Tidy (Hr.owe what) :=
  ⟨fun {F G rs rest a} e _ => by
    refine ⟨GoesOn.later e, ?_⟩
    have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
    cases e'
    exact fun _ _ => Iff.rfl⟩

instance tidy_drawsV (n : Nat) : Tidy (drawsV n) := tidy_of_same fun e => drawsV_same e

instance tidy_drawV : Tidy drawV :=
  tidy_of_same fun {F G rs rest a} e => by
    unfold drawV at e
    split at e
    · rename_i x G' rest' hx
      split at e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact drawsV_same hx
      · exact nomatch e
    · exact nomatch e

/-! ## The masked sumcheck, and the product levels -/

theorem hear_low {C : Aff} {k : MaskedSum.Call} {F G : Fork} {rs : List Fmt.RoundView}
    {h : MaskedSum.Heard} (hS : Sized F) (hh : MaskedSum.hear C k F rs = some (h, G)) :
    Reach F G :=
  ⟨MaskedSum.hear_keeps hh, fun j hj =>
    MaskedSum.hear_fills hS hh j (Or.inr (by rw [MaskedSum.hear_next hS hh] at hj; exact hj))⟩

theorem whole_low {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff} (hS : Sized F)
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) : Reach F G := by
  obtain ⟨_, Gm, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  have r1 := hear_low hS hh
  have Sm := r1.later.sized hS
  obtain ⟨e1, _, e3⟩ := MaskedSum.heard_lenK hh
  have nm := MaskedSum.hear_next hS hh
  have n2 := MaskedSum.row_next Sm hr
  refine r1.trans ⟨MaskedSum.row_keeps hr, fun j hj => MaskedSum.row_fills Sm hr j (Or.inr ?_)⟩
  rw [e1, e3]
  omega

instance tidy_sumV (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    Tidy (sumV C k endTerm) := ⟨fun e hS => whole_low hS (sumV_whole e)⟩

instance tidy_openV (C : Aff) (vs : List MaskedSum.Var) : Tidy (openV C vs) :=
  ⟨fun e hS => hear_low hS (openV_hear e)⟩

theorem level_low {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (hS : Sized F)
    (h : level m z order C F rs = some (o, G, rest)) : Reach F G := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          exact whole_low hS hw
      · exact nomatch h
    · exact nomatch h

theorem turn_low {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} (hS : Sized F) (h : turn order s m F rs = some (s', G, rest)) :
    Reach F G := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_low hS hx

theorem fold_low (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat)
    (x y : Carried × Fork × List Fmt.RoundView), Sized x.2.1 →
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → Reach x.2.1 y.2.1
  | [], x, y, _, h => by
    obtain rfl : x = y := Option.some.inj h
    exact Reach.refl _
  | i :: l, x, y, hS, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    have r1 := turn_low hS hz
    exact r1.trans (fold_low m0 orders l _ y (r1.later.sized hS) h)

instance tidy_run (m0 n : Nat) (orders : Nat → List Nat) (s : Carried) :
    Tidy (Hr.of (vRun m0 n orders s)) :=
  ⟨fun {F G rs rest a} e hS => fold_low m0 orders _ (s, F, rs) (a, G, rest) hS e⟩

/-! ## The lookup's own texts -/

instance tidy_tieV (w : Nat) (a : E) : Tidy (tieV w a) := by
  unfold tieV
  refine Tidy.bind inferInstance fun x => ?_
  refine Tidy.bind (tidy_foldlM (fun s _ => by tidy) _ _) fun _ => ?_
  infer_instance

theorem tidy_partsV : ∀ (n : Nat) (rows : Array Aff) (C : Aff), Tidy (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine Tidy.bind inferInstance fun w => ?_
    refine Tidy.bind (tidy_partsV n _ _) fun _ => ?_
    infer_instance

instance (n : Nat) (rows : Array Aff) (C : Aff) : Tidy (partsV n rows C) := tidy_partsV n rows C

theorem tidy_keysV (f : VFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff),
    Tidy (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine Tidy.bind inferInstance fun k => ?_
    refine Tidy.bind (tidy_keysV f xs Cs _) fun _ => ?_
    infer_instance

instance (f : VFace) (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff) :
    Tidy (keysV f xs Cs rows) := tidy_keysV f xs Cs rows

/-- **The lookup's rounds, heard in order.** -/
instance tidy_messagesV (f : VFace) : Tidy (messagesV f) := by
  unfold messagesV
  tidy

/-- **Where the lookup's hearing returns, it has changed no mark from its count of slots on.**
Conditional on the return of `hearV` and on the first ledger's arrays having their size. -/
theorem hearV_reach {f : VFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (h : hearV f F rs = some (g, G)) : Reach F G :=
  (tidy_messagesV f).reach (hearV_messages h).2 hS

#print axioms ProofFile.Honest.K3.Law.Reach.refl
#print axioms ProofFile.Honest.K3.Law.Reach.trans
#print axioms ProofFile.Honest.K3.Law.Tidy.step
#print axioms ProofFile.Honest.K3.Law.tidy_of_same
#print axioms ProofFile.Honest.K3.Law.Tidy.bind
#print axioms ProofFile.Honest.K3.Law.tidy_foldlM
#print axioms ProofFile.Honest.K3.Law.hear_low
#print axioms ProofFile.Honest.K3.Law.whole_low
#print axioms ProofFile.Honest.K3.Law.level_low
#print axioms ProofFile.Honest.K3.Law.turn_low
#print axioms ProofFile.Honest.K3.Law.fold_low
#print axioms ProofFile.Honest.K3.Law.tidy_partsV
#print axioms ProofFile.Honest.K3.Law.tidy_keysV
#print axioms ProofFile.Honest.K3.Law.tidy_messagesV
#print axioms ProofFile.Honest.K3.Law.hearV_reach

end ProofFile.Honest.K3.Law
