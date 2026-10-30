-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Packs.lean: conditional: from the hearing's return, on any
rounds, at any face: behind the lookup's hearing a value lies under every slot of the lookup's
window but the leaves' own; and the ledger's list of owed claims has the lookup's three. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there hearing, ledger, slot, sumcheck, leaves and key tree. In
this file: the lookup's window is the stretch of slots that the lookup takes; a text is a function
of the hearing's type `Hr`.

What is shown.
  `Pack F G`: G is later than F, and every slot from the count of slots of F on and below that of G
    is filled in G.
  `Packs x`: wherever the text x returns from a ledger whose arrays have their size, it packs; with
    instances for "do", for the small texts, the masked sumcheck heard whole, the product levels,
    and the lookup's own pieces but the sumcheck that is left open.
  `whole_pack`: the basic fact: a masked sumcheck that is heard whole fills the slots of its end
    values at the hearing and its own at the row.
  `heard_full`, `hearV_full`: behind the hearing every slot of the window is filled but the own
    slots of the leaves' sumcheck.
  `heard_full`, `hearV_owed3`: the list of owed claims has grown by three at least: so the three
    debts' numbers name claims of the list.

Hypotheses that remain.
  `hS`: the first ledger's arrays have their size (`Sized`).
Besides, the hearing's return (`h`, `hh`). In the steps: `h`, `h'`, `P`: `Pack`; `hx`, `hf`: the
texts that are joined are `Packs`; `e`, `hw`, `h`: the routine returns; `h`: (in `Longer.size_le`)
`Longer`. `h`: (in `packs_of_same`) the text leaves the ledger as it was.

Users. Honest/K3/Parts/KeyLeft.lean, Honest/K3/Law/Thread/K3Keeps.lean and
Honest/K3/Law/Thread/PadNamesOf.lean [not in this library] import this file.

Limits. All statements are implications. It says that a value lies under a slot, not which.
An instance: Honest/K3/Parts/PacksGuards.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.LeavesFree
import Johnson.Desc.ProofFile.Honest.K3.Law.DigitsBehind
import Johnson.Desc.Part.MaskedSumFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call ownSlots)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV leafVars)
open VerifiableInference.Desc.First.ProdV (LevelOut level turn Carried)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Digits (Longer Owes owe_spec)

variable {α β γ : Type}

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

/-! ## 1 The relation -/

/-- **G is later than F, and every slot from F's count of slots on and below G's is filled in G.**
-/
structure Pack (F G : Fork) : Prop where
  later : Later F G
  full : ∀ j, F.next ≤ j → j < G.next → Filled G j

theorem Pack.refl (F : Fork) : Pack F F := ⟨Later.refl F, fun _ a b => absurd b (Nat.not_lt.2 a)⟩

theorem Pack.trans {F G H : Fork} (h : Pack F G) (h' : Pack G H) : Pack F H :=
  ⟨h.later.trans h'.later, fun j a b => by
    by_cases hj : j < G.next
    · exact (h'.later.keep j (h.full j a hj)).1
    · exact h'.full j (Nat.not_lt.1 hj) b⟩

/-- **Wherever x returns from a ledger whose arrays have their size, it packs.** -/
class Packs (x : Hr α) : Prop where
  pack : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) → Sized F →
    Pack F G

/-- A walk's step: from the first ledger to the one behind the next piece. Conditional on the
piece's return. -/
theorem Packs.step {x : Hr α} [Packs x] {F F' G : Fork} {rs rest : List Fmt.RoundView} {a : α}
    (e : x F' rs = some (a, G, rest)) (hS : Sized F) (P : Pack F F') : Pack F G :=
  P.trans (Packs.pack e (P.later.sized hS))

/-! ## 2 "do" -/

/-- A text that leaves the ledger as it is. -/
theorem packs_of_same {x : Hr α}
    (h : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) → G = F) :
    Packs x := ⟨fun e _ => by rw [h e]; exact Pack.refl _⟩

instance packs_pure (a : α) : Packs (pure a : Hr α) :=
  packs_of_same fun e => (pure_spec e).2.1

theorem Packs.bind {x : Hr α} {f : α → Hr β} (hx : Packs x) (hf : ∀ a, Packs (f a)) :
    Packs (x >>= f) :=
  ⟨fun e hS => by
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some e
    have r1 := hx.pack h1 hS
    exact r1.trans ((hf a).pack h2 (r1.later.sized hS))⟩

instance packs_bind (x : Hr α) (f : α → Hr β) [Packs x] [∀ a, Packs (f a)] : Packs (x >>= f) :=
  Packs.bind inferInstance inferInstance

instance packs_ite (p : Prop) [Decidable p] (x y : Hr α) [Packs x] [Packs y] :
    Packs (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each "if" and each pattern. -/
local macro "packs" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Packs.bind ?_ ?_
    | intro _
    | split)

theorem packs_foldlM {f : β → γ → Hr β} (hf : ∀ s a, Packs (f s a)) :
    ∀ (l : List γ) (s : β), Packs (l.foldlM f s)
  | [], s => by
    show Packs (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show Packs (f s a >>= fun s' => l.foldlM f s')
    exact Packs.bind (hf s a) fun s' => packs_foldlM hf l s'

/-! ## 3 The small texts -/

instance packs_slot : Packs Hr.slot := packs_of_same fun e => (slot_spec e).2

instance packs_must (b : Bool) : Packs (Hr.must b) := packs_of_same fun e => (must_spec e).2

instance packs_owe (what : String) : Packs (Hr.owe what) :=
  ⟨fun {F G rs rest a} e _ => by
    refine ⟨GoesOn.later e, ?_⟩
    have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
    cases e'
    exact fun _ a b => absurd b (Nat.not_lt.2 a)⟩

instance packs_drawsV (n : Nat) : Packs (drawsV n) := packs_of_same fun e => drawsV_same e

instance packs_drawV : Packs drawV :=
  packs_of_same fun {F G rs rest a} e => by
    unfold drawV at e
    split at e
    · rename_i x G' rest' hx
      split at e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact drawsV_same hx
      · exact nomatch e
    · exact nomatch e

/-! ## 4 The masked sumcheck heard whole, and the product levels -/

/-- **A masked sumcheck that is heard whole fills all the slots that it takes**: its end values' at
the hearing, its own at the row. Conditional on its return and on the first ledger's arrays having
their size. -/
theorem whole_pack {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff} (hS : Sized F)
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) : Pack F G := by
  obtain ⟨_, Gm, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  have L1 := MaskedSum.hear_keeps hh
  have Sm := L1.sized hS
  have L2 := MaskedSum.row_keeps hr
  obtain ⟨e1, e2, e3⟩ := MaskedSum.heard_lenK hh
  have nm := MaskedSum.hear_next hS hh
  have n2 := MaskedSum.row_next Sm hr
  obtain ⟨_, _, fl, _⟩ := OnBytes.PscRun.hideRun_ok _ _ _ _ _ Sm (MaskedSum.row_write hr)
  refine ⟨L1.trans L2, fun j a b => ?_⟩
  by_cases hj : j < F.next + ownSlots k.all
  · have q := (fl (j - F.next) (by rw [Array.size_replicate, e3]; omega)).2.2.1
    rw [e1, show F.next + (j - F.next) = j by omega] at q
    exact q
  · have q := MaskedSum.hear_ends_filled hS hh (j - h.sEnd) (by rw [e2]; omega)
    rw [show h.sEnd + (j - h.sEnd) = j by rw [e2]; omega] at q
    exact (L2.keep j q).1

instance packs_sumV (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    Packs (sumV C k endTerm) := ⟨fun e hS => whole_pack hS (sumV_whole e)⟩

theorem level_pack {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (hS : Sized F)
    (h : level m z order C F rs = some (o, G, rest)) : Pack F G := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          exact whole_pack hS hw
      · exact nomatch h
    · exact nomatch h

theorem turn_pack {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} (hS : Sized F) (h : turn order s m F rs = some (s', G, rest)) :
    Pack F G := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_pack hS hx

theorem fold_pack (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat)
    (x y : Carried × Fork × List Fmt.RoundView), Sized x.2.1 →
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → Pack x.2.1 y.2.1
  | [], x, y, _, h => by
    obtain rfl : x = y := Option.some.inj h
    exact Pack.refl _
  | i :: l, x, y, hS, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    have r1 := turn_pack hS hz
    exact r1.trans (fold_pack m0 orders l _ y (r1.later.sized hS) h)

instance packs_run (m0 n : Nat) (orders : Nat → List Nat) (s : Carried) :
    Packs (Hr.of (vRun m0 n orders s)) :=
  ⟨fun {F G rs rest a} e hS => fold_pack m0 orders _ (s, F, rs) (a, G, rest) hS e⟩

/-! ## 5 The lookup's own pieces -/

instance packs_tieV (w : Nat) (a : E) : Packs (tieV w a) := by
  unfold tieV
  refine Packs.bind inferInstance fun x => ?_
  refine Packs.bind (packs_foldlM (fun s _ => by packs) _ _) fun _ => ?_
  infer_instance

theorem packs_partsV : ∀ (n : Nat) (rows : Array Aff) (C : Aff), Packs (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine Packs.bind inferInstance fun w => ?_
    refine Packs.bind (packs_partsV n _ _) fun _ => ?_
    infer_instance

instance (n : Nat) (rows : Array Aff) (C : Aff) : Packs (partsV n rows C) := packs_partsV n rows C

theorem packs_keysV (f : LFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff),
    Packs (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine Packs.bind inferInstance fun k => ?_
    refine Packs.bind (packs_keysV f xs Cs _) fun _ => ?_
    infer_instance

instance (f : LFace) (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff) :
    Packs (keysV f xs Cs rows) := packs_keysV f xs Cs rows

/-! ## 6 Behind the hearing -/

theorem Longer.size_le {F G : Fork} (h : Longer F G) : F.owed.size ≤ G.owed.size := by
  obtain ⟨l, e, _⟩ := h
  have := congrArg List.length e
  simp only [Array.length_toList, List.length_append] at this
  omega

/-- **Behind the hearing a value lies under every slot that the lookup has taken but the leaves'
sumcheck's own; and the list of owed claims has grown by three at least.** Conditional on the return
of `messagesV` and on the first ledger's arrays having their size. -/
theorem heard_full (f : LFace) {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (h : messagesV f F rs = some (g, G, rest)) :
    (∀ j, F.next ≤ j → j < G.next →
      (j < g.leaves.first ∨ g.leaves.first + (1 + f.mu + 2 * f.d) ≤ j) → Filled G j) ∧
      F.owed.size + 3 ≤ G.owed.size := by
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨qg, qG, _⟩ := pure_spec h
  have P13 : Pack F F13 :=
    Packs.step e13 hS <| Packs.step e12 hS <| Packs.step e11 hS <| Packs.step e10 hS <|
    Packs.step e9 hS <| Packs.step e8 hS <| Packs.step e7 hS <| Packs.step e6 hS <|
    Packs.step e5 hS <| Packs.step e4 hS <| Packs.step e3 hS <| Packs.step e2 hS <|
    Packs.step e1 hS (Pack.refl F)
  have S13 := P13.later.sized hS
  have hh := openV_hear e14
  have L14 := MaskedSum.hear_keeps hh
  have n14 := MaskedSum.hear_next S13 hh
  have S14 := L14.sized S13
  have q15 := drawsV_same e15
  have S15 : Sized F15 := q15 ▸ S14
  have P16 : Pack F15 F16 := Packs.pack e16 S15
  have q17 := (slot_spec e17).2
  have q18 := (must_spec e18).2
  have o14 : ownSlots ({ lead := 0, vs := leafVars f table.point, ends := none } : Call).all =
      1 + f.mu + 2 * f.d := own_leafVars f _
  have n14' : F14.next = F13.next + (1 + f.mu + 2 * f.d) := by
    rw [n14, o14]
    rfl
  have hfirst : leaves.first = F13.next := (MaskedSum.heard_lenK hh).1
  have eG : G = F16 := by rw [qG, q18, q17]
  have eg : g.leaves = leaves := by rw [qg]
  refine ⟨fun j a b hj => ?_, ?_⟩
  · rw [eg, hfirst] at hj
    rw [eG] at b ⊢
    rcases hj with hj | hj
    · have z1 := (L14.keep j (P13.full j a hj)).1
      rw [← q15] at z1
      exact (P16.later.keep j z1).1
    · exact P16.full j (by rw [q15, n14']; exact hj) b
  · have s1 : F1 = F := (slot_spec e1).2
    have s2 := (owe_spec e2).2
    have s3 := (owe_spec e3).2
    have s4 := (owe_spec e4).2
    have l : Longer F4 G := by
      rw [eG]
      exact (Owes.longer e5).trans <| (Owes.longer e6).trans <| (Owes.longer e7).trans <|
        (Owes.longer e8).trans <| (Owes.longer e9).trans <| (Owes.longer e10).trans <|
        (Owes.longer e11).trans <| (Owes.longer e12).trans <| (Owes.longer e13).trans <|
        (Owes.longer e14).trans <| (Owes.longer e15).trans (Owes.longer e16)
    have := Longer.size_le l
    rw [s1] at s2
    omega

/-- **Behind `hearV`: a value lies under every slot of the lookup's window but the leaves'
own.** Conditional on the return of `hearV` and on the first ledger's arrays having their size.
An instance: Honest/K3/Parts/PacksGuards.lean [not in this library] (by evaluation). -/
theorem hearV_full (f : LFace) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hh : hearV f F rs = some (g, G)) :
    ∀ j, F.next ≤ j → j < F.next + f.slots →
      (j < g.leaves.first ∨ g.leaves.first + (1 + f.mu + 2 * f.d) ≤ j) → Filled G j := by
  intro j a b
  exact (heard_full f hS (hearV_messages hh).2).1 j a (by rw [hearV_next f hS hh]; exact b)

/-- **Behind `hearV` the list of owed claims has grown by three at least.** Conditional on the same.
-/
theorem hearV_owed3 (f : LFace) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hh : hearV f F rs = some (g, G)) : F.owed.size + 3 ≤ G.owed.size :=
  (heard_full f hS (hearV_messages hh).2).2

#print axioms ProofFile.Honest.K3.Parts.Pack.refl
#print axioms ProofFile.Honest.K3.Parts.Pack.trans
#print axioms ProofFile.Honest.K3.Parts.Packs.step
#print axioms ProofFile.Honest.K3.Parts.packs_of_same
#print axioms ProofFile.Honest.K3.Parts.Packs.bind
#print axioms ProofFile.Honest.K3.Parts.packs_foldlM
#print axioms ProofFile.Honest.K3.Parts.whole_pack
#print axioms ProofFile.Honest.K3.Parts.level_pack
#print axioms ProofFile.Honest.K3.Parts.turn_pack
#print axioms ProofFile.Honest.K3.Parts.fold_pack
#print axioms ProofFile.Honest.K3.Parts.packs_partsV
#print axioms ProofFile.Honest.K3.Parts.packs_keysV
#print axioms ProofFile.Honest.K3.Parts.Longer.size_le
#print axioms ProofFile.Honest.K3.Parts.heard_full
#print axioms ProofFile.Honest.K3.Parts.hearV_full
#print axioms ProofFile.Honest.K3.Parts.hearV_owed3

end ProofFile.Honest.K3.Parts
