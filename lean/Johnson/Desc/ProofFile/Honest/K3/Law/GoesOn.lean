-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/GoesOn.lean: every text of the lookup's hearing
(Johnson/Desc/First/Look/Via/Rounds.lean), wherever it returns, returns a ledger that is later than
the one it was given (`OnBytes.PscRun.Later`: the count of slots has not gone back, the room is the
same, arrays of the right size stay so, and what lies under a filled slot is kept). Theorems, with
one class.

Terms. Honest/K3/GLOSSARY.md ("hearing", "ledger", "slot").

What is shown.
  `GoesOn x`: the class: wherever x returns, its ledger is later. The library has two definitions of
    this short name with other contents (Johnson/Desc/First/Batch/Law/FitsAtS.lean;
    Johnson/Desc/K5/Honest/Law/GoesOn.lean).
  Instances of the class: for "do": `pure`, bind, "if"; for `Hr.slot`, `Hr.owe`, `Hr.must`; for
    `drawsV`, `drawV`, `sumV`, `openV`, a run of product levels, `tieV`, `partsV`, `keysV`,
    `messagesV`.
  `hearV_later`: the same for `hearV`.
  `drawsV_same`, `slot_spec`, `must_spec`: three texts leave the ledger as it is.
  `sumV_whole`, `openV_hear`, `hearV_messages`: what three of the library's texts are where they
    return; Honest/K3/Law/Tidy.lean builds on them.
Helpers: `GoesOn.bind`, `goesOn_foldlM`, `whole_later`, `level_later`, `turn_later`, `fold_later`,
`run_later`, `goesOn_partsV`, `goesOn_keysV`. A local tactic macro "goesOn" is used in proofs alone.

Hypotheses that remain. The return of the text in question (`e`, `h` or `hw`). In `GoesOn.bind` and
`goesOn_foldlM`: the texts that are composed are in the class (`hx`, `hf`). In `fold_later` the
return stands without a name, in front of an arrow.

Follows. It is written after Johnson/Desc/First/Link/Law/LooksVia.lean, which shows in the same way
that these texts keep the ledger's arrays of trees.

Users. This file is imported by Honest/K3/Law/PlanesReturn.lean, Honest/K3/Law/Tidy.lean and
Honest/K3/Shape/Walk.lean.

Limits. "If it returns": nothing here says that a text returns.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.Part.MaskedSumLedger
import Johnson.Desc.Part.MaskedSumKeeps

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

/-- **Wherever x returns, its ledger is later than the one that it was given.** -/
class GoesOn (x : Hr α) : Prop where
  later : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) → Later F G

/-! ## "do" -/

instance goesOn_pure (a : α) : GoesOn (pure a : Hr α) :=
  ⟨fun {F G rs rest b} e => by
    have e' : some (a, F, rs) = some (b, G, rest) := e
    cases e'
    exact Later.refl F⟩

theorem GoesOn.bind {x : Hr α} {f : α → Hr β} (hx : GoesOn x) (hf : ∀ a, GoesOn (f a)) :
    GoesOn (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some e
    exact (hx.later h1).trans ((hf a).later h2)⟩

instance goesOn_bind (x : Hr α) (f : α → Hr β) [GoesOn x] [∀ a, GoesOn (f a)] :
    GoesOn (x >>= f) := GoesOn.bind inferInstance inferInstance

instance goesOn_ite (p : Prop) [Decidable p] (x y : Hr α) [GoesOn x] [GoesOn y] :
    GoesOn (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each "if" and each pattern. -/
local macro "goesOn" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine GoesOn.bind ?_ ?_
    | intro _
    | split)

theorem goesOn_foldlM {f : β → γ → Hr β} (hf : ∀ s a, GoesOn (f s a)) :
    ∀ (l : List γ) (s : β), GoesOn (l.foldlM f s)
  | [], s => by
    show GoesOn (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show GoesOn (f s a >>= fun s' => l.foldlM f s')
    exact GoesOn.bind (hf s a) fun s' => goesOn_foldlM hf l s'

/-! ## The small texts -/

/-- `Hr.slot` reads the count of slots and leaves the ledger as it is. -/
theorem slot_spec {F G : Fork} {rs rest : List Fmt.RoundView} {a : Nat}
    (e : Hr.slot F rs = some (a, G, rest)) : a = F.next ∧ G = F := by
  have e' : some (F.next, F, rs) = some (a, G, rest) := e
  cases e'
  exact ⟨rfl, rfl⟩

/-- `Hr.must` returns only at "true", and leaves the ledger as it is. -/
theorem must_spec {b : Bool} {F G : Fork} {rs rest : List Fmt.RoundView} {a : Unit}
    (e : Hr.must b F rs = some (a, G, rest)) : b = true ∧ G = F := by
  unfold Hr.must at e
  split at e
  · rename_i hb
    cases e
    exact ⟨hb, rfl⟩
  · exact nomatch e

/-- A round of samples leaves the ledger as it is. -/
theorem drawsV_same {n : Nat} {F G : Fork} {rs rest : List Fmt.RoundView} {a : Array E}
    (e : drawsV n F rs = some (a, G, rest)) : G = F := by
  unfold drawsV at e
  cases rs with
  | nil => exact nomatch e
  | cons r rs' =>
    dsimp only at e
    split at e
    · obtain ⟨x, _, e⟩ := Option.map_eq_some_iff.1 e
      exact (congrArg (fun y => y.2.1) e).symm
    · exact nomatch e

instance goesOn_slot : GoesOn Hr.slot :=
  ⟨fun e => by rw [(slot_spec e).2]; exact Later.refl _⟩

instance goesOn_must (b : Bool) : GoesOn (Hr.must b) :=
  ⟨fun e => by rw [(must_spec e).2]; exact Later.refl _⟩

instance goesOn_owe (what : String) : GoesOn (Hr.owe what) :=
  ⟨fun {F G rs rest a} e => by
    have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
    cases e'
    exact ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩⟩

instance goesOn_drawsV (n : Nat) : GoesOn (drawsV n) :=
  ⟨fun e => by rw [drawsV_same e]; exact Later.refl _⟩

instance goesOn_drawV : GoesOn drawV :=
  ⟨fun {F G rs rest a} e => by
    unfold drawV at e
    split at e
    · rename_i x G' rest' hx
      split at e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact (goesOn_drawsV 1).later hx
      · exact nomatch e
    · exact nomatch e⟩

/-! ## The masked sumcheck, and the product levels -/

theorem whole_later {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) : Later F G := by
  obtain ⟨_, _, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  exact (MaskedSum.hear_keeps hh).trans (MaskedSum.row_keeps hr)

/-- What `sumV` is where it returns: the part's own `whole` on the rounds that it cuts. -/
theorem sumV_whole {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs rest : List Fmt.RoundView} {x : MaskedSum.Heard × Aff}
    (e : sumV C k endTerm F rs = some (x, G, rest)) :
    MaskedSum.whole C k endTerm F (rs.take (VerifiableInference.Desc.K3.roundsOf k)) =
      some (x.1, x.2, G) := by
  unfold sumV at e
  split at e
  · exact nomatch e
  · split at e
    · rename_i h row G' hw
      split at e
      · exact nomatch e
      · simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨a1, a2, _⟩ := e
        subst a1 a2
        exact hw
    · exact nomatch e

/-- What `openV` is where it returns: the part's own `hear` without ends. -/
theorem openV_hear {C : Aff} {vs : List MaskedSum.Var} {F G : Fork} {rs rest : List Fmt.RoundView}
    {x : MaskedSum.Heard} (e : openV C vs F rs = some (x, G, rest)) :
    MaskedSum.hear C { lead := 0, vs := vs, ends := none } F (rs.take (vs.length + 1)) =
      some (x, G) := by
  unfold openV at e
  split at e
  · exact nomatch e
  · obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨h, G'⟩ := y
    simp only [Prod.mk.injEq] at e
    obtain ⟨a1, a2, _⟩ := e
    subst a1 a2
    exact hy

instance goesOn_sumV (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    GoesOn (sumV C k endTerm) := ⟨fun e => whole_later (sumV_whole e)⟩

instance goesOn_openV (C : Aff) (vs : List MaskedSum.Var) : GoesOn (openV C vs) :=
  ⟨fun e => MaskedSum.hear_keeps (openV_hear e)⟩

theorem level_later {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    Later F G := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          exact whole_later hw
      · exact nomatch h
    · exact nomatch h

theorem turn_later {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest)) : Later F G := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_later hx

theorem fold_later (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → Later x.2.1 y.2.1
  | [], x, y, h => by
    obtain rfl : x = y := Option.some.inj h
    exact Later.refl _
  | i :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    exact (turn_later hz).trans (fold_later m0 orders l _ y h)

theorem run_later {m0 n : Nat} {orders : Nat → List Nat} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : vRun m0 n orders s F rs = some (s', G, rest)) : Later F G :=
  fold_later m0 orders _ (s, F, rs) (s', G, rest) h

instance goesOn_run (m0 n : Nat) (orders : Nat → List Nat) (s : Carried) :
    GoesOn (Hr.of (vRun m0 n orders s)) := ⟨fun e => run_later e⟩

/-! ## The lookup's own texts -/

instance goesOn_tieV (w : Nat) (a : E) : GoesOn (tieV w a) := by
  unfold tieV
  refine GoesOn.bind inferInstance fun x => ?_
  refine GoesOn.bind (goesOn_foldlM (fun s _ => by goesOn) _ _) fun _ => ?_
  infer_instance

theorem goesOn_partsV : ∀ (n : Nat) (rows : Array Aff) (C : Aff), GoesOn (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine GoesOn.bind inferInstance fun w => ?_
    refine GoesOn.bind (goesOn_partsV n _ _) fun _ => ?_
    infer_instance

instance (n : Nat) (rows : Array Aff) (C : Aff) : GoesOn (partsV n rows C) :=
  goesOn_partsV n rows C

theorem goesOn_keysV (f : VFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff),
    GoesOn (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine GoesOn.bind inferInstance fun k => ?_
    refine GoesOn.bind (goesOn_keysV f xs Cs _) fun _ => ?_
    infer_instance

instance (f : VFace) (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff) :
    GoesOn (keysV f xs Cs rows) := goesOn_keysV f xs Cs rows

/-- **The lookup's rounds, heard in order.** -/
instance goesOn_messagesV (f : VFace) : GoesOn (messagesV f) := by
  unfold messagesV
  goesOn

/-- What `hearV` is where it returns. -/
theorem hearV_messages {f : VFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) : f.ok = true ∧ messagesV f F rs = some (g, G, []) := by
  unfold hearV at h
  split at h
  · rename_i hok
    split at h
    · rename_i g' G' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨a1, a2⟩ := h
      subst a1 a2
      exact ⟨hok, hm⟩
    · exact nomatch h
  · exact nomatch h

/-- **Where the lookup's hearing returns, its ledger is later.**
Conditional on the return of `hearV`. -/
theorem hearV_later {f : VFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) : Later F G :=
  (goesOn_messagesV f).later (hearV_messages h).2

#print axioms ProofFile.Honest.K3.Law.GoesOn.bind
#print axioms ProofFile.Honest.K3.Law.goesOn_foldlM
#print axioms ProofFile.Honest.K3.Law.slot_spec
#print axioms ProofFile.Honest.K3.Law.must_spec
#print axioms ProofFile.Honest.K3.Law.drawsV_same
#print axioms ProofFile.Honest.K3.Law.whole_later
#print axioms ProofFile.Honest.K3.Law.sumV_whole
#print axioms ProofFile.Honest.K3.Law.openV_hear
#print axioms ProofFile.Honest.K3.Law.level_later
#print axioms ProofFile.Honest.K3.Law.turn_later
#print axioms ProofFile.Honest.K3.Law.fold_later
#print axioms ProofFile.Honest.K3.Law.run_later
#print axioms ProofFile.Honest.K3.Law.goesOn_partsV
#print axioms ProofFile.Honest.K3.Law.goesOn_keysV
#print axioms ProofFile.Honest.K3.Law.goesOn_messagesV
#print axioms ProofFile.Honest.K3.Law.hearV_messages
#print axioms ProofFile.Honest.K3.Law.hearV_later

end ProofFile.Honest.K3.Law
