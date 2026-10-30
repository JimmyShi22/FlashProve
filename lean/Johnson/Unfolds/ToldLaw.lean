-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/ToldLaw.lean: the value of `ProofFile.toldChain` (Johnson/Desc/ProofFile/Told.lean) from
its steps' values; and: what the `mapM` of `Johnson.G.OfPlan.sentAt` returns does not hang on the
name that is handed in for a refusal's words.

Definition.
  `mineW l extra held`: a chain's trees with their tenants, in the order of sending: `toldChain`'s
    own term.
Statements. General.
  **`toldChain_of`**: from (hl) what the `mapM` of `toldAt` returns, (ht) what `treesSent` returns,
    (hc) the two lists of trees agree in depth and width: the value is `mineW l extra held`. Calls
    alone.
  `toOption_mapM_congr`: two routines that agree but for their refusals' words: so do their `mapM`s.
  `sentAt_any_name`, **`sent_any_name`**: what the `mapM` of `sentAt` returns at one name it returns
    at every name: so one closed fact serves `fileOf` ("…, first chain") and `toldChain` ("the
    tenants, first chain").
Whose text. `mineW` follows a term of `toldChain` (Johnson/Desc/ProofFile/Told.lean): this tree's
own file.

Limits. `toldChain_of`'s THREE FACTS ARE PREMISES. The key file's `Key.toldOfChain` calls
`toldChain` in its first line: that line alone is served here. No closed fact. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Told

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open OnBytes OnBytes.Params Johnson.G Johnson.G.OfPlan ProofFile

/-- A chain's trees with their tenants, in the order of sending. -/
def mineW (l : List (List (Nat × Root))) (extra : List Sent) (held : Option OracleNotice) :
    List Root :=
  ((l.flatten ++ extra.map fun t =>
      (t.round,
        ({ logLength := t.a, words := t.W, tenants := held.toList.map tenantOf } : Root))).mergeSort
    fun a b => a.1 ≤ b.1).map (·.2)

/-- **`toldChain`'s value, from its steps' values.** -/
theorem toldChain_of {at_ : String} {c : ChainSends} {P : Fmt.Plan} {extra : List Sent}
    {held : Option OracleNotice} {l : List (List (Nat × Root))} {theirs : List (Sent × Nat)}
    (hl : c.sends.mapM (toldAt c.codes (P.entries.length - P.rounds.length)) = some l)
    (ht : treesSent at_ c P extra = .ok theirs)
    (hc : ((mineW l extra held).map (fun r => (r.logLength, r.words)) !=
      theirs.map fun t => (t.1.a, t.1.W)) = false) :
    toldChain at_ c P extra held = .ok (mineW l extra held) := by
  unfold mineW at hc ⊢
  unfold toldChain
  simp only [hl, ht, Option.elim, bind, Except.bind, hc, pure, Except.pure, Bool.false_eq_true,
    ↓reduceIte]

/-- Two routines that agree but for their refusals' words: so do their `mapM`s. -/
theorem toOption_mapM_congr {ε ε' α β : Type} (f : α → Except ε β) (g : α → Except ε' β)
    (h : ∀ x, (f x).toOption = (g x).toOption) :
    ∀ l : List α, (l.mapM f).toOption = (l.mapM g).toOption
  | [] => by
    rw [List.mapM_nil, List.mapM_nil]
    rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons]
    have ha := h a
    have ih := toOption_mapM_congr f g h l
    cases ea : f a with
    | error e =>
      cases eb : g a with
      | error e' => rfl
      | ok b =>
        rw [ea, eb] at ha
        cases ha
    | ok b =>
      cases eb : g a with
      | error e' =>
        rw [ea, eb] at ha
        cases ha
      | ok b' =>
        rw [ea, eb] at ha
        obtain rfl : b = b' := Option.some.inj ha
        cases el : l.mapM f with
        | error e =>
          cases el' : l.mapM g with
          | error e' => rfl
          | ok bs =>
            rw [el, el'] at ih
            cases ih
        | ok bs =>
          cases el' : l.mapM g with
          | error e' =>
            rw [el, el'] at ih
            cases ih
          | ok bs' =>
            rw [el, el'] at ih
            obtain rfl : bs = bs' := Option.some.inj ih
            rfl

/-- What `sentAt` returns does not hang on the name for a refusal's words. -/
theorem sentAt_any_name (a b : String) (codes : Codes) (off : Nat) (x : Sending) :
    (sentAt a codes off x).toOption = (sentAt b codes off x).toOption := by
  unfold sentAt
  cases sendTag x.label with
  | none => rfl
  | some t =>
    cases layTrees codes x.sent.toArray with
    | none => rfl
    | some L => rfl

/-- **What the `mapM` of `sentAt` returns at one name it returns at every name.** -/
theorem sent_any_name {a : String} {codes : Codes} {off : Nat} {xs : List Sending}
    {l : List (List Sent)} (h : xs.mapM (sentAt a codes off) = .ok l) (b : String) :
    xs.mapM (sentAt b codes off) = .ok l := by
  have e := toOption_mapM_congr (sentAt a codes off) (sentAt b codes off)
    (sentAt_any_name a b codes off) xs
  rw [h] at e
  cases hb : xs.mapM (sentAt b codes off) with
  | error m =>
    rw [hb] at e
    cases e
  | ok l' =>
    rw [hb] at e
    exact congrArg Except.ok (Option.some.inj e).symm

end Johnson.Unfolds

#print axioms Johnson.Unfolds.toldChain_of
#print axioms Johnson.Unfolds.toOption_mapM_congr
#print axioms Johnson.Unfolds.sentAt_any_name
#print axioms Johnson.Unfolds.sent_any_name
