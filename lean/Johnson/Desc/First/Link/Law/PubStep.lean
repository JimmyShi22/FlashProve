-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PubStep.lean: THE RIDER ON THE PUBLIC ITEMS (`MgRides.pub`,
QuietRides.lean) AT THE COMPOSED PUBLIC TESTS (`pubAll`, Johnson/Desc/First/PubAll.lean), FOR A
LINK's THREE QUIET SUB-PROTOCOLS OF THE BATCHING KIND AND THE FRAME (our files call a sub-protocol a
block): the batching, the frame's sub-protocol behind it, the shutting. Over the kind-free rule for
what passes a place (Johnson/Desc/First/PubFoot.lean). Definitions and theorems.

What is said.
  `keeps9`: the four readers of the verifier's state that the three leave: the statement, what goes
    on to the later chains, the frame between segments, «can the pending claim on the weights be
    made». `hasRow_rest`: the last reads nothing of what the three write. `sameOn_of`: **`SameOn D
    keeps9 s s'` from `Rb` and `rest9`.** `foot0`: what a public item's test reads, at the empty map
    of the runs' names: a closed term; `foot_at`: where all that it names lies among readers without
    «the open segment's part» it is the table's own word at every structure of parameters. `stepB
    made A A'`: a Bool on two lists of public items: each item that is asked behind is made, or is
    asked in front and is either «the ledger is well laid» or booked as reading `keeps9` alone.
    `pubHeld_step`: **under that Bool's yes: where the public items hold in front, they hold
    behind**, from `SameOn D keeps9`, «the base's tests answer alike at the two states», «the ledger
    is well laid» kept, and the made items' tests.

Limits. The Bool's yes at the table's lists is an evaluation, in another file. «The ledger is well
laid» kept is SizedRides.lean's, under the runs' share. What is made (behind the frame's
sub-protocol: «the one sum can be taken») is a premise. The one equation's sub-protocol turns the
statement: it is not here. Nothing on soundness.

-/
import Johnson.Desc.First.PubFoot
import Johnson.Desc.First.Link.Law.Rest9
import Johnson.Desc.First.Link.Law.SizedRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S Item Pub PubData Meaning Rdr SameOn footBy footOf pubAll
  pubAll_same pubHeld pubOfItems ledgerB pubAll_ledger)

/-- The four readers that the three quiet sub-protocols leave. -/
def keeps9 : List Rdr := [.st, .out, .frame, .row]

/-- «Can the pending claim on the weights be made» reads nothing of what the three write. -/
theorem hasRow_rest (L₀ : LinkCtx) (F₀ : Fork) (t₀ : HTailF2) (lay : WsLay) (n : ℕ)
    (lin : Params.LinShape) :
    ReadsRest9 L₀ F₀ t₀ (Johnson.Desc.First.Walk.Law.hasRow lay n lin) := by
  intro s
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

/-- **The three leave these four readers.** -/
theorem sameOn_of (D : PubData) (L₀ : LinkCtx) (F₀ : Fork) (t₀ : HTailF2) (s s' : S) (R : Rb s s')
    (e : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) : SameOn D keeps9 s s' := by
  intro r hr
  simp only [keeps9, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact R.st
  · have h : (rest9 L₀ F₀ t₀ s').out = (rest9 L₀ F₀ t₀ s).out := congrArg S.out e
    exact h
  · have h : (rest9 L₀ F₀ t₀ s').check.frame = (rest9 L₀ F₀ t₀ s).check.frame :=
      congrArg (fun x : S => x.check.frame) e
    exact h
  · exact fun lay n lin => (hasRow_rest L₀ F₀ t₀ lay n lin).alike L₀ F₀ t₀ e

/-- Is the item «the segment's ledger is well laid»? -/
def isLedger : Pub → Bool
  | .ledger _ => true
  | _ => false

/-- What the test at a public item reads, at the empty map of the runs' names: a closed term. At an
item that is none of «the forms can be read», in its two forms, it is the table's own word at every
map (`foot_at`). -/
def foot0 : Pub → Option (List Rdr) := footBy fun _ _ _ => []

/-- Where all that `foot0` names lies among readers without «the open segment's part», the table's
word at a structure of parameters is the same. -/
theorem foot_at (D : PubData) (keeps : List Rdr) (hk : keeps.contains .seg = false) (q : Pub)
    (h : (foot0 q).any (fun R => R.all keeps.contains) = true) : footOf D q = foot0 q := by
  cases q with
  | formsIn m k r =>
    simp [foot0, footBy] at h
    simp [h.1] at hk
  | formsInT m k r =>
    simp [foot0, footBy] at h
    simp [h.1] at hk
  | more o n => cases o <;> rfl
  | _ => rfl

/-- **A Bool on two lists**: A: what is asked in front; A': behind. -/
def stepB (made A A' : List Pub) : Bool :=
  A'.all fun q => made.contains q ||
    (A.contains q && (isLedger q || (foot0 q).any fun R => R.all keeps9.contains))

variable {P W : Type}

/-- **THE PUBLIC ITEMS HOLD BEHIND.** -/
theorem pubHeld_step (Mg : Meaning P W) (D : PubData) (base : Pub → P × S → Bool)
    (hpub : Mg.pub = pubAll D base) (O O' : List Item) (Q Q' made : List Pub) (z : P) (s s' : S)
    (hB : stepB made (Q ++ pubOfItems O) (Q' ++ pubOfItems O') = true)
    (hs : SameOn D keeps9 s s') (hb : ∀ q, base q (z, s') = base q (z, s))
    (hl : ledgerOk s = true → ledgerOk s' = true)
    (hm : ∀ q ∈ made, Mg.pub q (z, s') = true) (h : pubHeld Mg O Q (z, s) = true) :
    pubHeld Mg O' Q' (z, s') = true := by
  unfold pubHeld at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro q hq
  have h1 := List.all_eq_true.1 hB q hq
  rcases Bool.or_eq_true_iff.1 h1 with hmade | h2
  · exact hm q (by simpa using hmade)
  · obtain ⟨hin, h3⟩ := Bool.and_eq_true_iff.1 h2
    have hfront := h q (by simpa using hin)
    rw [hpub] at hfront ⊢
    rcases Bool.or_eq_true_iff.1 h3 with hled | hfoot
    · cases q with
      | ledger m =>
        rw [pubAll_ledger] at hfront ⊢
        exact hl hfront
      | _ => simp [isLedger] at hled
    · have e0 := foot_at D keeps9 (by decide) q hfoot
      cases hf : foot0 q with
      | none => simp [hf] at hfoot
      | some R =>
        rw [hf] at hfoot e0
        have h4 : R.all keeps9.contains = true := hfoot
        rw [pubAll_same D base q R e0 z s s' (fun r hr => hs r (by
          have := List.all_eq_true.1 h4 r hr
          simpa using this)) (hb q)]
        exact hfront

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hasRow_rest
#print axioms VerifiableInference.Desc.LinkJoin.sameOn_of
#print axioms VerifiableInference.Desc.LinkJoin.foot_at
#print axioms VerifiableInference.Desc.LinkJoin.pubHeld_step
