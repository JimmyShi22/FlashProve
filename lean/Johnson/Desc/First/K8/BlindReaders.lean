-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/BlindReaders.lean: THE SMALLNESS TEST's DRAW AND THE READERS OF A SEGMENT's
RUNS OF CLAIMS: from "each run commutes with the draw" to "the run's reader has one value in front
of the draw's yes and behind it" (`TlBlind`, Johnson/Desc/First/K8/BlindPub.lean). A definition and
three theorems; rules over letters.

Why. The reader of a run IS the run itself, evaluated at the verifier's state
(`readerOf`, Johnson/Desc/First/Batch/ReaderOf.lean): of what the run returns it reads the claims
and the ledger of the state behind; of the state in front, the ledger. The state behind a run at the
state behind the draw is NOT the state behind that run at the state in front of the draw: it bears
the drawn matrix. So "the run's function is blind" is false as it stands; what holds, and what
suffices, is said by `RunBlind`.
  `RunBlind f`: wherever `Drawn s t`: f refuses at both or at neither; where it returns, it returns
    the same claims, and states with one ledger.
  `readerOf_blind`: every run of that name among what sub-protocol number b states is `RunBlind`:
    then `readerOf states b name` is `TlBlind`.
  `readersOfLink_blind`: the like for `readersOfLink H l`, at a name other than "K8.equations",
    where the second hole's reader is blind too.
  `readersAt_blind`: **the like for `readersAt lk X mH m` at a segment other than the output
    head's** (there the second hole answers nothing).
Limits. That a run is `RunBlind` is its files' to show. At the output head's segment the second
hole's reader is left as a premise. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.K8.BlindPub
import Johnson.Desc.First.Batch.ReadersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (RunOf Read readerOf readersOfLink readersAt LinkHoles statesOfLink
  holesAt)

/-- A run of claims commutes with the draw, as far as its reader reads it. -/
def RunBlind (f : S → Except String (List Claim × S)) : Prop :=
  ∀ s t, Drawn s t →
    ((f t).toOption.map fun z => (z.1, z.2.fork?)) = (f s).toOption.map fun z => (z.1, z.2.fork?)

theorem readerOf_blind (states : Nat → List (RunOf S)) (b : Nat) (name : String)
    (h : ∀ r ∈ states b, (r.1 == name) = true → RunBlind (r.2 0)) :
    TlBlind (readerOf states b name) := fun s t hd => by
  unfold readerOf
  cases hf : (states b).find? (fun r => r.1 == name) with
  | none => rfl
  | some r =>
    have hn : (r.1 == name) = true := List.find?_some (p := fun r : RunOf S => r.1 == name) hf
    have e := h r (List.mem_of_find?_eq_some hf) hn s t hd
    simp only [Option.bind_some]
    rw [blind_fork s t hd]
    cases ht : r.2 0 t with
    | error x =>
      cases hs : r.2 0 s with
      | error y => rfl
      | ok z =>
        rw [ht, hs] at e
        exact nomatch e
    | ok z' =>
      cases hs : r.2 0 s with
      | error y =>
        rw [ht, hs] at e
        exact nomatch e
      | ok z =>
        rw [ht, hs] at e
        have e' : (z'.1, z'.2.fork?) = (z.1, z.2.fork?) := Option.some.inj e
        obtain ⟨e1, e2⟩ := Prod.mk.inj e'
        cases s.fork? with
        | none => rfl
        | some F =>
          show ((z'.2.fork?).bind fun G => _) = (z.2.fork?).bind fun G => _
          rw [e1, e2]

theorem readersOfLink_blind (H : LinkHoles) (l : Link S Claim) (b : Nat) (name : String)
    (hn : (name == "K8.equations") = false)
    (h : ∀ r ∈ statesOfLink l b, (r.1 == name) = true → RunBlind (r.2 0))
    (hs : TlBlind (H.silent b name)) : TlBlind ((readersOfLink H l).forms b name) :=
  fun s t hd => by
  show (if (name == "K8.equations") = true then H.small t
    else match readerOf (statesOfLink l) b name t with
      | some R => some R
      | Option.none => H.silent b name t) =
    (if (name == "K8.equations") = true then H.small s
    else match readerOf (statesOfLink l) b name s with
      | some R => some R
      | Option.none => H.silent b name s)
  rw [hn, readerOf_blind (statesOfLink l) b name h s t hd, hs s t hd]
  rfl

theorem readersAt_blind (lk : Nat → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public)
    (mH m : Nat) (hm : (m == mH) = false) (b : Nat) (name : String)
    (hn : (name == "K8.equations") = false)
    (h : ∀ l, lk m = some l → ∀ r ∈ statesOfLink l b, (r.1 == name) = true → RunBlind (r.2 0)) :
    TlBlind ((readersAt lk X mH m).forms b name) := by
  cases hl : lk m with
  | none =>
    rw [VerifiableInference.Desc.K9.readersAt_none lk X mH m hl]
    exact fun _ _ _ => rfl
  | some l =>
    rw [VerifiableInference.Desc.K9.readersAt_some lk X mH m l hl]
    refine readersOfLink_blind _ l b name hn (h l hl) ?_
    unfold holesAt
    rw [hm]
    exact fun _ _ _ => rfl

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.readerOf_blind
#print axioms VerifiableInference.Desc.First.K8.readersOfLink_blind
#print axioms VerifiableInference.Desc.First.K8.readersAt_blind
