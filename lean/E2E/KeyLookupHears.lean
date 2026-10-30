--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLookupHears.lean: from an accept of the lookup's hearing on a view's rounds (`K3.hearV`,
Johnson/Desc/First/Look/Via/Rounds.lean) to an accept of the decision of the key file's own
sub-protocol "lookup" (`K3.lookupKind`, Johnson/Desc/First/Look/K3LookupGeneral.lean, as
Johnson/Desc/Key/Link.lean seats it). General in the lookup's numbers, the setting and the seat.
Statements and proofs; nothing is evaluated.

Why. An honest side of a lookup is typed and tried against `hearV`, general in the lookup's numbers
(`Face`). The key file's IOP as written in Lean hears its two lookups by another text (`hearG`, off
a tape). The library's `hearV_hearG` (Johnson/Top/H/K3Via/BridgeEntries.lean) carries an accept
over, under three premises on the plan's entries. Here two of them are shown to follow (one from
E2E/PlannerLookup.lean), so that «the planner makes the entries» is left, which the sub-protocol's
own test on the plan asks; and the step from the hearing to the sub-protocol's decision is made.

WHAT AN ACCEPT OF `hearV` IS WORTH. It is a matter of FORM: the face passes its tests; every item
sent is a scalar, and as many are sent and drawn as each call says; no position is drawn; the draw
of each further variable Y is not 0; nothing is left over; and the ledger's book-keeping (every slot
that a start form names is filled; the numbers that are laid are free). NO LINE COMPARES A SENT
VALUE WITH ANYTHING: the masked sumcheck's text completes each round's polynomial from the running
claim (Johnson/Desc/Part/MaskedSum4.lean), and the ledger's functions test numbers of slots and
marks alone (OnBytes/Model/Hide.lean: hide, hideRun, shown, publicPart). This is by reading; no
theorem says it. So a sender of the right counts is accepted here whatever it sends. What an honest
sender has beyond that is that the claims which the hearing LEAVES hold of its mask entries, its
keys and its bits: nothing of that is here.

What is shown.
  `static_entriesV`: at every face: every entry of `entriesV f` passes the tests that read an entry
    alone (`staticT`).   `static_of_fit`: so entries that pass `entriesFit f` do.   `ok_of_hearV`.
  **`hearG_of_hearV`**: `p.entries.isSome → hearV p.face F rs = some (g, G) → hearG p F rs = some
    (toHeardG g, G)`: the library's bridge with no test on the entries left.
  **`blockG_decide`**: for every seat, place and state: if the planner makes the place's entries, a
    ledger F is open at the state, no count of rows waits, F's next slot and room are the place's,
    and `hearV` accepts the rounds from F: then `lookupKind`'s decision accepts, and lays what was heard
    (`toHeardG`) and the ledger behind.
  **`key_decide`**: the same at the key file's seat and place, for every setting and every lookup,
    at a state whose ledger is the fresh one that the sub-protocol in front (`caller`) opens.

Limits.
- One way: from `hearV` to the sub-protocol.
- That the planner makes the entries is a premise. The sub-protocol's test on the plan (`PG.planOk`)
  asks it; that this test passes at the IOP at public files is not drawn from the library here.
- The sub-protocols without a round around the lookup (`caller`, `layer`) are not treated.
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import E2E.PlannerLookup
import Johnson.Desc.Key.Link

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Part (MaskedSum.entry MaskedSum.entries MaskedSum.Call)
open VerifiableInference.Desc.First (ProdV.levelEntries ProdV.runEntries)

/-! ## 1. The tests that read an entry alone, at the hearing's own list of entries -/

/-- The tests read neither how many scalars are sent nor what is drawn. -/
theorem static_entry (name : String) (a b c : ℕ) :
    staticT (MaskedSum.entry name a b c) = staticT (MaskedSum.entry name 0 0 0) := rfl

/-- An entry that the masked sumcheck's maker of entries makes under a name that passes. -/
def Made (e : Fmt.Entry) : Prop :=
  ∃ name a b c, e = MaskedSum.entry name a b c ∧ staticT (MaskedSum.entry name 0 0 0) = true

theorem Made.static {e : Fmt.Entry} (h : Made e) : staticT e = true := by
  obtain ⟨name, a, b, c, rfl, hs⟩ := h
  rw [static_entry]
  exact hs

theorem made_of (name : String) (a b c : ℕ)
    (h : staticT (MaskedSum.entry name 0 0 0) = true) : Made (MaskedSum.entry name a b c) :=
  ⟨name, a, b, c, rfl, h⟩

theorem made_entries (k : MaskedSum.Call) : ∀ e ∈ MaskedSum.entries k, Made e := by
  intro e he
  unfold MaskedSum.entries at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · rw [List.mem_singleton] at he
      subst he
      exact made_of _ _ _ _ (by decide)
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 he
      exact made_of _ _ _ _ (by decide)
  · cases hk : k.ends with
    | none => rw [hk] at he; cases he
    | some x =>
      rw [hk] at he
      rcases List.mem_cons.1 he with rfl | he
      · exact made_of _ _ _ _ (by decide)
      · rw [List.mem_singleton] at he
        subst he
        exact made_of _ _ _ _ (by decide)

theorem made_run (m0 n : ℕ) : ∀ e ∈ ProdV.runEntries m0 n, Made e := by
  intro e he
  unfold ProdV.runEntries at he
  obtain ⟨i, -, he⟩ := List.mem_flatMap.1 he
  unfold ProdV.levelEntries at he
  rcases List.mem_append.1 he with he | he
  · exact made_entries _ e he
  · rw [List.mem_singleton] at he
    subst he
    exact made_of _ _ _ _ (by decide)

theorem made_draw (name : String) (n : ℕ) (h : staticT (MaskedSum.entry name 0 0 0) = true) :
    Made (drawEntry name n) := made_of name 0 n 0 h

theorem made_entriesV (f : Face) : ∀ e ∈ entriesV f, Made e := by
  intro e he
  unfold entriesV at he
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at he
  rcases he with ((((((((((he | he) | he) | he) | he) | he) | he) | he) | he) | he) | he)
  · split at he
    · rw [List.mem_singleton] at he
      subst he
      exact made_draw _ _ (by decide)
    · cases he
  · subst he
    exact made_draw _ _ (by decide)
  · exact made_entries _ e he
  · obtain ⟨_, -, he⟩ := he
    exact made_entries _ e he
  · obtain ⟨_, -, he⟩ := he
    exact made_entries _ e he
  · subst he
    exact made_draw _ _ (by decide)
  · obtain ⟨_, -, he⟩ := he
    exact made_run _ _ e he
  · exact made_run _ _ e he
  · exact made_entries _ e he
  · subst he
    exact made_draw _ _ (by decide)
  · exact made_entries _ e he

/-- **Every entry of the hearing's own list passes the tests that read an entry alone**: at every
face. -/
theorem static_entriesV (f : Face) : (entriesV f).all staticT = true :=
  List.all_eq_true.2 fun e he => (made_entriesV f e he).static

/-- So do entries that are, but for the work bits, that list. -/
theorem static_of_fit {f : Face} {es : List Fmt.Entry} (h : entriesFit f es = true) :
    es.all staticT = true := by
  rw [← static_work es, show (es.map fun e => { e with work := 0 }) = entriesV f from eq_of_beq h]
  exact static_entriesV f

/-! ## 2. From the hearing on a view's rounds to the sub-protocol's decision -/

/-- Where the hearing accepts, the face passes its tests. -/
theorem ok_of_hearV {f : Face} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) : f.ok = true := by
  cases hk : f.ok with
  | true => rfl
  | false =>
    unfold hearV at h
    rw [hk] at h
    have h' : (none : Option (HeardV × Fork)) = some (g, G) := h
    cases h'

/-- **The library's bridge with no test on the plan's entries left**: that the planner makes them is
enough. -/
theorem hearG_of_hearV {p : PG} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hes : p.entries.isSome = true) (h : hearV p.face F rs = some (g, G)) :
    hearG p F rs = some (toHeardG g, G) := by
  obtain ⟨es, he⟩ := Option.isSome_iff_exists.1 hes
  have hfit : entriesFit p.face es = true := AtPublicFiles.PlanLookup.fit_of_planner (ok_of_hearV h) he
  exact hearV_hearG he hfit (static_of_fit hfit) h

/-- **The sub-protocol's own decision accepts.** -/
theorem blockG_decide {S Cl : Type} (seat : SeatG S Cl) (before : List (ℕ × ℕ)) (bits : ℕ)
    (guests : List (VerifiableInference.Desc.First.Look.Guest S Cl)) {p : PG}
    {s : S} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (cols : List (List (ℕ × List UInt64))) (hes : p.entries.isSome = true)
    (hF : seat.fork s = some F) (ho : (seat.owed s).noneWaits = true)
    (hn : F.next = p.first) (hr : F.ns = p.ns) (h : hearV p.face F rs = some (g, G)) :
    (lookupKind seat before bits guests p).decide s rs cols = .ok (seat.put s (toHeardG g) G) := by
  have hg := hearG_of_hearV hes h
  show (do
      let F ← VerifiableInference.Desc.named "K3: no ledger is open" (seat.fork s)
      VerifiableInference.Desc.need "K3: rows are owed in front" (seat.owed s).noneWaits
      VerifiableInference.Desc.need "K3: the ledger's count of slots" (F.next == p.first)
      VerifiableInference.Desc.need "K3: the ledger's room" (F.ns == p.ns)
      let x ← VerifiableInference.Desc.named "K3: the hearing" (hearG p F rs)
      pure (seat.put s x.1 x.2) : Except String S) = _
  rw [hF, ho]
  simp only [VerifiableInference.Desc.named, VerifiableInference.Desc.need, hn, hr, hg,
    beq_self_eq_true, bind, Except.bind, pure, Except.pure, if_true]

/-! ## 3. At the key file's seat and place -/

section Key
open VerifiableInference.Desc.Key

/-- **The key file's own sub-protocol "lookup" accepts**, at a state whose ledger is the fresh one
that the sub-protocol in front opens. -/
theorem key_decide (set : Params.Setting) (i : ℕ) (x : Lookup)
    {s : FirstState} {G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (cols : List (List (ℕ × List UInt64)))
    (hes : (lookupPlace set i x).entries.isSome = true)
    (hF : s.base.fork = some (({} : Fork).slots (faceOfLkp x).slots))
    (h : hearV (faceOfLkp x) (({} : Fork).slots (faceOfLkp x).slots) rs = some (g, G)) :
    (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)).decide s rs cols =
      .ok (lookupSeat.put s (toHeardG g) G) :=
  blockG_decide lookupSeat [(1, 0), (1, 1)] 0 [] cols hes hF rfl rfl rfl h

end Key

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.static_entriesV
#print axioms AtPublicFiles.KeyLookup.static_of_fit
#print axioms AtPublicFiles.KeyLookup.ok_of_hearV
#print axioms AtPublicFiles.KeyLookup.hearG_of_hearV
#print axioms AtPublicFiles.KeyLookup.blockG_decide
#print axioms AtPublicFiles.KeyLookup.key_decide
