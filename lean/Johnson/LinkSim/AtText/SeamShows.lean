-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamShows.lean: when two strategies of the link's protocol, each made of a
message function, disclose the same.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

The link's protocol in general form is linkProtocolOfRoundData C ds a xs dec (OnBytes/Flat/LinkSib.lean). A strategy
for it is made of a function next, from a round's number and the challenges so far to a message at
the level of a view (MsgV; the format's view, not the disclosed view): the items sent in the clear,
and the columns of the round's trees (stratOf, Johnson/Prover/Link/LinkFrame.lean). Two transcripts
disclose the same (Shows, Johnson/LinkSim/SpecForm.lean) if they have the same plain parts, and the
same symbols at the positions that the verifier reads and at every position that is not blinded. In
the link's protocol every position of the prover's own oracles is blinded, and what is read depends
on the verifier messages alone, through what they sample.

What this file proves. Spec.showsOfNext, proved as showsOfNext, holds for every choice of challenge
types C (CK), rounds' description ds, tables' depth a, list xs of openings of the stored tables and
decision function dec. If two message functions satisfy SameItems and SameCols at the challenges of
a verifier message ρ, then the runs of their two strategies against ρ disclose the same (Shows).

How it fits. SeamOfOut.lean proves the two premises from two outputs that agree where the verifier
looks (SameAt), and SeamGroups.lean carries that to the prover's and the simulator's strategies.
showsOfNext is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean), through
SeamOfOut.lean, SeamGroups.lean and Exact.lean.

The other names (namespace OnBytes.LinkSim.Seam).
  SameItems ds next next' Ds    round by round, at the challenges so far, the two messages' items
               give the same plain part of the protocol's type.
  SameCols ds next next' Ds     at every (tree of the prover, position) that the challenges Ds ask
               for, the two messages' columns give the same symbol of the protocol's type.
  plains_SL, read_SL            the two halves of the proof, by recursion on the rounds.
  sameItems_refl, sameCols_refl    both hold of a function and itself, by reflexivity; they show
               only that the premises can hold.
  toyD, notShows_toy            a negative test: Shows can be false. At one round that sends one
               element in the clear, the functions that send 1 and 0 do not disclose the same. It
               tests the plain parts only.

Limits.
- The second function may ignore the challenges so far that it is given: it is a variable.

Notes. This file does not say when two functions satisfy the two premises; SeamOfOut.lean does.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.SpecForm
import Johnson.Prover.Link.LinkFrame

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes.LinkSim
open OnBytes.Flat (linkProtocolOfRoundData)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK PlainOf View XO)
open TypedOracleCompiler.Run.PQ (RD SOf uL drawnSL posAtS posAtT wanted)

/-- Round by round, at the challenges so far, the two messages' items give the same plain part of
the protocol's type. -/
def SameItems (ds : List RD) (next next' : ℕ → List Fmt.Drawn → MsgV) (Ds : List Fmt.Drawn) :
    Prop :=
  ∀ j d, ds[j]? = some d →
    layP d.items (next j (Ds.take j)).vals = layP d.items (next' j (Ds.take j)).vals

/-- At every (tree of the prover, position) that the challenges ask for, the columns give the same
symbol of the protocol's type. (j, k): the round that sends the tree, and the tree's number in that
round. -/
def SameCols (ds : List RD) (next next' : ℕ → List Fmt.Drawn → MsgV) (Ds : List Fmt.Drawn) : Prop :=
  ∀ nx ∈ wanted ds Ds, ∀ j k d q, seatOf ds nx.1 = some (j, k) → ds[j]? = some d →
    posAtT d.trees k nx.2 = some q →
    orcT d.trees (next j (Ds.take j)).col q = orcT d.trees (next' j (Ds.take j)).col q

/-- Statement only; proved as showsOfNext below. **SameItems and SameCols at the challenges of ρ
give Shows of the two runs against ρ.** -/
def Spec.showsOfNext : Prop :=
  ∀ (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (X : Type) (dec : X → View → Bool) (x : X)
    (next next' : ℕ → List Fmt.Drawn → MsgV) (ρ : Rho (_root_.Run.Twin.up (SOf C ds))),
    SameItems ds next next' (drawnSL C ds ρ.2) → SameCols ds next next' (drawnSL C ds ρ.2) →
    Shows (linkProtocolOfRoundData C ds a xs dec) x ((stratOf C ds next).run ρ).1 ((stratOf C ds next').run ρ).1

section
variable (C : CK) (next next' : ℕ → List Fmt.Drawn → MsgV)

/-- The plain parts of the two runs. -/
theorem plains_SL : ∀ (ds : List RD) (i : ℕ) (hist : List Fmt.Drawn) (ρ : Rho (uL C ds)),
    (∀ j d, ds[j]? = some d →
      layP d.items (next (i + j) (hist ++ (drawnSL C ds ρ).take j)).vals =
        layP d.items (next' (i + j) (hist ++ (drawnSL C ds ρ).take j)).vals) →
    ((stratSL C ds i hist next).run ρ).1.plains = ((stratSL C ds i hist next').run ρ).1.plains
  | [], _, _, _, _ => rfl
  | d :: ds, i, hist, (c, ρ), h => by
      have e0 := h 0 d rfl
      rw [Nat.add_zero, List.take_zero, List.append_nil] at e0
      have eT := plains_SL ds (i + 1)
        (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) ρ fun j d' hd => by
          have e := h (j + 1) d' (by simpa using hd)
          rw [next_shift next i j hist (drawnSL C ds ρ),
            next_shift next' i j hist (drawnSL C ds ρ)]
          exact e
      show ((GPlain.mk d.entry.work (layP d.items (next i hist).vals) 0,
          Tr.plains ((stratSL C ds (i + 1)
            (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) next).run ρ).1) :
          Plains (uL C (d :: ds))) =
        (GPlain.mk d.entry.work (layP d.items (next' i hist).vals) 0,
          Tr.plains ((stratSL C ds (i + 1)
            (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) next').run ρ).1)
      rw [e0, eT]

/-- The symbol of the two runs at the position of (tree n of the prover, position x). -/
theorem read_SL : ∀ (ds : List RD) (i : ℕ) (hist : List Fmt.Drawn) (ρ : Rho (uL C ds)) (n x : ℕ)
    (p : OPos (uL C ds)), posAtS C ds n x = some p →
    (∀ j k d q, seatOf ds n = some (j, k) → ds[j]? = some d → posAtT d.trees k x = some q →
      orcT d.trees (next (i + j) (hist ++ (drawnSL C ds ρ).take j)).col q =
        orcT d.trees (next' (i + j) (hist ++ (drawnSL C ds ρ).take j)).col q) →
    ((stratSL C ds i hist next).run ρ).1.read p = ((stratSL C ds i hist next').run ρ).1.read p
  | [], _, _, _, _, _, _, hp, _ => by cases hp
  | d :: ds, i, hist, (c, ρ), n, x, p, hp, h => by
      unfold posAtS at hp
      split at hp
      · rename_i hn
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hp
        have e := h 0 n d q (by unfold seatOf; rw [if_pos hn]) rfl hq
        rw [Nat.add_zero, List.take_zero, List.append_nil] at e
        exact e
      · rename_i hn
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hp
        refine read_SL ds (i + 1)
          (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) ρ
          (n - d.trees.length) x q hq fun j k d' q' hs hd hq' => ?_
        have e := h (j + 1) k d' q' (by unfold seatOf; rw [if_neg hn, hs]; rfl)
          (by simpa using hd) hq'
        rw [next_shift next i j hist (drawnSL C ds ρ),
          next_shift next' i j hist (drawnSL C ds ρ)]
        exact e

end

/-- **Two message functions that give the same items, and the same columns where the challenges
ask, disclose the same.** -/
theorem showsOfNext : Spec.showsOfNext := by
  intro C ds a xs X dec x next next' ρ hI hC
  obtain ⟨c0, ρ'⟩ := ρ
  refine ⟨?_, fun p hp => ?_⟩
  · have e := plains_SL C next next' ds 0 [] ρ' fun j d hd => by
      rw [Nat.zero_add, List.nil_append]
      exact hI j d hd
    show (((), Tr.plains ((stratSL C ds 0 [] next).run ρ').1) :
        Plains (_root_.Run.Twin.up (SOf C ds))) =
      ((), Tr.plains ((stratSL C ds 0 [] next').run ρ').1)
    rw [e]
  · rcases hp with hp | hp
    · have er : Tr.rho ((stratOf C ds next).run
          ((c0, ρ') : Rho (_root_.Run.Twin.up (SOf C ds)))).1 = (c0, ρ') := Strat.rho_run _ _
      rw [er] at hp
      have hp' : p ∈ ((wanted ds (drawnSL C ds ρ')).filterMap fun nx =>
          (posAtS C ds nx.1 nx.2).map fun q =>
            (Sum.inr q : OPos (_root_.Run.Twin.up (SOf C ds)))).toFinset := hp
      obtain ⟨nx, hnx, he⟩ := List.mem_filterMap.1 (List.mem_toFinset.1 hp')
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 he
      exact read_SL C next next' ds 0 [] ρ' nx.1 nx.2 q hq fun j k d q' hs hd hq' => by
        rw [Nat.zero_add, List.nil_append]
        exact hC nx hnx j k d q' hs hd hq'
    · have h2 : (true : Bool) = false := hp
      cases h2

/-- A control that checks that the premises can hold: SameItems of a function with itself. -/
theorem sameItems_refl (ds : List RD) (next : ℕ → List Fmt.Drawn → MsgV) (Ds : List Fmt.Drawn) :
    SameItems ds next next Ds := fun _ _ _ => rfl

/-- SameCols of a function with itself. -/
theorem sameCols_refl (ds : List RD) (next : ℕ → List Fmt.Drawn → MsgV) (Ds : List Fmt.Drawn) :
    SameCols ds next next Ds := fun _ _ _ _ _ _ _ _ _ => rfl

/-- One round that sends one element in the clear, no tree, and samples nothing. -/
def toyD : RD := ⟨{ name := "" }, .nothing, [.e], [], []⟩

/-- **A negative test: Shows can be false**: the functions that send 1 and 0 in the clear do not
disclose the same. It tests the plain parts only. -/
theorem notShows_toy (C : CK) (a : ℕ) (xs : List XO)
    (ρ : Rho (_root_.Run.Twin.up (SOf C [toyD]))) :
    ¬ Shows (linkProtocolOfRoundData C [toyD] a xs fun (_ : Unit) _ => true) ()
      ((stratOf C [toyD] fun _ _ => ⟨[.e (1, 0, 0)], fun _ _ => []⟩).run ρ).1
      ((stratOf C [toyD] fun _ _ => ⟨[.e (0, 0, 0)], fun _ _ => []⟩).run ρ).1 := by
  obtain ⟨c0, c1, u⟩ := ρ
  intro h
  have h2 : (((), (((1, 0, 0) : Fmt.Ext), ()), ()) : Unit × (Fmt.Ext × Unit) × Unit) =
      ((), ((0, 0, 0), ()), ()) := h.1
  exact absurd (congrArg (fun z => z.2.1.1.1) h2) (by decide)

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.showsOfNext
#print axioms OnBytes.LinkSim.Seam.notShows_toy
