-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshFromRows.lean: the kind "the code switch" (K2): THE SECOND
LAW ON THE SENDER (`SendFreshLaw`, Honest/K2/Fresh.lean), AT THE CORE's OWN SENDER (`coreSender`,
Honest/K2/Sending.lean), FROM THE LIKE EQUATION ON THE SHARED SENDING's ROWS AT THE SAME TWO LISTS
OF ENTRIES (`RowsFreshAt`), WHICH STANDS HERE AS A NAMED PREMISE AND IS PROVED NOWHERE IN THIS FILE
OR BENEATH IT. One definition; statements with their proofs.

  `RowsFreshAt`  THE PREMISE, BY NAME: at a place, a ride and two lists of entries: under the shared
                 sending's public premises on the place, the seeds and the positions: what is cut
                 at the first list, what the two moves show (`shownR`, Johnson/SendSim/At/Sim.lean)
                 and what is cut at the second have one law with: fresh coins for the first list,
                 beside what is shown and cut at the second
  `cutAll_cast`, `map_cast_snd`   cuts, and uniform coins beside another uniform value, under
                 another spelling of the coins' count
  `sendFreshLaw_of_rowsAt`   THE END

Limits. THE END IS AS GOOD AS ITS PREMISE. The premise's equation is another writer's statement
(`Spec.rowsFresh`), copied, at two free lists in the stead of a book's; that `RowsFreshAt` follows
from that statement is one line, NOT TYPED: its file is not beneath this one. What must be asked of
the two lists for the premise to hold is not said here: the law's own hypothesis on them
(`bookFits`) and "the table that rides has one row" are not spent; whether `bookFits` at one spender
pays the premise at that spender waits on that writer's premise on the book. As in
Honest/K2/Law/CoreSenderLaw.lean the end stands at a sending in which every message with a main row is
sampled and at the shared sending's own table for a fresh mask. Nothing here says what the law would
mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Fresh
import Johnson.Desc.ProofFile.Honest.K2.Law.CoreSenderLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes.Slice (readE)
open OnBytes.SendSim.At (shownR budAt)

/-- **The premise, by name**: the second law's equation on the shared sending's rows, at two lists
of entries. es: what is spent. ks: what is known. -/
def RowsFreshAt (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (es ks : List Ahead) : Prop :=
  ∀ (first : Nat) (data : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))),
    K1.sendFits P ride = true → K1.seedsFit P ds = true →
    (∀ s ∈ K1.seedsAt P ds, readE s.2 ≠ 0) → budAt P asks →
    (Prob.unif (Cs (K1.dueR P ride))).map (fun c =>
        (cutAll c es, shownR P first ride data ds asks c, cutAll c ks)) =
      (Prob.unif (CsAll (es.map Ahead.named) × Cs (K1.dueR P ride))).map fun a =>
        (some a.1, shownR P first ride data ds asks a.2, cutAll a.2 ks)

/-- Cuts under another spelling of the coins' count. -/
theorem cutAll_cast {d d' : Due} (h : d = d') (c : Cs d) (es : List Ahead) :
    cutAll (h ▸ c) es = cutAll c es := by
  subst h
  rfl

/-- Uniform coins beside another uniform value, under another spelling of the coins' count. -/
theorem map_cast_snd {A β : Type} [Fintype A] [Nonempty A] {d d' : Due} (h : d = d')
    (f : A × Cs d' → β) :
    (Prob.unif (A × Cs d)).map (fun a => f (a.1, h ▸ a.2)) = (Prob.unif (A × Cs d')).map f := by
  subst h
  rfl

/-- **From the like equation on the shared sending's rows: the second law on the sender, at the
core's own sender**, at the same two lists: at a sending in which every message with a main row is
sampled, at the shared sending's own table for a fresh mask. hX: a premise, not proved here. -/
theorem sendFreshLaw_of_rowsAt {table : FreshTable} {codes : OnBytes.Codes}
    {sent : Array OnBytes.OracleNotice} {fresh : Option (Nat × Nat)} {es ks : List Ahead}
    (hX : RowsFreshAt (sendingPar codes sent) (rideOf sent fresh) es ks) (hw : NoWord sent)
    (htab : ∀ n h u r j, table n h u r j = (⟨n, h⟩ : K1.Ride).lay u r j) :
    SendFreshLaw (coreSender table) codes sent fresh es ks := by
  intro hf _ _ data seeds asks hs ha
  have hd := sendingDue_shared hf hw
  have hx := hX 0 (dataShared sent data) [⟨seeds, [], [], none⟩] [asks] hf (seeds_shared hs).1
    (seeds_shared hs).2 (bud_shared ha)
  have hL : (Prob.unif (Cs (sendingDue codes sent fresh))).map (fun c =>
      (cutAll c es, senderShows (coreSender table) codes sent fresh data seeds asks c,
        cutAll c ks)) =
      ((Prob.unif (Cs (K1.dueR (sendingPar codes sent) (rideOf sent fresh)))).map (fun c =>
        (cutAll c es, shownR (sendingPar codes sent) 0 (rideOf sent fresh) (dataShared sent data)
          [⟨seeds, [], [], none⟩] [asks] c, cutAll c ks))).map
        (fun t => (t.1, backShown (sendingPar codes sent) t.2.1, t.2.2)) := by
    rw [PMF.map_comp, ← map_cast hd]
    exact congrArg (fun f => PMF.map f (Prob.unif (Cs (sendingDue codes sent fresh))))
      (funext fun c => by
        show _ = (cutAll (hd ▸ c) es, backShown (sendingPar codes sent)
          (shownR (sendingPar codes sent) 0 (rideOf sent fresh) (dataShared sent data)
            [⟨seeds, [], [], none⟩] [asks] (hd ▸ c)), cutAll (hd ▸ c) ks)
        rw [cutAll_cast, cutAll_cast, shows_back hf hw htab])
  have hR : (Prob.unif (CsAll (es.map Ahead.named) × Cs (sendingDue codes sent fresh))).map
      (fun a => (some a.1, senderShows (coreSender table) codes sent fresh data seeds asks a.2,
        cutAll a.2 ks)) =
      ((Prob.unif (CsAll (es.map Ahead.named) ×
          Cs (K1.dueR (sendingPar codes sent) (rideOf sent fresh)))).map (fun a =>
        (some a.1, shownR (sendingPar codes sent) 0 (rideOf sent fresh) (dataShared sent data)
          [⟨seeds, [], [], none⟩] [asks] a.2, cutAll a.2 ks))).map
        (fun t => (t.1, backShown (sendingPar codes sent) t.2.1, t.2.2)) := by
    rw [PMF.map_comp, ← map_cast_snd hd]
    exact congrArg (fun f => PMF.map f
        (Prob.unif (CsAll (es.map Ahead.named) × Cs (sendingDue codes sent fresh))))
      (funext fun a => by
        show _ = (some a.1, backShown (sendingPar codes sent)
          (shownR (sendingPar codes sent) 0 (rideOf sent fresh) (dataShared sent data)
            [⟨seeds, [], [], none⟩] [asks] (hd ▸ a.2)), cutAll (hd ▸ a.2) ks)
        rw [cutAll_cast, shows_back hf hw htab])
  rw [hL, hR, hx]

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.cutAll_cast
#print axioms ProofFile.Honest.K2.map_cast_snd
#print axioms ProofFile.Honest.K2.sendFreshLaw_of_rowsAt
