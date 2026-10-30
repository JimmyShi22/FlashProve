-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/ItemObjects.lean: `TableOwes.hitems` (Johnson/Desc/First/Link/Law/LinkTable.lean), ONE
    ITEM's CLAUSE (`ItemIn`, Johnson/Desc/First/Link/Law/HitemsStill.lean) AT AN ENTRY AT WHICH THE
    LINK STATES THE LOOKUP ARGUMENT's RUN "objects". One theorem, general in the lookup's accessors
        (`K3.Seat`: how a lookup argument reads and writes the verifier's state) and in the tables
        of terms. A law file: no sub-protocol imports it.

Why. At this entry the reader is the run itself. The run's claims are the rows that the lookup has
    heard, as plain forms, and it lays nothing under a slot. The lookups' law has the run's
    values as the flat rows' residues at the data's mask row (`objVals`,
    Johnson/Top/H/Keep/RunsPlain.lean), through rounds that are picked out of the promise on the
    fixed part.

What is said. `item_objects`: **the clause**: from: the entry is of the order, is not the
    approximate range proof's, and the run "objects" at these accessors stands there; the accessors
        are the verifier's state's own (`AtS2`); what the lookup has heard is read off the fixed
        part; the table of terms there is `plainTm (objVals ..)`; and at the statement: a part is
    there; the lookups' promise `K3Ok` holds of what is fixed; the readers' second hole says
    nothing; the table's public test says yes.
  HOW. `run_of_reader`: what the reader gives is the run's own claims' forms; `objects_answer`:
      these are the rows heard, and the ledger behind the run is the ledger in front with a debt
      marked as paid: no late slot. `K3Ok` gives rounds for which what was heard stands at a ledger
      earlier than the part's; "stands" says of each row (`RowIs`) that its worth is the flat row's
      residue in the world of every later ledger, AT EVERY FUNCTION OF ENTRIES: so in the table's
      world of the arrays' own rows.

Limits. An implication. THE STATEMENT ENDS IN `ItemIn`: AN INCLUSION UNDER "THERE ARE": what the
    reader's forms are, and how many, stands in the proof alone. WHETHER `K3Ok` HOLDS OF WHAT IS
    FIXED AT A REAL STATE, and whether the public test says yes there, is not shown here. Nothing on
    "planes" or "join". No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Link.Law.HitemsStill
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Batch.Law.CoresTable
import Johnson.Top.H.Keep.RunsPlain
import Johnson.Top.H.Keep.K3Late
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H.Keep.ReaderIsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles (AtS2 objectsRun objVals K3Ok pick_some pick_spec objects_cut
        objects_answer lateOf_same)

variable {α W : Type} {F : Frame}

/-- **The clause at "objects".** -/
theorem item_objects (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hφh : ∀ s, seat.heard s = hd (φ s))
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (objectsRun seat)) (ht : tmOf o = plainTm (objVals hd lm jLK))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ a.1)) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true) :
    ItemIn L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  obtain ⟨z, G0, G, hz, hG0, hG, -, hRz⟩ := run_of_reader H L o hn _ hAt a.1 hsil R hR
  obtain ⟨F1, g, e1, e2, -⟩ := objects_cut seat (l := z.1) (s' := z.2) hz
  have hz' := objects_answer seat 0 e1 e2
  obtain rfl : z = (g.rows.toList.map seat.claim, seat.mark a.1 (F1.paid g.owedObjects)) :=
    Except.ok.inj (hz.symm.trans hz')
  obtain rfl : G0 = F1 := Option.some.inj (hG0.symm.trans ((hA.fork a.1).symm.trans e1))
  have hG' : G = G0.paid g.owedObjects := by
    have h1 : (seat.mark a.1 (G0.paid g.owedObjects)).fork? = some (G0.paid g.owedObjects) := by
      rw [hA.mark]
      exact fork_putFork a.1 G0 hG0 _
    exact Option.some.inj (hG.symm.trans h1)
  have hlate : K9.lateOf G0 G = [] := by
    rw [hG']
    exact lateOf_same G0 _ rfl
  have hforms : (g.rows.toList.map seat.claim).map (·.form) = g.rows.toList := by
    rw [List.map_map]
    exact (List.map_congr_left fun x _ => hA.form x).trans (List.map_id _)
  have hRz' : R = { forms := g.rows.toList, late := [] } := by
    rw [hRz, hlate]
    show K9.Read.mk ((g.rows.toList.map seat.claim).map (·.form)) [] = _
    rw [hforms]
  subst hRz'
  have hq2 : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hg' : hd (fixed9 φ a.1).1 = some g := by
    show hd (φ a.1) = _
    rw [← hφh]
    exact e2
  obtain ⟨rs0, hp⟩ := pick_some hd lm jLK hk hg' hq2
  obtain ⟨-, F0, u', hu', hI, hL⟩ := pick_spec hd lm jLK hp
  obtain rfl : pubOf b = u' := Option.some.inj (hq2.symm.trans hu')
  refine ⟨b, _, [(⟨(o.2, objectsRun seat), tmOf o, lenOf o⟩, objVals hd lm jLK)], hb, ?_, hR, hin,
    fun f hf => ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some (objectsRun seat) from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · refine List.mem_flatMap.2 ⟨_, List.mem_singleton.2 rfl, ?_⟩
    show f.value Reading.gl (worldOwn b [] (dataQ own b (rdW w))) ∈
      objVals hd lm jLK (fixed9 φ a.1) (dataQ own b (rdW w))
    have hf' : f ∈ g.rows.toList := hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf'
    have hi' : i < g.rows.size := by simpa using hi
    have hrow := hI.rows i hi' b.F hL (dataQ own b (rdW w)).mask
      (worldOwn b [] (dataQ own b (rdW w))).entry
    have hlen : i < (Fo.endsOf g.shape lm jLK rs0).rows.length := by
      rw [← hI.nRows]
      exact hi'
    unfold objVals
    rw [hp]
    refine List.mem_map.2 ⟨(Fo.endsOf g.shape lm jLK rs0).rows[i], List.getElem_mem hlen, ?_⟩
    rw [List.getD_eq_getElem _ _ hlen] at hrow
    rw [← hrow]
    have e3 : g.rows.getD i {} = g.rows.toList[i] := by
      simp [Array.getD, hi']
    rw [e3]
    rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.item_objects
