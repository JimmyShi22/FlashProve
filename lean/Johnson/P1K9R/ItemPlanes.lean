-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K9R/ItemPlanes.lean: `TableOwes.hitems` (Johnson/Desc/First/Link/Law/LinkTable.lean), ONE
ITEM's CLAUSE (`ItemIn`, Johnson/Desc/First/Link/Law/HitemsStill.lean) AT AN ENTRY AT WHICH THE LINK
STATES THE LOOKUP ARGUMENT's RUN "planes". Three theorems, general in the lookup's accessors
(`K3.Seat`), in the caller's readers and in the tables of terms. The sister of
Johnson/P1K9R/ItemObjects.lean. A law file: no sub-protocol imports it.

Why. At this entry the reader is the run itself. Unlike "objects", the run FILLS SLOTS: the window
of the sumcheck over the leaves; so the reader's list of late slots is not empty, and the table's
world (`worldOwn`, Johnson/Desc/Sound/FormsQ.lean) reads these slots by what the run will lay.

What is said. `item_planes`: **the clause**: from: the entry is of the order, is not the approximate
range proof's, and the run "planes" at these accessors and readers stands there; the accessors are
the verifier's state's own (`AtS2`) and fit each other (`SeatFits`); what the lookup has heard is
read off the fixed part; the table of terms there is `plainTm (plVals .. bv pv)`; and at the
statement: a part is there; the lookups' promise `K3Ok` holds of what is fixed; the readers' second
hole says nothing; the table's public test says yes; and THE CALLER's CLAUSE, hB and hP: in the
world of every ledger later than the part's, at the data's mask row and the arrays' own rows, the
caller's forms on the columns are worth bv and pv.
  HOW. `run_of_reader`: what the reader gives is the run's own claims' forms, with the slots that
    are late between the ledger in front and the ledger G behind. `value_behind`
    (Johnson/Top/H/Keep/LateWorld.lean): a form that passes the public test is worth in the table's
    world what it is worth in G's own world, at the same entries. `planes_worth`
    (Johnson/Top/H/K3RunsLaw.lean): in the world of every later ledger, AT EVERY FUNCTION OF
    ENTRIES, the run's three claims are worth the three values, down to the worths of the caller's
    forms.

  `item_planes_unit`: the same with the caller's clause said at the entries `entUnit`
    (Johnson/Desc/First/Link/Law/EntryUnit.lean: the cells by the snapshot's list of arrays) in the
    place of the arrays' own rows: the two agree at every array that the segment's list names
    (`ent_meets`, WorldsMeet.lean), and the public test says that of each entry of the RUN's forms
    (`named_of_formsIn`); of the CALLER's forms nothing of the kind is asked. `caller_at_table`:
    that clause, for a form of the caller's that is read off the fixed part and names no slot, at
    the value `refValQ`.

Limits. An implication. THE STATEMENTS END IN `ItemIn`: AN INCLUSION UNDER "THERE ARE": what the
run's forms are, and how many, stands in the proofs alone. `item_planes` is called by no file.
WHETHER `K3Ok` HOLDS OF WHAT IS FIXED AT A REAL STATE, whether the public test says yes there, and
THE CALLER's CLAUSE are not shown here. Nothing on "join". No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Link.Law.HitemsStill
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Batch.Law.CoresTable
import Johnson.Top.H.Keep.RunsPlain
import Johnson.Top.H.Keep.K3Late
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H.Keep.ReaderIsRun
import Johnson.Top.H.Keep.LateWorld
import Johnson.Desc.First.Link.Law.WorldsMeet
import Johnson.P1K9R.CallerFenced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (planesRun)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.OnPublicFiles (AtS2 SeatFits plVals K3Ok pick_some pick_spec planes_heard
        planes_worth bitOf pinOf fork_of_atS refValQ)

variable {α W : Type} {F : Frame}

/-- **The clause at "planes".** -/
theorem item_planes (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hs : SeatFits seat (·.form)) (hφh : ∀ s, seat.heard s = hd (φ s))
    (readers : K3.Readers S)
    (bv : α × Option Pub9 → Bound Cb.Gl.E → ℕ → ℕ → Cb.Gl.E)
    (pv : α × Option Pub9 → Bound Cb.Gl.E → ℕ → Cb.Gl.E)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (planesRun seat lm readers)) (ht : tmOf o = plainTm (plVals hd lm jLK bv pv))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ a.1)) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true)
    (hB : ∀ G, _root_.Fo.Later b.F G → ∀ k col,
      (bitOf readers a.1 k col).value Reading.gl
        (G.worldOf Reading.gl (dataQ own b (rdW w)).mask
          (worldOwn b [] (dataQ own b (rdW w))).entry) =
        bv (fixed9 φ a.1) (dataQ own b (rdW w)) k col)
    (hP : ∀ G, _root_.Fo.Later b.F G → ∀ col,
      (pinOf readers a.1 col).value Reading.gl
        (G.worldOf Reading.gl (dataQ own b (rdW w)).mask
          (worldOwn b [] (dataQ own b (rdW w))).entry) =
        pv (fixed9 φ a.1) (dataQ own b (rdW w)) col) :
    ItemIn L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  obtain ⟨z, G0, G, hz, hG0, hG, -, hRz⟩ := run_of_reader H L o hn _ hAt a.1 hsil R hR
  obtain ⟨F1, g, -, e2⟩ := planes_heard seat lm readers (l := z.1) (s' := z.2) hz
  obtain rfl : G0 = b.F := Option.some.inj (hG0.symm.trans (fork_of_atS hb))
  have hfk : seat.fork a.1 = some b.F := (hA.fork a.1).trans hG0
  have hq2 : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hg' : hd (fixed9 φ a.1).1 = some g := by
    show hd (φ a.1) = _
    rw [← hφh]
    exact e2
  obtain ⟨su, ok, -⟩ := hk g (pubOf b) hg' hq2
  obtain ⟨rs0, hp⟩ := pick_some hd lm jLK hk hg' hq2
  obtain ⟨-, F0, u', hu', hI, hL⟩ := pick_spec hd lm jLK hp
  obtain rfl : pubOf b = u' := Option.some.inj (hq2.symm.trans hu')
  obtain ⟨G', f1, -, l1, -, -, hv⟩ := planes_worth seat (·.form) hs lm readers Cb.Gl.E Reading.gl g
    jLK rs0 F0 b.F 0 a.1 z.2 z.1 e2 hfk hI hL ok su hz
  obtain rfl : G' = G := Option.some.inj (f1.symm.trans ((hA.fork z.2).trans hG))
  subst hRz
  have hval := hv G' (_root_.Fo.Later.refl G') (_root_.Fo.muOf (dataQ own b (rdW w)).mask)
    (worldOwn b [] (dataQ own b (rdW w))).entry
  refine ⟨b, _, [(⟨(o.2, planesRun seat lm readers), tmOf o, lenOf o⟩, plVals hd lm jLK bv pv)],
    hb, ?_, hR, hin, fun f hf => ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) =
        some (planesRun seat lm readers) from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · refine List.mem_flatMap.2 ⟨_, List.mem_singleton.2 rfl, ?_⟩
    show f.value Reading.gl (worldOwn b (K9.lateOf b.F G') (dataQ own b (rdW w))) ∈
      plVals hd lm jLK bv pv (fixed9 φ a.1) (dataQ own b (rdW w))
    have haff : K9.affIn own (K9.mergeOf a.1) (K9.lateOf b.F G') b f = true := by
      have h0 := hin
      unfold K9.formsIn at h0
      rw [K9.segAt_of_atS a.1 b hb, hR] at h0
      exact List.all_eq_true.1 (Bool.and_eq_true_iff.1 h0).2 f hf
    rw [value_behind own (K9.mergeOf a.1) b G' l1 (dataQ own b (rdW w)) f haff]
    have hlist : plVals hd lm jLK bv pv (fixed9 φ a.1) (dataQ own b (rdW w)) =
        z.1.map fun c => c.form.value Reading.gl
          (G'.worldOf Reading.gl (dataQ own b (rdW w)).mask
            (worldOwn b [] (dataQ own b (rdW w))).entry) := by
      have e0 : bv (fixed9 φ a.1) (dataQ own b (rdW w)) 0 = fun col =>
          (bitOf readers a.1 0 col).value Reading.gl (G'.worldOf Reading.gl
            (fun j => _root_.Fo.muOf (dataQ own b (rdW w)).mask (.mask j))
            (worldOwn b [] (dataQ own b (rdW w))).entry) :=
        (funext fun col => hB G' l1 0 col).symm
      have e1 : bv (fixed9 φ a.1) (dataQ own b (rdW w)) 1 = fun col =>
          (bitOf readers a.1 1 col).value Reading.gl (G'.worldOf Reading.gl
            (fun j => _root_.Fo.muOf (dataQ own b (rdW w)).mask (.mask j))
            (worldOwn b [] (dataQ own b (rdW w))).entry) :=
        (funext fun col => hB G' l1 1 col).symm
      have e3 : pv (fixed9 φ a.1) (dataQ own b (rdW w)) = fun col =>
          (pinOf readers a.1 col).value Reading.gl (G'.worldOf Reading.gl
            (fun j => _root_.Fo.muOf (dataQ own b (rdW w)).mask (.mask j))
            (worldOwn b [] (dataQ own b (rdW w))).entry) :=
        (funext fun col => hP G' l1 col).symm
      unfold plVals
      rw [hp, e0, e1, e3]
      exact hval.symm
    rw [hlist]
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
    exact List.mem_map.2 ⟨c, hc, rfl⟩

/-- **The clause at "planes", with the caller's clause said at the entries `entUnit`**: the cells
by the snapshot's list of arrays. So nothing is asked on whether the arrays that the CALLER's forms
name are named by the segment's list: that is had, of the public test, for the RUN's forms alone. -/
theorem item_planes_unit (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hs : SeatFits seat (·.form)) (hφh : ∀ s, seat.heard s = hd (φ s))
    (readers : K3.Readers S)
    (bv : α × Option Pub9 → Bound Cb.Gl.E → ℕ → ℕ → Cb.Gl.E)
    (pv : α × Option Pub9 → Bound Cb.Gl.E → ℕ → Cb.Gl.E)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hn : (o.2 == "K8.equations") = false)
    (hAt : At L o (planesRun seat lm readers)) (ht : tmOf o = plainTm (plVals hd lm jLK bv pv))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ a.1)) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true)
    (hB : ∀ G, _root_.Fo.Later b.F G → ∀ k col,
      (bitOf readers a.1 k col).value Reading.gl
        (G.worldOf Reading.gl (dataQ own b (rdW w)).mask
          (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))) =
        bv (fixed9 φ a.1) (dataQ own b (rdW w)) k col)
    (hP : ∀ G, _root_.Fo.Later b.F G → ∀ col,
      (pinOf readers a.1 col).value Reading.gl
        (G.worldOf Reading.gl (dataQ own b (rdW w)).mask
          (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))) =
        pv (fixed9 φ a.1) (dataQ own b (rdW w)) col) :
    ItemIn L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  obtain ⟨z, G0, G, hz, hG0, hG, -, hRz⟩ := run_of_reader H L o hn _ hAt a.1 hsil R hR
  obtain ⟨F1, g, -, e2⟩ := planes_heard seat lm readers (l := z.1) (s' := z.2) hz
  obtain rfl : G0 = b.F := Option.some.inj (hG0.symm.trans (fork_of_atS hb))
  have hfk : seat.fork a.1 = some b.F := (hA.fork a.1).trans hG0
  have hq2 : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hg' : hd (fixed9 φ a.1).1 = some g := by
    show hd (φ a.1) = _
    rw [← hφh]
    exact e2
  obtain ⟨su, ok, -⟩ := hk g (pubOf b) hg' hq2
  obtain ⟨rs0, hp⟩ := pick_some hd lm jLK hk hg' hq2
  obtain ⟨-, F0, u', hu', hI, hL⟩ := pick_spec hd lm jLK hp
  obtain rfl : pubOf b = u' := Option.some.inj (hq2.symm.trans hu')
  obtain ⟨G', f1, -, l1, -, -, hv⟩ := planes_worth seat (·.form) hs lm readers Cb.Gl.E Reading.gl g
    jLK rs0 F0 b.F 0 a.1 z.2 z.1 e2 hfk hI hL ok su hz
  obtain rfl : G' = G := Option.some.inj (f1.symm.trans ((hA.fork z.2).trans hG))
  subst hRz
  have hval := hv G' (_root_.Fo.Later.refl G') (_root_.Fo.muOf (dataQ own b (rdW w)).mask)
    (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))
  refine ⟨b, _, [(⟨(o.2, planesRun seat lm readers), tmOf o, lenOf o⟩, plVals hd lm jLK bv pv)],
    hb, ?_, hR, hin, fun f hf => ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) =
        some (planesRun seat lm readers) from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · refine List.mem_flatMap.2 ⟨_, List.mem_singleton.2 rfl, ?_⟩
    show f.value Reading.gl (worldOwn b (K9.lateOf b.F G') (dataQ own b (rdW w))) ∈
      plVals hd lm jLK bv pv (fixed9 φ a.1) (dataQ own b (rdW w))
    have haff : K9.affIn own (K9.mergeOf a.1) (K9.lateOf b.F G') b f = true := by
      have h0 := hin
      unfold K9.formsIn at h0
      rw [K9.segAt_of_atS a.1 b hb, hR] at h0
      exact List.all_eq_true.1 (Bool.and_eq_true_iff.1 h0).2 f hf
    rw [value_behind own (K9.mergeOf a.1) b G' l1 (dataQ own b (rdW w)) f haff]
    have hsw : f.value Reading.gl (G'.worldOf Reading.gl (dataQ own b (rdW w)).mask
          (worldOwn b (K9.lateOf b.F G') (dataQ own b (rdW w))).entry) =
        f.value Reading.gl (G'.worldOf Reading.gl (dataQ own b (rdW w)).mask
          (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))) := by
      refine value_eq _ _ f (fun x hx => ?_) fun _ _ => rfl
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1
        (named_of_formsIn _ own o.1 o.2 a.1 b _ hb hR hin f hf x hx)
      exact (ent_meets b (K9.lateOf b.F G') (dataQ own b (rdW w)) (fixed9 φ a.1) hq2 x.tree x.row
        x.idx y hy).symm
    rw [hsw]
    have hlist : plVals hd lm jLK bv pv (fixed9 φ a.1) (dataQ own b (rdW w)) =
        z.1.map fun c => c.form.value Reading.gl
          (G'.worldOf Reading.gl (dataQ own b (rdW w)).mask
            (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))) := by
      have e0 : bv (fixed9 φ a.1) (dataQ own b (rdW w)) 0 = fun col =>
          (bitOf readers a.1 0 col).value Reading.gl (G'.worldOf Reading.gl
            (fun j => _root_.Fo.muOf (dataQ own b (rdW w)).mask (.mask j))
            (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))) :=
        (funext fun col => hB G' l1 0 col).symm
      have e1 : bv (fixed9 φ a.1) (dataQ own b (rdW w)) 1 = fun col =>
          (bitOf readers a.1 1 col).value Reading.gl (G'.worldOf Reading.gl
            (fun j => _root_.Fo.muOf (dataQ own b (rdW w)).mask (.mask j))
            (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))) :=
        (funext fun col => hB G' l1 1 col).symm
      have e3 : pv (fixed9 φ a.1) (dataQ own b (rdW w)) = fun col =>
          (pinOf readers a.1 col).value Reading.gl (G'.worldOf Reading.gl
            (fun j => _root_.Fo.muOf (dataQ own b (rdW w)).mask (.mask j))
            (entUnit (fixed9 φ a.1) (dataQ own b (rdW w)))) :=
        (funext fun col => hP G' l1 col).symm
      unfold plVals
      rw [hp, e0, e1, e3]
      exact hval.symm
    rw [hlist]
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
    exact List.mem_map.2 ⟨c, hc, rfl⟩

/-- **The caller's clause at the table**: a form of the caller's that is read off the fixed part and
names no slot is worth, in the world of whatever ledger at the entries `entUnit`, its worth in the
world that the snapshot names (`refValQ`, Johnson/P1K9R/CallerFenced.lean). -/
theorem caller_at_table {ι : Type} (fQ : ι → α × Option Pub9 → Aff) (i : ι) (q : α × Option Pub9)
    (u : Pub9) (hq : q.2 = some u) (hns : (fQ i q).slots = #[]) (G : Fork) (y : Bound Cb.Gl.E) :
    (fQ i q).value Reading.gl (G.worldOf Reading.gl y.mask (entUnit q y)) =
      refValQ fQ entUnit i q y := by
  unfold refValQ
  rw [hq]
  refine value_eq _ _ _ (fun _ _ => rfl) fun x hx => ?_
  rw [hns] at hx
  cases hx

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.item_planes
#print axioms VerifiableInference.Desc.LinkJoin.item_planes_unit
#print axioms VerifiableInference.Desc.LinkJoin.caller_at_table
