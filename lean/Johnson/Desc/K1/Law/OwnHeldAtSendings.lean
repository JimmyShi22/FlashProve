-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/OwnHeldAtSendings.lean: IN FRONT
OF THE OUTPUT HEAD's TWO LATER SENDINGS (numbers 342 and 344) THE TABLE's PROMISE HOLDS THE PUBLIC
TEST THAT IS TIED TO THE CLAIM ON THE HEAD's OWN THREE RUNS; AND hquiet FROM THE SEGMENT's KIND.
Six theorems, two of them by the kernel.

Why. Our laws hwt_whole | hwtR_of (WtAt24.lean | WtBackAtReads.lean) ask hheard: "the head's reader
answers in front of the place". Kinds/Law/WeightHeardAt.lean's heard_at_T | heard_at_F get it from
just this public test's yes (and three premises of that file's, which read no list of extra public
tests, by its word). HERE the yes is got off OUR form of the promise (InAt), at ANY meaning Mg.

  ownT_open_at342 · own_open_at344  the claim is open there (the kernel).
  ownT_held_342  InAt … 342 x y → Mg.pub (.formsInT 24 4 "own") x = true.
  own_held_344   InAt … 344 x y → Mg.pub (.formsIn 24 4 "own") x = true.
  quiet_of_kind  where segment l's link has kind 2 (a head's), the quiet step behind its reads IS
                 ReadsQuiet.head at the ground's own letters: hquiet's payer, under "the link at
                 24 has kind 2".
What is not claimed. hheard itself (HeardAtSendings.lean has it, under its own premises). That the
link at 24 has kind 2. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.WtBackAtReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat KObj OnBytes.Slice
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound (CellsQ)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More start flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.Kinds.Head (seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt KeptW weightAt_kept keptW_reads_laid
  readsOf)
open VerifiableInference.Desc.K8 (ReadsQuiet.head ReadsQuiet.blockAt)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (k1Ix k1Reads k1Quiet)

set_option maxRecDepth 1000000 in
theorem ownT_open_at342 :
    Item.formsT 24 4 "own" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL 24 false) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem own_open_at344 :
    Item.forms 24 4 "own" ∈ openAt linksFull (flatPlacesOf linksFull true) (noL 24 true) := by
  decide +kernel

/-- What the promise holds of a public test that is tied to an open item. -/
theorem tied_held {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (k : ℕ) (x : Pp × S) (y : Strs)
    (h : InAt N Mg linksFull (flatPlacesOf linksFull true) k x y) (q : Pub)
    (hq : q ∈ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) k)) :
    Mg.pub q x = true := by
  obtain ⟨h, hm⟩ := h
  rcases h.2 with hx | ⟨h1, _⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    exact List.all_eq_true.1 h1.1.2 q (List.mem_append_right _ hq)

theorem ownT_held_342 {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (x : Pp × S) (y : Strs)
    (h : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL 24 false) x y) :
    Mg.pub (.formsInT 24 4 "own") x = true :=
  tied_held N Mg _ x y h _
    (List.mem_flatMap.2 ⟨_, ownT_open_at342, List.mem_singleton.2 rfl⟩)

theorem own_held_344 {Pp W : Type} (N : Numbers) (Mg : Meaning Pp W) (x : Pp × S) (y : Strs)
    (h : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL 24 true) x y) :
    Mg.pub (.formsIn 24 4 "own") x = true :=
  tied_held N Mg _ x y h _
    (List.mem_flatMap.2 ⟨_, own_open_at344, List.mem_singleton.2 rfl⟩)

/-- The quiet step behind a head's segment's reads. -/
theorem quiet_of_kind (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (hX : G.built[l]? = some X)
    (hk : X.kind = 2) :
    k1Quiet G l X = ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩ := by
  have hL : (G.built.toList.map fun Y => (Y.kind, Y.g))[l]? = some (X.kind, X.g) := by
    rw [List.getElem?_map, Array.getElem?_toList, hX]
    rfl
  unfold k1Quiet ProofFile.readsQuietAt ReadsQuiet.blockAt
  simp [hk, hL, ProofFile.orLoud]

end VerifiableInference.Desc.K1
