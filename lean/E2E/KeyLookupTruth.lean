--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLookupTruth.lean: WHAT AN HONEST SENDER OF A KEY FILE'S LOOKUP HAS BEYOND FORM, as a
statement: the claims that the hearing leaves hold of its mask entries, its keys and its bits.
Stated in the library's own three forms at the general face (Johnson/Desc/Key/KeyK3Items.lean:
`FormsObjects`, `WorthPlanes`, `WorthKeys`), and brought down to the form in which an honest side's
laws and toys evaluate a claim: on the ledger, with the mask entry under each SLOT. Definitions, one
structure, statements and proofs.

Why. The hearing of a lookup accepts any sender of the right counts (E2E/KeyLookupHears.lean's
head). What is consumed behind it (the rows that `layer` writes; the proximity test on the ranges'
group; the claims on keys) is true only of a sender whose hidden values are the right ones. The
library's table of joints for soundness says what «right» means at the border behind the lookup, of
a witness: a matrix, the multiplicities' message, the mask entries by (message, entry). An honest
side speaks of slots and its own coins. This file ties the two spellings, so that both sides meet in
one text.

What is defined.
  `worth G m a`: the form a on the ledger G, the mask entry under slot j being m j: the hidden value
    under a slot is what was shown less the factor times the mask entry.
  **`BySlots same f g G' cl m bit key`**: the three sentences in that spelling: every form of g.rows
    is worth 0 · for each of the three claims on the planes: lead + scalar · ⟨v, the bits⟩ is 0 ·
    for each part: the form beside its key tree's last point is worth the extension of alpha − key
    at that point.
  **`TruthAt same x L m mat valB mk l ranges codes g G home`**: the library's three forms at the key
    file's witness: the keys are `keyVec m L mat`, the bits are READ off the multiplicities' message
    valB by `bitVec` (Johnson/Desc/Key/KeyK3W.lean).
What is shown.
  `affAt_worth`: the library's `affAt` is `worth` at m j := mk (home j): by unfolding.
  **`truth_of_slots`**: where the leaves' sumcheck is closed (`closedAt`), every hidden value has a
    home, the forms are scoped and there are three claims and a form a part: `BySlots` at m j := mk
    (home j) gives the library's three forms.

Limits.
- NOTHING IS SHOWN OF ANY SENDER. `BySlots` is a premise: whoever lays the honest side of a lookup
  owes it.
- `closedAt` closes the leaves' sumcheck from the ledger behind the hearing; the key file's
  sub-protocol does so from that ledger with the first debt marked (E2E/KeyLookupAround.lean's
  `Left.planes`). That the two ledgers differ in the marks of debts alone is not shown here.
- `same` is a variable: the library's forms speak of machine elements up to a relation of the
  reader's.
- That the bits which `bitVec` reads are the bits of the keys' true counts is another file's
  (E2E/KeyPlanesRead.lean).
- Johnson/Desc/Key/KeyK3Items.lean and KeyK3W.lean hold statements alone.
  
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import E2E.KeyLookupAround
import Johnson.Desc.Key.KeyK3Items

set_option autoImplicit false

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key

/-- A form over hidden values, on a ledger, the mask entry under slot j being m j. -/
def worth (G : Fork) (m : ℕ → E) (a : Aff) : E :=
  a.slots.foldl (fun s t =>
    addE s (mulE t.2 (subE (G.vp.getD t.1 zeroE) (mulE (G.mf.getD t.1 zeroE) (m t.1))))) a.const

/-- The library's value of a form is that, at the mask entries of the slots' homes. -/
theorem affAt_worth (G : Fork) (home : Array Slot) (mk : Slot → E) (a : Aff) :
    affAt G home mk a = worth G (fun j => mk (home.getD j default)) a := rfl

/-- **The three sentences, by slots.** -/
structure BySlots (same : E → E → Prop) (f : Face) (g : HeardG) (G' : Fork)
    (cl : List PlaneClaim) (m : ℕ → E) (bit : ℕ → E) (key : ℕ → ℕ → E) : Prop where
  objects : ∀ a ∈ g.rows.toList, same (worth G' m a) zeroE
  planes : ∀ c ∈ cl, same (addE (worth G' m c.lead) (mulE c.scalar (planeSum f c.pairs bit))) zeroE
  keys : ∀ y ∈ g.keys.zipIdx, same (worth G' m y.1.2)
    (sumE (2 ^ f.parts.getD y.2 0) fun k =>
      mulE ((Tensor.eq y.1.1.toList.reverse).entry k) (subE g.alpha (key y.2 k)))

/-- **The library's three forms at the key file's witness.** -/
structure TruthAt (same : E → E → Prop) (x : Lookup) (L : Params.WfLookup) (m : Wf.Matrix)
    (mat : ℕ → ℕ → F) (valB : ℕ → E) (mk : Slot → E) (l : ℕ) (ranges : Params.WfPublic)
    (codes : Codes) (g : HeardG) (G : Fork) (home : Array Slot) : Prop where
  objects : FormsObjects same (faceOfLkp x) g G home mk
  planes : WorthPlanes same (faceOfLkp x) g G home mk (bitVec ranges codes l valB)
  keys : WorthKeys same (faceOfLkp x) g G home mk (keyVec m L mat)

theorem Scoped.lt {n : ℕ} {a : Aff} (h : Scoped n a) {home : Array Slot} (hh : home.size = n) :
    ∀ t ∈ a.slots, t.1 < home.size := fun t ht => hh ▸ h.2 t (Array.mem_toList_iff.2 ht)

/-- **From the sentences by slots to the library's three forms.** -/
theorem truth_of_slots {same : E → E → Prop} {f : Face} {g : HeardG} {G G' : Fork}
    {cl : List PlaneClaim} {home : Array Slot} {mk : Slot → E} {bit : ℕ → E} {key : ℕ → ℕ → E}
    (hc : closedAt f g G = some (cl, G')) (hh : home.size = f.slots) (h3 : cl.length = 3)
    (hn : g.keys.length = f.parts.length) (hr : ∀ a ∈ g.rows.toList, Scoped f.slots a)
    (hl : ∀ c ∈ cl, Scoped f.slots c.lead) (hk : ∀ k ∈ g.keys, Scoped f.slots k.2)
    (T : BySlots same f g G' cl (fun j => mk (home.getD j default)) bit key) :
    FormsObjects same f g G home mk ∧ WorthPlanes same f g G home mk bit ∧
      WorthKeys same f g G home mk key :=
  ⟨⟨cl, G', hc, fun a ha => ⟨(hr a ha).1, (hr a ha).lt hh, T.objects a ha⟩⟩,
    ⟨cl, G', hc, h3, fun c hcm => ⟨(hl c hcm).1, (hl c hcm).lt hh, T.planes c hcm⟩⟩,
    hn, ⟨cl, G', hc, fun y hy =>
      have hs := zipIdx_fst (P := fun k => Scoped f.slots k.2) g.keys 0 hk y hy
      ⟨hs.1, hs.lt hh, T.keys y hy⟩⟩⟩

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.affAt_worth
#print axioms AtPublicFiles.KeyLookup.truth_of_slots
