-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/BehindObjects.lean: the honest side of the kind "lookup"
(K3): THE ONE PUBLIC ITEM BEHIND THE SUB-PROTOCOL OF A LINK'S LOOKUP ON THE DIGITS THAT IS NONE OF
THE LOOKUPS' LAYER'S CONSTRUCTORS AND WHOSE MAKER THE TABLE NAMES THAT SUB-PROTOCOL:
`formsIn l k "objects"`: "every form that the run's reader gives at the state names only what is
there". Theorems.

WHAT THE ITEM ASKS OF THE STATE BEHIND (Johnson/Desc/First/Batch/FormsIn.lean, `K9.formsIn`; the
table's name "objects" stands for two runs, "objects" and "guests", at the lookup's own number):
the open segment is read off the state; the run's reader answers; and each form that it gives (at
"objects": the heard rows) names no entry, names slots alone that are filled in the state's ledger
and lie inside its arrays, none of them the slot of the merge's end value; and the mask row's
message is seated.

The library pays the item at its composed meaning at the full size (`objIn_dig`,
Johnson/Desc/Sound/MgAt/K3DigitsObjIn.lean). Here it is said AT A LETTER FOR THE MEANING, of which
ONE EQUATION is asked (hEq), and from an acceptance by the stated sub-protocol's decision.

  `rows_of_toHeard`   the program's structure has the rows that were heard
  `merge_free`        OURS: no heard row names the slot of the merge's end value, where that slot
                      lies outside the lookup's window (by
                      `heard_names`, Honest/K3/Parts/NamesOwn.lean)
  `objects_behind`    **the item holds behind the acceptance**
  `others_split`      a premise "every item of a list that is none of the lookups' layer's holds"
                      from this item and the rest

PREMISE · WHOSE. The acceptance; the ledger in front and its sizes; hmerge (payable by
`merge_free`): THE LOOKUPS'. hEq: the layer's that fills `formsIn` (the batching's); at the
library's composed meaning at the full size it is the rewriting inside the library's
`formsIn_make_mgAll` (same file as `objIn_dig`), with own := the link's group of the numbers, which
enters hmask too. hA, pass, hpass, hsame, hfO, hfG: the seat's and the link's readers and runs: the
description's. hmask: the mask row's message is sent and the book seats it: the senders' and the
book's. `merge_free`'s hout: the slot of the merge's end value is the end slot of the merge's own
masked sumcheck (OnBytes/Model/Merge.lean), another sub-protocol of the segment: taken in front of
the lookup it lies below the lookup's first slot, taken behind it at or above the lookup's last:
both arms stand in hout; which one holds at a segment is a line on the plan's numbers.

Limits. CONDITIONAL ON all of these. No instance of these hypotheses is exhibited in this file. At
claims of the library's own type (`Desc.Claim`), as the library's rule; the proof file's `ProofFile.Cl` is
that type (Johnson/Desc/ProofFile/LotCore.lean). On the verifier's side alone, but for
`merge_free`'s premise on the hearing. Nothing on soundness, completeness or any other property of a
protocol.
-/
import Johnson.Desc.Sound.MgAt.K3DigitsObjIn
import Johnson.Desc.ProofFile.Honest.K3.Parts.NamesOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Aff Fork)
open OnBytes.Model.Forest (Shape)
open VerifiableInference.Desc (Place Block Wit)
open VerifiableInference.Desc.K3 (theStated Readers pieceAt seatDigits HeardV hearV faceOf toHeard
  toHeardG)
open VerifiableInference.Desc.First (Pub Meaning)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles formsIn maskSeat
  mergeOf)
open VerifiableInference.OnPublicFiles
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (heard_names)

local notation "FS" => VerifiableInference.Desc.First.S

/-- The program's structure has the rows that were heard. -/
theorem rows_of_toHeard {h : Shape} {g : HeardV} {g' : OnBytes.Model.Forest.Heard}
    (e : toHeard h (toHeardG g) = some g') : g'.rows = g.rows := by
  unfold toHeard at e
  split at e
  · simp only at e
    split at e
    · cases e
      rfl
    · cases e
  · cases e

/-- **No heard row names the slot of the merge's end value.** CONDITIONAL ON the hearing's return,
on the seat reading its structure at t, and on that slot lying outside the lookup's window (a line
on numbers: not shown here). No instance of these hypotheses is exhibited in this file. -/
theorem merge_free {Cl : Type} (claim : Aff → Cl) (h : Shape) {F G : Fork} {rs : List Fmt.RoundView}
    {gV : HeardV} {g' : OnBytes.Model.Forest.Heard} {t : FS}
    (hh : hearV (faceOf h) F rs = some (gV, G)) (hg : toHeard h (toHeardG gV) = some g')
    (ht : (seatDigits claim).heard t = some g')
    (hout : ∀ j, mergeOf t = some j → j < F.next ∨ F.next + (faceOf h).slots ≤ j) :
    ∀ g, (seatDigits claim).heard t = some g → ∀ f ∈ g.rows.toList, ∀ y ∈ f.slots.toList,
      mergeOf t ≠ some y.1 := by
  intro g hgt f hf y hy hm
  obtain rfl : g' = g := Option.some.inj (ht.symm.trans hgt)
  obtain ⟨hok, hmsg⟩ := hearV_messages hh
  obtain ⟨c1, _⟩ := heard_names (two_le_planes_of_ok _ hok) hmsg
  rw [rows_of_toHeard hg] at hf
  obtain ⟨a, b⟩ := c1 f hf y hy
  rcases hout y.1 hm with h1 | h1 <;> omega

section
variable {Pp Wt : Type} (Mg : Meaning Pp Wt) {X : OnBytes.Model.Verify.Public}

/-- **CONDITIONAL ON what this file's head lists (no instance of them is exhibited in this file):
the item `formsIn l k "objects"` holds behind an acceptance by the stated sub-protocol's decision at
the digits' address.** -/
theorem objects_behind (H : LinkHoles) (lk : VerifiableInference.Desc.Link FS
    VerifiableInference.Desc.Claim)
    (readers : Nat → Option (Readers FS)) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (B : Block FS VerifiableInference.Desc.Claim)
    (claim : Aff → VerifiableInference.Desc.Claim)
    (h : theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) {l : Nat}
    (hi : a.link = some l) (hpc : a.piece = pieceAt X l true) {k B₀ : Nat}
    (own : List (Nat × Nat))
    (hEq : ∀ u : Pp × FS, Mg.pub (.formsIn l k "objects") u =
      ([(B₀, "objects"), (B₀, "guests")] : List (Nat × String)).all fun p =>
        formsIn (readersOfLink H lk) own p.1 p.2 u.2)
    (hA : AtS2 (seatDigits claim)) (z : Pp) (s s₂ : FS) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : B.decide s rs gs = .ok s₂) {F : Fork}
    (hF : s.fork? = some F) (hS : OnBytes.PscRun.Sized F) (pass : FS → FS → Prop)
    (hpass : ∀ t G, pass t (t.putFork G)) (hsame : ∀ t, pass t t)
    (hfO : ∃ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "objects") = some (n, r) ∧
      RunOver pass r (objectsRun (seatDigits claim)))
    (hfG : ∃ n r, (statesOfLink lk B₀).find? (fun x => x.1 == "guests") = some (n, r) ∧
      RunOver pass r (guestsRun
        ([] : List (VerifiableInference.Desc.First.Look.Guest FS VerifiableInference.Desc.Claim))))
    (hmask : ∀ c, segAt? s₂ = some c → (maskSeat own c).isSome = true)
    (hmerge : ∀ g, (seatDigits claim).heard s₂ = some g → ∀ f ∈ g.rows.toList,
      ∀ y ∈ f.slots.toList, mergeOf s₂ ≠ some y.1) :
    Mg.pub (.formsIn l k "objects") (z, s₂) = true := by
  obtain ⟨G, g, hG, hg, hNm, hSz⟩ :=
    digits_behind_named claim readers X codes shape a B h hOk l hi hpc s s₂ rs gs hd hF hS
  obtain ⟨Lc, hLc⟩ := link_some_of_fork hG
  obtain ⟨c, hc, -, hcF, -, -⟩ := segAt_make hLc hG (tl_some_of_fork hG)
  rw [hEq, List.all_eq_true]
  intro p hpm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
  rcases hpm with rfl | rfl
  · exact objects_formsIn H lk B₀ own (seatDigits claim) hA pass hpass hfO hc hg
      (by rw [hcF]; exact hNm) (by rw [hcF]; exact hSz) (hmask c hc) (hmerge g hg)
  · exact guests_formsIn H lk B₀ own pass hsame hfG hc

/-- "Every item of the list that the test rejects (like r = false) holds", from one item and the
rest. -/
theorem others_split (Q : List VerifiableInference.Desc.First.Pub)
    (like : VerifiableInference.Desc.First.Pub → Bool) (r₀ : VerifiableInference.Desc.First.Pub)
      (u : Pp × FS)
    (h0 : Mg.pub r₀ u = true)
    (hrest : ∀ r ∈ Q, like r = false → r ≠ r₀ → Mg.pub r u = true) :
    ∀ r ∈ Q, like r = false → Mg.pub r u = true := by
  intro r hr hk
  by_cases e : r = r₀
  · rw [e]
    exact h0
  · exact hrest r hr hk e

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.rows_of_toHeard
#print axioms ProofFile.Honest.K3.Law.AtThr.merge_free
#print axioms ProofFile.Honest.K3.Law.AtThr.objects_behind
#print axioms ProofFile.Honest.K3.Law.AtThr.others_split
