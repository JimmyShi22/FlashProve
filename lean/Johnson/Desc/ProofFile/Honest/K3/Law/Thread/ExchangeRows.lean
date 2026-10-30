-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeRows.lean: the honest side of the kind "lookup"
(K3): what the lookup's row owes behind its sub-protocol, first piece: the dictionary between the
run's coins and a witness's reading of places; what the program's structure of a hearing holds of
the description's structure; and the item on the rows of the library's row out. One definition of a
proposition, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the library says what stands behind a lookup's
sub-protocol in three items (Johnson/Top/H/K3RowOut.lean). Each speaks of a reading ν of places (a
mask entry; a cell of the planes' matrix), of the program's structure g of what was heard and of a
ledger, at all rounds for which that structure stands. The item on the rows is `K3OutRows`. `Left`
(Honest/K3/Law/LookLeftOf.lean) speaks of the description's structure of what was heard, at every
mask row under whose slots lie the coins that the stages spent (`MasksAre`,
Honest/K3/Law/Statements.lean).

What is shown.
  `Dict R ν`: the dictionary, the form of a hypothesis: the reading's mask entries under the
    lookup's slots are the coins that the course's stages spent. It is `MasksAre` at these mask
    entries. No statement of this file shows it of any witness.
  `toHeard_parts`: what the program's structure holds of the description's: shape, rows, theta,
    alpha, the form that the key tree leaves, the two points of the planes, the two halves of the
    key point.
  `outRows_of_zero`: on the library's side alone, over any commutative ring: where every heard row
    is worth 0 at one later ledger, at the reading's mask row, the item on the rows holds. No run of
    claims is involved.
  `outRows_of_left`: the item on the rows, at every ledger later than the one behind the hearing.
    Conditional on `Left` and `Dict`.

Hypotheses that remain.
  `hg`: the program's structure g is made of what was heard (`toHeard` returns).
  `hL`, `hz`: (in `outRows_of_zero`) H is later than F'; every heard row is worth 0 at H.
  `hLeft`, `hD`, `hL`: (in `outRows_of_left`) `Left`; `Dict`; F' is later than the ledger G behind
    the hearing.

How the proof goes. It rests on `Cb.Fo.PlaneClaims.rows_claim`
(OnBytes/Tie/Pv/Lookup/Forest/FoClaimsMeet.lean) and `laterFo_of_psc`
(Johnson/Top/H/K3LeftStatement.lean).

Users. `Dict` stands in statements of Honest/K3/Law/Thread/ExchangeKeys.lean,
Honest/K3/Law/Thread/ExchangePlanes.lean and Honest/K3/Law/Thread/ExchangeReading.lean;
`toHeard_parts` is called in ExchangeKeys.lean and in Honest/K3/Law/Thread/JoinBracket.lean
[not in this library]. Honest/K3/Good/Live/Runs.lean imports this file too.

Limits. No instance of these hypotheses is exhibited in this file. No course with a reading that
meets `Dict` is shown. At a structure for which no rounds stand the item holds of every reading.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.LookLeftOf
import Johnson.Top.H.K3LeftStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.Model.Forest (Shape)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.K3 (HeardV toHeard toHeardG)
open VerifiableInference.OnPublicFiles (K3OutRows laterFo_of_psc)

variable {W : Type}

/-- **The dictionary**: under the lookup's slots the reading's mask entries are the coins that the
course's stages spent. It is the form of a hypothesis. -/
def Dict (R : Course W) (ν : _root_.Fo.Pl → GE) : Prop := MasksAre R fun j => ν (.mask j)

/-- **What the program's structure of a hearing holds of the description's.** -/
theorem toHeard_parts {h : Shape} {gV : HeardV} {g : OnBytes.Model.Forest.Heard}
    (hg : toHeard h (toHeardG gV) = some g) :
    ∃ point form, gV.keys = [(point, form)] ∧ g.shape = h ∧ g.rows = gV.rows ∧ g.theta = gV.theta ∧
      g.alpha = gV.alpha ∧ g.cEnd = form ∧ g.zb0 = gV.zb0 ∧ g.zb1 = gV.zb1 ∧
      g.zx = point.extract 0 h.dT ∧ g.zy = point.extract h.dT point.size := by
  unfold toHeard at hg
  have hk : (toHeardG gV).keys = gV.keys := rfl
  rw [hk] at hg
  match hkk : gV.keys, hg with
  | [(point, form)], hg =>
    simp only at hg
    split at hg
    · obtain rfl := Option.some.inj hg
      exact ⟨point, form, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd hg (by simp)

/-- **On the library's side alone: where every heard row is worth 0 at one later ledger, at the
reading's mask row, the item on the rows holds.** -/
theorem outRows_of_zero {K : Type} [CommRing K] (ρ : Reading K) (g : OnBytes.Model.Forest.Heard)
    (F' H : Fork) (lm first : Nat) (ν : _root_.Fo.Pl → K) (entry : Nat → Nat → Nat → K)
    (hL : _root_.Fo.Later F' H)
    (hz : ∀ a ∈ g.rows.toList, a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0) :
    K3OutRows g.shape lm first ν ρ g F' := by
  intro rs hI y hy
  rw [← Cb.Fo.PlaneClaims.rows_claim ρ g lm first rs F' hI H hL ν entry] at hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
  exact hz a ha

/-- **The item on the rows of the row out**, at the program's structure of what was heard and at
every ledger later than the one behind the hearing. The item at a later ledger says more:
the structure stands there for more rounds. Conditional on `Left` and `Dict`. No instance of these
hypotheses is exhibited in this file. -/
theorem outRows_of_left (R : Course W) (planes : List (E × E) → GE) (keys : Nat → Array E → GE)
    (gV : HeardV) (G : Fork) (h : Shape) (g : OnBytes.Model.Forest.Heard)
    (hg : toHeard h (toHeardG gV) = some g) (hLeft : Left R planes keys gV G) (F' : Fork)
    (hL : OnBytes.PscRun.Later G F') (lm first : Nat) (ν : _root_.Fo.Pl → GE) (hD : Dict R ν) :
    K3OutRows h lm first ν Reading.gl g F' := by
  obtain ⟨_, _, _, hs, hr, _⟩ := toHeard_parts hg
  have key := outRows_of_zero Reading.gl g F' F' lm first ν (fun _ _ _ => 0)
    (laterFo_of_psc (OnBytes.PscRun.Later.refl F')) (by
      rw [hr]
      exact (hLeft.1 F' _ _ hL hD).1)
  rw [hs] at key
  exact key

#print axioms ProofFile.Honest.K3.Law.Exchange.toHeard_parts
#print axioms ProofFile.Honest.K3.Law.Exchange.outRows_of_zero
#print axioms ProofFile.Honest.K3.Law.Exchange.outRows_of_left

end ProofFile.Honest.K3.Law.Exchange
