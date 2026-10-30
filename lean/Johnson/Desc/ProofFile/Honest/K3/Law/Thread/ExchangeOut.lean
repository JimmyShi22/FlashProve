-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeOut.lean: the honest side of the kind "lookup"
(K3): THE LIBRARY'S ROW OUT BEHIND AN HONEST LOOKUP, in one theorem; and its three items as the
table of joints has them at a carried state. Theorems with proofs; no definition.

`K3Out` (Johnson/Top/H/K3RowOut.lean) is what the library says stands behind a lookup's
sub-protocol: the rows, the planes and the keys, each at all rounds for which the heard structure
stands. Honest/K3/Law/Thread/ExchangeRows.lean, ExchangePlanes.lean and ExchangeKeys.lean give the
three from `Left`; here their premises are gathered once.

  `zb_sizes_of`     the two points of the planes have mu + d coordinates, where what was heard
                    is the run's
  `rowOut_of_left`  CONDITIONAL, as listed below: `K3Out h lm first ν kv Reading.gl g F'`
  `worth_of_left`   the same at a carried state that holds the ledger F' and the heard structure
                    g: the item "objects" in its inner form, worth "planes", worth "keys"
                    (`K3Objects`, `K3WorthPlanes`, `K3WorthKeys`, Johnson/Top/H/K3Worth.lean), at
                    the witness's reading nu w and key vectors Kv w

THE PREMISES, ONCE.
  public            the face is the shape's; the library's test on the shape; 5 ≤ lm ≤ kT + 5
  of the hearing    it returned from a ledger with its sizes and room; the program's structure of it
                    is g; what was heard is the run's, with its points
  of the summands   `Left`, at the planes' values and the keys' extension of data D at the
                    specification's own numbers
  of the ledger F'  its sizes; later than the one behind the hearing; the leaves' own slots still
                    owed; the planes' debt not yet marked
  OF THE READING ν AND THE VECTORS kv   ν reads 0 at the place "zero"; D's BITS ARE ν's READINGS OF
                    THEIR PLACES; D's KEYS ARE THE JOINT VECTOR OF kv; THE DICTIONARY: under the
                    lookup's slots ν's mask entries are the coins spent

hD takes `Dict R ν`, which unfolds to `MasksAre`, as a hypothesis: neither test on the book nor
`CoinsAre` stands in these sentences: a caller brings them (`dictAt`, DictAt.lean). The letter first
is free here: a caller lays the site's own. The library's limit on `K3Out` holds here too
(Johnson/Top/H/K3RowOut.lean's head): at a record whose g and F' no rounds could have left it holds
of every witness for nothing; `K3Stands` shuts that: shown for the lookups, conditional, in
StandsAt.lean (`stands_at`), StandsBehind.lean (`stands_member`) and LaysStands.lean.

Limits. One part of keys (a proof file's lookup). That the table's own reading and key vectors at an
honest witness meet the last four premises is shown nowhere here. The fourth item, on the caller's
riders: Honest/K3/Law/Thread/ExchangeRider.lean. No instance of these hypotheses is exhibited in
this file. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeKeys
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangePlanes
import Johnson.Top.H.K3Worth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E)
open OnBytes.Model (Fork Reading)
open OnBytes.Model.Forest (Shape)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Later)
open OnBytes.HonestTrace.Look (Data)
open VerifiableInference.Desc.K3 (HeardV faceOf hearV toHeard toHeardG unpaid)
open VerifiableInference.Desc.First.Look (planesOk)
open VerifiableInference.OnPublicFiles (K3Out K3Objects K3WorthPlanes K3WorthKeys k3Worth_of_out)
open ProofFile.Honest.K3.Law.Spec (planesOf keysOf)

/-- The two points of the planes have mu + d coordinates, where what was heard is the run's. -/
theorem zb_sizes_of {f : LFace} {gV : HeardV} {base : Nat} {heard : List Fmt.Drawn}
    (hP : PointsAgree f gV base heard) : gV.zb0.size = f.mu + f.d ∧ gV.zb1.size = f.mu + f.d := by
  rw [hP.zb0, hP.zb1]
  constructor
  · show ((varChals _ _ _ _ (f.mu + f.d)).toArray).size = _
    simp [varChals]
  · show ((varChals _ _ _ _ (f.mu + f.d)).toArray).size = _
    simp [varChals]

/-- **CONDITIONAL, as the file's head lists: THE LIBRARY'S ROW OUT BEHIND AN HONEST LOOKUP.**
No instance of these hypotheses is exhibited in this file. -/
theorem rowOut_of_left {W : Type} (R : Course W) (h : Shape) (hf : R.f = faceOf h) (lm jLK : Nat)
    (D : Data _root_.Fo.Pl KE) (hDN : D.N = _root_.Fo.numsF h lm jLK (up R.pts.theta))
    {F G F' : Fork} {x : List Fmt.RoundView} {gV : HeardV} {g : OnBytes.Model.Forest.Heard} (hS : Sized F)
    (hroom : F.next + (faceOf h).slots ≤ F.ns) (hh : hearV (faceOf h) F x = some (gV, G))
    (hg : toHeard h (toHeardG gV) = some g) (hH : HeardIs R gV)
    (hP : PointsAgree R.f gV R.a.base (R.t.heard ++ R.ds))
    (hLeft : Left R (planesOf D) (keysOf D) gV G) (hok : FoNums.ok h = true)
    (hpo : planesOk h lm = true) (hS' : Sized F') (hL : Later G F')
    (ho : OnBytes.PscRun.SlotsOwed F' (F.next + firstSlot (faceOf h) .leaves)
      (Stage.own (faceOf h) .leaves))
    (hu : unpaid F' g.owedPlanes = true) (first : Nat) (ν : _root_.Fo.Pl → GE) (h0 : ν .zero = 0)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = ν (D.N.bAt u j))
    (kv : Nat → Nat → GE)
    (hkey : ∀ x, x < 2 ^ h.v → D.key x = OnBytes.Ends.jointKey h kv (up R.pts.theta) x)
    (hD : Dict R ν) : K3Out h lm first ν kv Reading.gl g F' := by
  obtain ⟨z0, z1⟩ := zb_sizes_of hP
  have hv : h.v < 64 := Nat.lt_trans (Cb.Fo.ok_parts hok).1.2.2.2.2.1 (by decide)
  rw [hf] at z0 z1
  have hDv : D.v = h.v := by
    unfold Data.v
    rw [hDN]
    exact (Cb.Fo.ok_v hok).symm
  exact ⟨outRows_of_left R _ _ gV G h g hg hLeft F' hL lm first ν hD,
    outPlanes_of_left R h hf _ D lm jLK _ hDN hS hroom hh hg hLeft hok hpo hv z0 z1 hS' hL ho hu
      first ν
      h0 hbit hD,
    outKeys_of_left R _ D gV G h g hg hok (by rw [hf]; rfl) hH hP hLeft kv hDv hkey F' hL lm first ν
      hD⟩

/-- **CONDITIONAL on the same, at the witness's reading and key vectors: the three items at a
carried state** that holds the ledger F' and the heard structure g. No instance of these hypotheses
is exhibited in this file. -/
theorem worth_of_left {W S Wt : Type} (R : Course W) (h : Shape) (hf : R.f = faceOf h)
    (lm jLK : Nat)
    (D : Data _root_.Fo.Pl KE) (hDN : D.N = _root_.Fo.numsF h lm jLK (up R.pts.theta))
    {F G F' : Fork} {x : List Fmt.RoundView} {gV : HeardV} {g : OnBytes.Model.Forest.Heard} (hS : Sized F)
    (hroom : F.next + (faceOf h).slots ≤ F.ns) (hh : hearV (faceOf h) F x = some (gV, G))
    (hg : toHeard h (toHeardG gV) = some g) (hH : HeardIs R gV)
    (hP : PointsAgree R.f gV R.a.base (R.t.heard ++ R.ds))
    (hLeft : Left R (planesOf D) (keysOf D) gV G) (hok : FoNums.ok h = true)
    (hpo : planesOk h lm = true) (hS' : Sized F') (hL : Later G F')
    (ho : OnBytes.PscRun.SlotsOwed F' (F.next + firstSlot (faceOf h) .leaves)
      (Stage.own (faceOf h) .leaves))
    (hu : unpaid F' g.owedPlanes = true) (first : Nat) (fork : S → Option Fork)
    (heard : S → Option OnBytes.Model.Forest.Heard) (nu : Wt → _root_.Fo.Pl → GE)
    (Kv : Wt → Nat → Nat → GE) (s : S) (w : Wt) (hfork : fork s = some F')
      (hheard : heard s = some g)
    (h0 : nu w .zero = 0)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = nu w (D.N.bAt u j))
    (hkey : ∀ x, x < 2 ^ h.v → D.key x = OnBytes.Ends.jointKey h (Kv w) (up R.pts.theta) x)
    (hD : Dict R (nu w)) :
    K3Objects fork heard h lm first nu s w ∧ K3WorthPlanes fork heard h lm first nu s w ∧
      K3WorthKeys fork heard h lm first nu Kv s w :=
  k3Worth_of_out fork heard h lm first nu Kv hfork hheard
    (rowOut_of_left R h hf lm jLK D hDN hS hroom hh hg hH hP hLeft hok hpo hS' hL ho hu first
      (nu w)
      h0 hbit (Kv w) hkey hD)

#print axioms ProofFile.Honest.K3.Law.Exchange.zb_sizes_of
#print axioms ProofFile.Honest.K3.Law.Exchange.rowOut_of_left
#print axioms ProofFile.Honest.K3.Law.Exchange.worth_of_left

end ProofFile.Honest.K3.Law.Exchange
