--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/K8Owed.lean: THE DEBT MadeOwed AT THE 25 NUMBERS OF THE KIND K8
(the smallness test's draw), AT ANY D, AT THE BASE THAT ANSWERS "FALSE": FROM TWO NAMED PREMISES:
the earlier runs' tests are blind to the draw (hBl), and the ONE item that is new behind the draw
holds there (new). And so the row HandsR. Theorems, proved; three of them closed facts by the
kernel.



CALLED, NOT TYPED ANEW (the draw's own authors'): Drawn, drawn_of_yes (Johnson/Desc/First/K8/
TieRides.lean): every accepting decision of the draw lays two fields of the approximate range
proof's parameters and nothing else · TlBlind, k8Sort, pubAll_blind (Johnson/Desc/First/K8/
BlindPub.lean): the composed public test over the base "false" has one value in front of such a step
and behind it, at every item of the sorts k8Sort · k8_pub_full (BlindAtMg.lean, off the
kernel's k8PubB_full, TableAtK8.lean): in front of the draw in segment l every item asked is of
these sorts; behind it at most one more is asked: formsIn l (pcOf l) "small".

  drawn_lot   a sub-protocol of the seat's lots of the kind K8: every accepting decision is Drawn.
  linksW_full, placesW_full, k8_spot   our written list is theirs; a number 14 l + i + 2 of the kind
    K8 is their ixOf l, and its piece i + 1 their pcOf l: closed facts.
  k8_table   k8_pub_full in the letters of the ride (frontAt, behindAt,
    Johnson/Goal/Meaning/QuietRide.lean).
  k8_where   in scope, where b = c.blocksInOrder[k] is of the kind K8 in segment l: l < 25, k = ixOf l, its
    piece is pcOf l, and b stands under a lot's own sub-protocol of the kind K8.
  k8_owed   **MadeOwed at b = c.blocksInOrder[k] of the kind K8.** An item of the debt's list is asked
    behind. If it is asked in front too, it is of k8Sort: pubAll_blind hands its "true" on from the
    promise's public test in front. Else it is the one new item.
  k8_rows   so HandsR there (rows_at_base, Johnson/IMR/RowsAtPaid.lean).

OBJECT: c.blocksInOrder[k] at the 25 numbers ixOf l. USER: Johnson/IMR/RowsAtRch.lean. LETTERS: N,
D, z, Fk: free.

What is not claimed. hBl at any D. "new" at any state. Anything at a base that answers otherwise
than "false". That any state is reached, or that any step accepts. No soundness.
-/
import Johnson.IMR.HearOfQuiet
import Johnson.IMR.RowsAtPaid
import Johnson.P1K8R.BlindAtMg

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.Sound (moreAll linksFull)
open VerifiableInference.Desc.First (S Numbers Pub PubData pubAll ePubAt kindsBeforeBatching flatPlacesOf)
open VerifiableInference.Desc.First.K8 (Drawn drawn_of_yes TlBlind k8Sort pubAll_blind)
open VerifiableInference.Desc.Keeps (Decides)
open Meaning.Ride (frontAt behindAt madeAtK)
open P1K8T (ixOf pcOf k8_pub_full)
open ProofFile (Cl)

/-- **A sub-protocol of the seat's lots of the kind K8: every accepting decision is a draw's.** -/
theorem drawn_lot {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b' : Block S Cl} (hb : b' ∈ L.blocks G) (hk : b'.place.kind = .K8) : Decides Drawn b' := by
  obtain rfl : L = ProofFile.P1K8.lot Z := lot_of_kind hL hb (by rw [hk]; rfl)
  have hb'' : b' ∈ ProofFile.k8Whole Z G := by
    rcases blocks_mem hb with ⟨y, hy, -⟩ | h
    · exact nomatch hy
    · exact h
  obtain ⟨l, Xl, -, rfl⟩ := k8Whole_mem hb''
  exact fun s rs gs s' hd => drawn_of_yes (Cl := Cl) (ProofFile.k8ParW Z G Xl l).toPar s s' rs gs hd

/-- Our written list of segments is the full list of the draw's authors. -/
theorem linksW_full : linksW = linksFull := by decide +kernel

theorem placesW_full : placesW = flatPlacesOf linksFull true := by
  unfold placesW
  rw [linksW_full]

/-- A number of the kind K8 in front of a batching, and its piece, in the authors' letters. -/
theorem k8_spot : ∀ l < 25, ∀ i < 10, (kindsBeforeBatching (subAt l) (l == 0))[i]? = some KindName.K8 →
    14 * l + i + 2 = ixOf l ∧ i + 1 = pcOf l := by decide +kernel

/-- No segment hears at more than nine places in front of its batching. -/
theorem hear_short : ∀ l < 25, (kindsBeforeBatching (subAt l) (l == 0)).length < 10 := by decide +kernel

/-- **The table at the draw's border, in the ride's letters.** -/
theorem k8_table {l : ℕ} (hl : l ≤ 24) {p : Place} (hp : placesW[ixOf l]? = some p) :
    (∀ q ∈ frontAt moreAll linksW placesW (ixOf l), k8Sort l (pcOf l) q = true) ∧
      ∀ q ∈ behindAt moreAll linksW placesW (ixOf l) p,
        q ∈ frontAt moreAll linksW placesW (ixOf l) ∨ q = Pub.formsIn l (pcOf l) "small" := by
  rw [placesW_full] at hp
  have h := k8_pub_full hl hp
  unfold frontAt behindAt
  rw [placesW_full, linksW_full, ← VerifiableInference.Desc.Sound.mgMore_is]
  exact ⟨h.1, h.2.1⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Where a sub-protocol of the kind K8 stands.** -/
theorem k8_where (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hk : b.place.kind = .K8) {l : ℕ} (hl : b.place.link = some l) :
    l < 25 ∧ k = ixOf l ∧ b.place.piece = pcOf l ∧
      ∃ (b' : Block S Cl) (L : ProofFile.Lot), L ∈ ProofFile.onlineFirstChainBlockTables Z ∧ b' ∈ L.blocks Bs.G₀ ∧
        b'.place.kind = .K8 ∧ b.UnderR b' := by
  obtain ⟨l', i, k0, b', name, hl', hk0, ⟨L, hL, hb'⟩, hp, hla, rfl⟩ :=
    hear_of_quiet hS hR O hb (by rw [hk]; decide)
  have ep := alone_place hla
  rw [ep] at hk hl ⊢
  obtain rfl : k0 = .K8 := hk
  obtain rfl : l' = l := Option.some.inj hl
  have hi : i < 10 := Nat.lt_trans (List.getElem?_eq_some_iff.1 hk0).1 (hear_short l' hl')
  obtain ⟨ei, epc⟩ := k8_spot l' hl' i hi hk0
  exact ⟨hl', ei, epc, b', L, hL, hb', congrArg Place.kind hp, alone_underR hla⟩

/-- **THE DEBT AT THE SMALLNESS TEST's DRAW.** -/
theorem k8_owed {Q : Type} {N : Numbers} {D : PubData} {z : Q} {Fk : ℕ → S → Prop}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hk : b.place.kind = .K8) {l : ℕ} (hl : b.place.link = some l)
    (hBl : ∀ j r, j < b.place.piece → ∀ p ∈ D.runs l j r,
      TlBlind fun s => if D.ah p.1 p.2 then
          VerifiableInference.Desc.K9.formsInA (D.Rd l) (D.N.sent l) (D.N.group l) p.1 p.2 s
        else VerifiableInference.Desc.K9.formsIn (D.Rd l) (D.N.group l) p.1 p.2 s)
    (new : ∀ s s', Fk k s → Yes 0 b s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW (EAt D (fun _ _ => false) linksW placesW z) k s = true →
      pubAll D (fun _ _ => false) (.formsIn l b.place.piece "small") (z, s') = true) :
    MadeOwed Fk N linksW placesW D (fun _ _ => false) z 0 k b b.place := by
  obtain ⟨hl', rfl, hpc, b', L, hL, hb', hk', hU⟩ := k8_where hS hR O hb hk hl
  have hpW := place_at hS hR O hb
  rw [hpc] at hBl new
  obtain ⟨T1, T2⟩ := k8_table (by omega) hpW
  intro s s' f hy h0 h1 hx q hq
  obtain ⟨rs, cols, n, e⟩ := hy.under hU
  obtain ⟨-, -, -, hd⟩ := VerifiableInference.Desc.step_inv 0 b' s s' rs cols n e
  have hD : Drawn s s' := drawn_lot hL hb' hk' s _ _ s' hd
  unfold madeAtK at hq
  rcases T2 q (List.mem_filter.1 hq).1 with hfront | rfl
  · have hv : pubAll D (fun _ _ => false) q (z, s') = pubAll D (fun _ _ => false) q (z, s) :=
      pubAll_blind D l (pcOf l) q (T1 q hfront) hBl z s s' hD
    rw [hv]
    have e' : ePubAt (pubAll D fun _ _ => false) moreAll linksW placesW (ixOf l) (z, s) = true :=
      (xk_parts hx).2.2.2.2
    unfold ePubAt at e'
    exact List.all_eq_true.1 e' q hfront
  · exact new s s' f hy h0 h1 hx

/-- **SO THE ROW AT THE DRAW.** -/
theorem k8_rows {Q : Type} {D : PubData} {z : Q} {p : ProofFile.InstPub} {Fk : ℕ → S → Prop}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hk : b.place.kind = .K8) {l : ℕ} (hl : b.place.link = some l)
    (hFk : ∀ s, Fk k s → RF 0 c.blocksInOrder (ProofFile.startS Z) p k s)
    (hBl : ∀ j r, j < b.place.piece → ∀ q ∈ D.runs l j r,
      TlBlind fun s => if D.ah q.1 q.2 then
          VerifiableInference.Desc.K9.formsInA (D.Rd l) (D.N.sent l) (D.N.group l) q.1 q.2 s
        else VerifiableInference.Desc.K9.formsIn (D.Rd l) (D.N.group l) q.1 q.2 s)
    (new : ∀ s s', Fk k s → Yes 0 b s s' → s.failed = none → s'.failed = none →
      XK (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW
        (EAt D (fun _ _ => false) linksW placesW z) k s = true →
      pubAll D (fun _ _ => false) (.formsIn l b.place.piece "small") (z, s') = true) :
    HandsR Fk (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW
      (LPFK9.HandsAt.EW D (fun _ _ => false) z) 0 k b :=
  rows_at_base hS hR O hF N₀ hb (by rw [hk]; decide) hFk (k8_owed hS hR O hb hk hl hBl new)

end IM

#print axioms IM.drawn_lot
#print axioms IM.k8_spot
#print axioms IM.k8_table
#print axioms IM.k8_where
#print axioms IM.k8_owed
#print axioms IM.k8_rows
