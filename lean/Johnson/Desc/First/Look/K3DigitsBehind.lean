-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/First/Look/K3DigitsBehind.lean (over a letter Mg; the door's name
«frame.liveIs» is none of K3's items): the lookup on the digits of a segment's approximate
range proof: THE TABLE's PROMISE BEHIND THE BLOCK, AT EVERY MEANING THAT SAYS AT K3's OWN ITEMS WHAT
THE LOOKUPS' LAYER SAYS (K3At X D L Mg, K3At.lean): the premise «behind» of k3_digits_row_seated_cut
(K3DigitsSeatedCut.lean) CUT BY SORT OF CLAUSE: through the rule for a quiet row (onQ_step_quiet,
Johnson/Desc/Sound/PromiseRidesQ.lean): what is K3's own is paid from the four facts in hand; what
is another layer's stays, each as a named premise on Mg. NO RESULT ON THE PROTOCOL.

Main names.
  k3Like q: the item is of one of the constructors that K3's layer fills (read off the constructor
    alone: no public parameters).
  digAllowedB Q i o q: of these, what may be open behind the digits' block: lookOut i (7 + o) · and,
    if open in front too: lookOut i (2 + o), leftOn of any segment.
  digTableB M links ps k a i o: A Bool ON THE TABLE ALONE: every item that is open or tied behind
    block number k is either none of K3's or allowed.
  pubP_cases: a small fact on constructors.
  piece_calls: the table's 2 + shift sub is K3.pieceAt X i false, from hpcT with hpc.
  k3_digits_behind_at: THE END.
PAID: «a mark stays», the statement's groups, the book's places: SameBut · «decodes»: in hand ·
shapeAt one border on: shapeAt_rides (Johnson/Desc/First/ShapeRides.lean) from
its Bool sameStand, with sameBut_standOf (K3ShapeBehind.lean) · bookAt one border on:
bookAt_step (Johnson/Desc/First/BookFit.lean) from the Bool bookFit and «this block tells no tree» ·
pubHeld at K3's items: lookOut i (7 + o) from k3OnOut in hand (fOut_at) · lookOut i (2 + o) from the
promise in front and DigLeft's last clause · leftOn: true by K3At · pubP at leftOn: leftOn_stays
(K3LeftItem.lean) at DigLeft's four facts, the ledger's sizes from k3OnIn.
LEFT, EACH ANOTHER LAYER's, ON Mg: hIn (inOrder rides) · hHeld, hSh, hNc (held, shown, no collision
ride at the open pins' tenants) · othersPub (every item behind that is none of K3's: ledger,
freeAbove, indexIs, indexThere, unheard …, AND formsIn i (7 + o) "objects", WHOSE MAKER THE TABLE
NAMES THIS BLOCK) · othersP (pubP at every item but left, leftOn). AND Bools ON THE TABLE AND THE
NUMBERS: hk1 with hfitS (sameStand) · hTab (digTableB) · hbf (bookFit) with hn.
OBJECT. The table's onQ at block numbers k and k + 1; no sub-protocol's text (the four facts are
handed in).
USER. «behind» in k3_digits_seatLaws_term (K3DigitsAtTerm.lean).
LETTERS. X, D, L, Mg; N, links, ps, k, a, a', i, sub, z; u, v; x.

Compiled with the whole library.
Limits. A rule over letters. digTableB hangs on Mg.more: evaluated at the empty door alone
(K3DigitsTable.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves
import Johnson.Desc.First.Look.K3At
import Johnson.Desc.Sound.DigitsRow
import Johnson.Desc.First.Look.K3ShapeBehind
import Johnson.Desc.Sound.PromiseRidesQ
import Johnson.Desc.First.ShapeRides
import Johnson.Desc.First.BookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers More openSets pubSets start
  sampledIn shift pubFit pubRowM pubStartM moreItem stepOpen pubStep pubOfItems pubHeld
  quietRow shapeAt bookAt sameStand shapeAt_rides bookFit bookAt_step)

/-- The item is of one of the constructors that K3's layer fills. -/
def k3Like : Pub → Bool
  | .lookIn _ _ => true
  | .lookOut _ _ => true
  | .linkFresh _ => true
  | .left _ => true
  | .leftOn _ => true
  | _ => false

/-- Of these, what may be open behind the digits' block of segment i. -/
def digAllowedB (Q : List Pub) (i o : ℕ) (q : Pub) : Bool :=
  q == .lookOut i (7 + o) ||
    (Q.contains q && (q == .lookOut i (2 + o) || match q with
      | .leftOn _ => true
      | _ => false))

/-- **A Bool on the table alone**: every item that is open or tied behind block number k is either
none of K3's or allowed. -/
def digTableB (M : More) (links : List ModelPart) (ps : List Desc.Place) (k : ℕ) (a : Desc.Place)
    (i o : ℕ) : Bool :=
  (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links a) ++
    pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD [])
      (Desc.First.rowOf links a))).all
    fun q => !k3Like q || digAllowedB ((pubSets M links ps)[k]?.getD []) i o q

theorem pubP_cases (q : Pub) : (∃ m, q = .left m) ∨ (∃ m, q = .leftOn m) ∨
    ((∀ m, q ≠ .left m) ∧ ∀ m, q ≠ .leftOn m) := by
  cases q <;> simp

/-- The table's count of the calls' piece is K3.pieceAt's, where the digits' is. -/
theorem piece_calls (X : Verify.Public) (i o : ℕ) (e : 7 + o = Desc.K3.pieceAt X i true) :
    2 + o = Desc.K3.pieceAt X i false := by
  unfold Desc.K3.pieceAt at e ⊢
  split at e <;> simp_all
  omega

section
variable {Cells Tok P : Type} {Fr : Frame} (links : List ModelPart)

/-- **THE PROMISE BEHIND THE DIGITS' BLOCK, UNDER K3At.** -/
theorem k3_digits_behind_at (X : Verify.Public) (D : Desc.First.Look.Sent)
    (L : K3Letters Cells Tok) (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
    (hK : K3At X D L Mg) (N : Numbers) (ps : List Desc.Place) (k : ℕ)
    (a a' : Desc.Place) (hk : ps[k]? = some a) (hk1 : ps[k + 1]? = some a')
    (hfitS : sameStand links a a' = true) (i : ℕ) (hi : a.link = some i) (sub : ModelPart)
    (hsub : links[i]? = some sub) (hpcT : a.piece = 7 + shift sub)
    (hpc : a.piece = Desc.K3.pieceAt X i true)
    (hTab : digTableB Mg.more links ps k a i (shift sub) = true)
    {x : Desc.First.Look.Place} (hlook : lookAt X i true = some x) (z : P)
    (u v : Desc.First.S × Fr.E.Str)
    (ha : onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) k u)
    (hOnIn : Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) u.1 =
      true)
    (T : SameBut u.1 v.1)
    (hOut : Desc.K3.k3OnOut (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x) v.1 =
      true)
    (hdec : Mg.decodes (z, v.1) (strsOf Fr v.2))
    (DL : DigLeft u.1 v.1)
    (hIn : Mg.inOrder (z, u.1) = true → Mg.inOrder (z, v.1) = true)
    (told : List (List Desc.Oracle)) (hbf : bookFit N ps told = true) (hn : told[k]? = some [])
    (hHeld : ∀ e ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.held e.1 e.2 (z, u.1) = true → Mg.held e.1 e.2 (z, v.1) = true)
    (hSh : ∀ e ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.shown e.1 e.2 (strsOf Fr u.2) → Mg.shown e.1 e.2 (strsOf Fr v.2))
    (hNc : ∀ e ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
      Mg.noColl e.1 e.2 (z, u.1) (strsOf Fr u.2) → Mg.noColl e.1 e.2 (z, v.1) (strsOf Fr v.2))
    (othersPub : ∀ r ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links a) ++
        pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD [])
          (Desc.First.rowOf links a)),
      k3Like r = false → Mg.pub r (z, v.1) = true)
    (othersP : ∀ r ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links a),
      (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → Mg.pubP r (z, v.1)) :
    onQ (Fr := Fr) N Mg links ps (fun s => (z, s)) (k + 1) v := by
  have e7 : 7 + shift sub = Desc.K3.pieceAt X i true := hpcT.symm.trans hpc
  have e2 : 2 + shift sub = Desc.K3.pieceAt X i false := piece_calls X i _ e7
  obtain ⟨F, Gk, hF, hG, hLk, hZ, hOth⟩ := DL
  obtain ⟨Fk, hFk, hSz, -⟩ := k3OnIn_ledger hOnIn
  obtain rfl : F = Fk := Option.some.inj (hF.symm.trans hFk)
  obtain ⟨hLat, hSzG, -⟩ := hZ hSz
  have hrow := digits_row links a i sub hi hsub hpcT
  have hq : quietRow (Desc.First.rowOf links a) = true := by
    unfold quietRow
    rw [hrow.1, hrow.2.1]
    rfl
  have hTab' := List.all_eq_true.1 hTab
  refine onQ_step_quiet N Mg links ps (fun s => (z, s)) k a hk hq u v ha ?_
    (fun _ => hdec) ?_ ?_ ?_ hIn ?_
    (fun _ hb => bookAt_step N ps told hbf k (List.getElem?_eq_some_iff.1 hk).1 hn u.1 v.1 T.book
      (by rw [T.st]) hb) ?_ hHeld hSh hNc
  · -- a mark stays
    intro hm
    show v.1.failed ≠ none
    rw [T.failed]
    exact hm
  · -- the book-keeping one border on
    intro hun
    obtain ⟨-, hor⟩ := ha
    rcases hor with hbad | ⟨hB, -, -, -⟩
    · exact absurd hun hbad
    · simp only [Bool.and_eq_true] at hB
      have h0 := hB.1.1.1.1.1
      rw [hk] at h0
      rw [hk1]
      exact shapeAt_rides links a a' u.1 v.1 hfitS (sameBut_standOf T)
        (by unfold Desc.First.S.noneWaits; rw [T.rowsOwed]) (by rw [T.link]) h0
  · show v.1.st.groups = u.1.st.groups
    rw [T.st]
  · show v.1.book.place = u.1.book.place
    rw [T.book]
  · -- the public items
    intro _ hfront
    unfold pubHeld at hfront ⊢
    rw [List.all_eq_true] at hfront ⊢
    intro r hr
    have ht := hTab' r hr
    cases hl : k3Like r with
    | false =>
      exact othersPub r hr hl
    | true =>
      rw [hl] at ht
      simp only [Bool.not_true, Bool.false_or, digAllowedB, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ht
      rcases ht with rfl | ⟨hQm, rfl | hm⟩
      · show Mg.pub (.lookOut i (7 + shift sub)) (z, v.1) = true
        rw [e7]
        exact fOut_at hK i true hlook z v.1 hOut
      · have hf : Mg.pub (.lookOut i (2 + shift sub)) (z, u.1) = true :=
          hfront _ (List.mem_append_left _ hQm)
        show Mg.pub (.lookOut i (2 + shift sub)) (z, v.1) = true
        rw [e2] at hf ⊢
        rw [hK.lookOut] at hf ⊢
        unfold k3OnOutAt placeAt at hf ⊢
        cases hc : lookAt X i false with
        | none =>
          rw [hc] at hf
          cases hf
        | some xc =>
          rw [hc] at hf
          exact hOth _ rfl hf
      · cases r with
        | leftOn m => exact hK.leftOn m _
        | _ => cases hm
  · -- the Prop-valued items
    intro _ hfrontP r hr
    rcases pubP_cases r with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨h1, h2⟩
    · have ht := hTab' _ (List.mem_append_left _ hr)
      simp [k3Like, digAllowedB] at ht
    · have ht := hTab' _ (List.mem_append_left _ hr)
      simp only [k3Like, Bool.not_true, Bool.false_or, digAllowedB, Bool.or_eq_true,
        Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ht
      have hQm : Pub.leftOn m ∈ (pubSets Mg.more links ps)[k]?.getD [] := by
        rcases ht with hc | ⟨hQm, -⟩
        · cases hc
        · exact hQm
      have hfp : Mg.pubP (.leftOn m) (z, u.1) := hfrontP _ hQm
      rw [hK.pLeftOn] at hfp
      obtain ⟨p, hp, Lp⟩ := hfp
      show Mg.pubP (.leftOn m) (z, v.1)
      rw [hK.pLeftOn]
      exact ⟨p, hp, leftOn_stays hLk hF hG hLat hSzG Lp⟩
    · exact othersP r hr h1 h2

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.piece_calls
#print axioms VerifiableInference.OnPublicFiles.k3_digits_behind_at
