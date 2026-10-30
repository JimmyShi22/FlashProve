-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/OpensRides.lean: «A YES HANDS THE CONDITION ON», AT THE TABLE's OWN
PROMISE (`onT`, LinkTiedAt.lean), OVER THE ONE EQUATION's PIECE: the law's premise hon3. Its row
opens a class of rows, so the table's rule for a quiet row does not serve: here is the rule for a
row that closes and opens NO PIN (it may close and open classes of rows), and its use at that piece.
Theorems.

What is said.
  `onAt_step_nopin`: **the table's promise rides past a block whose row closes and opens no pin**,
    clause by clause: as the table's own rule for a quiet row (Johnson/Desc/First/PromiseRides.lean:
    `onAt_step_held`), but that the tests on the open rows and on the members are asked behind AT
    THE OPEN SET BEHIND. `onT_rides_nopin`: the same at `onT … k` and `onT … (k + 1)`, with the
    meaning's share as `MgRides` (QuietRides.lean). `hon3_at`: **for a piece that holds a block each
    of whose yeses is the one equation's: `onT … k a` and the piece's yes give `onT … (k + 1) b`**:
    the share of the verifier's state by EqLays.lean and EqHands.lean.

Limits. `MgRides` IS A PREMISE AT EVERY PAIR OF STATES: payable only at a filling of the table's
meaning. The premises on public data are EqHands.lean's (the facts on the written list:
LinkPlacesFit.lean's `fit_eq`; the plan's numbers: shown of none). hg («the group that the link's
context names is the plan's group of the segment») is asked of the promise in front: no clause of it
is shown here to give that. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.EqHands
import Johnson.Desc.First.Link.Law.FromPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub BlockRow Meaning Numbers start rowOf
  openSets pubSets pubRowM pubStep stepOpen shapeAt rowsHeld membersHeld pubHeld bookAt sampledIn
  samplesHeld onAt rowSegs rowsDue)
open _root_.Run.PQ (CK)

variable {P W : Type}

/-- **THE PROMISE RIDES PAST A BLOCK WHOSE ROW CLOSES AND OPENS NO PIN.** -/
theorem onAt_step_nopin (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (p p' : Option Place)
    (O : List Item) (Q Q' : List Pub) (r : BlockRow) (a b : P × S) (y y' : Strs)
    (hi : ∀ i ∈ r.ins, i.isPin = false) (ho : ∀ i ∈ r.outs, i.isPin = false)
    (ha : onAt N Mg links p O Q a y)
    (hMark : a.2.failed ≠ none → b.2.failed ≠ none)
    (hDec : Mg.decodes a y → Mg.decodes b y')
    (hShape : a.2.failed = none → b.2.failed = none → shapeAt links p' b.2 = true)
    (hR : a.2.failed = none → b.2.failed = none → rowsHeld N O a.2 = true →
      rowsHeld N (stepOpen O r) b.2 = true)
    (hM : a.2.failed = none → b.2.failed = none → membersHeld N O a.2 = true →
      membersHeld N (stepOpen O r) b.2 = true)
    (hIn : a.2.failed = none → b.2.failed = none → Mg.inOrder a = true → Mg.inOrder b = true)
    (hPub : a.2.failed = none → b.2.failed = none → pubHeld Mg O Q a = true →
      pubHeld Mg (stepOpen O r) Q' b = true)
    (hBook : a.2.failed = none → b.2.failed = none → bookAt N p a.2 = true →
      bookAt N p' b.2 = true)
    (hPP : a.2.failed = none → b.2.failed = none → (∀ q ∈ Q, Mg.pubP q a) →
      ∀ q ∈ Q', Mg.pubP q b)
    (hHeld : a.2.failed = none → b.2.failed = none → ∀ x ∈ sampledIn N O,
      Mg.held x.1 x.2 a = true → Mg.held x.1 x.2 b = true)
    (hSN : a.2.failed = none → b.2.failed = none → ∀ x ∈ sampledIn N O,
      Mg.shown x.1 x.2 y ∧ Mg.noColl x.1 x.2 a y → Mg.shown x.1 x.2 y' ∧ Mg.noColl x.1 x.2 b y') :
    onAt N Mg links p' (stepOpen O r) Q' b y' := by
  have hsam : sampledIn N (stepOpen O r) = sampledIn N O :=
    First.sampledIn_of_filter N O (stepOpen O r) (First.stepOpen_filter Item.isPin O r hi ho)
  refine ⟨hDec ha.1, ?_⟩
  by_cases hb : b.2.failed = none
  · have hm : a.2.failed = none := Classical.byContradiction fun h => hMark h hb
    rcases ha.2 with hx | ⟨hB, hs, hall, hpp⟩
    · exact absurd hm hx
    · right
      simp only [Bool.and_eq_true] at hB
      obtain ⟨⟨⟨⟨⟨_, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hB
      refine ⟨?_, ?_, ?_, hPP hm hb hpp⟩
      · rw [hShape hm hb, hR hm hb h2, hM hm hb h3, hIn hm hb h4, hPub hm hb h5, hBook hm hb h6]
        rfl
      · unfold samplesHeld at hs ⊢
        rw [hsam]
        apply List.all_eq_true.2
        intro x hx
        exact hHeld hm hb x hx (List.all_eq_true.1 hs x hx)
      · intro x hx
        rw [hsam] at hx
        exact hSN hm hb x hx (hall x hx)
  · left
    exact hb

variable {F : Frame}

/-- The same at the table's own promises with «no mark». -/
theorem onT_rides_nopin (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place)
    (z : P) (k : ℕ) (p : Place) (hp : pl[k]? = some p)
    (hi : ∀ i ∈ (rowOf links p).ins, i.isPin = false)
    (ho : ∀ i ∈ (rowOf links p).outs, i.isPin = false) (a b : S × F.E.Str)
    (hf : b.1.failed = a.1.failed) (hShape : shapeAt links pl[k + 1]? b.1 = true)
    (hR : rowsHeld Nm (stepOpen ((openSets links pl (start links))[k]?.getD []) (rowOf links p))
      b.1 = true)
    (hM : membersHeld Nm (stepOpen ((openSets links pl (start links))[k]?.getD [])
      (rowOf links p)) b.1 = true)
    (hBook : bookAt Nm pl[k + 1]? b.1 = true) (M : MgRides Nm Mg links pl z k p a b)
    (ha : onT Nm Mg links pl (fun s : S => (z, s)) k a) :
    onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b := by
  refine ⟨?_, by show ¬ b.1.failed ≠ none; rw [hf]; exact ha.2⟩
  have hq := ha.1
  unfold onQ at hq ⊢
  rw [First.openSets_succ links pl (start links) k p hp,
    First.pubSets_succ Mg.more links pl k p hp]
  exact onAt_step_nopin Nm Mg links pl[k]? pl[k + 1]? _ _ _ (rowOf links p) (z, a.1) (z, b.1) _ _
    hi ho hq (fun h => by show b.1.failed ≠ none; rw [hf]; exact h) M.dec (fun _ _ => hShape)
    (fun _ _ _ => hR) (fun _ _ _ => hM) (fun _ _ => M.inOrder) (fun _ _ => M.pub)
    (fun _ _ _ => hBook) (fun _ _ => M.pubP) (fun _ _ => M.held)
    fun _ _ x hx h => ⟨M.shown x hx h.1, M.noColl x hx h.2⟩

variable {C : CK}

/-- **hon3 AT onT**: over the one equation's piece. -/
theorem hon3_at (Nm : Numbers) (Mg : Meaning P W) (links : List ModelPart) (pl : List Place) (z : P)
    (k m : ℕ) (p p' : Place) (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p')
    (hn : NextIn links p p') (hins : (rowOf links p).ins = [.total m])
    (houts : (rowOf links p).outs = [.row m .equation])
    (fresh : Item.row m .equation ∉ (openSets links pl (start links))[k]?.getD [])
    (seg : m ∈ rowSegs ((openSets links pl (start links))[k]?.getD []))
    (hat : Nm.rowsAt m .equation =
      (rowsDue Nm ((openSets links pl (start links))[k]?.getD []) m, 1))
    (inj : ∀ m' ∈ rowSegs ((openSets links pl (start links))[k]?.getD []), m' ≠ m →
      Nm.groupAt m' ≠ Nm.groupAt m)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim W) (hb : pe.b = below b₃)
    (hg : ∀ a : S × F.E.Str, onT Nm Mg links pl (fun s : S => (z, s)) k a →
      ∀ x, atS.get? a.1 = some x → Nm.groupAt m = x.L.check.group)
    (M : ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → pe.ior.red.out a τ = some b →
      MgRides Nm Mg links pl z k p a b) :
    ∀ a τ b, onT Nm Mg links pl (fun s : S => (z, s)) k a → pe.ior.red.out a τ = some b →
      onT Nm Mg links pl (fun s : S => (z, s)) (k + 1) b := by
  intro a τ b ha hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  obtain ⟨x, row, G0, hx, hG, El⟩ := eq_lays pw b₃ hb₃ _ _ _ _ _ j hstep
  obtain ⟨h1, h2, h3, _, _, h6⟩ := onT_bools Nm Mg links pl z k a ha
  refine onT_rides_nopin Nm Mg links pl z k p hp (by rw [hins]; simp [Item.isPin])
    (by rw [houts]; simp [Item.isPin]) a b El.failed ?_
    (eq_rows Nm _ _ m hins houts fresh seg hat inj a.1 b.1 _ row G0 El hG (hg a ha x hx) h2)
    (eq_members Nm _ _ m hins houts fresh seg a.1 b.1 _ row El h3)
    (eq_book Nm _ _ ht hm a.1 b.1 _ row El h6) (M a τ b ha hout) ha
  rw [hp] at h1
  rw [hp']
  exact eq_shape links p p' hn a.1 b.1 _ row El h1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.onAt_step_nopin
#print axioms VerifiableInference.Desc.LinkJoin.onT_rides_nopin
#print axioms VerifiableInference.Desc.LinkJoin.hon3_at
