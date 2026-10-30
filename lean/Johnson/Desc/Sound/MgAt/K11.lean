-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K11.lean: THE PREMISES THAT THE LAW OF THE MERGE OF THE CLAIMS ON THE
COMMITTED TABLE (kind K11) ASKS OF A FILLING OF THE TABLE OF JOINTS HOLD AT THE COMPOSED MEANING
`mgAll D Mg`. One definition, one lemma, one theorem. It proves nothing of any sub-protocol. Typed
by the kind's own authors as a hand to the composed meaning's.

What is said. `mergeFill_at`: `MergeFill` (Johnson/Top/H0/MergeLaw/TieThreeFour.lean), all eleven
fields, at every D and every Mg beneath, at: the readers of the verifier's state D.smp and D.decT;
the merge's reading of the mask row at posM := `posMask R`; own := D.N.group m; the number of claims
D.d1.ncl m and the row's shape D.d1.lin; Wa a letter; Wb := `idxAt`.
  `idxAt D ni posI xI b`: what the payer of "wo" needs of the state behind the merge: the mask
    entries of the index masks' message, as the reader of the pile of pending rows (D.rw13) reads
    them, are the merge's reading of that message at the member xI.
  `woHere_sized`: `woHere_of_fillR` (Johnson/Top/H0/Fill/TiesP1.lean) where the reader's two sizes
    are letters that equal the layout's.

THE PREMISES THAT ARE LEFT.
  Closed facts on the table, at D.links, ps, k, m: hins, houts, hctx: the row at the merge's place;
    hoL, hoF: "ledger m" and "freeAbove m" are open at border k by the composed list of extra public
    tests; hsub: segment m is the output head's.
  On D's parameters: hns: the built segment m has Pm.nMsg slots. hxM, hsM, hfM: xM is a member of
    D.ms, sits at a place of the head's first sending, and is the first member with its place. hxI,
    hsI: xI is a member and sits at D.N.index. hlk, hst, hr: the chain's link m, whose sub-protocol
    number 8 states under "the merge" a run r that accepts just where the merge's run of claims
    does, with the same answers (at the IOP as written in Lean that run stands under a guard: it is
    not the merge's run to the letter). hwt: THE LEMMA THAT JOINS THE TWO SENTENCES FOR "weights":
    where Wa holds of the state, D.wt m follows from the layer's `wtP1` at the cells' reader rc and
    `maskRowAt`. Wa is a letter: what that lemma needs of the state in front of the merge. hlay,
    hnR, hkC: the layer's layout is the merge's; the pile's reader's two sizes are the layout's.
    hmat: the pile's matrix off the cells is rc.

How each field is paid. The row's three, and the two on what is open: the premises. The two tests:
`pubAll_ledger`, `pubAll_freeAbove` with hns. The pins: `mgAll_pin`, `mgAll_pinW` at the two
members. "weights": `weights_field`, over `mgAll_forms` (no run stands under that name at the head).
"merged": `mgAll_forms` at the run (8, "the merge"), `formsQ_link_merge`
(Johnson/Top/H0/MergeLaw/MergedAtLink.lean), `merged_at_member` (MaskRow.lean). "wo": `mgAll_wo`,
`woHere_sized`.

Limits. Every premise above is shown at no closed value here. `idxAt` is shown at no state. Nothing
on soundness.
-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.Sound.MgAt.Runs
import Johnson.Desc.Sound.MaskRowAt
import Johnson.Top.H0.MergeLaw.TieThreeFour
import Johnson.Top.H0.MergeLaw.MergedAtLink
import Johnson.Top.H0.Fill.TiesP1

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Slice
open OnBytes.Model (WsShape wsLayOf)
open VerifiableInference.Desc (Link Claim Place)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers pubSets)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim)
open VerifiableInference.Desc.K13.Law (lowBits)
open Johnson.Desc.First.Walk.Law (hasRow)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- What the payer of "wo" needs of the verifier's state behind the merge: the pile's reader's mask
entries of the index masks' message are the merge's reading of that message at the member xI. -/
def idxAt (ni : ℕ) (posI : ℕ → Bool × ℕ × ℕ) (xI : Mem) (b : S) : Prop :=
  ∀ (z : P) (w : Wit (CellsQ rows cols) Tok MsgT) (c : ℕ),
    (D.rw13 (z, b) w).mask ⟨b.out.indexMasks, c⟩ = vecBy D.cs D.arr ni posI xI w c

/-- `woHere_of_fillR` (Johnson/Top/H0/Fill/TiesP1.lean) where the pile's reader's two sizes are
letters that equal the layout's. -/
theorem woHere_sized {Pp W : Type} (Pm : HeadMergeP) {s₀ : WsShape} {p3 : Bool} {lkW : ℕ}
    (h : wsLayOf s₀ p3 lkW = .ok Pm.lay) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (ni : ℕ)
    (ui : Fin Pm.lay.U.size) (sv : ℕ) (hsv : sv < Pm.nMsg) (c : ℕ) (hc : c < ni)
    (d : First.FillP1.PubData) (hlay : d.lay = Pm.lay) {nR kC : ℕ} (hnR : nR = d.lay.m0)
    (hkC : kC = d.lay.lk) (rw : Pp × S → W → First.FillP1.PileWit nR kC) (m : ℕ) (a : Pp × S)
    (y : Strs) (w : W) (cell : ℕ → ℕ → GE) (idx : ℕ → GE) (hw : First.FillP1.woAt d rw m a y w)
    (hr : hasRow d.lay (d.ncl m) d.lin a.2 = true) (he : EntryAt a.2 c)
    (hmat : ∀ (i : Fin nR) (C : ℕ), C < 2 ^ kC → (rw a w).mat i (lowBits kC C) = cell i C)
    (hmask : ∀ c', (rw a w).mask ⟨a.2.out.indexMasks, c'⟩ = idx c') :
    WoHere (recNums Pm h hn ni ui sv hsv c hc) (d.ncl m) d.lin cell idx a.2 := by
  subst hnR hkC
  exact First.FillP1.woHere_of_fillR Pm h hn ni ui sv hsv c hc d hlay rw m a y w cell idx hw hr he
    hmat hmask

/-- **THE MERGE's PREMISES ON THE FILLING HOLD AT THE COMPOSED MEANING.** -/
theorem mergeFill_at (rc : CellsQ rows cols → ℕ → ℕ → GE) (xM xI : Mem)
    (posI : ℕ → Bool × ℕ × ℕ) (Pm : HeadMergeP) {s₀ : WsShape} {p3 : Bool} {lkW : ℕ}
    (h : wsLayOf s₀ p3 lkW = .ok Pm.lay) (hn : 2 * Pm.lay.lk + 3 ≤ Pm.nMsg) (ni R : ℕ)
    (ps : List Place) (k m : ℕ) (l : Link S Claim) (name : String) (Wa : S → Prop)
    -- closed facts on the table
    (hins : (rowQ D.links ps k).ins = [.forms m 4 "weights"])
    (houts : (rowQ D.links ps k).outs = [.forms m 9 "merged", .wo m])
    (hctx : (rowQ D.links ps k).ctx = [.pinW, .pin m 0, .pinI])
    (hoL : Pub.ledger m ∈ (pubSets (mgAll D Mg).more D.links ps)[k]?.getD [])
    (hoF : Pub.freeAbove m ∈ (pubSets (mgAll D Mg).more D.links ps)[k]?.getD [])
    (hsub : D.links[m]? = some .head)
    -- on D's parameters
    (hns : (D.built[m]?).map (·.ns) = some Pm.nMsg)
    (hxM : xM ∈ D.ms) (hsM : seatOf xM ∈ D.N.sent m 0)
    (hfM : (D.ms.find? fun y => decide (seatOf y = seatOf xM)) = some xM)
    (hxI : xI ∈ D.ms) (hsI : seatOf xI = D.N.index)
    (hlk : D.lk m = some l)
    (r : ℕ → S → Except String (List Claim × S))
    (hst : ((K9.statesOfLink l 8).find? fun x => x.1 == "the merge") = some (name, r))
    (hr : ∀ n t y, r n t = .ok y ↔ headMergeClaim n t = .ok y)
    (hwt : ∀ a y w, Wa a.2 → First.FillP1.wtP1 Pm ni (fun w => rc w.cells)
      (maskRowAt D.cs D.arr D.ms D.N m) a y w → D.wt m a y w)
    (hlay : D.d1.lay = Pm.lay) (hnR : nR = D.d1.lay.m0) (hkC : D.P13.lin.kCol = D.d1.lay.lk)
    (hmat : ∀ (M : CellsQ rows cols) (i : Fin nR) (C : ℕ), C < 2 ^ D.P13.lin.kCol →
      D.mat13 M i (lowBits D.P13.lin.kCol C) = rc M i C) :
    MergeFill D.cs D.G D.arr (fun z s => D.smp (z, s)) rc (fun z c s => D.decT c (z, s))
      (D.d1.ncl m) D.d1.lin xM xI (posMask R) posI Pm h hn ni (D.N.group m) R
      Wa (idxAt D ni posI xI) D.N (mgAll D Mg) D.links ps k m where
  ins := hins
  outs := houts
  ctx := hctx
  ledgerOpen := hoL
  freeOpen := hoF
  ledgerIs := fun _ => rfl
  freeIs := fun a => by
    show (D.pubD.nsOf m).any (fun n => First.freeAboveB n a.2) = _
    show ((D.built[m]?).map (·.ns)).any (fun n => First.freeAboveB n a.2) = _
    rw [hns]
    rfl
  pins := fun z a y w ⟨h1, h2, h3⟩ =>
    ⟨h1, (h2 (seatOf xM) hsM).2 xM hxM rfl, (hsI ▸ h3 : pinJT D.cs D.G D.arr D.smp D.ms
      (seatOf xI).1 (seatOf xI).2 (z, a) y w).2 xI hxI rfl⟩
  weights := fun z a y w ui sv hsv c hc hr hM hA hw => by
    refine weights_field (Mg := mgAll D Mg) (m := m) D.ms hfM (maskRowAt D.cs D.arr D.ms D.N m)
      (fun z a w a9 e j => maskRowAt_of_part D.cs D.arr D.ms D.N m (z, a) w j a9 e) ?_
      z a y w ui sv hsv c hc hr hM hA hw
    intro z a y w hA' hq
    show (∀ p ∈ D.runs m 4 "weights", _) ∧ ("weights" = "weights" → D.wt m (z, a) y w)
    refine ⟨fun p hp => ?_, fun _ => hwt _ _ _ hA' hq⟩
    have e : D.runs m 4 "weights" = [] := by
      show runsAt D.links m 4 "weights" = []
      rw [runsAt_of D.links m .head hsub]
      exact runs_head.2.2.2.2.1
    rw [e] at hp
    exact absurd hp (List.not_mem_nil)
  merged := fun z b y w ui sv hsv c hc _ hb hM hm => by
    have hm' : (∀ p ∈ D.runs m 9 "merged",
      if D.ah p.1 p.2 = true then
        formsQA (D.N.sent m) (D.N.group m) (D.Rd m) p.1 p.2 b (seatTab D.cs D.arr D.ms w)
      else formsQ (D.Rd m) (D.N.group m) p.1 p.2 b (seatTab D.cs D.arr D.ms w)) ∧
      ("merged" = "weights" → D.wt m (z, b) y w) := hm
    have e : (8, "the merge") ∈ D.runs m 9 "merged" :=
      mem_runsAt D.links m .head hsub 9 "merged" _ (by rw [runs_head.2.2.2.2.2.2.2]; simp)
    have hf := hm'.1 _ e
    have hah : D.ah 8 "the merge" = false := by
      show ("the merge" == "K8.equations") = false
      decide
    rw [if_neg (by rw [hah]; simp)] at hf
    have hRd : D.Rd m =
        K9.readersOfLink (K9.holesAt X (VerifiableInference.OnPublicFiles.headLink X) m l) l :=
      K9.readersAt_some D.lk X _ m l hlk
    rw [hRd] at hf
    exact merged_at_member (recNums Pm h hn ni ui sv hsv c hc) D.cs D.arr D.ms
      (mergeStates "the merge") (D.N.group m) 8 "the merge" "the merge"
      (mergeStates_find "the merge" 8) hb w _ _ xM R hM hfM
      (formsQ_link_merge X _ m l _ 8 "the merge" name (by decide) r hst hr b _ hf)
  wo := fun z b y w ui sv hsv c hc _ he _ hRow hI hw =>
    woHere_sized Pm h hn ni ui sv hsv c hc D.d1 hlay hnR hkC D.rw13 m (z, b) y w _ _ hw
      (by rw [hlay]; exact hRow) he (fun i C hC => hmat w.cells i C hC) (hI z w)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mergeFill_at
