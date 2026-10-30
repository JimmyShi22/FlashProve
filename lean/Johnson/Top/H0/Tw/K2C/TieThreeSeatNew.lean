-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeSeatNew.lean: code switching: hAt OF THE THIRD TIE AT A PLACE, IN ITS
THREE ARMS (hAt_link | hAt_head | hAt_finish, Tw/K2C/TieThreeArms.lean), AT seatN := seatNew N m r
AND THE TIE's m := m + 1, WITH THE PREMISE hS PAID: by hS_seatNew (Tw/K2C/SentByPlace.lean),
hbase_at_place (Tw/K2C/ThreeCounts.lean) and len_of_tests (Tw/K2C/ThreeTogether.lean). A JOINING:
every step is a call. NO SUB-PROTOCOL IMPORTS THIS FILE.
  hS_new                         hS at seatNew, at pIn := ps[k]?, from the list below
  hAt_link_new | hAt_head_new | hAt_finish_new   HAt … (seatNew N m r) … k (m + 1) n0 grp
IN hS's PLACE, BY NAME: two tests on public data (sentPlaceB N (m + 1) ps[k]? codes sent ·
membersPlanB Z rad N (m + 1) r) · hlay (closed) · hF (two clauses of K2.Fence at the front) · h0 :
p.firstTree = 0 · hen (the way in leaves the book and the roots) · hBook (atFirstBook behind the way
in: the first clause of the fourth tie's own hBook). The arms' other premises stay as they are.
ft IS A FREE LETTER IN hBook. By report (no theorem says it): atFirstBook ft ALSO
says "the tree at place z bears ft + z": beside h0 (p.firstTree = 0) and yes_numbered it can be
met at a non-empty book ONLY AT ft = 0: the caller must lay ft := 0 (the first chain's). Nothing in
this file's premises ties ft to p: the clash would show at the assembler, who has yes_numbered
beside.
  hen_id | hen_finish            hen at the two real ways in (the identity; K2.finishFrontQ)
LIMITS. Those of the files named. No premise is shown met here. No soundness is claimed. On hiding
nothing.
-/
import Johnson.Top.H0.Tw.K2C.TieThreeArms
import Johnson.Top.H0.Tw.K2C.ThreeTogether

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.K12.Door (atFirstBook)
open Johnson.Desc.First.Walk.Tied (OpenedKeeps)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

section
variable {F : Frame} {P Cells Tok Cl Xi : Type} {r : SwRow} (h : r.ok = true)
  (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
      h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
      h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (G : FileDescription Xi) (base : ℕ) (d₁ d₂ : RDT) (p : K2.P2)
  (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
  (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
  (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop)
  (k m n0 grp : ℕ)
  (codes : Codes) (sent : Array OracleNotice) (lay₀ : TreeLay) (Z : ProofFile.Pub) (rad : ℕ → ℕ → ℕ)
  (ft : ℕ)
  (hPl : sentPlaceB N (m + 1) ps[k]? codes sent = true) (hlay : layTrees codes sent = some lay₀)
  (hB : membersPlanB Z rad N (m + 1) r = true)
  (hF : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
      switchNotices fx.T fx.others = sent ∧ fx.st.codes = codes)
  (h0 : p.firstTree = 0)
  (hen : ∀ s t, enter s = .ok t → t.book = s.book ∧ t.roots = s.roots)
  -- ft: the caller lays 0 (the head's note)
  (hBook : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → atFirstBook ft t = true)

include hPl hlay hB hF h0 hen hBook

/-- **hS at seatNew**, at pIn := ps[k]?. -/
theorem hS_new : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
      ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
        ∀ i : Fin r.l.length, seatNew N m r i =
          (p.firstTree + (t.roots + lay.tree.getD i.val 0), lay.part.getD i.val 0) :=
  hS_seatNew p enter Mg links ps z Rch k hPl hlay (Nat.le_of_eq (len_of_tests hPl hlay hB)) hF
    (hbase_at_place N Mg links ps z k p enter Rch ft h0 hen hBook)

variable (h32 : p.logN ≤ 32) (hL : r.cs.lengthsOk = true)
  (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (olds : List ℕ)
  (hnd : olds.Nodup) (h0f : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
  (hpub : frontPubB r.l.length f₀ = true) (hkA : r.keptAt W = true)
  (C : ∀ W₀, Renumbered W W₀ → CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK
      rowK (plK W₀) W₀)
  (hT1 : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
      frontB2 f₀ W grp 0 n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others))
  (hgrp : N.groupAt (m + 1) = grp) (d : ℕ) (hd : d = baseCount r.set .request r.g)
  (hone : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
      ∀ κ ∈ (placeFrame W n0 olds).kept,
        (fx.st.oracles.getD κ.old default).sampleRows.size = 1)

include h32 hL hnd h0f hcs hpub hkA C hT1 hgrp hd hone

/-- **hAt at a segment's code switch, at seatNew.** -/
theorem hAt_link_new (hlv : ∀ s t' s', leave s t' = .ok s' → OpenedKeeps t' s')
    (hDl : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ W₀, K2.frameAt fx = some W₀ →
            ∃ pIn pOut s, K2.LinkDebts N (m + 1) pIn pOut s d fx W₀ lay) :
    HAt h iJ iQ G (seatNew N m r) base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k (m + 1) n0
      grp :=
  hAt_link h iJ iQ G (seatNew N m r) base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k (m + 1)
    n0 grp h32 hL f₀ W olds hnd h0f hcs hpub hkA C hT1 hgrp d hd hone
    (hS_new p enter N Mg links ps z Rch k m codes sent lay₀ Z rad ft hPl hlay hB hF h0 hen hBook)
    hlv hDl

/-- **hAt at the head's code switch, at seatNew.** -/
theorem hAt_head_new
    (hlv : ∀ s t' s', leave s t' = .ok s' →
      ∃ Pq u, K2.headOpenQ Pq t' = .ok u ∧ OpenedKeeps u s')
    (hDs : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ W₀, K2.frameAt fx = some W₀ →
            ∃ pIn pOut bs n, K2.SwitchDebts N (m + 1) pIn pOut bs d n fx W₀ lay) :
    HAt h iJ iQ G (seatNew N m r) base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k (m + 1) n0
      grp :=
  hAt_head h iJ iQ G (seatNew N m r) base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k (m + 1)
    n0 grp h32 hL f₀ W olds hnd h0f hcs hpub hkA C hT1 hgrp d hd hone
    (hS_new p enter N Mg links ps z Rch k m codes sent lay₀ Z rad ft hPl hlay hB hF h0 hen hBook)
    hlv hDs

/-- **hAt at the finish's code switch, at seatNew.** -/
theorem hAt_finish_new (hlv : ∀ s t' s', leave s t' = .ok s' → K2.finishBehindQ t' = .ok s')
    (hDs : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ W₀, K2.frameAt fx = some W₀ →
            ∃ pIn pOut bs n, K2.SwitchDebts N (m + 1) pIn pOut bs d n fx W₀ lay) :
    HAt h iJ iQ G (seatNew N m r) base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k (m + 1) n0
      grp :=
  hAt_finish h iJ iQ G (seatNew N m r) base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k
    (m + 1) n0 grp h32 hL f₀ W olds hnd h0f hcs hpub hkA C hT1 hgrp d hd hone
    (hS_new p enter N Mg links ps z Rch k m codes sent lay₀ Z rad ft hPl hlay hB hF h0 hen hBook)
    hlv hDs

end

/-- The way in at a segment's and at the head's code switch: the identity leaves all. -/
theorem hen_id : ∀ s t : Rec, (fun s : Rec => (Except.ok s : Except String Rec)) s = .ok t →
    t.book = s.book ∧ t.roots = s.roots := fun s t e => by
  obtain rfl : s = t := Except.ok.inj e
  exact ⟨rfl, rfl⟩

/-- The way in at the finish. -/
theorem hen_finish : ∀ s t : Rec, K2.finishFrontQ s = .ok t → t.book = s.book ∧ t.roots = s.roots :=
  fun _ _ e => K2.finishFrontQ_book e

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hS_new
#print axioms VerifiableInference.Desc.First.K2Caller.hAt_link_new
#print axioms VerifiableInference.Desc.First.K2Caller.hAt_head_new
#print axioms VerifiableInference.Desc.First.K2Caller.hAt_finish_new
#print axioms VerifiableInference.Desc.First.K2Caller.hen_id
#print axioms VerifiableInference.Desc.First.K2Caller.hen_finish
