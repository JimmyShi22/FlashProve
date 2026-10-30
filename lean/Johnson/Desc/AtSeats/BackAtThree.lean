--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
BackAtThree.lean: THE PIECE "CAST.4" OF THE ROWS K01_law AND
K13_law: FOUR MORE SHARES OF `IM.Shares` (the ten shares from which (S1) follows
at the proof file's first chain), IN THAT STRUCTURE's OWN LETTERS, at the further tests
E := `EPub z Mg linksW placesW`: the field "back" at j = 2 and j = 3, the
field "last", the field "first" at l = 0. A cast: calls alone; nothing new is proved of a
sub-protocol's step.
On words: "the state" is the value of type S that the fold of the IOP as written in Lean carries
from one sub-protocol to the next; "the lot" is the list of sub-protocols that a kind's house hands
to the proof file's description (`ProofFile.onlineFirstChainBlockTables`).
OBJECT. `IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft k b` (what one
sub-protocol owes) at k = 355 (kind K13's sub-protocol), 356 (W's commitment), 357 (the chain's last
sub-protocol) and 2 (the first segment's opening).
USER. Whoever fills `IM.Shares`: our joints' pen.
LETTERS. N, Mg, z, ft, F, y₀, rw, mk as in `hands_M3_pub`, `hands_M4_pub`, `hands_G_pub`; Z, G₀, j,
k, b, b': the fields' own; msg: the message that the shape gives for W; X: the value of `zeroAt`;
nm: a name.
  back_at_two     "back" at j = 2: the lot's own sub-protocol at (1, none, 3, K13) stands under
                  `atM3 (K13.whereOf Z)`: `IM.lot_K13` (Johnson/IMR/BackSeat.lean), `lot_under`
                  (Johnson/Desc/K13/Law/LotSits.lean), `IM.Hands.under`, `hands_M3_pub`.
  back_at_three   "back" at j = 3: at (1, none, 4, K1): under `atM4 (K13.whereOf Z) (K1.sendAtS …)`:
                  `IM.lot_M4`, `lot4_under`, `hands_M4_pub`.
  back_two_three  **both, in the field's own form, fenced by j = 2 ∨ j = 3.**
  xk_at_seal      at a row with `RowSeal` (Johnson/Desc/K13/Law/AtTableSeal.lean: the row is empty,
                  no place behind, no public item comes, as many trees and messages behind as in
                  front)
                  the tests at border k give the tests at border k + 1 AT THE SAME STATE.
  last_share      **"last"**: `hands_seal`, one call; its premise
                  stays.
  last_share_row  **"last" from `RowSeal` at 357**: that premise is paid by `xk_at_seal`.
  joined_under    in the goals' scope: a sub-protocol that is `IM.Joined` of the lot's own at
                  (1, some 0, 1, K1) stands under `K1.openingZero`: `IM.lot_K1`, `IM.k1_mem`,
                  `IM.frames_zero` (Johnson/IMR/FirstUnder.lean), by the steps of `IM.first_under`.
  first_at_zero   **"first" at l = 0**: `hands_G_pub`.
PREMISES THAT STAY, BY NAME, all at linksW, placesW: at 355 `RowM3`, `FillM3` · at 356, at every msg
that the shape gives, `RowM4`, `FillM4`, hPl (the two tests on the list of rounds) · at 357
`RowSeal` · at 2 `RowG`, and at every name and at the X that `zeroAt` gives `FillG`; hgroups, hown ·
a frame F with a string y₀ of it · at 2 the goals' scope (hS, hR, O): without it row 0 of
`framesOf` could be the head's.
What is not claimed. That any of these premises holds at the numbers and the meaning that are meant.
The other shares. The call into `IM.Shares` itself. Nothing on soundness, on an honest prover or on
hiding.
-/
import Johnson.Desc.AtSeats.HandsMore
import Johnson.Desc.AtSeats.HandsAtSeal
import Johnson.IMR.WrittenList
import Johnson.IMR.BackSeat
import Johnson.IMR.FirstUnder
import Johnson.Desc.K13.Law.LotSits
import Johnson.Desc.K13.Law.AtTableSeal

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace HashBuild
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Seat (zeroAt fvsOf)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers More Pub Item Meaning kindsBeforeBatching backKinds)
open VerifiableInference.Desc.K13 (Where atM3 atM4)
open VerifiableInference.Desc.Sound (Frame)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open IM (linksW placesW subAt)
open ProofFile (Cl)

variable {Pp W : Type}

/-! ## 1 The field "back" at j = 2 and j = 3 -/

/-- **"back" at j = 2: kind K13's sub-protocol.** -/
theorem back_at_two {nR : ℕ} (F : Frame) (y₀ : F.E.Str) (N : Numbers) (Mg : Meaning Pp W) (z : Pp)
    (ft : ℕ) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (rw : Pp × S → W → Wit GE nR (K13.whereOf Z).lin.kCol)
    (hT : RowM3 N Mg.more linksW placesW 355)
    (hF : FillM3 Cl (K13.whereOf Z) N Mg rw
      ((First.pubSets Mg.more linksW placesW)[355]?.getD [])) :
    ∀ (k : KindName) (b' : Block S Cl), (backKinds true)[2]? = some k →
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
      b'.place = { chain := 1, link := none, piece := 2 + 1, kind := k } →
      IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft (353 + 2) b' := by
  intro k b' hk hL hp
  obtain ⟨L, hL, hb⟩ := hL
  have h2 : (backKinds true)[2]? = some KindName.K13 := rfl
  obtain rfl : KindName.K13 = k := Option.some.inj (h2.symm.trans hk)
  obtain ⟨rfl, -⟩ := IM.lot_K13 hL hb (by rw [hp])
  exact IM.Hands.under (lot_under Z G₀ b' hb)
    (hands_M3_pub F y₀ N Mg linksW placesW z ft 355 (K13.whereOf Z) rw hT hF)

/-- **"back" at j = 3: W's commitment.** msg: the message that the shape gives. -/
theorem back_at_three (F : Frame) (y₀ : F.E.Str) (N : Numbers) (Mg : Meaning Pp W) (z : Pp)
    (ft : ℕ) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (hT : ∀ msg, linMessageW Z.first.lin = some msg → RowM4 N Mg.more linksW placesW 356
      (K1.layOf (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4
        msg)).shapes.size
      (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg).sent.size)
    (hF : ∀ msg, linMessageW Z.first.lin = some msg → FillM4 Cl (K13.whereOf Z)
      (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) N Mg
      ((First.pubSets Mg.more linksW placesW)[356]?.getD []) placesW[356]?)
    (hPl : ∀ msg, linMessageW Z.first.lin = some msg →
      wSitsItem ∈ (First.pubSets Mg.more linksW placesW)[356 + 1]?.getD [] →
      planSitsB (K13.whereOf Z)
          (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) = true ∧
        planSeatB N placesW[356]?
          (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) = true) :
    ∀ (k : KindName) (b' : Block S Cl), (backKinds true)[3]? = some k →
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
      b'.place = { chain := 1, link := none, piece := 3 + 1, kind := k } →
      IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft (353 + 3) b' := by
  intro k b' hk hL hp
  obtain ⟨L, hL, hb⟩ := hL
  have h3 : (backKinds true)[3]? = some KindName.K1 := rfl
  obtain rfl : KindName.K1 = k := Option.some.inj (h3.symm.trans hk)
  obtain ⟨rfl, -⟩ := IM.lot_M4 hL hb (by rw [hp]) (by rw [hp])
  obtain ⟨msg, hm, hu⟩ := lot4_under Z G₀ b' hb
  exact IM.Hands.under hu (hands_M4_pub F y₀ N Mg linksW placesW z ft 356 (K13.whereOf Z) _
    (hT msg hm) (hF msg hm) (hPl msg hm))

/-- **THE FIELD "back" OF `IM.Shares`, CUT TO j = 2 AND j = 3.** -/
theorem back_two_three {nR : ℕ} (F : Frame) (y₀ : F.E.Str) (N : Numbers) (Mg : Meaning Pp W)
    (z : Pp) (ft : ℕ) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (rw : Pp × S → W → Wit GE nR (K13.whereOf Z).lin.kCol)
    (hT3 : RowM3 N Mg.more linksW placesW 355)
    (hF3 : FillM3 Cl (K13.whereOf Z) N Mg rw
      ((First.pubSets Mg.more linksW placesW)[355]?.getD []))
    (hT4 : ∀ msg, linMessageW Z.first.lin = some msg → RowM4 N Mg.more linksW placesW 356
      (K1.layOf (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4
        msg)).shapes.size
      (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg).sent.size)
    (hF4 : ∀ msg, linMessageW Z.first.lin = some msg → FillM4 Cl (K13.whereOf Z)
      (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) N Mg
      ((First.pubSets Mg.more linksW placesW)[356]?.getD []) placesW[356]?)
    (hPl : ∀ msg, linMessageW Z.first.lin = some msg →
      wSitsItem ∈ (First.pubSets Mg.more linksW placesW)[356 + 1]?.getD [] →
      planSitsB (K13.whereOf Z)
          (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) = true ∧
        planSeatB N placesW[356]?
          (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) = true) :
    ∀ (j : ℕ) (k : KindName) (b' : Block S Cl), j = 2 ∨ j = 3 → (backKinds true)[j]? = some k →
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
      b'.place = { chain := 1, link := none, piece := j + 1, kind := k } →
      IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft (353 + j) b' := by
  intro j k b' hj
  rcases hj with rfl | rfl
  · exact back_at_two F y₀ N Mg z ft Z G₀ rw hT3 hF3 k b'
  · exact back_at_three F y₀ N Mg z ft Z G₀ hT4 hF4 hPl k b'

/-! ## 2 The field "last" -/

/-- **At an empty last row the tests at border k give the tests at border k + 1, at the same
state.** -/
theorem xk_at_seal {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart} {ps : List Place} {z : Pp}
    {k : ℕ} {p : Place} (hT : RowSeal N Mg.more links ps k p) (s : S)
    (hx : IM.XK N links ps (EPub z Mg links ps) k s = true) :
    IM.XK N links ps (EPub z Mg links ps) (k + 1) s = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := IM.xk_parts hx
  obtain ⟨e1, e2, e3⟩ := epub_parts h5
  have hO : openAt links ps (k + 1) = openAt links ps k := by
    have h := First.openSets_succ links ps (First.start links) k p hT.place
    rw [stepOpen_empty _ _ hT.ins hT.outs] at h
    exact h
  have hO' : IM.openAt links ps (k + 1) = IM.openAt links ps k := hO
  have hs : First.shapeAt links ps[k + 1]? s = true := by
    rw [hT.place] at h1
    rw [hT.last]
    unfold First.shapeAt at h1 ⊢
    simp only [Bool.and_eq_true, hT.stand, hT.noWait, Bool.or_false] at h1 ⊢
    exact ⟨h1.1.1, h1.1.2⟩
  have hb : First.bookAt N ps[k + 1]? s = true := by
    unfold First.bookAt at h4 ⊢
    rw [hT.trees, hT.msgs]
    exact h4
  have he : EPub z Mg links ps (k + 1) s = true := by
    refine epub_of e1 (fun q hq => e2 q (hT.pubs q ?_)) fun q hq => e3 q ?_
    · rw [← First.pubSets_succ Mg.more links ps k p hT.place]
      exact hq
    · rw [← hO]
      exact hq
  unfold IM.XK IM.BK
  rw [hO', hs, h2, h3, hb, he]
  rfl

/-- **THE FIELD "last" OF `IM.Shares`**; what the table says of the two borders stays a premise. -/
theorem last_share (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (Z : ProofFile.Pub)
    (hT : ∀ s, s.failed = none →
      IM.XK N linksW placesW (EPub z Mg linksW placesW) 357 s = true →
      IM.XK N linksW placesW (EPub z Mg linksW placesW) (357 + 1) s = true) :
    IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft 357
      ((ChainEnd.chainEnd 1 5 true (K13.inFrontOf Z) First.endAsks : Block S Unit).retype :
        Block S Cl) :=
  hands_seal N linksW placesW _ ft 357 1 5 true _ _ hT

/-- **THE FIELD "last" OF `IM.Shares`, FROM WHAT IS ASKED OF THE TABLE AT THE ROW.** -/
theorem last_share_row (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (Z : ProofFile.Pub)
    (p : Place) (hT : RowSeal N Mg.more linksW placesW 357 p) :
    IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft 357
      ((ChainEnd.chainEnd 1 5 true (K13.inFrontOf Z) First.endAsks : Block S Unit).retype :
        Block S Cl) :=
  last_share N Mg z ft Z fun s _ hx => xk_at_seal hT s hx

/-! ## 3 The field "first" at l = 0 -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Fd : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **In scope, whatever is joined of the lot's own sub-protocol at link 0's first place stands
under the bare joined sub-protocol `K1.openingZero`.** G₀: any letters of the lots. -/
theorem joined_under (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL Fd Z Bs base c A B) {G₀ : ProofFile.Ground}
    {b b' : Block S Cl} (hL : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hp : b'.place = { chain := 1, link := some 0, piece := 1, kind := .K1 })
    (hj : IM.Joined Z 0 b b' { chain := 1, link := some 0, piece := 1, kind := .K1 }) :
    ∃ X, zeroAt Z.p.built.links Z.p.X = some X ∧
      b.UnderR (K1.openingZero G₀.first (K1.gpOf Z) b.name X (fvsOf Z.p.built.links)
        Z.first.lin.kCol : Block S Cl) := by
  obtain ⟨L, hL, hb⟩ := hL
  obtain ⟨x, hx, rfl⟩ := IM.lot_K1 hL hb (by rw [hp]) (l := 0) (by rw [hp])
  rcases IM.k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, hX, hn, rfl | rfl⟩
  · obtain ⟨fs, f, hfs, hf, -⟩ := id hj
    obtain ⟨X, hX, hop⟩ := IM.frames_zero hS hR O hfs hf
    refine ⟨X, hX, ?_, fun s rs gs t hy => ?_⟩
    · rw [hj.rounds]
      exact (List.append_nil _).symm
    · obtain ⟨fs', f', m, hfs', hf', h1, -, h3, -, -⟩ := hj.yes hy
      obtain rfl : fs = fs' := Except.ok.inj (hfs.symm.trans hfs')
      obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
      rw [hop] at h3
      have h1' : (K1.firstSegmentOpening G₀.first (K1.gpOf Z) : Block S Cl).decide s
          (rs.take (K1.firstSegmentOpening G₀.first (K1.gpOf Z) : Block S Cl).rounds.length)
          (gs.take (K1.firstSegmentOpening G₀.first (K1.gpOf Z) : Block S Cl).openings) = .ok m := h1
      show ((K1.firstSegmentOpening G₀.first (K1.gpOf Z) : Block S Cl).decide s
          (rs.take (K1.firstSegmentOpening G₀.first (K1.gpOf Z) : Block S Cl).rounds.length)
          (gs.take (K1.firstSegmentOpening G₀.first (K1.gpOf Z) : Block S Cl).openings)).bind
          (fun s' => Johnson.Desc.First.Walk.openLayZero X (fvsOf Z.p.built.links)
            Z.first.lin.kCol s') = .ok t
      rw [h1']
      exact h3
  · exfalso
    have epc : pr = 1 := congrArg Place.piece hp
    rcases IM.numbers_pieces hn with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · exfalso
    have epc : pd = 1 := congrArg Place.piece hp
    rcases IM.numbers_pieces hn with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

/-- **THE FIELD "first" OF `IM.Shares`, CUT TO l = 0**, in scope. -/
theorem first_at_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL Fd Z Bs base c A B) (N : Numbers)
    (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (G₀ : ProofFile.Ground) (mk : List Pub)
    (hT : RowG N Mg.more linksW placesW 2
      (K1.layOf (K1.firstPar G₀.first (K1.gpOf Z))).shapes.size
      (K1.firstPar G₀.first (K1.gpOf Z)).sent.size mk)
    (hF : ∀ (nm : String) (X : LayPar), zeroAt Z.p.built.links Z.p.X = some X →
      FillG Cl G₀.first (K1.gpOf Z) nm X (fvsOf Z.p.built.links) Z.first.lin.kCol N Mg
        ((First.pubSets Mg.more linksW placesW)[2]?.getD []) placesW[2]? mk)
    (hgroups : ∀ x, Mg.pub .noneSent x = true → N.groupAt 0 = x.2.st.groups.size)
    (hown : ∀ x, Mg.inOrder x = true → First.bookAt N placesW[2]? x.2 = true →
      K1.ownSeatsB N (openAt linksW placesW (2 + 1)) (K1.firstPar G₀.first (K1.gpOf Z))
        (x.2.check.frame.atMoment 0).length x.2.book.trees.size = true) :
    ∀ (k : KindName) (b b' : Block S Cl), (kindsBeforeBatching (subAt 0) (0 == 0))[0]? = some k →
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
      b'.place = { chain := 1, link := some 0, piece := 1, kind := k } →
      IM.Joined Z 0 b b' { chain := 1, link := some 0, piece := 1, kind := k } →
      IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft (14 * 0 + 2) b := by
  intro k b b' hk hL hp hj
  have h0 : (kindsBeforeBatching (subAt 0) (0 == 0))[0]? = some KindName.K1 := rfl
  obtain rfl : KindName.K1 = k := Option.some.inj (h0.symm.trans hk)
  obtain ⟨X, hX, hu⟩ := joined_under hS hR O hL hp hj
  exact IM.Hands.under hu (hands_G_pub N Mg linksW placesW z ft 2 G₀.first (K1.gpOf Z) b.name X
    (fvsOf Z.p.built.links) Z.first.lin.kCol mk hT (hF b.name X hX) hgroups hown)

end

end HashBuild

#print axioms HashBuild.back_at_two
#print axioms HashBuild.back_at_three
#print axioms HashBuild.back_two_three
#print axioms HashBuild.xk_at_seal
#print axioms HashBuild.last_share
#print axioms HashBuild.last_share_row
#print axioms HashBuild.joined_under
#print axioms HashBuild.first_at_zero
