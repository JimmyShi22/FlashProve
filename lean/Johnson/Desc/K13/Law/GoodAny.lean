-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/GoodAny.lean: kind K13's law of the batching, general in the state and in the
block: of any block that decides by the kind's text. Definitions, and statements with their proofs.

Johnson/Desc/K13/Law/Good2.lean and Johnson/Desc/K13/Law/PinA.lean have the law at the first chain's
record and at the joined block of that record's lens. Their proofs spend of the record and the lens
three facts at a yes alone. Here these are one premise on the block's decision.
Main names:
  `ByBatt b P partF rowB`: **the premise**: partF: a reader: the part that the text is handed, off
    the state in front; rowB: a reader: the rows on the table, off the state behind. Where b says
    yes: the reader gives a part; the text `batt` has answered at that part's fields, on the first
    2 + kCol of the rounds; the part's pile names the entries of the part's ledger alone; and the
    rows behind are just the row that the text handed on.
  `pieceAt F b rows base dZ d0 ds`: the piece that holds b at the batching's stretch: as `pieceM3`.
  `pieceAt_key`: what its yes gives.
  `goodIn_any`: **the law**: `Piece.GoodIn` of that piece: in front: the pin, and all rows of the
    part's pile are true; behind: the pin, and all of rowB's rows are true. The pin reads the
    statement; that it fixes the matrix and the ledger's mask entries is asked under the condition
    in front; that it goes back, and that the promise behind is kept, are asked at a yes, under
    the condition in front too.
  `LensLaw X`: what is asked of a lens: where a part that keeps heard, indexMasks and pile and owes
    nothing is written, a part is read that has these four and the written claim. `lensLaw_of_same`:
    a lens that reads such a part back as it was written has it.
  `partIn X`, `rowOut X`: the two readers at a lens: the part behind `enter`; the claim's row.
  `byBatt_joined`: **the kind's three blocks in a row, at any lens with that law, meet the
    premise.**
  `ByBatt.behind`: so does a block behind a block without a round whose yes is a function.
  `lensLaw_atS`: a member: the first chain's record's lens has the law (it does NOT read every such
    part back as it was written: it writes back the statement alone of the part's ground).
  `not_byBatt_yes`: a try: a block that says yes to all does not meet the premise at a reader that
    gives no row behind.
Used of `verify-on-bytes`: nothing beside what Johnson/Desc/K13/Law/Law.lean and
Johnson/Desc/K13/Law/Agree.lean name.

What is not claimed. `Declared` is a test on a plan's written rounds. That a pin of the protocol
meets the premises. The number nR of the matrix's rows is a free letter. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.PinA

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {T Cl W : Type} {nR : ℕ}

/-- **The premise on the block's decision.** -/
structure ByBatt (b : Block T Cl) (P : Where) (partF : T → Option Part)
    (rowB : T → List TensorRow) : Prop where
  yes : ∀ t t' rs gs, b.decide t rs gs = .ok t' → ∃ (p : Part) (out : TensorRow × St),
    partF t = some p ∧
    batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d (rs.take (2 + P.lin.kCol)) = .ok out ∧
    (∀ r ∈ p.pile, OnLedger p.indexMasks r) ∧ rowB t' = [out.1]

/-- The piece that holds a block at the batching's stretch. -/
def pieceAt (F : Frame) (b : Block T Cl) (rows base : ℕ) (dZ d0 : RDT) (ds : List RDT) :
    Piece (ckP .two) F T Cl W where
  b := b
  base := base
  ds := dZ :: d0 :: ds
  back := []
  ext := fun _ _ w => w
  err := (mapsOf dZ d0 ds).err (errK rows ds.length)

/-- What the piece's yes gives. -/
theorem pieceAt_key (F : Frame) (P : Where) (b : Block T Cl) (base : ℕ) (dZ d0 : RDT)
    (ds : List RDT) (hk : P.lin.kCol = ds.length) (partF : T → Option Part)
    (rowB : T → List TensorRow) (hb : ByBatt b P partF rowB) (a : T × F.E.Str) :
    ∀ τ b', (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' →
      (mapsOf dZ d0 ds).pass τ = true ∧
      ∃ r rs' p out, (rvT (ckP .two) (dZ :: d0 :: ds) τ).map noDigest = r :: rs' ∧
        partF a.1 = some p ∧
        batt p.owed ds.length P.rows p.pile p.indexMasks p.d (r :: rs') = .ok out ∧
        (∀ r ∈ p.pile, OnLedger p.indexMasks r) ∧ rowB b'.1 = [out.1] := by
  intro τ b' hb'
  have hb2 : (if sTests (ckP .two) (pieceAt (W := W) F b P.rows base dZ d0 ds).stage a.2 τ
      then (pieceAt (W := W) F b P.rows base dZ d0 ds).run a.1
        (sView (ckP .two) (pieceAt (W := W) F b P.rows base dZ d0 ds).stage a.2 τ)
      else none).map (fun xo =>
        (xo, (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.imp a.2 τ)) = some b' := hb'
  by_cases ht : sTests (ckP .two) (pieceAt (W := W) F b P.rows base dZ d0 ds).stage a.2 τ = true
  · rw [if_pos ht] at hb2
    cases hrun : (pieceAt (W := W) F b P.rows base dZ d0 ds).run a.1
        (sView (ckP .two) (pieceAt (W := W) F b P.rows base dZ d0 ds).stage a.2 τ) with
    | none =>
      rw [hrun] at hb2
      cases hb2
    | some s' =>
      rw [hrun] at hb2
      obtain rfl := Option.some.inj hb2
      simp only [sTests, Bool.and_eq_true] at ht
      refine ⟨(maps_pass dZ d0 ds τ).trans ht.1.1, ?_⟩
      obtain ⟨gs, _, hdec⟩ := single_ok hrun
      obtain ⟨p, out, hp, hbt, hl, hr2⟩ := hb.yes _ _ _ _ hdec
      have e1 : ((rvT (ckP .two) (dZ :: d0 :: ds) τ ++ []).map noDigest).take
          (2 + P.lin.kCol) = (rvT (ckP .two) (dZ :: d0 :: ds) τ).map noDigest := by
        rw [List.append_nil]
        refine List.take_of_length_le ?_
        rw [List.length_map, rvT_len, hk]
        simp
        omega
      have hbt' : batt p.owed P.lin.kCol P.rows p.pile p.indexMasks p.d
          (((rvT (ckP .two) (dZ :: d0 :: ds) τ ++ []).map noDigest).take
            (2 + P.lin.kCol)) = .ok out := hbt
      rw [e1, hk] at hbt'
      obtain ⟨mZ, cZ, τ1⟩ := τ
      exact ⟨_, _, p, out, rfl, hp, hbt', hl, hr2⟩
  · rw [if_neg ht] at hb2
    cases hb2

/-- **The law, general in the state and in the block.** k: the number of the variables' written
rounds. -/
theorem goodIn_any (F : Frame) (P : Where) (b : Block T Cl) (base : ℕ) (dZ d0 : RDT)
    (ds : List RDT) (hD : Declared P dZ d0 ds) (k : ℕ) (hk : ds.length = k)
    (partF : T → Option Part) (rowB : T → List TensorRow) (hb : ByBatt b P partF rowB)
    (rw : W → Wit GE nR k) (Pin : T × F.E.Str → W → Prop) (on on' : T × F.E.Str → Prop)
    (hdet : ∀ a p w w', on a → partF a.1 = some p → Pin a w → Pin a w' →
      AgreeAt p.indexMasks (rw w) (rw w'))
    (hback : ∀ a τ b' w, on a →
      (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' → Pin b' w → Pin a w)
    (hon : ∀ a τ b', on a → (pieceAt (W := W) F b P.rows base dZ d0 ds).ior.red.out a τ = some b' →
      on' b') :
    (pieceAt (W := W) F b P.rows base dZ d0 ds).GoodIn on on'
      (fun a w => Pin a w ∧ ∀ p, partF a.1 = some p → ∀ r ∈ p.pile, Holds ρg (rw w) r)
      (fun a w => Pin a w ∧ ∀ r ∈ rowB a.1, Holds ρg (rw w) r) := by
  subst hk
  obtain ⟨nZ, aZ, hZ⟩ := sends_of_entry (d := dZ) (by rw [hD.sigma.1]; rfl)
    (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; rfl) (by rw [hD.sigma.1]; exact Nat.zero_le 1)
    (by rw [hD.sigma.1]; exact Nat.zero_le 64) hD.sigma.2.1 hD.sigma.2.2
  obtain ⟨n0, a0, h0⟩ := sends_of_entry (d := d0) (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; rfl)
    (by rw [hD.eps.1]; rfl) (by rw [hD.eps.1]; exact Nat.zero_le 1)
    (by rw [hD.eps.1]; exact Nat.zero_le 64) hD.eps.2.1 hD.eps.2.2
  have hs : ∀ d ∈ ds, ∃ n a, SendsDraws (toRD d) n 1 0 a := fun d hd => by
    obtain ⟨he, hk⟩ := hD.vars d hd
    exact sends_of_entry (by rw [he]; rfl) (by rw [he]; rfl) (by rw [he]; rfl)
      (by rw [he]; exact Nat.zero_le 1) (by rw [he]; exact Nat.zero_le 64) hk.1 hk.2
  intro a ha
  have key := pieceAt_key (W := W) F P b base dZ d0 ds hD.len partF rowB hb a
  cases hp : partF a.1 with
  | none =>
    refine Doomed.of_forall _ _ fun τ b' hb' => ?_
    obtain ⟨_, _, _, p, _, _, hp', _⟩ := key τ b' hb'
    rw [hp] at hp'
    cases hp'
  | some p =>
    by_cases hn : p.pile.length = P.rows
    · by_cases hl : ∀ r ∈ p.pile, OnLedger p.indexMasks r
      · have hDm := batt_sound2 ρg nR ds.length W rw (Pin a) p.indexMasks
          (fun w w' => hdet a p w w' ha hp) p.owed P.rows p.pile p.d F.E a.2 hl
        have hfit : (mapsOf dZ d0 ds).carry.Fits (errK p.pile.length ds.length)
            ((mapsOf dZ d0 ds).err (errK P.rows ds.length)) := by
          rw [hn]
          exact (mapsOf dZ d0 ds).fits (mapsOf_ok hZ h0 hs) _
        refine CarryS.doomed (mapsOf dZ d0 ds).carry _ _ hfit _ _ ?_ ?_ hDm
        · intro τ hτ b' hb'
          rw [Maps.tr_of_pass _ τ (key τ b' hb').1] at hτ
          cases hτ
        · intro τ τ' hτ hbad b' hb'
          obtain ⟨hps, r, rs', p', out, e, hp', hbt, _, hr2⟩ := key τ b' hb'
          rw [hp] at hp'
          obtain rfl := Option.some.inj hp'
          rw [Maps.tr_of_pass _ τ hps] at hτ
          obtain rfl := Option.some.inj hτ
          obtain ⟨r1, rs1, x, t, hd, o, e1, _, _, hx, _, _, hh, _, _, _⟩ := batt_ok hbt
          obtain ⟨rfl, rfl⟩ := List.cons.inj e1
          refine ⟨hon a τ b' ha hb', fun w hw => ⟨hback a τ b' w ha hb' hw.1, fun q hq => ?_⟩⟩
          rw [hp] at hq
          obtain rfl := Option.some.inj hq
          exact hbad r rs' x hd out hx hh (whole_read nR _ F.E dZ d0 ds τ r rs' x hd e hx hh) hbt w
            (hback a τ b' w ha hb' hw.1) (hw.2 out.1 (by rw [hr2]; exact List.mem_singleton.2 rfl))
      · refine Doomed.of_forall _ _ fun τ b' hb' => ?_
        obtain ⟨_, _, _, p', _, _, hp', _, hl', _⟩ := key τ b' hb'
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact absurd hl' hl
    · refine Doomed.of_forall _ _ fun τ b' hb' => ?_
      obtain ⟨_, r, rs', p', out, _, hp', hbt, _, _⟩ := key τ b' hb'
      rw [hp] at hp'
      obtain rfl := Option.some.inj hp'
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hlen, _⟩ := batt_ok hbt
      exact absurd hlen hn

/-! ## At a lens -/

/-- **What is asked of a lens**: where a part that keeps heard, indexMasks and pile, and owes
nothing, is written, a part is read that has these four and the written claim. -/
def LensLaw (X : Lens T) : Prop :=
  ∀ t p p', X.get? t = some p → p'.heard = p.heard → p'.indexMasks = p.indexMasks →
    p'.pile = p.pile → p'.owed = none → ∃ q, X.get? (X.set t p') = some q ∧ q.heard = p'.heard ∧
      q.indexMasks = p'.indexMasks ∧ q.pile = p'.pile ∧ q.owed = none ∧ q.lin = p'.lin

/-- A lens that reads such a part back as it was written has it. -/
theorem lensLaw_of_same (X : Lens T)
    (h : ∀ t p p', X.get? t = some p → p'.heard = p.heard → p'.indexMasks = p.indexMasks →
      p'.pile = p.pile → p'.owed = none → X.get? (X.set t p') = some p') : LensLaw X :=
  fun t p p' hp h1 h2 h3 h4 => ⟨p', h t p p' hp h1 h2 h3 h4, rfl, rfl, rfl, h4, rfl⟩

/-- The part that the text is handed: behind the chain's coming to its end. -/
def partIn (X : Lens T) (t : T) : Option Part := (X.enter t).bind X.get?

/-- The rows on the table behind: the claim's row. -/
def rowOut (X : Lens T) (t : T) : List TensorRow :=
  match X.get? t with
  | some p => (p.lin.map fun l => [rowOfClaim l.claim]).getD []
  | none => []

/-- **The kind's three blocks in a row, at any lens with the law, meet the premise.** -/
theorem byBatt_joined (X : Lens T) (hX : LensLaw X) (P : Where) (n₁ n₂ : String) :
    ByBatt (((frontB (Cl := Cl) X P).andThen n₁ (claimCombinationBlock X P)).andThen n₂ (quietB X P)) P
      (partIn X) (rowOut X) where
  yes := by
    intro t t' rs gs h
    have h' : (((frontB (Cl := Cl) X P).decide t ((rs.take (2 + P.lin.kCol)).take 0)
        ((gs.take ((frontB (Cl := Cl) X P).andThen n₁ (claimCombinationBlock X P)).openings).take
          (frontB (Cl := Cl) X P).openings)).bind fun s₁ =>
        (claimCombinationBlock (Cl := Cl) X P).decide s₁ ((rs.take (2 + P.lin.kCol)).drop 0)
          ((gs.take ((frontB (Cl := Cl) X P).andThen n₁ (claimCombinationBlock X P)).openings).drop
            (frontB (Cl := Cl) X P).openings)).bind (fun s₂ =>
        (quietB (Cl := Cl) X P).decide s₂ (rs.drop (2 + P.lin.kCol))
          (gs.drop ((frontB (Cl := Cl) X P).andThen n₁ (claimCombinationBlock X P)).openings)) = .ok t' := by
      have e : ((frontB (Cl := Cl) X P).andThen n₁ (claimCombinationBlock X P)).rounds.length =
          2 + P.lin.kCol := by
        simp [Block.andThen, frontB, still, claimCombinationBlock, battRounds]
        omega
      rw [← e]
      exact h
    obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
    obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
    obtain ⟨p, he, hp, hfit⟩ := frontB_fit X P h1
    obtain ⟨p₁, out, hp₁, hbt, rfl⟩ := battB_ok X P h2
    rw [hp] at hp₁
    obtain rfl := Option.some.inj hp₁
    obtain ⟨p₂, msg, hp₂, rfl⟩ := quietB_ok X P h3
    obtain ⟨q₂, g2, a1, a2, a3, a4, a5⟩ := hX s₁ p
      { p with owed := none, lin := some { claim := memberClaim out.1 }, d := out.2 }
      hp rfl rfl rfl rfl
    rw [g2] at hp₂
    obtain rfl := Option.some.inj hp₂
    obtain ⟨q₃, g3, _, _, _, _, c5⟩ := hX _ q₂ { q₂ with msg := msg } g2 rfl rfl rfl a4
    refine ⟨p, out, ?_, hbt, onLedger_of_fit hfit, ?_⟩
    · unfold partIn
      rw [he]
      exact hp
    · unfold rowOut
      rw [g3]
      have e : q₃.lin = some { claim := memberClaim out.1 } := c5.trans a5
      show (q₃.lin.map fun l => [rowOfClaim l.claim]).getD [] = [out.1]
      rw [e]
      show [rowOfClaim (memberClaim out.1)] = [out.1]
      rw [rowOfClaim_member]

/-- **So does a block behind a block without a round whose yes is a function of the state.** -/
theorem ByBatt.behind {b : Block T Cl} {P : Where} {partF : T → Option Part}
    {rowB : T → List TensorRow} (hb : ByBatt b P partF rowB) (q : Block T Cl) (nm : String)
    (hq : q.rounds = []) (qf : T → Option T)
    (hqf : ∀ t rs gs t₁, q.decide t rs gs = .ok t₁ → qf t = some t₁) :
    ByBatt (q.andThen nm b) P (fun t => (qf t).bind partF) rowB where
  yes := by
    intro t t' rs gs h
    have h' : (q.decide t (rs.take q.rounds.length) (gs.take q.openings)).bind (fun m =>
        b.decide m (rs.drop q.rounds.length) (gs.drop q.openings)) = .ok t' := h
    obtain ⟨m, h1, h2⟩ := ebind_ok.1 h'
    rw [hq] at h2
    obtain ⟨p, out, hp, hbt, hl, hr⟩ := hb.yes _ _ _ _ h2
    refine ⟨p, out, ?_, hbt, hl, hr⟩
    show (qf t).bind partF = some p
    rw [hqf _ _ _ _ h1]
    exact hp

/-- What the first chain's record's lens reads at the chain's end. -/
theorem atS_get {s : S} {o : First.MemOwn} (h : s.here = .mem o) :
    atS.get? s = some
      { owed := if s.noneWaits then none else s.rowsOwed, heard := s.out.reply,
        indexMasks := s.out.indexMasks, pile := s.out.pending, msg := o.msg, ids := o.ids,
        lin := o.lin, d := dOf s } := by
  simp only [atS, h, dOf]

/-- **A member**: the first chain's record's lens has the law. -/
theorem lensLaw_atS : LensLaw atS := by
  intro t p p' hp h1 h2 h3 h4
  obtain ⟨a, hs, _, _, _⟩ := get_mem hp
  rw [atS_get hs] at hp
  obtain rfl := Option.some.inj hp
  have hs' : (atS.set t p').here = .mem ⟨p'.msg, p'.ids, p'.lin⟩ := by simp only [atS, hs]
  have ho : (atS.set t p').out = t.out := by simp only [atS, hs]
  have hr : (atS.set t p').rowsOwed = p'.owed := by simp only [atS, hs]
  refine ⟨_, atS_get hs', ?_, ?_, ?_, ?_, rfl⟩
  · show (atS.set t p').out.reply = p'.heard
    rw [ho, h1]
  · show (atS.set t p').out.indexMasks = p'.indexMasks
    rw [ho, h2]
  · show (atS.set t p').out.pending = p'.pile
    rw [ho, h3]
  · show (if (atS.set t p').noneWaits then none else (atS.set t p').rowsOwed) = none
    rw [hr, h4]
    exact ite_self _

/-- **A try**: a block that says yes to all does not meet the premise at a reader that gives no row
behind. -/
theorem not_byBatt_yes (b : Block T Cl) (P : Where) (partF : T → Option Part) (t : T)
    (hb : b.decide t [] [] = .ok t) : ¬ ByBatt b P partF (fun _ => []) := by
  intro H
  obtain ⟨_, _, _, _, _, h⟩ := H.yes _ _ _ _ hb
  cases h

end VerifiableInference.Desc.K13.Law

