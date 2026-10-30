-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Good.lean: kind K13's joined block at its place, as a piece of the first chain,
has what a block with a promise owes (`Piece.GoodIn`). Statements with their proofs.

The verifier is the frame's own fold at the list of this one block. The law of the text
(`batt_sound`) is carried from the typed rounds to the written ones by the library's
`CarryS.doomed` along `mapsOf`.
Main names:
  `single_ok`: where the fold at one block says yes, the block's own decision has said yes on all
    the rounds shown. General in the block.
  `errK`, `pieceM3`: the typed errors; the piece: the extractor is the identity; each written error
    is the typed one times the number of written challenges that go to one typed value.
  `RowsHold rw Pin`: what stands at both borders: the witness is pinned to the oracles, and all rows
    on the table (`S.rows`) are true of what the reader takes from it.
  `atM3_goodIn`: **the law.**
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/Law.lean and Johnson/Desc/K13/Law/AtM3.lean
name.

What is not claimed. The premises: the stretch has a written round for each column variable; each
written round draws one element and no position; the pin fixes what the reader takes; the pin is
carried back over the piece. Johnson/Desc/K13/Law/Tries.lean meets them at the block's own entries
and at every local decoder. No promise is made or spent: both conditions hold of all statements.
That the errors are small is not said. Nothing on the block behind W's commitment, on an honest
prover or on hiding. At a reader that takes all mask entries from one world the premise on the pin
cannot be met by a real run (it fixes a value at every mask entry of every message, and messages are
sent behind these draws): there the law is true and idle. The law to carry on is that of
Johnson/Desc/K13/Law/Good2.lean. That the piece is owed just its stretch and that its trees are
listed: Johnson/Desc/K13/Law/Tile.lean, under a test on data. The number nR of the matrix's rows is
a free letter: that it is the plan's is said nowhere but in Johnson/Desc/K13/Law/Caller.lean.

-/
import Johnson.Desc.K13.Law.View
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop Run
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open Johnson.L5.Layers (rd sRound sRounds errTo)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece foldRun)

/-- A test of the format's passes exactly if it is true. -/
theorem dneed_ok {name : String} {b : Bool} {u : Unit} :
    VerifiableInference.Desc.need name b = .ok u ↔ b = true := by
  cases b <;> simp [VerifiableInference.Desc.need]

/-- **Where the fold at one block says yes**: the rounds have the block's form, they are all the
block's, and the block's own decision has said yes on them. -/
theorem single_ok {T Cl : Type} {name : String} {ft : ℕ} {b : Block T Cl} {s s' : T} {v : Fmt.View}
    (h : (chainAt name ft [b] s v).toOption = some s') :
    ∃ gs, roundsFit b.rounds v.rounds = true ∧ b.decide s (v.rounds.map noDigest) gs = .ok s' := by
  unfold chainAt at h
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
  cases hfb : foldBlocks ft [b] s v.rounds v.opened with
  | error e =>
    rw [hfb] at h
    cases h
  | ok z =>
    obtain ⟨s1, rs1, c1⟩ := z
    rw [hfb] at h
    simp only [foldBlocks, List.splitAt_eq] at hfb
    split at hfb
    · cases hfb
    · split at hfb
      · cases hfb
      · next s2 k hst =>
        obtain ⟨rfl, rfl, rfl⟩ : s2 = s1 ∧ v.rounds.drop b.rounds.length = rs1 ∧
            v.opened.drop k = c1 := by
          have := Except.ok.inj hfb
          exact ⟨congrArg (·.1) this, congrArg (·.2.1) this, congrArg (·.2.2) this⟩
        cases hd : v.rounds.drop b.rounds.length with
        | cons _ _ =>
          rw [hd] at h
          cases h
        | nil =>
          cases hc : v.opened.drop k with
          | cons _ _ =>
            rw [hd, hc] at h
            cases h
          | nil =>
            rw [hd, hc] at h
            obtain rfl := Option.some.inj h
            rw [List.take_of_length_le (List.drop_eq_nil_iff.1 hd)] at hst
            simp only [Block.step, bind_ok, dneed_ok, pure_ok] at hst
            obtain ⟨_, h1, _, _, s3, hdec, he⟩ := hst
            obtain rfl : s3 = s2 := congrArg Prod.fst he
            exact ⟨_, h1, hdec⟩

/-! ## The piece -/

/-- The typed errors: n - 1 at the draw, 1 at the sum's round, 2 at each variable's. -/
def errK (n k : ℕ) : Err (shapeK k) :=
  (n - 1, 1, errTo (sRounds (fmtOf GE k)) (pRounds (fmtOf GE k)) (pErr (fmtOf GE k)))

/-- They are the library's at a pile of n rows. -/
theorem eps_eq (nR k : ℕ) (pile : List TensorRow) (Ex : ExtSpec) :
    Cb.Pv.BattShort.eps (parOf ρg nR k pile) Ex = errK pile.length k := rfl

variable {Cl W : Type} {nR : ℕ}

/-- **The joined block at its stretch**: the round of the draw, the round of the sum, a round for
each column variable. The extractor is the identity. The errors are the typed ones, each times the
number of written challenges that the format's sampler takes to one typed value. -/
def pieceM3 (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT) :
    Piece (ckP .two) F S Cl W where
  b := atM3 P
  base := base
  ds := dZ :: d0 :: ds
  back := []
  ext := fun _ _ w => w
  err := (mapsOf dZ d0 ds).err (errK P.rows ds.length)

/-- **What stands at both borders of the place**: the witness is pinned to the oracles, and all rows
on the table are true of what the reader takes from it. In front of the place the rows are the pile;
behind it the one row of the claim (`S.rows`). -/
def RowsHold {F : Frame} {k : ℕ} (rw : W → Wit GE nR k) (Pin : F.E.Str → W → Prop)
    (a : S × F.E.Str) (w : W) : Prop :=
  Pin a.2 w ∧ ∀ r ∈ a.1.rows, Holds ρg (rw w) r

/-- **What the joined block owes, it has.** -/
theorem atM3_goodIn (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hk : P.lin.kCol = ds.length) {nZ n0 aZ a0 : ℕ}
    (hZ : SendsDraws (toRD dZ) nZ 1 0 aZ) (h0 : SendsDraws (toRD d0) n0 1 0 a0)
    (hs : ∀ d ∈ ds, ∃ n a, SendsDraws (toRD d) n 1 0 a)
    (rw : W → Wit GE nR ds.length) (Pin : F.E.Str → W → Prop)
    (hdet : ∀ y w w', Pin y w → Pin y w' → rw w = rw w')
    (hback : ∀ a τ b w, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b →
      Pin b.2 w → Pin a.2 w) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun _ => True) (fun _ => True)
      (RowsHold rw Pin) (RowsHold rw Pin) := by
  intro a _
  have key : ∀ τ b, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.red.out a τ = some b →
      (mapsOf dZ d0 ds).pass τ = true ∧
      ∃ r rs' out, (rvT (ckP .two) (dZ :: d0 :: ds) τ).map noDigest = r :: rs' ∧
        batt (owedOf a.1) ds.length P.rows a.1.out.pending a.1.out.indexMasks (dOf a.1)
          (r :: rs') = .ok out ∧
        a.1.rows = a.1.out.pending ∧ b.1.rows = [out.1] := by
    intro τ b hb
    have hb' : (if sTests (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ
        then (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).run a.1
          (sView (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ)
        else none).map (fun xo =>
          (xo, (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).ior.imp a.2 τ)) = some b := hb
    by_cases ht : sTests (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ
        = true
    · rw [if_pos ht] at hb'
      cases hrun : (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).run a.1
          (sView (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage a.2 τ) with
      | none =>
        rw [hrun] at hb'
        cases hb'
      | some s' =>
        rw [hrun] at hb'
        obtain rfl := Option.some.inj hb'
        simp only [sTests, Bool.and_eq_true] at ht
        refine ⟨(maps_pass dZ d0 ds τ).trans ht.1.1, ?_⟩
        obtain ⟨gs, _, hdec⟩ := single_ok hrun
        obtain ⟨out, hbt, hr1, hr2⟩ := atM3_ok hdec
        have e1 : ((rvT (ckP .two) (dZ :: d0 :: ds) τ ++ []).map noDigest).take
            (2 + P.lin.kCol) = (rvT (ckP .two) (dZ :: d0 :: ds) τ).map noDigest := by
          rw [List.append_nil]
          refine List.take_of_length_le ?_
          rw [List.length_map, rvT_len, hk]
          simp
          omega
        have hbt' : batt (owedOf a.1) P.lin.kCol P.rows a.1.out.pending a.1.out.indexMasks
            (dOf a.1) (((rvT (ckP .two) (dZ :: d0 :: ds) τ ++ []).map noDigest).take
              (2 + P.lin.kCol)) = .ok out := hbt
        rw [e1, hk] at hbt'
        obtain ⟨mZ, cZ, τ1⟩ := τ
        exact ⟨_, _, out, rfl, hbt', hr1, hr2⟩
    · rw [if_neg ht] at hb'
      cases hb'
  by_cases hn : a.1.out.pending.length = P.rows
  · have hD := batt_sound ρg nR ds.length W rw (Pin a.2) (hdet a.2) (owedOf a.1) P.rows
      a.1.out.pending a.1.out.indexMasks (dOf a.1) F.E a.2
    have hfit : (mapsOf dZ d0 ds).carry.Fits (errK a.1.out.pending.length ds.length)
        ((mapsOf dZ d0 ds).err (errK P.rows ds.length)) := by
      rw [hn]
      exact (mapsOf dZ d0 ds).fits (mapsOf_ok hZ h0 hs) _
    refine CarryS.doomed (mapsOf dZ d0 ds).carry _ _ hfit _ _ ?_ ?_ hD
    · intro τ hτ b hb
      rw [Maps.tr_of_pass _ τ (key τ b hb).1] at hτ
      cases hτ
    · intro τ τ' hτ hbad b hb
      obtain ⟨hp, r, rs', out, e, hbt, hr1, hr2⟩ := key τ b hb
      rw [Maps.tr_of_pass _ τ hp] at hτ
      obtain rfl := Option.some.inj hτ
      obtain ⟨r1, rs1, x, t, hd, o, e1, _, _, hx, _, _, hh, _, _, _⟩ := batt_ok hbt
      obtain ⟨rfl, rfl⟩ := List.cons.inj e1
      refine ⟨trivial, fun w hw => ⟨hback a τ b w hb hw.1, ?_⟩⟩
      rw [hr1]
      exact hbad r rs' x hd out hx hh (whole_read nR _ F.E dZ d0 ds τ r rs' x hd e hx hh) hbt w
        (hback a τ b w hb hw.1) (hw.2 out.1 (by rw [hr2]; exact List.mem_singleton.2 rfl))
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    obtain ⟨_, r, rs', out, _, hbt, _, _⟩ := key τ b hb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hlen, _⟩ := batt_ok hbt
    exact absurd hlen hn

end VerifiableInference.Desc.K13.Law
