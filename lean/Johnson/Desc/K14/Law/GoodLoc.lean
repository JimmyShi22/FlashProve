-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/GoodLoc.lean: the law of (loc_x) in the form that the rule of composition asks
of a block at its stretch (Piece.GoodIn): for the block "LOC" of the shared chain.

  On4             the promise at both borders: the stored table's shape meets its conditions, and
                  o_u has its table at every statement that grows out of the record's.
  in front of "LOC"   Base, and the code word of the folded row is within e' locations of the fold
                  of the stored table's columns (NearAt).
  behind "LOC"        Base.
  loc_goodIn      by the bridge goodIn_of_count: the lost lists are those all of whose locations lie
                  where (loc_x)'s equation holds of a pinned witness's words though the code word is
                  not near: no more than (2 ^ logN - e' - 1) ^ n, n the number of locations drawn.
  posPiece, loc_goodIn4   at the shared chain's own fourth block, in the library's field, at one
                  written round, with the carriage paid by the library's maps of written rounds.

What is not claimed. PREMISES OF BOTH, EACH UNDER THE PROMISE IN FRONT ALONE (On4 and a letter Prm):
at a yes a witness that is pinned behind the block is pinned
in front of it, and a second letter Prm' holds behind; two witnesses pinned by one statement have
the same words on o_u; THE COLUMNS THAT THE STEP SHOWS THE BLOCK ARE THE STORED TABLE's (hcols). OF
loc_goodIn: the extractor is the identity; the stretch's written round reads as one typed draw of a
list of locations, the one that the block reads, at errors that fit (G, fits, hread). OF loc_goodIn4
in their place: the written round draws n positions below 2 ^ logN and no element (SendsDraws). A
block that refuses all has GoodIn too. Nothing on what "near" gives of the folded row's message. No
soundness of a verifier.

-/
import Johnson.Desc.K14.Law.GoodFold
import Johnson.Desc.K14.Law.LocNear
import Johnson.Desc.K14.Law.LocRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block chainAt foldBlocks noDigest groupsOf regroup OpenedColumn)
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)
open Iop.IOR (drawRound)

variable {W : Type} {C : CK} {F : Frame}

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)
variable (rw : W → Words K) (Pin : St × F.E.Str → W → Prop)

/-- The promise at both borders of "LOC". -/
def On4 (p : Par) (a : St × F.E.Str) : Prop :=
  p.S.fold.index.ok = true ∧ ∀ T, Grows a.1.st T → PlacedU T p.S.fold a.1.loc.oU

open Classical in
/-- **"LOC" in the form of the rule of composition.** tab: the stored table's columns, off the
oracles; n: the number of locations drawn; c: a number that is at least (2 ^ logN - e' - 1) ^ n. -/
theorem loc_goodIn (pc : Piece C F St Unit W) (p : Par)
    (hl : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → loc p d rs gs = some d')
    (hext : ∀ a τ w, pc.ext a τ w = w)
    (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, On4 p a → Prm a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hkeep : ∀ a τ b, On4 p a → Prm a → pc.ior.red.out a τ = some b → Prm' b)
    (hdet : ∀ (a : St × F.E.Str) w w', On4 p a → Prm a → Pin a w → Pin a w' →
      AgreeOn a.1.loc.oU.oracle (rw w) (rw w'))
    (tab : F.E.Str → Nat → List UInt64) (e' n c : Nat)
    (hc : (2 ^ p.S.fold.index.code.logN - e' - 1) ^ n ≤ c)
    (hcols : ∀ (a : St × F.E.Str) τ b cols, pc.ior.red.out a τ = some b →
      shownGroups F.ft pc.b (rvT C pc.ds τ ++ pc.back) (sView C pc.stage a.2 τ).opened = [cols] →
      ∀ x col, cols.lookup x = some col → col = tab a.2 x)
    (G : St × F.E.Str →
      CarryS (uLT C pc.ds) [drawRound (Fin n → Fin (2 ^ p.S.fold.index.code.logN))])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ a τ b r4, pc.ior.red.out a τ = some b →
      (rvT C pc.ds τ ++ pc.back).map noDigest = [r4] →
      ∃ Q, (G a).tr τ = some (((), ()), Q, ()) ∧
        r4.drawn.poss = List.ofFn fun i => (Q i).val) :
    pc.GoodIn (fun a => On4 p a ∧ Prm a) (fun b => On4 p b ∧ Prm' b)
      (fun a w => Base ρ rw Pin a w ∧ NearAt ρ p a.1 (rw w) (tab a.2) e') (Base ρ rw Pin) := by
  refine goodIn_of_count pc _ _ _ _ (Fin n → Fin (2 ^ p.S.fold.index.code.logN)) c G fits
    (fun a Q => ∃ w, Pin a w ∧ ¬ NearAt ρ p a.1 (rw w) (tab a.2) e' ∧
      ∀ i, LocAt ρ p a.1 (rw w) (tab a.2) (Q i).val) ?_ ?_
  · intro a ha
    by_cases hw0 : ∃ w0, Pin a w0 ∧ ¬ NearAt ρ p a.1 (rw w0) (tab a.2) e'
    · obtain ⟨w0, hp0, hn0⟩ := hw0
      refine le_trans (cnt_mono (Q := fun Q : Fin n → Fin (2 ^ p.S.fold.index.code.logN) =>
        ∀ i, LocAt ρ p a.1 (rw w0) (tab a.2) (Q i).val) fun Q hQ => ?_) ?_
      · obtain ⟨w, hp, _, hall⟩ := hQ
        have aU := hdet a w0 w ha.1 ha.2 hp0 hp
        intro i
        have h0 := hall i
        unfold LocAt at h0 ⊢
        have e : (fun k => rw w a.1.loc.oU.oracle .main (a.1.loc.oU.lay.index k)) =
            fun k => rw w0 a.1.loc.oU.oracle .main (a.1.loc.oU.lay.index k) :=
          funext fun k => aU _
        rwa [e] at h0
      · rw [cnt_eq_card]
        have e : (Finset.univ.filter fun Q : Fin n → Fin (2 ^ p.S.fold.index.code.logN) =>
            ∀ i, LocAt ρ p a.1 (rw w0) (tab a.2) (Q i).val) =
            Fintype.piFinset fun _ : Fin n => Finset.univ.filter
              fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
                LocAt ρ p a.1 (rw w0) (tab a.2) x.val := by
          ext Q
          simp [Fintype.mem_piFinset]
        rw [e, Fintype.card_piFinset_const]
        exact le_trans (Nat.pow_le_pow_left (card_locAt_lt ρ p a.1 (rw w0) (tab a.2) e' hn0) n) hc
    · rw [cnt_false fun Q hQ => hw0 (by obtain ⟨w, hp, hn, _⟩ := hQ; exact ⟨w, hp, hn⟩)]
      exact Nat.zero_le _
  · intro a τ b ha' hout
    obtain ⟨ha, hprm⟩ := ha'
    have hd := piece_groups pc a τ b hout
    have k4 := hl _ _ _ _ hd
    obtain ⟨r4, cols, hr, hg⟩ := loc_one _ _ _ _ _ k4
    obtain ⟨Q, htr, hQ⟩ := hread a τ b r4 hout hr
    rw [hr, hg] at k4
    obtain ⟨o4, l4⟩ := onward_loc p a.1 b.1 r4 cols k4
    refine ⟨_, htr, fun hnl => ⟨⟨⟨ha.1, fun T gT => ?_⟩, hkeep a τ b ha hprm hout⟩,
      fun w hw => ?_⟩⟩
    · rw [l4]; exact ha.2 T (o4.grows.trans gT)
    · obtain ⟨hpin, hU, hO⟩ := hw
      have hpa := hback a τ b w ha hprm hout hpin
      rw [hext]
      refine ⟨⟨hpa, ?_, ?_⟩, ?_⟩
      · rw [← l4]; exact hU.back ρ o4
      · rw [← l4]; exact hO.back ρ o4
      · by_contra hn
        refine hnl ⟨w, hpa, hn, fun i => ?_⟩
        obtain ⟨e, re, se⟩ := hU
        rw [l4] at re se
        have hx : (Q i).val ∈ locations p r4 := by
          unfold locations
          rw [hQ]
          refine List.mem_map.2 ⟨(Q i).val, ?_, Nat.mod_eq_of_lt (Q i).isLt⟩
          exact (List.mem_ofFn' _ _).2 ⟨i, rfl⟩
        obtain ⟨col, hcol, hEq⟩ := locSays ρ p a.1 b.1 e r4 cols e.st (rw w) k4 re.later se ha.1
          (ha.2 e.st (o4.grows.trans re.grows)) _ hx
        rw [hcols a τ b cols hout hg _ col hcol] at hEq
        exact hEq

/-- The fourth block decides by "LOC". -/
theorem loc_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ d rs gs d', b4.decide d rs gs = .ok d' → loc P.par d rs gs = some d' := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  exact fun d rs gs d' h => why_some h

/-- The piece that holds a block at one written round that draws t positions below 2 ^ a: no round
is laid behind; the extractor is the identity; the errors are the written count that bears e. -/
def posPiece (b : Block St Unit) (base : Nat) (d : RDT) (a t e : Nat) :
    Piece (ckP .two) F St Unit W :=
  ⟨b, base, [d], [], fun _ _ w => w, (posMaps d a t).err ((e, ()) : Nat × Unit)⟩

/-- **"LOC" in the form of the rule of composition**, at the chain's own fourth block. e: a number
that is at least (2 ^ logN - e' - 1) ^ n. -/
theorem loc_goodIn4 (rg : W → Words GE) (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (base : Nat) (d : RDT) {ns n : Nat}
    (hd : SendsDraws (toRD d) ns 0 n P.par.S.fold.index.code.logN)
    (tab : F.E.Str → Nat → List UInt64) (e' e : Nat)
    (he : (2 ^ P.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e)
    (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ x τ b w, On4 P.par x → Prm x → (posPiece (W := W) (F := F) b4 base d
      P.par.S.fold.index.code.logN n e).ior.red.out x τ = some b → Pin b w → Pin x w)
    (hkeep : ∀ x τ b, On4 P.par x → Prm x → (posPiece (W := W) (F := F) b4 base d
      P.par.S.fold.index.code.logN n e).ior.red.out x τ = some b → Prm' b)
    (hdet : ∀ (x : St × F.E.Str) w w', On4 P.par x → Prm x → Pin x w → Pin x w' →
      AgreeOn x.1.loc.oU.oracle (rg w) (rg w'))
    (hcols : ∀ (x : St × F.E.Str) τ b cols, (posPiece (W := W) (F := F) b4 base d
        P.par.S.fold.index.code.logN n e).ior.red.out x τ = some b →
      shownGroups F.ft b4 (rvT (ckP .two) [d] τ ++ [])
        (sView (ckP .two) (posPiece (W := W) (F := F) b4 base d
          P.par.S.fold.index.code.logN n e).stage x.2 τ).opened = [cols] →
      ∀ y col, cols.lookup y = some col → col = tab x.2 y) :
    (posPiece (W := W) (F := F) b4 base d P.par.S.fold.index.code.logN n e).GoodIn
      (fun x => On4 P.par x ∧ Prm x) (fun x => On4 P.par x ∧ Prm' x)
      (fun x w => Base OnBytes.Model.Reading.gl rg Pin x w ∧
        NearAt OnBytes.Model.Reading.gl P.par x.1 (rg w) (tab x.2) e')
      (Base OnBytes.Model.Reading.gl rg Pin) := by
  refine loc_goodIn OnBytes.Model.Reading.gl rg Pin
    (posPiece (W := W) (F := F) b4 base d P.par.S.fold.index.code.logN n e) P.par
    (loc_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl) (fun _ _ _ => rfl) Prm Prm' hback hkeep hdet tab
    e' n e he
    hcols (fun _ => (posMaps d P.par.S.fold.index.code.logN n).carry)
    (fun _ => (posMaps d P.par.S.fold.index.code.logN n).fits (posMaps_ok hd) _) ?_
  intro x τ b r4 hout hr
  have ht := piece_tests _ x τ b hout
  simp only [sTests, Bool.and_eq_true] at ht
  have hp : (posMaps d P.par.S.fold.index.code.logN n).pass τ = true :=
    (posMaps_pass d _ _ τ).trans ht.1.1
  obtain ⟨m, c, ⟨⟩⟩ := τ
  have hr' : [noDigest (shownAt d m c)] = [r4] := hr
  obtain rfl := (List.cons.inj hr').1
  exact ⟨gPos P.par.S.fold.index.code.logN n _ (valsOf (toRD d) c),
    (posMaps d P.par.S.fold.index.code.logN n).tr_of_pass (m, c, ()) hp, poss_shown hd m c⟩

end Desc.K14.Law
