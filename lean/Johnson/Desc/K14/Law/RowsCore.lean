-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/RowsCore.lean: THE LAWS OF "(rec_gamma)" AND OF "LOC" IN THE FORM OF THE RULE
OF COMPOSITION, WITH ONLY THE BLOCK's OWN ROWS BEHIND, GENERAL IN THE RECORD AND IN THE TWO
PROMISES.

Why. The laws of Johnson/Desc/K14/Law/RecRow.lean and GoodLoc.lean have behind the block "all
constraints on the two groups hold at their tests" (Base). A table of joints whose items are classes
of open rows asks of a block's own law only what its row names: behind "LOC": the rows (loc_x) AS
THEY LIE IN THE RECORD, and o_u's pin. Here the two laws stand in that form.
  RowsU i n d m   the constraints number i, …, i + n - 1 on G_u, as they lie in the record d, hold
                  of the words m, read at d's own statement.
  RowsUL i n d m  the same, said at a statement that has grown out of d's: the form in which the two
                  cores have their rows behind: it rides back over a sending too.
  recSaysOwn, locSaysOwn   what the rows that the place itself has laid mean: recSays and locSays
                  (Johnson/Desc/K14/Law/Joint.lean) without the group's other rows.
  rec_core        **"(rec_gamma)"**: for certain. In front: PinA, and (rec_gamma)'s equation at
                  every seed (RecAll). Behind: PinB, and the rows i₀, …, i₀ + answers - 1 on G_u
                  (RowsUL).
  loc_core        **"LOC"**: but for (2 ^ logN - e' - 1) ^ n lists of locations. In front: PinA, and
                  near (NearAt). Behind: PinB, and the rows i₀, …, i₀ + n - 1 on G_u (RowsUL).
T: a record that holds the chain's own (get : T → St); any type of claims; on, on': letters, with
"on a, a yes: on' b". OF THE PROMISE IN FRONT THE PROOFS SPEND: the stored table's shape meets its
conditions, o_u has its table at every statement that grows out of the record's (what On4 says), and
G_u HAS JUST i₀ OPEN ROWS. The pattern is that of Johnson/Desc/K14/Law/GoodFoldAt.lean: zeta_core.

What is not claimed. The premises of the two older laws stay, under the letter on: the extractor is
the identity; at a yes a witness with PinB behind has PinA in front; two witnesses with PinA at one
statement have the same words on o_u; the columns shown are the stored table's; the written round
reads as one typed draw, at errors that fit. PinA, PinB, on, on' are letters: no member is shown. A
block that refuses all has GoodIn too. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.RecRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure)
open _root_.Run.PQ (CK)
open Iop.IOR (drawRound)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- The constraints number i, …, i + n - 1 on G_u, as they lie in the record, hold of the words. -/
def RowsU (i n : Nat) (d : St) (m : Words K) : Prop :=
  Means.AllSay ρ d.st (((rowsOn d d.loc.gU).drop i).take n) m

/-- The same, SAID AT A STATEMENT THAT HAS GROWN OUT OF THE RECORD's: a row's claim is a sum over
    all
messages of the statement at which it is said, and behind o_omega's sending the statement has more
messages than where the rows of "(rec_gamma)" and "LOC" were laid. So these two classes are said at
"some later statement": that form rides back over every step onward, a sending too; whoever shows
the rows at the record's own statement has it (rowsUL_of_own); and the two cores spend no more: they
read the rows at any statement at which o_u is placed. -/
def RowsUL (i n : Nat) (d : St) (m : Words K) : Prop :=
  ∃ T, Grows d.st T ∧ Means.AllSay ρ T (((rowsOn d d.loc.gU).drop i).take n) m

/-- At the record's own statement. -/
theorem rowsUL_of_own (i n : Nat) (d : St) (m : Words K) (h : RowsU ρ i n d m) :
    RowsUL ρ i n d m := ⟨d.st, Grows.refl _, h⟩

/-- **What the constraints that "(rec_gamma)" itself has laid mean.** -/
theorem recSaysOwn (p : Par) (d d' : St) (rs : List Fmt.RoundView) (T : Statement) (m : Words K)
    (h : laysRec p d rs = some d')
    (hs : ∀ rows, rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ rows →
      rows.length = p.S.fold.index.answers → Means.AllSay ρ T rows m)
    (hi : p.S.fold.index.ok = true) (hP : PlacedU T p.S.fold d.loc.oU) : RecAll ρ p d m := by
  intro x hx
  obtain ⟨hok, _, rows, hrows, hU, _⟩ := laysRecW p d d' rs h
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
  have hfit : d.loc.key.fits p.S.fold.index = true := hok.1
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  have hlen : rows.length = p.S.fold.index.answers := by
    rw [length_mapM _ _ _ hrows, List.length_zipIdx]
    exact hfit.1.2
  obtain ⟨row, hrow, hg⟩ := mem_mapM _ _ _ hrows x hx
  have hsay : Means.Says ρ T row m := hs rows hU hlen row hrow
  have hx' : d.loc.key.seeds[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  have hlt : x.2 < p.S.fold.index.answers := by
    rw [← hfit.1.2]
    exact (List.getElem?_eq_some_iff.1 hx').1
  have hz : x.1.z.length = p.S.fold.index.cubeBits := hfit.2 _ (List.mem_of_getElem? hx')
  exact (recMeansW ρ T p.S.fold x.1 x.2 _ _ _ row hi hlt hz hg hP m).1 hsay

/-- **What the constraints that "LOC" itself has laid mean.** -/
theorem locSaysOwn (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (T : Statement) (m : Words K) (h : loc p d [r] [cols] = some d')
    (hs : ∀ rows, rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ rows →
      rows.length = r.drawn.poss.length → Means.AllSay ρ T rows m)
    (hi : p.S.fold.index.ok = true) (hP : PlacedU T p.S.fold d.loc.oU) :
    ∀ x ∈ locations p r, ∃ col, cols.lookup x = some col ∧
      LocEq ρ p.S.fold (generatorAt p.S.fold.index.code x)
        (fun r => ρ.val ((weights p.S d.loc).getD r zeroE)) (weights p.S d.loc).size
        (fun r => ρ.val (ofF (col.toArray.getD r 0)))
        (fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k)) := by
  intro x hx
  obtain ⟨_, rows, hrows, hlen, hU, _⟩ := laysLocW p d d' r cols h
  obtain ⟨row, hrow, hg⟩ := mem_mapM _ _ _ hrows x hx
  have hsay : Means.Says ρ T row m := hs rows hU hlen row hrow
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hg
  obtain ⟨col, hcol, hg⟩ := hg
  exact ⟨col, hcol, (locMeansW ρ T p.S.fold x _ _ _ row hi hg hP m).1 hsay⟩

/-- The rows from i₀ on, n of them, are the rows that were laid behind i₀ rows. -/
theorem slice_new {α : Type} (old new : List α) (i₀ n : Nat) (h0 : old.length = i₀)
    (hn : new.length = n) : ((old ++ new).drop i₀).take n = new := by
  rw [List.drop_left' h0, List.take_of_length_le (Nat.le_of_eq hn)]

variable {W : Type} {C : CK} {F : Frame} (rw : W → Words K)

/-- **"(rec_gamma)": the core.** -/
theorem rec_core {T Cl : Type} (get : T → St) (pc : Piece C F T Cl W) (p : Par)
    (hl : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → laysRec p (get d) rs = some (get d'))
    (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : T × F.E.Str → Prop)
    (PinA PinB : T × F.E.Str → W → Prop)
    (hst : ∀ a, on a → p.S.fold.index.ok = true ∧
      ∀ T', Grows (get a.1).st T' → PlacedU T' p.S.fold (get a.1).loc.oU)
    (i₀ : Nat) (hi₀ : ∀ a, on a → (rowsOn (get a.1) (get a.1).loc.gU).length = i₀)
    (hon : ∀ a τ b, on a → pc.ior.red.out a τ = some b → on' b)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → PinB b w → PinA a w) :
    pc.GoodIn on on' (fun a w => PinA a w ∧ RecAll ρ p (get a.1) (rw w))
      (fun b w => PinB b w ∧ RowsUL ρ i₀ p.S.fold.index.answers (get b.1) (rw w)) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha hout => ?_
  obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
  have k3 := hl _ _ gs _ hd
  obtain ⟨o, l⟩ := onward_laysRec p (get a.1) (get b.1) _ k3
  refine ⟨hon a τ b ha hout, fun w hw => ?_⟩
  obtain ⟨hpin, T, gT, hrows⟩ := hw
  rw [hext]
  refine ⟨hback a τ b w ha hout hpin, ?_⟩
  refine recSaysOwn ρ p (get a.1) (get b.1) _ T (rw w) k3 (fun rows hU hlen => ?_)
    (hst a ha).1 ((hst a ha).2 _ (o.grows.trans gT))
  rw [l, hU, slice_new _ _ _ _ (hi₀ a ha) hlen] at hrows
  exact hrows

open Classical in
/-- **"LOC": the core.** tab: the stored table's columns, off the oracles; n: the number of
locations drawn; c: a number that is at least (2 ^ logN - e' - 1) ^ n. -/
theorem loc_core {T Cl : Type} (get : T → St) (pc : Piece C F T Cl W) (p : Par)
    (hl : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → loc p (get d) rs gs = some (get d'))
    (hext : ∀ a τ w, pc.ext a τ w = w) (on on' : T × F.E.Str → Prop)
    (PinA PinB : T × F.E.Str → W → Prop)
    (hst : ∀ a, on a → p.S.fold.index.ok = true ∧
      ∀ T', Grows (get a.1).st T' → PlacedU T' p.S.fold (get a.1).loc.oU)
    (i₀ : Nat) (hi₀ : ∀ a, on a → (rowsOn (get a.1) (get a.1).loc.gU).length = i₀)
    (hon : ∀ a τ b, on a → pc.ior.red.out a τ = some b → on' b)
    (hback : ∀ a τ b w, on a → pc.ior.red.out a τ = some b → PinB b w → PinA a w)
    (hdet : ∀ (a : T × F.E.Str) w w', on a → PinA a w → PinA a w' →
      AgreeOn (get a.1).loc.oU.oracle (rw w) (rw w'))
    (tab : F.E.Str → Nat → List UInt64) (e' n c : Nat)
    (hc : (2 ^ p.S.fold.index.code.logN - e' - 1) ^ n ≤ c)
    (hcols : ∀ (a : T × F.E.Str) τ b cols, pc.ior.red.out a τ = some b →
      shownGroups F.ft pc.b (rvT C pc.ds τ ++ pc.back) (sView C pc.stage a.2 τ).opened = [cols] →
      ∀ x col, cols.lookup x = some col → col = tab a.2 x)
    (G : T × F.E.Str →
      CarryS (uLT C pc.ds) [drawRound (Fin n → Fin (2 ^ p.S.fold.index.code.logN))])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ a τ b r4, pc.ior.red.out a τ = some b →
      (rvT C pc.ds τ ++ pc.back).map noDigest = [r4] →
      ∃ Q, (G a).tr τ = some (((), ()), Q, ()) ∧
        r4.drawn.poss = List.ofFn fun i => (Q i).val) :
    pc.GoodIn on on' (fun a w => PinA a w ∧ NearAt ρ p (get a.1) (rw w) (tab a.2) e')
      (fun b w => PinB b w ∧ RowsUL ρ i₀ n (get b.1) (rw w)) := by
  refine goodIn_of_count pc _ _ _ _ (Fin n → Fin (2 ^ p.S.fold.index.code.logN)) c G fits
    (fun a Q => ∃ w, PinA a w ∧ ¬ NearAt ρ p (get a.1) (rw w) (tab a.2) e' ∧
      ∀ i, LocAt ρ p (get a.1) (rw w) (tab a.2) (Q i).val) ?_ ?_
  · intro a ha
    by_cases hw0 : ∃ w0, PinA a w0 ∧ ¬ NearAt ρ p (get a.1) (rw w0) (tab a.2) e'
    · obtain ⟨w0, hp0, hn0⟩ := hw0
      refine le_trans (cnt_mono (Q := fun Q : Fin n → Fin (2 ^ p.S.fold.index.code.logN) =>
        ∀ i, LocAt ρ p (get a.1) (rw w0) (tab a.2) (Q i).val) fun Q hQ => ?_) ?_
      · obtain ⟨w, hp, _, hall⟩ := hQ
        have aU := hdet a w0 w ha hp0 hp
        intro i
        have h0 := hall i
        unfold LocAt at h0 ⊢
        have e : (fun k => rw w (get a.1).loc.oU.oracle .main ((get a.1).loc.oU.lay.index k)) =
            fun k => rw w0 (get a.1).loc.oU.oracle .main ((get a.1).loc.oU.lay.index k) :=
          funext fun k => aU _
        rwa [e] at h0
      · rw [cnt_eq_card]
        have e : (Finset.univ.filter fun Q : Fin n → Fin (2 ^ p.S.fold.index.code.logN) =>
            ∀ i, LocAt ρ p (get a.1) (rw w0) (tab a.2) (Q i).val) =
            Fintype.piFinset fun _ : Fin n => Finset.univ.filter
              fun x : Fin (2 ^ p.S.fold.index.code.logN) =>
                LocAt ρ p (get a.1) (rw w0) (tab a.2) x.val := by
          ext Q
          simp [Fintype.mem_piFinset]
        rw [e, Fintype.card_piFinset_const]
        exact le_trans
          (Nat.pow_le_pow_left (card_locAt_lt ρ p (get a.1) (rw w0) (tab a.2) e' hn0) n) hc
    · rw [cnt_false fun Q hQ => hw0 (by obtain ⟨w, hp, hn, _⟩ := hQ; exact ⟨w, hp, hn⟩)]
      exact Nat.zero_le _
  · intro a τ b ha hout
    have hd := piece_groups pc a τ b hout
    have k4 := hl _ _ _ _ hd
    obtain ⟨r4, cols, hr, hg⟩ := loc_one _ _ _ _ _ k4
    obtain ⟨Q, htr, hQ⟩ := hread a τ b r4 hout hr
    rw [hr, hg] at k4
    obtain ⟨o4, l4⟩ := onward_loc p (get a.1) (get b.1) r4 cols k4
    refine ⟨_, htr, fun hnl => ⟨hon a τ b ha hout, fun w hw => ?_⟩⟩
    obtain ⟨hpin, T, gT, hrows⟩ := hw
    have hpa := hback a τ b w ha hout hpin
    rw [hext]
    refine ⟨hpa, ?_⟩
    by_contra hn
    refine hnl ⟨w, hpa, hn, fun i => ?_⟩
    have hx : (Q i).val ∈ locations p r4 := by
      unfold locations
      rw [hQ]
      refine List.mem_map.2 ⟨(Q i).val, ?_, Nat.mod_eq_of_lt (Q i).isLt⟩
      exact (List.mem_ofFn' _ _).2 ⟨i, rfl⟩
    obtain ⟨col, hcol, hEq⟩ := locSaysOwn ρ p (get a.1) (get b.1) r4 cols T (rw w) k4
      (fun rows hU hlen => by
        have hlen' : rows.length = n := by rw [hlen, hQ, List.length_ofFn]
        rw [l4, hU, slice_new _ _ _ _ (hi₀ a ha) hlen'] at hrows
        exact hrows)
      (hst a ha).1 ((hst a ha).2 _ (o4.grows.trans gT)) _ hx
    rw [hcols a τ b cols hout hg _ col hcol] at hEq
    exact hEq

end Desc.K14.Law
