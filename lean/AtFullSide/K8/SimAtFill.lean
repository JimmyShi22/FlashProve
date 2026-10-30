-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/SimAtFill.lean: the smallness test at a filling that is a letter: its rows, with their
simulators, at the prover that the maker returns at a filling whose lots hold the kind's one lot and
no other side of the kind, and at the base prover, which `onlineProverPartsInUse` makes.

  `hex_base`, `ho_base`   the base filling's lots hold that lot, and no other lot has a half at a place
                   of the kind
  `small_block_at`   at each of the 25 segments the first chain's member: its place, its one round,
                   its empty list of oracle messages
  `small_row_good`   `Good` at a row's own side, from that member
  `smallSLot_rows_mem`, `smallSLot_rows_length`   what the rows are
  `zeroDraw`, `zeroDraw_fits`, `comb_zeroDraw`, `small_stop_zero`   exact is not empty: at the draw
                   of zeros, which fits the round, the second stop does not speak
  `small_rows_fill`   **the five clauses together, at any such filling**: how many rows · each row's half is the
                   prover's · every member of the kind has a row · On and bud hold everywhere · `Good`

Good stands at A := B := False: its fields plays and acc are met for nothing, and fits, exact and
fresh are what is said. exact is asked where the part's second stop does not speak. That no entry of
the book lends a coin of the part is had of the book at the written description
(AtFullSide/K8/BookAtK8.lean).
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.SmallSLot
import Johnson.Desc.ProofFile.Honest.K8.HalfAtFill
import Johnson.Desc.ProofFile.Honest.K8.PlaysAtOwnMats
import Johnson.Desc.ProofFile.Honest.K8.PlaysAtWider
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import AtFullSide.K12.ReturnsAtFillW
import AtFullSide.K12.TwiceFirstW
import Johnson.P1K8R.Tied
import AtFullSide.K8.BookAtK8
import Johnson.Desc.ProofFile.Honest.Small.Book
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place Block KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par Seats approximateRangeProofDrawKind atS)
open VerifiableInference.Desc.First.K8.Honest (seats_of_alone)
open P5J (AtMgA TS)
open ProofFile.Honest.Small (noneSpent spentBy_of_noneSpent)

/-! ## 2 The filling -/

section Filling
variable {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz)
  (O : OnlineProverArguments) (Zq : Pub) (G : Ground)

/-- The kind's lists of matrices at every filling of the protocol. -/
abbrev matsO : Pub → Ground → LinkH → Nat → List (Nat × String × Nat) :=
  fun _ G _ l => K3.matsOwn G.W l

/-- The wide filling holds the kind's lot. -/
theorem hex_base : ∃ M ∈ (onlineProverPartsInUse I o Sz O).lots,
    M.halves Zq G = (smallLot (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id matsO).halves Zq G := by
  refine ⟨smallLot id matsO, ?_, rfl⟩
  rw [widerFillAtCPUOWM_lots]
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
  rw [widerFillAt_lots]
  exact List.mem_map.2 ⟨_, k8_pair_mem I o Sz O, rfl⟩

/-- Every other lot's halves stand at places of other kinds. -/
theorem ho_base : ∀ M ∈ (onlineProverPartsInUse I o Sz O).lots,
    (∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K8) ∨
      M.halves Zq G =
        (smallLot (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) id matsO).halves Zq G := by
  intro L hL
  rw [widerFillAtCPUOWM_lots] at hL
  simp only [List.mem_append, List.mem_singleton] at hL
  rcases hL with ((h1 | rfl) | rfl) | rfl
  · exact ho_wider I o Sz O Zq G L h1
  · refine Or.inl fun y hy e => ?_
    rw [closeLotAt_kinds I Sz Zq G y hy] at e
    cases e
  · refine Or.inl fun y hy e => ?_
    rw [proxLotAt_kinds I Sz Zq G y hy] at e
    cases e
  · refine Or.inl fun y hy e => ?_
    rw [AtFullSide.K12.wHalf_place I o O Zq G y hy] at e
    cases e

end Filling

/-! ## 3 The members -/

section Members
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- No two members of the first chain stand at one place. -/
theorem first_nodup : (cF.blocksInOrder.map (·.place)).Nodup := by
  have hp := Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hn := orderOf_nodup hp
  unfold orderOf at hn
  exact hn.of_append_left.of_append_left

/-- **The member at a segment's draw.** -/
theorem small_block_at {l : ℕ} (hl : l < 25) :
    ∃ (G₀ : ProofFile.Ground) (Xl : LinkH) (blk : Block S ProofFile.Cl),
      ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.built[l]? = some Xl ∧
      cF.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2]? = some blk ∧
      blk.place = ⟨1, some l, (ProofFile.k8Par Zp G₀ Xl l).piece, .K8⟩ ∧
      Seats blk (approximateRangeProofDrawKind (Cl := ProofFile.Cl) atS (ProofFile.k8Par Zp G₀ Xl l)) ∧ blk.oracles = [[]] := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, b, Xb, e1, e2, eX, la, ep, -⟩ := IM.k8_of_head h.scope h.reads O
    have h0 := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope h.scope h.reads O (l := 24) (by omega) 5] at h0
    refine ⟨Bs.G₀, Xb, b, O.blank, eX, h0, ?_, seats_of_alone la, oracles_of_alone la⟩
    rw [ep]
    exact (congrArg (·.place) la).trans rfl
  · rw [if_neg h24]
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · have hg : g < 12 := by omega
      obtain ⟨Lk, b, Xb, hpl, e1, e2, eX, la, -, ep, -⟩ := IM.k8_of_layers h.scope h.reads O g hg
      have h0 := IM.hear_at_flat e1 e2
      rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g) (by omega) 4] at h0
      refine ⟨Bs.G₀, Xb, b, O.blank, eX, h0, ?_, seats_of_alone la, oracles_of_alone la⟩
      rw [ep]
      exact (congrArg (·.place) la).trans rfl
    · have hg : g < 12 := by omega
      obtain ⟨Lk, b, Xb, a, e1, e2, eX, la, -, ep, -⟩ := IM.k8_of_attention h.scope h.reads O g hg
      have h0 := IM.hear_at_flat e1 e2
      rw [IM.flatIx_scope h.scope h.reads O (l := 2 * g + 1) (by omega) 4] at h0
      refine ⟨Bs.G₀, Xb, b, O.blank, eX, h0, ?_, seats_of_alone la, oracles_of_alone la⟩
      rw [ep]
      exact (congrArg (·.place) la).trans rfl

end Members

/-! ## 4 `Good` at a row -/

section Row
variable {W₀ Rc Xi Tr X Pb Cl : Type} {Bk : ProverCoinCounts}

/-- **`Good` at a row's own side**, from its member. -/
theorem small_row_good {bs : List (Block S Cl)} (hn : (bs.map (·.place)).Nodup) {b : Nat}
    {blk : Block S Cl} (hb : bs[b]? = some blk) (cells : Tr → Cells)
    (P : Par × List (Nat × String × Nat))
    (hs : Seats blk (approximateRangeProofDrawKind (Cl := Cl) atS P.1)) (ho : blk.oracles = [[]])
    (hp : blk.place = smallPlace P.1) (hf : smallFits P = true)
    (hB : noneSpent Bk ⟨blk.place, 0⟩ = true)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (ord : List Place)
    (chain firstTree : Nat) (fs : List (Fall S)) :
    ∃ σ, Side.seated bs (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).place
        (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).row fs = some σ ∧
      Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
        (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).On
        (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).bud := by
  have hfind : bs.find? (fun y => y.place == smallPlace P.1) = some blk := by
    rw [← hp]
    exact find_at bs b blk hn hb
  have hσ : Side.seated bs
      (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).place
      (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).row fs =
      some ⟨blk, smallRow cells P, fallOf fs (smallPlace P.1)⟩ := by
    show Side.seated bs (smallPlace P.1) (smallRow cells P) fs = _
    unfold Side.seated
    rw [hfind]
    rfl
  refine ⟨_, hσ, small_hand pre bs cells P fs _ φ Bk ord chain firstTree
    (VerifiableInference.Desc.First.K8.round P.1) hσ hf hs.1 ?_ ho fun q => ?_⟩
  · simp [VerifiableInference.Desc.First.K8.round, Fmt.DeclaredRound.items, Fmt.Entry.cut]
  · exact spentBy_of_noneSpent hB q

/-- Every row of the lot is the row at a built segment. -/
theorem smallSLot_rows_mem {cells : Tr → Cells}
    {mats : Pub → Ground → LinkH → Nat → List (Nat × String × Nat)} {Z : Pub} {G : Ground}
    {u : Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hu : u ∈ (smallSLot cells mats).rows Z G) :
    ∃ (l : ℕ) (Xl : LinkH), G.built[l]? = some Xl ∧
      u = smallBare cells (k8Par Z G Xl l, mats Z G Xl l) := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
  have e := List.mem_zipIdx_iff_getElem?.1 hy
  rw [Array.getElem?_toList] at e
  exact ⟨y.2, y.1, e, rfl⟩

/-- There is a row at each built segment. -/
theorem smallSLot_rows_of_built (cells : Tr → Cells)
    (mats : Pub → Ground → LinkH → Nat → List (Nat × String × Nat)) {Z : Pub} {G : Ground}
    {l : ℕ} {Xl : LinkH} (hX : G.built[l]? = some Xl) :
    smallBare cells (k8Par Z G Xl l, mats Z G Xl l) ∈
      (smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells mats).rows Z G := by
  refine List.mem_map.2 ⟨(Xl, l), List.mem_zipIdx_iff_getElem?.2 ?_, rfl⟩
  rw [Array.getElem?_toList]
  exact hX

/-- As many rows as built segments. -/
theorem smallSLot_rows_length (cells : Tr → Cells)
    (mats : Pub → Ground → LinkH → Nat → List (Nat × String × Nat)) (Z : Pub) (G : Ground) :
    ((smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells mats).rows Z G).length =
      G.built.size := by
  simp [smallSLot]

end Row

/-! ## 5 exact is not empty -/

section Live
variable {W₀ Rc Xi Tr X : Type}

/-- The draw whose entries are all 0, of the round's declared size. -/
def zeroDraw (p : Par) : Fmt.Drawn :=
  ⟨[], [], List.replicate (VerifiableInference.Desc.First.K8.columns p * p.tau) 0, none⟩

/-- It fits the round. -/
theorem zeroDraw_fits (p : Par) :
    drawFit (VerifiableInference.Desc.First.K8.round p) (zeroDraw p) = true := by
  have hk : (Fmt.kindOf "RNG").isSome = true := by rfl
  simp [drawFit, zeroDraw, VerifiableInference.Desc.First.K8.round, VerifiableInference.Desc.drawsMarkedNonzeroHaveNonzeroWords,
    hk]

/-- Each combination at that draw is 0. -/
theorem comb_zeroDraw (p : Par) (cell : VerifiableInference.Desc.First.K8.Honest.CellsAt)
    (n mu i u : Nat) :
    VerifiableInference.Desc.First.K8.Honest.comb p cell (List.replicate n (0 : Int)).toArray mu i u
      = 0 := by
  have he : ∀ k : Nat, (Array.replicate n (0 : Int))[k]?.getD 0 = 0 := by
    intro k
    by_cases hk : k < n
    · simp [hk]
    · simp [hk]
  have hf : ∀ (l : List Nat) (z : Int), z = 0 →
      l.foldl (fun z c => z + VerifiableInference.Desc.First.K8.Honest.entry p
        (List.replicate n (0 : Int)).toArray mu c u * cell mu i c) z = 0 := by
    intro l
    induction l with
    | nil => intro z hz; exact hz
    | cons c l ih =>
      intro z hz
      refine ih _ ?_
      simp [VerifiableInference.Desc.First.K8.Honest.entry, he, hz]
  exact hf _ 0 rfl

/-- **The second stop does not speak at that draw**, at every input: so exact's last premise can be
met at each row. -/
theorem small_stop_zero (cells : Tr → Cells) (P : Par × List (Nat × String × Nat))
    (v : Local W₀ Rc Xi Tr) (loc : List Fmt.Drawn) :
    ∀ q ∈ (smallHalf (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells P).parts,
      q.stopAt (some v) loc [zeroDraw P.1] = none := by
  intro q hq
  obtain rfl := List.mem_singleton.1 hq
  have hl : VerifiableInference.Desc.First.K8.Honest.leaves P.1 (askOfInput cells P.2 v).cell
      (zeroDraw P.1).trits.toArray = none := by
    unfold VerifiableInference.Desc.First.K8.Honest.leaves
    simp only [List.findSome?_eq_none_iff]
    intro mu _ i _ u _
    simp only [zeroDraw, comb_zeroDraw]
    rfl
  simp [Part.stopAt, Part.lift, smallPart, smallHid, List.range_succ, List.findSome?, hl]

end Live

/-! ## 6 The rows at a return of the maker -/

section Rows
variable {W₀ Rc X₀ X : Type} {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
  {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- A place of the kind stands at one of the 25 numbers. -/
theorem k8_at_number {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K8) :
    ∃ l, l < 25 ∧ b = 14 * l + (if l = 24 then 5 else 4) + 2 := by
  obtain ⟨l, hl, rfl⟩ := P1K8T.k8_places_full b p hp hk
  refine ⟨l, Nat.lt_succ_of_le hl, ?_⟩
  unfold P1K8T.ixOf
  split
  · subst_vars
    rfl
  · rfl

/-- The rows stand at different places. -/
theorem small_rows_nodup (Zq : Pub) (G : Ground) :
    (((smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id matsO).rows Zq G).map
      (·.place)).Nodup := by
  have h := AtFullSide.K12.k8_once (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) id matsO Zq G
  have e : ((smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id matsO).rows
        Zq G).map (·.place) =
      ((smallLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) id matsO).halves Zq G).map
        (·.place) := by
    simp only [smallSLot, smallLot, List.map_map]
    rfl
  rw [e]
  exact h

/-- **What the rows say at a return A of the maker**: how many · each row's half is what the search of
the prover's first chain finds at its place · every member of the kind has a row · On and bud hold
everywhere · `Good` at each row's own side. -/
abbrev SmallRowsSay (A : OnlineProverWithDescription W₀ Rc Cells X₀ X) (cF : Chain TS ProofFile.Cl) : Prop :=
    ((smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id matsO).rows
        A.Z A.G).length = 25 ∧
    (∀ u ∈ (smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id
        matsO).rows A.Z A.G,
      A.H.first.find? (fun g => g.place == u.place) = some u.half) ∧
    (∀ b ∈ cF.blocksInOrder, b.place.kind = KindName.K8 →
      ∃ u ∈ (smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id
        matsO).rows A.Z A.G, u.place = b.place) ∧
    (∀ u ∈ (smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id
        matsO).rows A.Z A.G,
      (∀ v c m f, u.On v c m f) ∧ ∀ n ds asks, u.bud n ds asks) ∧
    ∀ u ∈ (smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id
        matsO).rows A.Z A.G,
      ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
        (φ : Face (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) Inst)
        (ord : List Place) (chain firstTree : Nat) (fs : List (Fall S)),
        ∃ σ, Side.seated cF.blocksInOrder u.place u.row fs = some σ ∧
          Good pre φ σ A.B ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
            u.On u.bud

/-- **The five clauses, at a filling whose lots hold the kind's lot and no other side of the kind.** -/
theorem small_rows_fill
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G =
      (smallLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) id matsO).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K8) ∨
      M.halves A.Z A.G =
        (smallLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) id matsO).halves A.Z A.G) :
    SmallRowsSay A cF := by
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have h25 : A.G.built.size = 25 := (IM.ground_gets h.scope h.reads hZ hG).1
  have eG : ∀ {G₀ : ProofFile.Ground}, ProofFile.blankBy ProofFile.pureRoad.links A.Z = some G₀ → G₀ = A.G :=
    fun hb => Option.some.inj (hb.symm.trans hG)
  refine ⟨by rw [smallSLot_rows_length, h25], ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨l, Xl, hX, rfl⟩ := smallSLot_rows_mem hu
    exact (k8_half_any_fill id matsO hA hex ho hX).trans
      (congrArg some (smallBare_half _ _).symm)
  · intro b hb hk
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi' : cF.blocksInOrder[i]? = some cF.blocksInOrder[i] := List.getElem?_eq_getElem hi
    have hps : P5J.At.ps[i]? = some cF.blocksInOrder[i].place := by
      have e := P5J.At.places_paid h.scope h.reads h.laid
      rw [← e]
      unfold VerifiableInference.Desc.First.blockPlaces
      rw [List.getElem?_map, hi']
      rfl
    obtain ⟨l, hl, rfl⟩ := k8_at_number hps hk
    obtain ⟨G₀, Xl, blk, hb₀, hX, hf, hp, -, -⟩ := small_block_at h hl
    obtain rfl := eG hb₀
    obtain rfl : cF.blocksInOrder[14 * l + (if l = 24 then 5 else 4) + 2] = blk :=
      Option.some.inj (hi'.symm.trans hf)
    exact ⟨_, smallSLot_rows_of_built id matsO hX, hp.symm⟩
  · intro u hu
    obtain ⟨l, Xl, hX, rfl⟩ := smallSLot_rows_mem hu
    exact ⟨fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩
  · intro u hu pre φ ord chain firstTree fs
    obtain ⟨l, Xl, hX, rfl⟩ := smallSLot_rows_mem hu
    have hl : l < 25 := h25 ▸ (Array.getElem?_eq_some_iff.1 hX).1
    obtain ⟨G₀, Xl', blk, hb₀, hX', hf, hp, hs, ho'⟩ := small_block_at h hl
    obtain rfl := eG hb₀
    obtain rfl : Xl' = Xl := Option.some.inj (hX'.symm.trans hX)
    have hlen := hlen_matsOwn h hA l Xl' hX
    exact small_row_good (first_nodup h) hf id (ProofFile.k8Par A.Z A.G Xl' l, K3.matsOwn A.G.W l) hs ho' hp
      (by simp [smallFits, hlen, k8Par_lens A.Z A.G Xl' l])
      (AtFullSide.K8.k8_noneSpent (AtFullSide.K8.book_at_maker h hA) (by rw [hp])) pre φ ord chain
      firstTree fs

/-- **exact is not empty**: at each row there is a draw of the declared size at which the part does
not stop. One draw: it shuts out a part that always stops, and no more. -/
theorem small_rows_live_fill
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x) :
    ∀ u ∈ (smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id
        matsO).rows A.Z A.G, ∀ (fs : List (Fall S)) σ,
      Side.seated cF.blocksInOrder u.place u.row fs = some σ →
      ∀ (v : Local W₀ Rc Inst Cells) (loc : List Fmt.Drawn),
        ∃ ds, drawsFit σ.block.rounds ds = true ∧ rowStopAt (some v) σ.half.parts loc ds = none := by
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have h25 : A.G.built.size = 25 := (IM.ground_gets h.scope h.reads hZ hG).1
  intro u hu fs σ hσ v loc
  obtain ⟨l, Xl, hX, rfl⟩ := smallSLot_rows_mem hu
  have hl : l < 25 := h25 ▸ (Array.getElem?_eq_some_iff.1 hX).1
  obtain ⟨G₀, Xl', blk, hb₀, hX', hf, hp, hs, -⟩ := small_block_at h hl
  obtain rfl : G₀ = A.G := Option.some.inj (hb₀.symm.trans hG)
  obtain rfl : Xl' = Xl := Option.some.inj (hX'.symm.trans hX)
  have hfind : cF.blocksInOrder.find? (fun y => y.place == smallPlace (ProofFile.k8Par A.Z A.G Xl' l)) =
      some blk := by
    have e : smallPlace (ProofFile.k8Par A.Z A.G Xl' l) = blk.place := hp.symm
    rw [e]
    exact find_at _ _ blk (first_nodup h) hf
  have hσ' : Side.seated cF.blocksInOrder (smallPlace (ProofFile.k8Par A.Z A.G Xl' l))
      (smallRow id (ProofFile.k8Par A.Z A.G Xl' l, K3.matsOwn A.G.W l)) fs = some σ := hσ
  unfold Side.seated at hσ'
  rw [hfind] at hσ'
  obtain rfl := Option.some.inj hσ'
  refine ⟨[zeroDraw (ProofFile.k8Par A.Z A.G Xl' l)], ?_, ?_⟩
  · show drawsFit blk.rounds _ = true
    rw [hs.1]
    show (drawFit _ _ && drawsFit [] []) = true
    rw [zeroDraw_fits]
    rfl
  · have hq := small_stop_zero (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) id
      (ProofFile.k8Par A.Z A.G Xl' l, K3.matsOwn A.G.W l) v loc _ (List.mem_singleton.2 rfl)
    show rowStopAt (some v) (smallHalf (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) id
      (ProofFile.k8Par A.Z A.G Xl' l, K3.matsOwn A.G.W l)).parts loc _ = none
    simp only [smallHalf, rowStopAt, List.map_cons, List.map_nil]
    simpa [rowStopAt] using hq

/-- **The tie as an equation of lists.** Where the filling's lots are a list in which one lot lays the
kind's halves and the others no half of the kind, the prover's sides of the kind, in order, are the
rows' halves. -/
theorem small_first_filter (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {L₁ L₂ : List (HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X)}
    {M : HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X} (hl : P.lots = L₁ ++ M :: L₂)
    (hM : M.halves A.Z A.G =
      (smallLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) id matsO).halves A.Z A.G)
    (h₁ : ∀ N ∈ L₁, ∀ y ∈ N.halves A.Z A.G, y.place.kind ≠ KindName.K8)
    (h₂ : ∀ N ∈ L₂, ∀ y ∈ N.halves A.Z A.G, y.place.kind ≠ KindName.K8) :
    A.H.first.filter (fun g => g.place.kind == KindName.K8) =
      ((smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id matsO).rows
        A.Z A.G).map (·.half) := by
  obtain ⟨-, -, -, -, -, -, -, hfirst, -⟩ := atPure_ok hA
  have none_of : ∀ L : List (HLot (Local W₀ Rc Inst Cells) (Local W₀ Rc Inst Cells) X),
      (∀ N ∈ L, ∀ y ∈ N.halves A.Z A.G, y.place.kind ≠ KindName.K8) →
      (L.flatMap fun N => N.halves A.Z A.G).filter (fun g => g.place.kind == KindName.K8) = [] := by
    intro L hL
    refine List.filter_eq_nil_iff.2 fun y hy hk => ?_
    obtain ⟨N, hN, hyN⟩ := List.mem_flatMap.1 hy
    exact hL N hN y hyN (beq_iff_eq.1 hk)
  have e : ((smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) (Pb := Inst) id matsO).rows
        A.Z A.G).map (·.half) =
      (smallLot (W₀ := W₀) (Rc := Rc) (Xi := Inst) (X := X) id matsO).halves A.Z A.G := by
    simp only [smallSLot, smallLot, List.map_map]
    rfl
  rw [e, hfirst]
  show (P.lots.flatMap fun N => N.halves A.Z A.G).filter _ = _
  rw [hl, List.flatMap_append, List.flatMap_cons, List.filter_append, List.filter_append,
    none_of L₁ h₁, none_of L₂ h₂, hM, List.nil_append, List.append_nil]
  refine List.filter_eq_self.2 fun y hy => ?_
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
  rfl

/-- **At the wide filling**: the prover's sides of the kind are the rows' halves. -/
theorem small_first_filter_base {W₀' : Type} {I : WiderIn W₀'} {o : SecondHashFunctionArgument}
    {Sz : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A₀ : OnlineProverWithDescription W₀' IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o Sz O) = .ok A₀) :
    A₀.H.first.filter (fun g => g.place.kind == KindName.K8) =
      ((smallSLot (W₀ := W₀') (Rc := IndexCommitterCoins) (Xi := Inst) (X := Unit) (Pb := Inst) id matsO).rows
        A₀.Z A₀.G).map (·.half) := by
  have hk := FirstFill.widerKinds I o Sz O A₀.Z A₀.G
  refine small_first_filter hA (L₁ := ((widerPairs I o Sz O).dropLast).map (·.1))
    (L₂ := [closeLotAt I Sz, proxLotAt I Sz, wLotAt I o O]) (M := smallLot id matsO) rfl rfl ?_ ?_
  · intro N hN y hy e
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hN
    have hmem : q ∈ widerPairs I o Sz O := List.mem_of_mem_dropLast hq
    have hq2 : q.2 ≠ KindName.K8 := by
      simp only [widerPairs, List.dropLast, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact hq2 ((hk.all q hmem y hy).symm.trans e)
  · intro N hN y hy e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hN
    rcases hN with rfl | rfl | rfl
    · rw [closeLotAt_kinds I Sz A₀.Z A₀.G y hy] at e
      cases e
    · rw [proxLotAt_kinds I Sz A₀.Z A₀.G y hy] at e
      cases e
    · rw [AtFullSide.K12.wHalf_place I o O A₀.Z A₀.G y hy] at e
      cases e

/-- **At the wide filling**: the five clauses at the base prover. -/
theorem small_rows_at_base {W₀' : Type} {I : WiderIn W₀'} {o : SecondHashFunctionArgument}
    {Sz : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments} {A₀ : OnlineProverWithDescription W₀' IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o Sz O) = .ok A₀)
    (h : AtMgA OnBytes.secondHashFunction Z D r A₀.Z Np cF x) : SmallRowsSay A₀ cF :=
  small_rows_fill hA h (hex_base I o Sz O A₀.Z A₀.G) (ho_base I o Sz O A₀.Z A₀.G)

end Rows

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.hex_base
#print axioms ProofFile.Honest.K8.ho_base
#print axioms ProofFile.Honest.K8.first_nodup
#print axioms ProofFile.Honest.K8.small_block_at
#print axioms ProofFile.Honest.K8.small_row_good
#print axioms ProofFile.Honest.K8.smallSLot_rows_mem
#print axioms ProofFile.Honest.K8.smallSLot_rows_of_built
#print axioms ProofFile.Honest.K8.smallSLot_rows_length
#print axioms ProofFile.Honest.K8.zeroDraw_fits
#print axioms ProofFile.Honest.K8.comb_zeroDraw
#print axioms ProofFile.Honest.K8.small_stop_zero
#print axioms ProofFile.Honest.K8.small_rows_nodup
#print axioms ProofFile.Honest.K8.small_rows_fill
#print axioms ProofFile.Honest.K8.small_rows_live_fill
#print axioms ProofFile.Honest.K8.small_rows_at_base
