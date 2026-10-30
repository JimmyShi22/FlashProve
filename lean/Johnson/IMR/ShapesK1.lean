-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ShapesK1.lean: FoldFacts' FIELD "K12.msgShapes": THE DEBT ShapesOn
(Johnson/IMR/ShapesFold.lean) AT KIND K1's 52 PLACES, PAID, at the named table snAt Z Bs.G₀ placesW
(Johnson/Desc/K12/Door/SentAtPlace.lean): at every state, at every o, with no premise on scope.
Theorems, proved.

Compiled with the whole library.

CALLED, NOT TYPED: the kind's own three laws on the list of shapes: firstAtS_shapesIn,
commitAtS_shapesIn, sendAtS_shapesIn (Johnson/Desc/K1/Law/ShapesAtRecord.lean); atM4_mid, rowsB_same
(Johnson/Desc/K13/Law/); two_rounds, hear_placeW, place_356 and the case split of
Johnson/IMR/SendsK1.lean,
whose proofs these follow arm by arm.

  shapesOf_is   shapesOf (Johnson/IMR/ShapesFold.lean) and shapesIn (ShapesAtRecord.lean) are one
                term: by
    rfl. TWO NAMES FOR ONE DEFINITION: one of them may fall.
  noticesOf_one   one sending's notices' shapes are the kind's shapesOf P.
  stay_of_sameAll   two statements with the same shape, mark, sample rows and pad at every number
    (SameAll) have one list of shapes.
  shapes_firstAtS, shapes_laterAt, shapes_k1Reads, shapes_atM4   the law at the four makers.
  shapes_K1_link, shapes_K1_back   ShapeDebts' debts at K1's places inside the links (51) and at W's
    commitment (356).

OBJECT: the lots' own sub-protocols of kind K1. USER: ShapesLeft.lean. LETTERS: ft, G: free.

What is not claimed. K2's 25 places, K12's one. No soundness.
-/
import Johnson.IMR.SendsK1
import Johnson.IMR.ShapesJoin
import Johnson.Desc.K1.Law.ShapesAtRecord

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S kindsBeforeBatching backKinds)
open VerifiableInference.Desc.K12.Door (snAt)
open ProofFile (Cl)

/-- One name for one term: the list of the shapes, here and at kind K1's laws. -/
theorem shapesOf_is (st : OnBytes.Statement) :
    shapesOf st = VerifiableInference.Desc.Ground.shapesIn st := rfl

/-- One sending's notices' shapes are kind K1's "shapes of the place's notices". -/
theorem noticesOf_one (P : VerifiableInference.Desc.K1.Par) :
    noticesOf [P.sent] = VerifiableInference.Desc.K1.shapesOf P := by
  unfold noticesOf VerifiableInference.Desc.K1.shapesOf
  simp

/-- Two statements with the same shape, mark, sample rows and pad at every number have one list of
shapes. -/
theorem stay_of_sameAll {T T' : OnBytes.Statement}
    (h : VerifiableInference.Desc.K13.Law.SameAll T T') : shapesOf T' = shapesOf T := by
  apply List.ext_getElem?
  intro i
  unfold shapesOf
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
  have e := h.2 i
  unfold VerifiableInference.Desc.K13.Law.sampleOf at e
  have e' := congrArg (fun x => x.map (·.1)) e
  simpa [Option.map_map, Function.comp_def] using e'

/-- K1's first sending. -/
theorem shapes_firstAtS (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar) (ft : ℕ)
    (G : S → Prop) :
    ShapesOn ft G [(VerifiableInference.Desc.K1.firstPar q gp).sent]
      ((VerifiableInference.Desc.K1.firstSegmentOpening q gp : Block S Unit).retype : Block S Cl) := by
  intro s s' rs cols n _ hy
  obtain ⟨r₁, r₂, gs, hd⟩ := two_rounds (a := _) (c := _) rfl hy
  have hd' : (VerifiableInference.Desc.K1.firstSegmentOpening q gp : Block S Unit).decide s [r₁, r₂] gs =
      .ok s' := hd
  rw [noticesOf_one]
  exact VerifiableInference.Desc.K1.firstAtS_shapesIn q gp s s' r₁ r₂ gs hd'

/-- A later sending. -/
theorem shapes_laterAt (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : ℕ) (arrays : Option (List ℕ)) (ft : ℕ) (G : S → Prop) :
    ShapesOn ft G [(VerifiableInference.Desc.K1.parLater q gp link piece moment).sent]
      ((VerifiableInference.Desc.K1.laterAt q gp link piece moment arrays : Block S Unit).retype :
        Block S Cl) := by
  intro s s' rs cols n _ hy
  obtain ⟨r₁, r₂, gs, hd⟩ := two_rounds (a := _) (c := _) rfl hy
  have hd' : (VerifiableInference.Desc.K1.laterAt q gp link piece moment arrays :
      Block S Unit).decide s [r₁, r₂] gs = .ok s' := hd
  rw [noticesOf_one]
  exact VerifiableInference.Desc.K1.commitAtS_shapesIn _ link moment arrays s s' r₁ r₂ gs hd'

/-- The reads' place's sub-protocol: K1's later sending with the quiet sub-protocol joined behind
it. -/
theorem shapes_k1Reads (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (X : OnBytes.Model.Stages.LinkH)
    (pr : ℕ) (reads : Option (List ℕ)) (ft : ℕ) (G : S → Prop) :
    ShapesOn ft G
      [(VerifiableInference.Desc.K1.parLater G₀.first (VerifiableInference.Desc.K1.gpOf Z) l pr
        1).sent]
      ((k1Reads Z G₀ l X pr reads).retype : Block S Cl) := by
  intro s s' rs cols n _ hy
  obtain ⟨h1, gs, h2⟩ := VerifiableInference.Desc.K1.step_ok ft _ s s' rs cols n hy
  have hlen := VerifiableInference.Desc.Sound.roundsFit_len _ _ h1
  obtain ⟨u, hk, hq⟩ := VerifiableInference.Desc.Keeps.ebind_ok
    (x := (VerifiableInference.Desc.K1.laterAt G₀.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1
      reads : Block S Unit).decide s ((rs.map VerifiableInference.Desc.noDigest).take 2) _) h2
  have h2le : 2 ≤ rs.length := by
    rw [hlen]
    show 2 ≤ (_ :: _ :: _ : List Fmt.DeclaredRound).length
    simp
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, (rs.map VerifiableInference.Desc.noDigest).take 2 = [r₁, r₂] := by
    rcases rs with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at h2le
    · simp at h2le
    · exact ⟨_, _, rfl⟩
  rw [e] at hk
  have Q := (Meaning.K2.orLoud_whole (R := Meaning.K2.Quiet)
    fun b hb => Meaning.K2.readsQuietAt_quiet hb).1 u _ _ s' hq
  rw [Q.1.1, noticesOf_one]
  exact VerifiableInference.Desc.K1.commitAtS_shapesIn _ l 1 reads s u r₁ r₂ _ hk

/-- W's commitment. -/
theorem shapes_atM4 (p : VerifiableInference.Desc.K13.Where) (P' : VerifiableInference.Desc.K1.Par)
    (ft : ℕ) (G : S → Prop) :
    ShapesOn ft G [P'.sent]
      ((VerifiableInference.Desc.K13.atM4 p (VerifiableInference.Desc.K1.sendAtS P') :
        Block S Unit).retype : Block S Cl) := by
  intro s s' rs cols n _ hy
  obtain ⟨r₁, r₂, gs, hd⟩ := two_rounds (a := _) (c := _) rfl hy
  have hd' : (VerifiableInference.Desc.K13.atM4 p (VerifiableInference.Desc.K1.sendAtS P') :
      Block S Unit).decide s [r₁, r₂] gs = .ok s' := hd
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := VerifiableInference.Desc.K13.Law.atM4_mid hd'
  rw [stay_of_sameAll (VerifiableInference.Desc.K13.Law.rowsB_same h2), noticesOf_one]
  exact VerifiableInference.Desc.K1.sendAtS_shapesIn P' s s₁ r₁ r₂ g₁ h1

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K1's places inside the links, the first sending among them**: the lot's own sub-protocol at
(1, some l, i + 1, K1) pays the debt on the shapes at the named term: at every state; at every o;
no premise on scope. -/
theorem shapes_K1_link {ft : ℕ} {G : S → Prop} {l i : ℕ} (hl : l < 25)
    (hk : (kindsBeforeBatching (subAt l) (l == 0))[i]? = some KindName.K1)
    {b' : Block S Cl} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀)
    (hp : b'.place = { chain := 1, link := some l, piece := i + 1, kind := .K1 }) :
    ShapesOn ft G (snAt Z Bs.G₀ placesW (14 * l + i + 2)) b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨x, hx, rfl⟩ := lot_K1 hL hb' (by rw [hp]) (l := l) (by rw [hp])
  have hW := hear_placeW hl hk
  rcases k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, -, hn, rfl | rfl⟩
  · have e : (⟨1, some 0, 1, .K1⟩ : Place) = ⟨1, some l, i + 1, .K1⟩ := hp
    obtain ⟨rfl, rfl⟩ : l = 0 ∧ i = 0 := by
      injection e with _ e2 e3 _
      exact ⟨(Option.some.inj e2).symm, by omega⟩
    rw [VerifiableInference.Desc.K12.Door.snAt_k1_first Z Bs.G₀ placesW _ 0 hW]
    exact shapes_firstAtS _ _ ft G
  · have e : (⟨1, some l', pr, .K1⟩ : Place) = ⟨1, some l, i + 1, .K1⟩ := hp
    obtain ⟨rfl, rfl⟩ : l' = l ∧ pr = i + 1 := by
      injection e with _ e2 e3 _
      exact ⟨Option.some.inj e2, e3⟩
    have h5 : i + 1 ≤ 5 ∧ i + 1 ≠ 1 := by rcases numbers_pieces hn with ⟨a, -⟩ | ⟨a, -⟩ <;> omega
    rw [VerifiableInference.Desc.K12.Door.snAt_k1_later Z Bs.G₀ placesW _ l' (i + 1) hW h5.2,
      if_pos h5.1]
    exact shapes_k1Reads Z Bs.G₀ l' X (i + 1) reads ft G
  · have e : (⟨1, some l', pd, .K1⟩ : Place) = ⟨1, some l, i + 1, .K1⟩ := hp
    obtain ⟨rfl, rfl⟩ : l' = l ∧ pd = i + 1 := by
      injection e with _ e2 e3 _
      exact ⟨Option.some.inj e2, e3⟩
    have h5 : ¬ (i + 1 ≤ 5) ∧ i + 1 ≠ 1 := by
      rcases numbers_pieces hn with ⟨-, a⟩ | ⟨-, a⟩ <;> omega
    rw [VerifiableInference.Desc.K12.Door.snAt_k1_later Z Bs.G₀ placesW _ l' (i + 1) hW h5.2,
      if_neg h5.1]
    exact shapes_laterAt _ _ l' (i + 1) 2 digits ft G

/-- **W's commitment (356)**: the lot's own sub-protocol at (1, none, 4, K1). -/
theorem shapes_K1_back (O : Open o pol lay KL F Z Bs base c A B) {ft : ℕ} {G : S → Prop}
    {b' : Block S Cl} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀)
    (hp : b'.place = { chain := 1, link := none, piece := 4, kind := .K1 }) :
    ShapesOn ft G (snAt Z Bs.G₀ placesW 356) b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨-, w, hw, rfl⟩ := lot_M4 hL hb' (by rw [hp]) (by rw [hp])
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hw
  rw [VerifiableInference.Desc.K12.Door.snAt_w Z Bs.G₀ placesW 356 4 place_356, O.first, hm]
  exact shapes_atM4 _ _ ft G

end

end IM

#print axioms IM.stay_of_sameAll
#print axioms IM.shapes_firstAtS
#print axioms IM.shapes_laterAt
#print axioms IM.shapes_k1Reads
#print axioms IM.shapes_atM4
#print axioms IM.shapes_K1_link
#print axioms IM.shapes_K1_back
