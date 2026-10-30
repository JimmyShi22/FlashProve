-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FlatCases.lean: ALL THE SEATS IN ONE WALK: IN THE GOALS' SCOPE EVERY ONE OF THE 358
SUB-PROTOCOLS (blocks) OF THE PROOF FILE's FIRST CHAIN's FLAT LIST IS OF ONE OF TEN FORMS, EACH WITH
ITS NUMBER AND WITH WHAT ITS SEAT SAYS.
WHY. The join of e₁'s half on the verifier's state (Johnson/IMR/GrownJoin.lean: s1_of_shares) walked
the flat list inside its own proof; a second user asked for the same walk with another conclusion.
Here the walk stands once, as an inductive proposition and one theorem; whoever wants a sentence on
every sub-protocol of the chain proves it
at ten forms.
OBJECT. c.blocksInOrder[k]? = some b, c the first chain of the IOP as written in Lean (ProofFile.onlineDescription's return), opened (Johnson/IMR/SeatOpen.lean: Open). USER. Other files of Johnson/IMR/ · the join's seated form (Johnson/IMR/GrownSeated.lean).
CALLED: front_of · frame_of · first_sits · chain_hear_alone · k9_of · close_of | close_numbers · chain_back_any | back_numbers · seal_seated · flatIx_scope · places_scope | places_len.

  FlatCase Z G₀ c k b   THE TEN FORMS: front (0) · laid (14 l + 1) · first (14 l + 2) · hear (14 l + i + 2, 1 ≤ i) · batch (14 l + nAt l + 2) · behind (+ 3) · close (+ 4 + j) · cleared (+ 7) · back (353 + j) · last (357).
  flat_cases        in scope: c.blocksInOrder[k]? = some b → FlatCase Z Bs.G₀ c k b.
  rounds_of_lot     in scope: a sub-protocol of the flat list declares no round · or just the rounds of a lot's own sub-protocol at its place, whose test on the plan passes where its own does · or it is a link's batching (of the kind K9; K9's own maker's rounds) · or one of a link's closing's three (closeOf p Q's member's rounds).

What is not claimed. Nothing on what a sub-protocol decides beyond its seat's own clauses. Nothing at an o other than secondHashFunction. No soundness.
-/
import Johnson.IMR.FrontSeat
import Johnson.IMR.FirstSeats
import Johnson.IMR.PlacesScope
import Johnson.IMR.SealSeat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching closeKinds backKinds)
open ProofFile (Cl)

/-- **THE TEN FORMS.** -/
inductive FlatCase (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) : ℕ → Block S Cl → Prop
  | front (b : Block S Cl) (hr : b.rounds = [])
      (hd : ∀ s rs gs t, b.decide s rs gs = .ok t ↔ t = s) : FlatCase Z G₀ c 0 b
  | laid (l : ℕ) (hl : l < 25) (b : Block S Cl) (hr : b.rounds = [])
      (hd : ∀ s rs gs t, b.decide s rs gs = .ok t ↔
        Johnson.Desc.First.Walk.layFront l s = .ok t ∧ t.failed = none ∧
          ProofFile.sameReply s t = true) : FlatCase Z G₀ c (14 * l + 1) b
  | first (l : ℕ) (hl : l < 25) (k : KindName) (b b' : Block S Cl)
      (hk : (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k)
      (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
      (hp : b'.place = { chain := 1, link := some l, piece := 1, kind := k })
      (hj : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := k }) :
      FlatCase Z G₀ c (14 * l + 2) b
  | hear (l : ℕ) (hl : l < 25) (i : ℕ) (hi : 1 ≤ i) (k : KindName) (b b' : Block S Cl)
      (name : String) (hk : (kindsBeforeBatching (subAt l) (l == 0))[i]? = some k)
      (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
      (hp : b'.place = { chain := 1, link := some l, piece := i + 1, kind := k })
      (hla : LaidAlone ProofFile.sameReply b b' name
        { chain := 1, link := some l, piece := i + 1, kind := k }) :
      FlatCase Z G₀ c (14 * l + i + 2) b
  | batch (l : ℕ) (hl : l < 25) (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where)
      (e1 : c.links[l]? = some Lk) (hp : k9At Z l = some p)
      (hal : ∀ g, LaidAlone ProofFile.sameReply (Lk.batch g)
        (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p g) (Lk.batch g).name
        (a9Of l (subAt l))) :
      FlatCase Z G₀ c (14 * l + nAt l + 2)
        (Lk.batch (VerifiableInference.Desc.claimsInBy Lk.each Lk.hear Lk.order))
  | behind (l : ℕ) (hl : l < 25) (Lk : Link S Cl) (b : Block S Cl) (e1 : c.links[l]? = some Lk)
      (hr : b.rounds = []) (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) :
      FlatCase Z G₀ c (14 * l + nAt l + 3) b
  | close (l : ℕ) (hl : l < 25) (p : VerifiableInference.Desc.K9.Where)
      (Q : VerifiableInference.Desc.First.Close.Par) (j : ℕ) (k : KindName) (b : Block S Cl)
      (x : Block S Unit) (hp : k9At Z l = some p)
      (hQ : ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q) (hk : closeKinds[j]? = some k)
      (ex : (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x)
      (hla : LaidAlone ProofFile.sameReply b x.retype b.name (cAt l (subAt l) j k)) :
      FlatCase Z G₀ c (14 * l + nAt l + 4 + j) b
  | cleared (l : ℕ) (hl : l < 25) (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
      (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (b : Block S Cl)
      (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
      (hf : fs[l]? = some f) (hr : b.rounds = [])
      (hd : ∀ s rs gs t, b.decide s rs gs = .ok t ↔
        f.clear s = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true) :
      FlatCase Z G₀ c (14 * l + nAt l + 7) b
  | back (j : ℕ) (k : KindName) (b b' : Block S Cl) (name : String)
      (hk : (backKinds true)[j]? = some k) (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
      (hp : b'.place = { chain := 1, link := none, piece := j + 1, kind := k })
      (hla : LaidAlone ProofFile.sameReply b b' name
        { chain := 1, link := none, piece := j + 1, kind := k }) :
      FlatCase Z G₀ c (353 + j) { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }
  | last (lot : ((VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true
        (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks :
        Block S Unit).retype : Block S Cl) ∈ (VerifiableInference.Desc.K13.lotEnd Z).blocks G₀)
      (hla : LaidAlone ProofFile.sameReply c.last
        ((VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true
          (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks :
          Block S Unit).retype : Block S Cl) c.last.name
        { chain := 1, link := none, piece := 5, kind := .frame }) :
      FlatCase Z G₀ c 357 { c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter }

/-- No sub-protocol in front of a batching is of the kind K9 or K10. -/
theorem hear_plain {sub : ModelPart} {f : Bool} {i : ℕ} {k : KindName}
    (h : (kindsBeforeBatching sub f)[i]? = some k) : k ≠ KindName.K9 ∧ k ≠ KindName.K10 := by
  have hm := List.mem_of_getElem? h
  constructor <;> rintro rfl <;> revert hm <;> cases sub <;> cases f <;> decide

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **ALL THE SEATS IN ONE WALK.** -/
theorem flat_cases (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ k b, c.blocksInOrder[k]? = some b → FlatCase Z Bs.G₀ c k b := by
  intro k b hb
  have hlen : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]
  have hk : k < 358 := hlen ▸ (List.getElem?_eq_some_iff.1 hb).1
  have hcase : k = 0 ∨ (∃ l j, l < 25 ∧ j < nAt l + 7 ∧ k = 14 * l + 1 + j) ∨
      (∃ j, j < 4 ∧ k = 353 + j) ∨ k = 357 := by
    by_cases h0 : k = 0
    · exact Or.inl h0
    by_cases h1 : k ≤ 336
    · refine Or.inr (Or.inl ⟨(k - 1) / 14, (k - 1) % 14, by omega, ?_, by omega⟩)
      unfold nAt
      rw [if_neg (by omega)]
      omega
    by_cases h2 : k ≤ 352
    · exact Or.inr (Or.inl ⟨24, k - 337, by omega, by unfold nAt; rw [if_pos rfl]; omega, by omega⟩)
    by_cases h3 : k ≤ 356
    · exact Or.inr (Or.inr (Or.inl ⟨k - 353, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (by omega)))
  rcases hcase with rfl | ⟨l, j, hl, hj, rfl⟩ | ⟨j, hj, rfl⟩ | rfl
  · obtain ⟨b0, e0, hr, -, -, -, hd⟩ := front_of O
    obtain rfl : b0 = b := Option.some.inj (e0.symm.trans hb)
    exact .front b0 hr hd
  · obtain ⟨-, fs, hfs, hall⟩ := frame_of hS hR O
    obtain ⟨Lk, f, bL, bB, bC, e1, hn, hf, -, hlayf, hLay, hClear, iL, rL, dL, iB, rB, dB, iC, rC,
      dC⟩ := hall l hl
    have hn' : Lk.hear.length = nAt l := hn
    have hsub := subs_scope hS hR O l hl
    have hj' : j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ nAt l) ∨ j = nAt l + 1 ∨ j = nAt l + 2 ∨
        (∃ q, q < 3 ∧ j = nAt l + 3 + q) ∨ j = nAt l + 6 := by
      by_cases a : j ≤ nAt l + 2
      · omega
      · by_cases a2 : j ≤ nAt l + 5
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j - (nAt l + 3), by omega, by omega⟩)))))
        · omega
    rcases hj' with rfl | rfl | ⟨j2, jn⟩ | rfl | rfl | ⟨q, hq, rfl⟩ | rfl
    · obtain rfl : bL = b := Option.some.inj (iL.symm.trans hb)
      refine .laid l hl bL rL fun s rs gs t => ?_
      rw [dL, hLay s t, hlayf]
    · obtain ⟨k0, hk0⟩ : ∃ k0, (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k0 := by
        cases (subAt l) <;> cases (l == 0) <;> exact ⟨_, rfl⟩
      obtain ⟨Lk', b0, e1', e2, L, hL, b', hb', ep, hjn⟩ := first_sits hS hR O l hl k0 hk0
      have hix := hear_at_flat e1' e2
      rw [flatIx_scope hS hR O (by omega) 0] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      exact .first l hl k0 b0 b' hk0 ⟨L, hL, hb'⟩ ep hjn
    · obtain ⟨Lk9, -, -, -, e9, -, -, -, -, -, -, -, -, -, -, -, -, hlen9, -⟩ := (k9_of hS hR O).2 l hl
      obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
      obtain ⟨k1, hk1⟩ : ∃ k1, (kindsBeforeBatching (subAt l) (l == 0))[j - 1]? = some k1 :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hlen9, hn']; omega)⟩
      obtain ⟨h9, h10⟩ := hear_plain hk1
      have hn9 : nAt l ≤ 9 := by unfold nAt; split <;> omega
      obtain ⟨Lk', b0, e1', e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
        chain_hear_alone O.made O.places O.chain l (subAt l) hsub (j - 1) k1 hk1 h9 h10
          ⟨by omega, by omega⟩
      have hix := hear_at_flat e1' e2
      rw [flatIx_scope hS hR O (by omega) (j - 1),
        show 14 * l + (j - 1) + 2 = 14 * l + 1 + j by omega] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      rw [show 14 * l + 1 + j = 14 * l + (j - 1) + 2 by omega]
      exact .hear l hl (j - 1) (by omega) k1 b0 b' sp.name hk1 ⟨L, hL, hb'⟩ ep hla
    · obtain ⟨Lk9, p, -, -, e9, hp, -, -, -, -, hal, i9, -⟩ := (k9_of hS hR O).2 l hl
      obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
      rw [hn', show 14 * l + nAt l + 2 = 14 * l + 1 + (nAt l + 1) by omega] at i9
      obtain rfl := Option.some.inj (i9.symm.trans hb)
      rw [show 14 * l + 1 + (nAt l + 1) = 14 * l + nAt l + 2 by omega]
      exact .batch l hl Lk p e1 hp hal
    · rw [hn', show 14 * l + nAt l + 3 = 14 * l + 1 + (nAt l + 2) by omega] at iB
      obtain rfl : bB = b := Option.some.inj (iB.symm.trans hb)
      rw [show 14 * l + 1 + (nAt l + 2) = 14 * l + nAt l + 3 by omega]
      exact .behind l hl Lk bB e1 rB dB
    · obtain ⟨LkC, p, Q, eC, hp, hQ, hcl⟩ := close_of hS hR O l hl
      obtain rfl : Lk = LkC := Option.some.inj (e1.symm.trans eC)
      obtain ⟨kq, hkq⟩ : ∃ kq, closeKinds[q]? = some kq :=
        ⟨_, List.getElem?_eq_getElem (by show q < 3; exact hq)⟩
      obtain ⟨b0, x, e2, ex, hla⟩ := hcl q kq hkq
      have hix := close_numbers hS hR O hl e1 e2
      rw [hn', show 14 * l + nAt l + 4 + q = 14 * l + 1 + (nAt l + 3 + q) by omega] at hix
      obtain rfl : b0 = b := Option.some.inj (hix.symm.trans hb)
      rw [show 14 * l + 1 + (nAt l + 3 + q) = 14 * l + nAt l + 4 + q by omega]
      exact .close l hl p Q q kq b0 x hp hQ hkq ex hla
    · rw [hn', show 14 * l + nAt l + 7 = 14 * l + 1 + (nAt l + 6) by omega] at iC
      obtain rfl : bC = b := Option.some.inj (iC.symm.trans hb)
      rw [show 14 * l + 1 + (nAt l + 6) = 14 * l + nAt l + 7 by omega]
      refine .cleared l hl fs f bC hfs hf rC fun s rs gs t => ?_
      rw [dC, hClear s t]
  · obtain ⟨-, -, -, hallB⟩ := base_made O.made
    obtain ⟨several, hsev, -, hbk⟩ := chain_back_any hallB (makers_K9 Z Bs.G₀) O.places O.chain
    obtain rfl : several = true := hsev.2 (base_has_K13 O)
    obtain ⟨kj, hkj⟩ : ∃ kj, (backKinds true)[j]? = some kj :=
      ⟨_, List.getElem?_eq_getElem (by show j < 4; exact hj)⟩
    have hk9 : kj ≠ KindName.K9 := by
      have hm := List.mem_of_getElem? hkj
      rintro rfl
      revert hm
      decide
    obtain ⟨b0, e0, sp, -, L, hL, b', hb', -, ep, hla⟩ := hbk j kj hkj hk9
    have hix := (back_numbers hS hR O).1 j b0 e0
    obtain rfl := Option.some.inj (hix.symm.trans hb)
    exact .back j kj b0 b' sp.name hkj ⟨L, hL, hb'⟩ ep hla
  · obtain ⟨b', hm, rfl, hla⟩ := seal_seated O
    have hix := (back_numbers hS hR O).2
    obtain rfl := Option.some.inj (hix.symm.trans hb)
    exact .last hm hla

/-- **Four arms: a sub-protocol declares no round | a lot's block's | K9's batch's | a closeOf
member's.** -/
theorem rounds_of_lot (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) :
    b.rounds = [] ∨
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b' ∈ L.blocks Bs.G₀, b'.place = b.place ∧
        b.rounds = b'.rounds ∧ (b.planOk = true → b'.planOk = true)) ∨
      (∃ l p g, k9At Z l = some p ∧ b.place.kind = KindName.K9 ∧
        b.rounds = (VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p g :
          Block S Cl).rounds) ∨
      (∃ (l : ℕ) (p : VerifiableInference.Desc.K9.Where) (Q : VerifiableInference.Desc.First.Close.Par)
        (j : ℕ) (k' : KindName) (x : Block S Unit), k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
        closeKinds[j]? = some k' ∧ b.place.kind = k' ∧
        (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x ∧
        b.rounds = x.rounds) := by
  cases flat_cases hS hR O k b hb with
  | front b hr hd => exact Or.inl hr
  | laid l hl b hr hd => exact Or.inl hr
  | first l hl k0 b b' hk lot hp hj =>
    obtain ⟨L, hL, hb'⟩ := lot
    obtain ⟨fs, f, -, -, e⟩ := hj.planOk
    have hr := hj.rounds
    obtain ⟨fs', f', -, -, eb⟩ := hj
    refine Or.inr (Or.inl ⟨L, hL, b', hb', ?_, hr, fun h => ?_⟩)
    · rw [hp, eb]
      rfl
    · rw [e] at h
      exact (Bool.and_eq_true_iff.1 h).1
  | hear l hl i hi k0 b b' name hk lot hp hla =>
    obtain ⟨L, hL, hb'⟩ := lot
    exact Or.inr (Or.inl ⟨L, hL, b', hb', by rw [hp, alone_place hla], alone_rounds hla,
      fun h => by rw [← alone_planOk hla]; exact h⟩)
  | behind l hl Lk b e1 hr hd => exact Or.inl hr
  | cleared l hl fs f b hfs hf hr hd => exact Or.inl hr
  | batch l hl Lk p e1 hp hal =>
    exact Or.inr (Or.inr (Or.inl ⟨l, p, _, hp, by rw [alone_place (hal _)], alone_rounds (hal _)⟩))
  | close l hl p Q j k0 b x hp hQ hk ex hla =>
    exact Or.inr (Or.inr (Or.inr ⟨l, p, Q, j, k0, x, hp, hQ, hk, by rw [alone_place hla], ex,
      alone_rounds hla⟩))
  | back j k0 b b' name hk lot hp hla =>
    obtain ⟨L, hL, hb'⟩ := lot
    refine Or.inr (Or.inl ⟨L, hL, b', hb', ?_, ?_, fun h => ?_⟩)
    · rw [hp]
      exact (alone_place hla).symm
    · show b.rounds = b'.rounds
      exact alone_rounds hla
    · rw [← alone_planOk hla]
      exact (Bool.and_eq_true_iff.1 h).1
  | last lot hla =>
    refine Or.inr (Or.inl ⟨VerifiableInference.Desc.K13.lotEnd Z, ?_, _, lot, ?_, ?_, fun h => ?_⟩)
    · unfold ProofFile.onlineFirstChainBlockTables
      simp
    · exact (alone_place hla).symm ▸ rfl
    · show c.last.rounds = _
      exact alone_rounds hla
    · rw [← alone_planOk hla]
      exact (Bool.and_eq_true_iff.1 h).1

end

end IM

#print axioms IM.flat_cases
#print axioms IM.rounds_of_lot
