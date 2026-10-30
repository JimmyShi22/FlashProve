-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ShapesK2.lean: FoldFacts' FIELD "K12.msgShapes": THE DEBT ShapesOn
(Johnson/IMR/ShapesFold.lean) AT KIND K2's 25 PLACES, PAID UNDER THE THREE FENCES K2Fences
(Johnson/IMR/SendsK2.lean),
at the named table snAt Z G placesW. Theorems, proved.

Compiled with the whole library.

CALLED, NOT TYPED: the kind's own laws, general in a relation that the eight quiet functions of the
ground keep: Still, firstFront_still, sendP_still, switchBehind_still, firstBehind_still, and
stands, link_inv, head_inv, finish_inv, switchE_inv, sendByL8_iff, sendOpen_iff
(Johnson/Top/H0/Tw/K2C/); coreStill_shapes, recvP_shapesIn
(Johnson/Desc/K1/Law/ShapesAtRecord.lean); lot_K2, k2_mem (Johnson/IMR/K2Seat.lean); the case split
of
Johnson/IMR/SendsK2.lean, whose proofs these follow arm by arm.

  yes_shapes   THE LAW AT THE SWITCH's DECISION: an accepting appends the shapes of what the front
    that it takes off the state announces, and turns none: the proof of that kind's yes_size
    (K2C/StillKeeps.lean) at the relation "the same list of shapes".
  k2_yes_shapes   under the fence's first clause at the state in front: the shapes of the plan's own
    messages are appended.
  headOpenQ_shapes, finishFrontQ_shapes, finishBehindQ_shapes   the quiet steps around the switch
    turn no shape.
  shapes_K2_link, shapes_K2_finish   the lot's own sub-protocol at (1, some l, pc, K2) and at (1,
    none, 1, K2): ShapesOn at the states of Gd, at snAt.
  shapeDebts_fenced   in the goals' scope, at the second hash function: K2Fences and ONE debt,
    ShapesOn at the proximity test (354), give ShapeDebts (Johnson/IMR/ShapesJoin.lean).

OBJECT: the lots' own sub-protocols of kind K2. LETTERS: ft, Gd, s₀: free.

What is not claimed. K2Fences. The debt at 354. NO MEMBER. No soundness.
-/
import Johnson.IMR.SendsK2
import Johnson.IMR.ShapesLeft

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront finishFront
  firstBehind)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn Grows)
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open VerifiableInference.Desc.First.K2 (P2 FrontOf Still decideWith)
open VerifiableInference.Desc.Ground (shapesIn coreStill_shapes)
open VerifiableInference.Desc.K1 (recvP_shapesIn)
open VerifiableInference.Desc.K12.Door (snAt)
open ProofFile (Cl)

/-- The same list of shapes. -/
abbrev SameShapes (T T' : Statement) : Prop := shapesIn T' = shapesIn T

/-- **THE LAW AT THE SWITCH's DECISION, ON THE SHAPES**: an accepting appends the shapes of what the
front that it takes off the state announces, and turns none. -/
theorem yes_shapes {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ x : _root_.Tw.K2.Front, FrontOf p s x ∧
      shapesIn s'.st = shapesIn s.st ++ (switchNotices x.T x.others).toList.map (·.shape) := by
  have H : Still SameShapes := coreStill_shapes
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : SwOut} {roots : Nat},
      _root_.Tw.K2.switchE switchBehind (VerifiableInference.Desc.First.K2.par9 p) sendByL8
        ⟨s.st, s.book, s.roots, f, [], s.noneWaits⟩ x r₁ r₂
        (VerifiableInference.Desc.First.K2.flat p gs) = .ok (w, roots) →
      shapesIn w.st = shapesIn x.st ++ (switchNotices x.T x.others).toList.map (·.shape) := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := VerifiableInference.Desc.First.K2.switchE_inv hw
    obtain ⟨ids, took, d', hs, rfl⟩ :=
      (VerifiableInference.Desc.First.K2.sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
    obtain ⟨_, _, sd, an, hx⟩ :=
      (VerifiableInference.Desc.First.K2.sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
    obtain ⟨d₁, h1, q1⟩ := VerifiableInference.Desc.First.K2.sendP_still H hx
    have q2 : SameShapes d'.st w.st :=
      VerifiableInference.Desc.First.K2.switchBehind_still H k.hBehind
    exact q2.trans (q1.trans (recvP_shapesIn _ _ _ _ _ h1))
  rcases (VerifiableInference.Desc.First.K2.stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ :=
      VerifiableInference.Desc.First.K2.link_inv hp h
    have a2 := key k.hSwitch
    have a0 : SameShapes s.st x.st := VerifiableInference.Desc.First.K2.firstFront_still H k.hFront
    refine ⟨x, Or.inl ⟨hp, k.hFront⟩, ?_⟩
    rw [k.hOut]
    have a3 : SameShapes w.st S' := VerifiableInference.Desc.First.K2.firstBehind_still H k.hBehind
    show shapesIn S' = _
    rw [a3, a2, a0]
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := VerifiableInference.Desc.First.K2.head_inv hp h
    have a2 := key k.hSwitch
    refine ⟨_, Or.inr (Or.inl ⟨hp, a, G, k.hHere, k.hGroup, rfl⟩), ?_⟩
    rw [k.hOut]
    exact a2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := VerifiableInference.Desc.First.K2.finish_inv hp h
    have a2 := key k.hSwitch
    refine ⟨_, Or.inr (Or.inr ⟨hp, a, G, k.hHere, k.hLaid, rfl⟩), ?_⟩
    rw [k.hOut]
    exact a2

theorem noticesOf_single (sent : Array OracleNotice) :
    noticesOf [sent] = sent.toList.map (·.shape) := by
  unfold noticesOf
  simp

/-- … under the fence's first clause at the state in front. -/
theorem k2_yes_shapes {p : P2} {sent : Array OracleNotice} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : decideWith sendByL8 p s rs gs = .ok s')
    (hF : ∀ x, FrontOf p s x → switchNotices x.T x.others = sent) :
    shapesOf s'.st = shapesOf s.st ++ noticesOf [sent] := by
  obtain ⟨x, hx, e⟩ := yes_shapes h
  rw [hF x hx] at e
  rw [noticesOf_single]
  exact e

theorem headOpenQ_shapes {HP : VerifiableInference.Desc.First.K2.HeadPar} {s s' : S}
    (h : VerifiableInference.Desc.First.K2.headOpenQ HP s = .ok s') :
    shapesOf s'.st = shapesOf s.st :=
  stay_of_grows (VerifiableInference.Desc.First.K2.headOpenQ_keeps
    VerifiableInference.Desc.Ground.groundKeeps_grows h)
    (VerifiableInference.Desc.First.K2.headOpenQ_size h)

theorem finishFrontQ_shapes {s s' : S}
    (h : VerifiableInference.Desc.First.K2.finishFrontQ s = .ok s') :
    shapesOf s'.st = shapesOf s.st :=
  stay_of_grows (VerifiableInference.Desc.First.K2.finishFrontQ_keeps
    VerifiableInference.Desc.Ground.groundKeeps_grows h)
    (VerifiableInference.Desc.First.K2.finishFrontQ_size h)

theorem finishBehindQ_shapes {s s' : S}
    (h : VerifiableInference.Desc.First.K2.finishBehindQ s = .ok s') :
    shapesOf s'.st = shapesOf s.st := by
  rw [VerifiableInference.Desc.First.K2.finishBehindQ_st h]

/-- **K2's lot's own sub-protocol at a place inside a link.** -/
theorem shapes_K2_link {ft : ℕ} {Z : ProofFile.Pub} {G : ProofFile.Ground} {Gd : S → Prop} {l pc j : ℕ}
    {b' : Block S Cl} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G)
    (hp : b'.place = { chain := 1, link := some l, piece := pc, kind := .K2 })
    (hW : placesW[j]? = some { chain := 1, link := some l, piece := pc, kind := .K2 })
    (hF : ∀ s, Gd s → ∀ (Pp : P1K2.Prep) (n : P1K2.Nums) (a : Place) (nm : String)
      (st : VerifiableInference.Desc.First.K2.At), P1K2.prepOf Z G = some Pp →
      P1K2.numsAt Pp (some l) = some n → st ≠ .finish →
      ∀ x, FrontOf (k2P Z a nm st n) s x → switchNotices x.T x.others = n.sent) :
    ShapesOn ft Gd (snAt Z G placesW j) b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨x, hx, rfl⟩ := lot_K2 hL hb' (by rw [hp])
  have hp' : x.place = { chain := 1, link := some l, piece := pc, kind := .K2 } := hp
  have hK := k2_mem hx
  rw [hp'] at hK
  intro s s' rs cols n hg hy
  obtain ⟨-, gs, hd⟩ := VerifiableInference.Desc.K1.step_ok ft _ s s' rs cols n hy
  have hd' : x.decide s (rs.map VerifiableInference.Desc.noDigest) gs = .ok s' := hd
  rcases hK with ⟨-, hm⟩ | ⟨Pp, nn, hP, hn, harm⟩
  · obtain ⟨e, he⟩ := hm s (rs.map VerifiableInference.Desc.noDigest) gs
    rw [he] at hd'
    cases hd'
  · have hn' : P1K2.numsAt Pp (some l) = some nn := hn
    have esn : snAt Z G placesW j = [nn.sent] := by
      rw [VerifiableInference.Desc.K12.Door.snAt_k2 Z G placesW j pc (some l) hW, hP]
      show ((P1K2.numsAt Pp (some l)).map (·.sent)).toList = _
      rw [hn']
      rfl
    rw [esn]
    rcases harm with ⟨h0, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
    · cases h0
    · rw [ex] at hd'
      obtain ⟨m, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok hd'
      rw [headOpenQ_shapes h2]
      exact k2_yes_shapes h1 (hF s hg Pp nn _ _ .head hP hn' (by decide))
    · rw [ex] at hd'
      exact k2_yes_shapes hd' (hF s hg Pp nn _ _ .link hP hn' (by decide))

/-- **K2's finish (353).** -/
theorem shapes_K2_finish {ft : ℕ} {Z : ProofFile.Pub} {G : ProofFile.Ground} {Gd : S → Prop}
    {b' : Block S Cl} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G)
    (hp : b'.place = { chain := 1, link := none, piece := 1, kind := .K2 })
    (hF : ∀ s, Gd s → ∀ (Pp : P1K2.Prep) (n : P1K2.Nums) (a : Place) (nm : String) (m : S),
      P1K2.prepOf Z G = some Pp → P1K2.numsAt Pp none = some n →
      VerifiableInference.Desc.First.K2.finishFrontQ s = .ok m →
      ∀ x, FrontOf (k2P Z a nm .finish n) m x → switchNotices x.T x.others = n.sent) :
    ShapesOn ft Gd (snAt Z G placesW 353) b' := by
  obtain ⟨L, hL, hb'⟩ := lot
  obtain ⟨x, hx, rfl⟩ := lot_K2 hL hb' (by rw [hp])
  have hp' : x.place = { chain := 1, link := none, piece := 1, kind := .K2 } := hp
  have hK := k2_mem hx
  rw [hp'] at hK
  intro s s' rs cols n hg hy
  obtain ⟨-, gs, hd⟩ := VerifiableInference.Desc.K1.step_ok ft _ s s' rs cols n hy
  have hd' : x.decide s (rs.map VerifiableInference.Desc.noDigest) gs = .ok s' := hd
  rcases hK with ⟨-, hm⟩ | ⟨Pp, nn, hP, hn, harm⟩
  · obtain ⟨e, he⟩ := hm s (rs.map VerifiableInference.Desc.noDigest) gs
    rw [he] at hd'
    cases hd'
  · have hn' : P1K2.numsAt Pp none = some nn := hn
    have esn : snAt Z G placesW 353 = [nn.sent] := by
      rw [VerifiableInference.Desc.K12.Door.snAt_k2 Z G placesW 353 1 none place_353, hP]
      show ((P1K2.numsAt Pp none).map (·.sent)).toList = _
      rw [hn']
      rfl
    rw [esn]
    rcases harm with ⟨-, ex⟩ | ⟨l', HP, h0, -, -⟩ | ⟨l', h0, -⟩
    · rw [ex] at hd'
      obtain ⟨m₂, h12, h3⟩ := VerifiableInference.Desc.Keeps.ebind_ok hd'
      obtain ⟨m₁, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok h12
      rw [finishBehindQ_shapes h3, ← finishFrontQ_shapes h1]
      exact k2_yes_shapes h2 (hF s hg Pp nn _ _ m₁ hP hn' h1)
    · cases h0
    · cases h0

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **WHAT IS LEFT FOR THE SHAPES, WITH K2's 25 PAID UNDER THE THREE FENCES: ONE DEBT, AT 354.** -/
theorem shapeDebts_fenced (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {s₀ : S}
    (K : K2Fences ft Z Bs.G₀ c s₀)
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ 354) (snAt Z Bs.G₀ placesW 354) b') :
    ShapeDebts ft (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀ := by
  refine shapeDebts_left hS hR O ?_ ?_ ?_ k12
  · intro l h1 h24 b' lot hp
    have hk : (kindsBeforeBatching (subAt l) (l == 0))[0]? = some KindName.K2 := by
      rw [first_kind l h24, if_neg (by omega)]
    exact shapes_K2_link lot hp (hear_placeW (i := 0) (by omega) hk)
      (fun s hg => K.link l (by omega) s hg)
  · intro b' lot hp
    have hk : (kindsBeforeBatching (subAt 24) (24 == 0))[1]? = some KindName.K2 := by decide
    exact shapes_K2_link lot hp (hear_placeW (l := 24) (i := 1) (by omega) hk)
      (fun s hg => K.head s hg)
  · intro b' lot hp
    exact shapes_K2_finish lot hp (fun s hg => K.finish s hg)

end

end IM

#print axioms IM.yes_shapes
#print axioms IM.k2_yes_shapes
#print axioms IM.shapes_K2_link
#print axioms IM.shapes_K2_finish
#print axioms IM.shapeDebts_fenced
