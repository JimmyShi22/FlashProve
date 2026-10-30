-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ShapesJoin.lean: FoldFacts' FIELD "K12.msgShapes", IN THE GOALS' SCOPE, AT THE
SECOND HASH FUNCTION: the debt ShapesOn at all 358 numbers of the first chain, from the debts on the
book (SendDebts, Johnson/IMR/SendsJoin.lean) and four that stay for the shapes; and the field's own
sentence at
the proof file's own first state and the planner's own list. Theorems, proved.

Compiled with the whole library.

  ShapeDebts ft sn Z G₀ c s₀   WHAT STAYS FOR THE SHAPES: first, hear, back: SendDebts' three fields
    on the sub-protocols of the kinds that send (K1, K2, K12), with ShapesOn in SendsOn's place;
    grows: at every number whose kind does not send every accepting decision lets the statement
    grow.
  ShapesOn.under, shapes_first_on   the two rules for a payer: a seated sub-protocol's debt is its
    lot's own's; at a link's first place the frame's "opened" turns no shape.
  shapes_scope   SendDebts, ShapeDebts, and the first state has the code table and is in step:
    ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ j) (sn j) at every c.blocksInOrder[j]. At the 280 numbers whose kind
    does not send: by shapes_of_sends (Johnson/IMR/ShapesCalm.lean) off sends_scope: whatever pays
      the book's
    debt there pays this one. At the 78 that send: by the case split flat_cases.
  shapes_start   THE TOP: at the table snAt Z Bs.G₀ placesW
    (Johnson/Desc/K12/Door/SentAtPlace.lean), under the test sendsAreB at 358, from ProofFile.startS Z p
    without a mark: behind the first k sub-protocols, k ≤ 358: atFirstShapes (msgsOfChain
    Z.made.proof.1) = true.

OBJECT: foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out.
LETTERS: ft, p, k, rs, cols: free.

What is not claimed. Any field of SendDebts or ShapeDebts. That the test accepts (it has been
evaluated at three sets of public files: it accepted). NO MEMBER: that the debts can be met together
is not shown. No soundness.
-/
import Johnson.IMR.SendsJoin
import Johnson.IMR.ShapesCalm
import Johnson.IMR.ShapesSide

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks Grows)
open VerifiableInference.Desc.First (S kindsBeforeBatching closeKinds backKinds)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB msgsOfChain atFirstShapes)
open ProofFile (Cl)

/-- **WHAT STAYS FOR THE SHAPES**, beside the debts on the book. -/
structure ShapeDebts (ft : ℕ) (sn : ℕ → List (Array OracleNotice)) (Z : ProofFile.Pub)
    (G₀ : ProofFile.Ground) (c : Chain S Cl) (s₀ : S) : Prop where
  first : ∀ l < 25, ∀ (k : KindName) (b' : Block S Cl),
    (kindsBeforeBatching (subAt l) (l == 0))[0]? = some k → senderKind k = true →
    (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := some l, piece := 1, kind := k } →
    ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ (14 * l + 2)) (sn (14 * l + 2)) b'
  hear : ∀ l < 25, ∀ (i : ℕ) (k : KindName) (b' : Block S Cl), 1 ≤ i →
    (kindsBeforeBatching (subAt l) (l == 0))[i]? = some k → senderKind k = true →
    (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } →
    ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ (14 * l + i + 2)) (sn (14 * l + i + 2)) b'
  back : ∀ (j : ℕ) (k : KindName) (b' : Block S Cl), (backKinds true)[j]? = some k →
    senderKind k = true → (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
    b'.place = { chain := 1, link := none, piece := j + 1, kind := k } →
    ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ (353 + j)) (sn (353 + j)) b'
  grows : ∀ (j : ℕ) (b : Block S Cl), c.blocksInOrder[j]? = some b → senderKind b.place.kind = false →
    ∀ s rs gs s', b.decide s rs gs = .ok s' → Grows s.st s'.st

/-- The debt of a seated sub-protocol is its lot's own's: at the states of G. -/
theorem ShapesOn.under {ft : ℕ} {G : S → Prop} {snd : List (Array OracleNotice)}
    {b b' : Block S Cl} (h : ShapesOn ft G snd b') (hU : b.UnderR b') : ShapesOn ft G snd b :=
  fun s s' rs cols n hg hy => h s s' rs cols n hg (VerifiableInference.Desc.step_under hU hy)

/-- At a link's first place, two stages: the frame's "opened" turns no shape. -/
theorem shapes_first_on {ft : ℕ} {G : S → Prop} {snd : List (Array OracleNotice)} {Z : ProofFile.Pub}
    {l : ℕ} {b b' : Block S Cl} {a : Place} (hj : Joined Z l b b' a)
    (h : ShapesOn ft G snd b') : ShapesOn ft G snd b := by
  intro s s' rs cols n hg hy
  obtain ⟨fs, f, m, hfs, hf, h1, -, h3, -, -⟩ := hj.step hy
  have hm := List.mem_of_getElem? hf
  obtain ⟨-, k2, -⟩ := (frames_calm hfs hm).2.1 m s' h3
  have g : Grows m.st s'.st := (Meaning.K2.framesOf_grows hfs f hm).2.1 m s' h3
  rw [stay_of_grows g k2]
  exact h s m rs cols n hg h1

theorem joined_spot {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place}
    (h : Joined Z l b b' a) : b.place = a := by
  obtain ⟨fs, f, -, -, e⟩ := h
  rw [e]
  rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN SCOPE: THE DEBT ON THE SHAPES AT EVERY NUMBER**, from the debts on the book and what stays
for the shapes. -/
theorem shapes_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {codes : Codes}
    {sn : ℕ → List (Array OracleNotice)} {s₀ : S} (D : SendDebts ft codes sn Z Bs.G₀ c s₀)
    (E : ShapeDebts ft sn Z Bs.G₀ c s₀) (hc : s₀.st.codes = codes) (hi : InStep s₀) :
    ∀ j b, c.blocksInOrder[j]? = some b → ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ j) (sn j) b := by
  intro j b hb
  have hkind : kindW j = some b.place.kind := by
    unfold kindW
    rw [place_at hS hR O hb]
    rfl
  have hall := sends_scope hS hR O D
  by_cases hs : senderKind b.place.kind = true
  · cases flat_cases hS hR O j b hb with
    | front b hr hd =>
      rw [kinds_ends.1] at hkind
      rw [← Option.some.inj hkind] at hs
      exact absurd hs (by decide)
    | laid l hl b hr hd =>
      rw [(kinds_at hl).1] at hkind
      rw [← Option.some.inj hkind] at hs
      exact absurd hs (by decide)
    | first l hl k0 b b' hk lot hp hj =>
      rw [joined_spot hj] at hs
      exact shapes_first_on hj (E.first l hl k0 b' hk hs lot hp)
    | hear l hl i hi k0 b b' name hk lot hp hla =>
      rw [alone_place hla] at hs
      exact (E.hear l hl i k0 b' hi hk hs lot hp).under (alone_underR hla)
    | batch l hl Lk p e1 hp hal =>
      rw [(kinds_at hl).2.1] at hkind
      rw [← Option.some.inj hkind] at hs
      exact absurd hs (by decide)
    | behind l hl Lk b e1 hr hd =>
      rw [(kinds_at hl).2.2.1] at hkind
      rw [← Option.some.inj hkind] at hs
      exact absurd hs (by decide)
    | close l hl p Q q k0 b x hp hQ hk ex hla =>
      rw [alone_place hla] at hs
      have hm := List.mem_of_getElem? hk
      have hs' : senderKind k0 = true := hs
      exfalso
      clear hs hla hk hkind hb ex
      revert hm hs'
      cases k0 <;> decide
    | cleared l hl fs f b hfs hf hr hd =>
      rw [(kinds_at hl).2.2.2.2.2.2] at hkind
      rw [← Option.some.inj hkind] at hs
      exact absurd hs (by decide)
    | back q k0 b b' name hk lot hp hla =>
      have hs' : senderKind k0 = true := by
        have e : b.place = { chain := 1, link := none, piece := q + 1, kind := k0 } :=
          alone_place hla
        have hs2 : senderKind b.place.kind = true := hs
        rw [e] at hs2
        exact hs2
      exact (E.back q k0 b' hk hs' lot hp).under (underR_bare (alone_underR hla))
    | last lot hla =>
      rw [kinds_ends.2.2] at hkind
      rw [← Option.some.inj hkind] at hs
      exact absurd hs (by decide)
  · have e : sn j = [] := D.calm j _ hkind (by simpa using hs)
    have hj : j ≤ c.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1
    have h1 := hall j b hb
    rw [e] at h1 ⊢
    exact shapes_of_sends h1 (fun s hr => reached_step hall hc hi hj hr)
      (E.grows j b hb (by simpa using hs))

/-- **THE FIELD's OWN SENTENCE, AT THE PROOF FILE's OWN FIRST STATE AND THE PLANNER's OWN LIST.** -/
theorem shapes_start (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} (p : ProofFile.InstPub)
    (D : SendDebts ft Z.first.codes (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p))
    (E : ShapeDebts ft (snAt Z Bs.G₀ placesW) Z Bs.G₀ c (ProofFile.startS Z p))
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ placesW) = true)
    (hu : (ProofFile.startS Z p).failed = none) {k : ℕ} (hk : k ≤ 358) {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out) :
    atFirstShapes (msgsOfChain Z.made.proof.1) out.1 = true := by
  have hlen : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]
  obtain ⟨c0, b0, i0⟩ := start_three O p hu
  have h0 : (ProofFile.startS Z p).st.oracles = #[] := by
    have hz : (ProofFile.startS Z p).st.oracles.size = 0 := by
      have : (ProofFile.startS Z p).st.oracles.size = (ProofFile.startS Z p).book.place.size := i0
      rw [this, b0]
      rfl
    exact Array.eq_empty_of_size_eq_zero hz
  exact shapes_field (shapes_scope hS hR O D E c0 i0) (hlen ▸ hB) h0 (hlen ▸ hk) hf

end

end IM

#print axioms IM.shapes_first_on
#print axioms IM.shapes_scope
#print axioms IM.shapes_start
