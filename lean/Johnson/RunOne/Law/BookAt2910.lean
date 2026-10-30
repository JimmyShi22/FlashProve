-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/BookAt2910.lean: IN FRONT OF THE KEY FILE's SHARED CHAIN's TWO PROXIMITY TESTS THE BOOK's TREES OF THE CHAIN's THREE SAMPLED MESSAGES (o_u · o_omega · the split's masks) HAVE THE SHAPES THAT THE KEY FILE's IOP AS WRITTEN IN LEAN TELLS OF THE TREES 6 · 7 · 8: OFF THE HISTORY. Statements with proofs; each proof is a walk over named laws.
WHY OFF THE HISTORY. The tables' invariant at a border of the shared chain (on₂: shape₂ and Free₂, on the verifier's state) counts the book's trees and places the messages; no clause of it speaks of a tree's SHAPE. The Bool seatX (Johnson/Desc/Sound/SeatsCarried.lean) does, and every sub-protocol of the chain hands it on.

Main names:
  seatX_hist: at every state of the shared chain that was reached at a border k ≤ 10 the Bool seatX holds at k: by the rule reached_held_inv (Johnson/Top/Fire/Code/ReachedInv.lean) over seatX_same (the front) · seatX_k14 (the kind K14's eight sub-protocols) · seatX_onGu (the first proximity test). The two layouts are letters.
  told_two: what the kind K14's eight sub-protocols tell of trees is what its two sendings tell, one behind the other. KIN: the inner step «hb» of told_of_chain (Johnson/Desc/K12/Coin/ToldAtFile.lean), which is not exported: said again here, by its own proof.
  told_u | told_omega: so the key file's IOP as written in Lean tells at 6 + τ what "send o_u" tells of its tree τ, and at 6 + (that sending's trees) + τ what "send o_omega" tells of its tree τ; 6: the trees of which the first chain tells: a premise (h6).
  shape_of_laid: a tree of the book that has a layout's shape number τ, and what a sending with that layout tells of τ: ShapeIs.
  TreeTold B o': a definition: the book B places message o' at some q; the tree q.1 is there; of the tree 6 + q.1 something is told; ShapeIs of the two.
  trees_2910_of: at a state reached at a border 6 ≤ k ≤ 10: TreeTold of the statement's messages 0 · 2 · 3. The layouts and h6 are premises.
  lays_full | lays_full_no: by the kernel: at the written key's shape and codes "send o_u"'s messages can be said and both layouts can be made; a negative test.
  trees_2910: that in scope. shapeIs_2910: in the form that the proximity test's kind's files ask: k' ∈ [3, 4, 5] · (plan₂ …).orc k' = some o' · place[o']? = some q · (atSix k').1 = off₂N q.1 ⊢ ∀ o, oracleAt (atSix k').1 = some o → ∃ T, trees[q.1]? = some T ∧ ShapeIs T.shape o.
  shapeIs_2910_placed: the same with the premise on atSix paid by the tables' clause Placed (a field of Free₂ and of Tests₂) at a letter off₂ that is off₂N at every number.

Words: "book": the state's list of trees and of the messages' places in them; "layout": what layTrees, the routine that places a prover's message's oracle messages in trees, returns; "border k": in front of sub-protocol k of the chain's flat list.
OBJECT: St₂.book at Hist₂ (Fk X N P) D k a against FileDescription.oracleAt. USER: none yet (meant: the clause on the word at rows 2.9 | 2.10 of the proximity test's kind's files). LETTERS: X N P · D · the scope's.
Limits. It GIVES the trees at every reached state; it is empty only where nothing is reached or scope fails. That an honest key file reaches these borders is not shown here. That scope's premises can be met together is not shown here. Nothing on a tree's number, source, parts or root. One size. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.Sound.SeatsCarried
import Johnson.Desc.K12.Coin.ToldAtFile
import Johnson.Desc.K12.Coin.MembersLaid
import Johnson.Top.Fire.Code.ReachedInv
import Johnson.Top.Fire.Code.KeyASide2Paid
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.RunOne.Law.StepSide2
import Johnson.RunOne.KeyTenInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.BookAt2910
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (Source LaterPlaces madeAt sourceOf Placed)
open VerifiableInference.Desc.K12.Coin (ShapeIs told_shape told_length oracleAt_mid withU_size withOmega_size)
open _root_.Desc.K14 (P14 St withU withOmega blocksOr blocks)
open _root_.Desc.K14.Law.Fence (seatX seatX_same seatX_k14 seatX_onGu seatX_place)
open Johnson.G.OfPlan (Made)
open Johnson.G (writtenKFull)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Sound.Light (parAt atClaim desc_eight_named)
open Johnson.RunOne.KeyRows23 (Fk P₂ St₂ plan₂ atSix shapeAt front₂_same form_of_fileOk masks_of_form)
open Johnson.RunOne.KeyLetters (told_shared first_tells_six chains_of)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (key_in_scope)
open Johnson.RunOne.Sound (rounds_in_scope)
open Johnson.RunOne.Law.K12FwdAt (asks_U)
open Johnson.RunOne.Law.K12SeatsAt (fk_U_at)
open Johnson.RunOne.Law.StepSide2 (table_eight)
open Johnson.RunOne.Law.RngAsked (asksPlan_ok)
open LPFD (Hist₂ st₂ reached_held_inv front_at off₂N fileOk_of_planOk')

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- **The Bool "the book carries the two sendings' layouts" at every state that the shared chain reaches, up to the second proximity test's front.** -/
theorem seatX_hist (hp : (Fk X N P).planOk = true) (sentU : Array OracleNotice) (layU layO : TreeLay)
    (hU : withU (parAt X P).S = some sentU) (hlU : layTrees (parAt X P).codes sentU = some layU)
    (hlO : layTrees (parAt X P).codes (withOmega (parAt X P).S) = some layO) (D : WholeD)
    (k : ℕ) (a : P₂ × St₂) (hk : k ≤ 10) (h : Hist₂ (Fk X N P) D k a) :
    seatX (parAt X P) sentU layU layO k a.2 = true := by
  obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, hbl, s1, s2, s3, s4, s5, s6, s7, s8⟩ := desc_eight_named X N P hp
  refine reached_held_inv _ (Fk X N P).shared.blocksInOrder (st₂ (Fk X N P) D)
    (fun k s => seatX (parAt X P) sentU layU layO k s = true) 10 ?_ ?_ k a hk h
  · rintro a ⟨_, e⟩
    show seatX (parAt X P) sentU layU layO 0 a.2 = true
    rw [e]
    rfl
  · intro j hj b hb s s' rs gs _ hy hX
    have K := fun (i : ℕ) (c : Block St Unit) (hc : [b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈][i]? = some c)
        (hy' : c.decide s (rs.map noDigest) gs = .ok s') (hX' : seatX (parAt X P) sentU layU layO (i + 1) s = true) =>
      seatX_k14 (parAt X P) b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ hbl sentU hU layU layO hlU hlO i c hc s s' _ gs hy' hX'
    match j, hj, hb, hX with
    | 0, _, hb, hX =>
      obtain rfl := front_at X N P b hb
      obtain rfl := front₂_same X s _ gs s' hy
      exact seatX_same (parAt X P) sentU layU layO 0 _ _ rfl (.inl (by omega)) hX
    | 1, _, hb, hX => obtain rfl := Option.some.inj (s1.symm.trans hb); exact K 0 b₁ rfl hy hX
    | 2, _, hb, hX => obtain rfl := Option.some.inj (s2.symm.trans hb); exact K 1 b₂ rfl hy hX
    | 3, _, hb, hX => obtain rfl := Option.some.inj (s3.symm.trans hb); exact K 2 b₃ rfl hy hX
    | 4, _, hb, hX => obtain rfl := Option.some.inj (s4.symm.trans hb); exact K 3 b₄ rfl hy hX
    | 5, _, hb, hX => obtain rfl := Option.some.inj (s5.symm.trans hb); exact K 4 b₅ rfl hy hX
    | 6, _, hb, hX => obtain rfl := Option.some.inj (s6.symm.trans hb); exact K 5 b₆ rfl hy hX
    | 7, _, hb, hX => obtain rfl := Option.some.inj (s7.symm.trans hb); exact K 6 b₇ rfl hy hX
    | 8, _, hb, hX => obtain rfl := Option.some.inj (s8.symm.trans hb); exact K 7 b₈ rfl hy hX
    | 9, _, hb, hX =>
      have hat := fk_U_at X N P
      rw [table_eight X N P hp] at hat
      obtain rfl := Option.some.inj (hat.symm.trans hb)
      obtain ⟨he, ha, _, _⟩ := asksPlan_ok (asks_U X N P (fileOk_of_planOk' _ hp))
      exact seatX_onGu (parAt X P) sentU layU layO _ he ha s s' _ gs hy hX
    | n + 10, hj, _, _ => exact absurd hj (by omega)

/-- What the kind's eight sub-protocols tell of trees: what its two sendings tell, one behind the other. -/
theorem told_two (Q : P14) (sU : Array OracleNotice) (hU : withU Q.S = some sU) :
    oraclesOf (blocksOr Q) = _root_.Desc.K14.oraclesOf Q.codes sU [[0], []] ++
      _root_.Desc.K14.oraclesOf Q.codes (withOmega Q.S) [[1], [1, 0]] := by
  unfold _root_.Desc.K14.blocksOr _root_.Desc.K14.blocks
  simp [hU, oraclesOf, _root_.Desc.K14.sendAt, _root_.Desc.K14.parK1, K1.Par.sent]

/-- **At the trees of "send o_u".** -/
theorem told_u (h6 : (oraclesOf (Fk X N P).first.blocksInOrder).length = 6) (sU : Array OracleNotice) (hU : withU (parAt X P).S = some sU)
    (τ : ℕ) (o : VerifiableInference.Desc.Oracle) (ho : (_root_.Desc.K14.oraclesOf (parAt X P).codes sU [[0], []])[τ]? = some o) :
    (Fk X N P).oracleAt (6 + τ) = some o := by
  obtain ⟨R, hR⟩ := told_shared X N P
  have h := oracleAt_mid (Fk X N P) [] _ (_root_.Desc.K14.oraclesOf (parAt X P).codes (withOmega (parAt X P).S) [[1], [1, 0]] ++ R)
    (by rw [hR, told_two _ sU hU, List.append_assoc]; rfl) τ o ho
  rw [h6] at h
  simpa using h

/-- **At the trees of "send o_omega".** -/
theorem told_omega (h6 : (oraclesOf (Fk X N P).first.blocksInOrder).length = 6) (sU : Array OracleNotice) (hU : withU (parAt X P).S = some sU)
    (layU : TreeLay) (hl : Own.treesMade (parAt X P).codes sU = some layU)
    (τ : ℕ) (o : VerifiableInference.Desc.Oracle) (ho : (_root_.Desc.K14.oraclesOf (parAt X P).codes (withOmega (parAt X P).S) [[1], [1, 0]])[τ]? = some o) :
    (Fk X N P).oracleAt (6 + layU.shapes.size + τ) = some o := by
  obtain ⟨R, hR⟩ := told_shared X N P
  have h := oracleAt_mid (Fk X N P) (_root_.Desc.K14.oraclesOf (parAt X P).codes sU [[0], []]) _ R
    (by rw [hR, told_two _ sU hU, List.append_assoc]) τ o ho
  rw [h6, told_length (parAt X P).codes sU _ layU hl] at h
  exact h

/-- A tree of the book with a layout's shape, against what a sending with that layout tells of it. -/
theorem shape_of_laid (codes : Codes) (sent : Array OracleNotice) (gs : List (List ℕ)) (lay : TreeLay)
    (hl : layTrees codes sent = some lay) (hg : gs.length = sent.size) (B : TreeBook) (z τ : ℕ) (hτ : τ < lay.shapes.size)
    (hB : (B.trees[z]?).map (·.shape) = some (lay.shapes.getD τ default)) :
    ∃ T o, B.trees[z]? = some T ∧ (_root_.Desc.K14.oraclesOf codes sent gs)[τ]? = some o ∧ ShapeIs T.shape o := by
  obtain ⟨T, hT, e⟩ := Option.map_eq_some_iff.1 hB
  have hs : lay.shapes[τ]? = some T.shape := by
    rw [e, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hτ]
    rfl
  obtain ⟨o, ho, hS⟩ := told_shape codes sent gs lay (by rw [Own.treesMade_eq]; exact hl) hg τ T.shape hs
  exact ⟨T, o, hT, ho, hS⟩

/-- What is said of one message of the shared chain's statement. -/
def TreeTold (B : TreeBook) (o' : ℕ) : Prop :=
  ∃ q T o, B.place[o']? = some q ∧ B.trees[q.1]? = some T ∧ (Fk X N P).oracleAt (6 + q.1) = some o ∧ ShapeIs T.shape o

/-- **The three trees, the layouts as letters.** -/
theorem trees_2910_of (hp : (Fk X N P).planOk = true) (h6 : (oraclesOf (Fk X N P).first.blocksInOrder).length = 6)
    (sentU : Array OracleNotice) (layU layO : TreeLay)
    (hU : withU (parAt X P).S = some sentU) (hlU : layTrees (parAt X P).codes sentU = some layU)
    (hlO : layTrees (parAt X P).codes (withOmega (parAt X P).S) = some layO) (D : WholeD)
    (k : ℕ) (a : P₂ × St₂) (h6k : 6 ≤ k) (hk : k ≤ 10) (h : Hist₂ (Fk X N P) D k a) :
    TreeTold X N P a.2.book 0 ∧ TreeTold X N P a.2.book 2 ∧ TreeTold X N P a.2.book 3 := by
  have hform := form_of_fileOk X N P (fileOk_of_planOk' _ hp)
  have hM : (parAt X P).S.masksAhead = true := masks_of_form _ hform
  have hS : (parAt X P).S.sharedSplitNeeded = true := by
    have h' := hform
    simp only [LKFU.Shape23.formOk, Bool.and_eq_true] at h'
    exact h'.1.2
  have sU := withU_size (parAt X P).S sentU hM hU
  have sO := withOmega_size (parAt X P).S hS
  obtain ⟨pU, pO⟩ := seatX_place (parAt X P) sentU layU layO k a.2 ⟨by omega, by omega⟩
    (seatX_hist X N P hp sentU layU layO hU hlU hlO D k a hk h)
  have hlU' : Own.treesMade (parAt X P).codes sentU = some layU := by rw [Own.treesMade_eq]; exact hlU
  have omega_at : ∀ i, i < 2 → TreeTold X N P a.2.book (2 + i) := by
    intro i hi
    obtain ⟨p1, p2⟩ := pO i (by omega)
    obtain ⟨T, o, hT, ho, hSh⟩ := shape_of_laid (parAt X P).codes (withOmega (parAt X P).S) [[1], [1, 0]] layO hlO (by rw [sO]; rfl)
      a.2.book _ _ (OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO (by omega)) p2
    rw [sU] at p1
    have t := told_omega X N P h6 sentU hU layU hlU' (layO.tree.getD i 0) o ho
    rw [Nat.add_assoc] at t
    exact ⟨_, T, o, p1, hT, t, hSh⟩
  refine ⟨?_, omega_at 0 (by omega), omega_at 1 (by omega)⟩
  obtain ⟨p1, p2⟩ := pU 0 (by omega)
  obtain ⟨T, o, hT, ho, hSh⟩ := shape_of_laid (parAt X P).codes sentU [[0], []] layU hlU (by rw [sU]; rfl)
    a.2.book _ _ (OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlU (by omega)) p2
  exact ⟨_, T, o, p1, hT, told_u X N P h6 sentU hU _ o ho, hSh⟩

/-- At the written key's shape and codes the first sending's messages can be said and both layouts can be made. -/
theorem lays_full : ((withU keyFull.once.shape).bind fun u => layTrees keyFull.codes u).isSome = true ∧
    (layTrees keyFull.codes (withOmega keyFull.once.shape)).isSome = true := by decide +kernel

/-- A negative test: without the main rows' codes the first layout cannot be made (the mask rows would be longer than the main rows of their tree). -/
theorem lays_full_no : ((withU keyFull.once.shape).bind fun u => layTrees { keyFull.codes with base := #[] } u).isSome = false := by decide +kernel

section
variable {X N P}
variable {Zp : VerifierAndGoals.PublicFiles} {Z : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Made}

/-- **The three trees, in scope.** -/
theorem trees_2910 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = writtenKFull)
    (D : WholeD) (k : ℕ) (a : P₂ × St₂) (h6k : 6 ≤ k) (hk : k ≤ 10) (h : Hist₂ (Fk X N P) D k a) :
    TreeTold X N P a.2.book 0 ∧ TreeTold X N P a.2.book 2 ∧ TreeTold X N P a.2.book 3 := by
  have hD : (Fk X N P).data "key file" = .ok writtenKFull := by rw [hD₀, hDK]
  have hkey : X.chains.made.sized.key = keyFull := (congrArg (·.made.sized.key) (chains_of hX)).trans (key_in_scope hZ hP hm)
  have h6 := first_tells_six X N P hp hD (rounds_in_scope hZ hP hm hX hp hw).1
  have eS : (parAt X P).S = keyFull.once.shape := congrArg (·.once.shape) hkey
  have eC : (parAt X P).codes = keyFull.codes := congrArg (·.codes) hkey
  obtain ⟨l1, l2⟩ := lays_full
  obtain ⟨layU, hb⟩ := Option.isSome_iff_exists.1 l1
  obtain ⟨sentU, hU, hlU⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨layO, hlO⟩ := Option.isSome_iff_exists.1 l2
  exact trees_2910_of X N P hp h6 sentU layU layO (by rw [eS]; exact hU) (by rw [eC]; exact hlU) (by rw [eC, eS]; exact hlO) D k a h6k hk h

/-- **In the form that the proximity test's kind's files ask.** -/
theorem shapeIs_2910 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = writtenKFull)
    (D : WholeD) (k : ℕ) (a : P₂ × St₂) (h6k : 6 ≤ k) (hk : k ≤ 10) (h : Hist₂ (Fk X N P) D k a)
    (k' : ℕ) (hk' : k' ∈ [3, 4, 5]) (o' : ℕ) (ho' : (plan₂ (shapeAt X)).orc k' = some o') (q : ℕ × ℕ) (hq : a.2.book.place[o']? = some q)
    (hz : (atSix k').1 = off₂N q.1) :
    ∀ o, (Fk X N P).oracleAt (atSix k').1 = some o → ∃ T, a.2.book.trees[q.1]? = some T ∧ ShapeIs T.shape o := by
  obtain ⟨t0, t2, t3⟩ := trees_2910 hZ hP hm hX hp hw DK hD₀ hDK D k a h6k hk h
  have key : TreeTold X N P a.2.book o' := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk'
    rcases hk' with rfl | rfl | rfl
    · obtain rfl : 0 = o' := Option.some.inj ho'
      exact t0
    · obtain rfl : 2 = o' := Option.some.inj ho'
      exact t2
    · obtain rfl : 3 = o' := Option.some.inj ho'
      exact t3
  obtain ⟨q₁, T, o₁, hq₁, hT, ho₁, hS⟩ := key
  obtain rfl : q₁ = q := Option.some.inj (hq₁.symm.trans hq)
  intro o ho
  rw [hz] at ho
  obtain rfl : o₁ = o := Option.some.inj (ho₁.symm.trans ho)
  exact ⟨T, hT, hS⟩

/-- The same, the premise on atSix paid by the tables' clause Placed, at a letter off₂ that is off₂N at every number. -/
theorem shapeIs_2910_placed (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol Z) (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (DK : WholeD)
    (hD₀ : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a)) (hDK : DK.at OnBytes.Slice.frS.P.T.a = writtenKFull)
    (D : WholeD) (k : ℕ) (a : P₂ × St₂) (h6k : 6 ≤ k) (hk : k ≤ 10) (h : Hist₂ (Fk X N P) D k a)
    (off₂ : ℕ → ℕ) (hoff : ∀ z, off₂ z = off₂N z) (l : List ℕ) (hpl : Placed (plan₂ (shapeAt X)).orc (fun o => a.2.book.place[o]?) off₂ atSix l)
    (k' : ℕ) (hk' : k' ∈ [3, 4, 5]) (hl : k' ∈ l) (o' : ℕ) (ho' : (plan₂ (shapeAt X)).orc k' = some o') (q : ℕ × ℕ)
    (hq : a.2.book.place[o']? = some q) :
    ∀ o, (Fk X N P).oracleAt (atSix k').1 = some o → ∃ T, a.2.book.trees[q.1]? = some T ∧ ShapeIs T.shape o := by
  obtain ⟨o₂, t, a1, a2, a3⟩ := hpl k' hl
  obtain rfl : o₂ = o' := Option.some.inj (a1.symm.trans ho')
  obtain rfl : t = q := Option.some.inj (a2.symm.trans hq)
  exact shapeIs_2910 hZ hP hm hX hp hw DK hD₀ hDK D k a h6k hk h k' hk' _ ho' _ hq ((congrArg Prod.fst a3).trans (hoff _))

end

end Johnson.RunOne.Law.BookAt2910

#print axioms Johnson.RunOne.Law.BookAt2910.seatX_hist
#print axioms Johnson.RunOne.Law.BookAt2910.told_two
#print axioms Johnson.RunOne.Law.BookAt2910.told_u
#print axioms Johnson.RunOne.Law.BookAt2910.told_omega
#print axioms Johnson.RunOne.Law.BookAt2910.shape_of_laid
#print axioms Johnson.RunOne.Law.BookAt2910.trees_2910_of
#print axioms Johnson.RunOne.Law.BookAt2910.lays_full
#print axioms Johnson.RunOne.Law.BookAt2910.lays_full_no
#print axioms Johnson.RunOne.Law.BookAt2910.trees_2910
#print axioms Johnson.RunOne.Law.BookAt2910.shapeIs_2910
#print axioms Johnson.RunOne.Law.BookAt2910.shapeIs_2910_placed
