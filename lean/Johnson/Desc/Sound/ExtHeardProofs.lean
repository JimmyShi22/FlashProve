-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/ExtHeardProofs.lean: the proofs of the nine statements of
Johnson/Desc/Sound/ExtHeard.lean, each under its statement's name with a small first letter.

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ExtHeard
import Johnson.Desc.Sound.FoldHeardProofs
import Johnson.Desc.Sound.FileKnowsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- What has a value as an option went on. -/
theorem toOptionOk {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) : x = .ok a := by
  cases x with
  | error e => exact nomatch h
  | ok b => exact congrArg Except.ok (Option.some.inj h)

/-- Where a block's reduction puts out b: the fold over that one block went on, from the record in
front, on the stretch's written rounds with what is put behind them, to b's record. -/
theorem pieceOk {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W) (a : S × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (b : S × F.E.Str) (hb : p.ior.red.out a τ = some b) :
    chainAt p.b.name F.ft [p.b] a.1
      ⟨rvT C p.ds τ ++ p.back, (sView C p.stage a.2 τ).opened⟩ = .ok b.1 := by
  obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hs' : (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none) =
      some s' := hs
  split at hs'
  · exact toOptionOk hs'
  · cases hs'

theorem leavesBelow : LeavesBelow := by
  intro S Cl α h b hb s rs gs s' H
  have H' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := H
  split at H'
  · exact hb _ _ _ _ H'
  · exact nomatch H'

theorem laysBelow : LaysBelow := by
  intro S Cl α h rd b hb s rs gs s' H
  have H' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := H
  split at H'
  · exact hb _ _ _ _ H'
  · exact nomatch H'

theorem leavesOutOfBlock : LeavesOutOfBlock := by
  intro S Cl W α C F h p hp a τ b hb
  exact foldLeaves S Cl α h F.ft [p.b] a.1 _ _ _
    (fun c hc => (List.mem_singleton.1 hc) ▸ hp) (chainAtOk (pieceOk p a τ b hb))

theorem setsOfLays : SetsOfLays := by
  intro S Cl W Tok C F tok heard rd p hl he a τ b w hb
  rw [← he a τ w]
  exact chainLays S Cl (Option Tok) heard rd p.b.name F.ft [] p.b [] a.1 b.1 _ hl
    (fun c hc => nomatch hc) (pieceOk p a τ b hb)

theorem rowLeavesOut : RowLeavesOut := by
  intro S Cl W α C F h p l
  induction l generalizing p with
  | nil =>
    intro hall a τ b hb
    exact hall p List.mem_cons_self a τ b hb
  | cons q l ih =>
    intro hall a τ b hb
    have hb0 : (p.ior.seq (rowIOR q l)).red.out a τ = some b := hb
    rw [IOR.red_seq_out] at hb0
    obtain ⟨b', h1, h2⟩ := Option.bind_eq_some_iff.1 hb0
    rw [ih q (fun r hr => hall r (List.mem_cons_of_mem _ hr)) b' _ b h2]
    exact hall p List.mem_cons_self a _ b' h1

theorem hearsRowOf : HearsRowOf := by
  intro S₀ S Cl W Tok C F tok h₀ h rd g hL hY pre blk post
  induction pre with
  | nil =>
    intro p l hm hl hp he
    have hm' : p.b :: l.map (·.b) = g blk :: post.map g := hm
    obtain ⟨e₁, e₂⟩ := List.cons.inj hm'
    have he' : ∀ a τ w,
        rd (shownAt [] p.b (rvT C p.ds τ ++ p.back)) = some (tok (p.ext a τ w)) := by
      simpa only [List.length_nil, ExtRowAt] using he
    simp only [List.length_nil, HearsRowAt]
    refine ⟨setsOfLays S Cl W Tok C F tok h rd p (e₁ ▸ hY blk hl) he', fun r hr => ?_⟩
    have hr' : r.b ∈ post.map g := e₂ ▸ List.mem_map.2 ⟨r, hr, rfl⟩
    obtain ⟨c, hc, ec⟩ := List.mem_map.1 hr'
    exact leavesOutOfBlock S Cl W (Option Tok) C F h r (ec ▸ hL c (hp c hc))
  | cons c pre ih =>
    intro p l hm hl hp he
    cases l with
    | nil => simp only [List.length_cons, ExtRowAt] at he
    | cons q l =>
      have hm' : p.b :: (q :: l).map (·.b) = g c :: (pre ++ blk :: post).map g := hm
      have he' : p.PassesTok tok ∧ ExtRowAt tok rd pre.length q l := by
        simpa only [List.length_cons, ExtRowAt] using he
      simp only [List.length_cons, HearsRowAt]
      exact ⟨he'.1, ih q l (List.cons.inj hm').2 hl hp he'.2⟩

theorem rowExtHeard : RowExtHeard := by
  intro S Cl W Tok C F tok heard d n p l
  induction l generalizing n p with
  | nil =>
    intro hr a τ b w hb
    cases n with
    | zero =>
      have hr' : p.SetsTok tok heard ∧ ∀ r ∈ ([] : List (Piece C F S Cl W)), r.LeavesOut heard := by
        simpa only [HearsRowAt] using hr
      exact hr'.1 a τ b w hb
    | succ n =>
      simp only [HearsRowAt] at hr
  | cons q l ih =>
    intro hr a τ b w hb
    have hb0 : (p.ior.seq (rowIOR q l)).red.out a τ = some b := hb
    rw [IOR.red_seq_out] at hb0
    obtain ⟨b', h1, h2⟩ := Option.bind_eq_some_iff.1 hb0
    have he : rowExt d p (q :: l) a τ w =
        p.ext a (Iop.Tr.fst (s := p.ior.shape) (t := (rowIOR q l).shape) τ)
          (rowExt d q l b' (Iop.Tr.snd (s := p.ior.shape) (t := (rowIOR q l).shape) τ) w) := by
      show Reduction.extSeq p.ior.red (rowIOR q l).red p.ext (rowExt d q l) d a τ w = _
      unfold Reduction.extSeq
      simp only
      split
      · rename_i c hc
        have e : c = b' := Option.some.inj (hc.symm.trans h1)
        rw [e]
      · rename_i hn
        exact nomatch hn.symm.trans h1
    rw [he]
    cases n with
    | zero =>
      have hr' : p.SetsTok tok heard ∧ ∀ r ∈ q :: l, r.LeavesOut heard := by
        simpa only [HearsRowAt] using hr
      rw [rowLeavesOut S Cl W (Option Tok) C F heard q l hr'.2 b' _ b h2]
      exact hr'.1 a _ b' _ h1
    | succ n =>
      have hr' : p.PassesTok tok ∧ HearsRowAt tok heard n q l := by
        simpa only [HearsRowAt] using hr
      rw [hr'.1]
      exact ih n q hr'.2 b' _ b w h2

theorem ownOut : OwnOut := by
  intro S Cl W C F name p l ds e h ht a τ
  subst e
  have k := foldIsRow S Cl W C F name p l h ht a (cast (congrArg Iop.Tr h.symm) τ)
  rw [← k]
  simp only [foldRed, cast_cast, cast_eq]

theorem firstHoldsAt : FirstHoldsAt := by
  intro C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 Tok tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ tok heard n
    back₁ hf hr hback b τ₁ w₁ b₁ hb
  have hb' : (T.row tF tJ t3 okF okJ ok3).S₁.ior.red.out b τ₁ = some b₁ := hb
  rw [eqA tF tJ t3 T okF okJ ok3 hf.base₁] at hb'
  split at hb'
  · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hb'
    have hc' := (ownOut S₁ Cl W C _ T.n₁ T.p₁ T.l₁ D.ds₁ hf.data₁ h₁ hf.tiled₁ _ _).symm.trans hc
    have k := rowExtHeard S₁ Cl W Tok C _ tok heard T.d n T.p₁ T.l₁ hr _ _ c w₁ hc'
    show heard (back₁ (T.out₁ b.1 c.1)) = _
    rw [hback]
    exact k
  · cases hb'

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.leavesBelow
#print axioms VerifiableInference.Desc.Sound.laysBelow
#print axioms VerifiableInference.Desc.Sound.leavesOutOfBlock
#print axioms VerifiableInference.Desc.Sound.setsOfLays
#print axioms VerifiableInference.Desc.Sound.rowLeavesOut
#print axioms VerifiableInference.Desc.Sound.hearsRowOf
#print axioms VerifiableInference.Desc.Sound.rowExtHeard
#print axioms VerifiableInference.Desc.Sound.ownOut
#print axioms VerifiableInference.Desc.Sound.firstHoldsAt
