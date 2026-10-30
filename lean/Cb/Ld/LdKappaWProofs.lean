-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaWProofs.lean: the proofs of the two statements of Cb/Ld/LdKappaW.lean.

Main names (statements and hypotheses: Cb/Ld/LdKappaW.lean):
  `ldKappaW`: the five lists at most κ, with the bits `Z.bits ws`.
  `ldKappaW_work`: the work vectors with exactly these bits.

`ldKappaW`: the last theorem of Cb/Ld/LdKappaWorkRef.lean (`ldKappaW_objR`) at the towers and at the
reference request, along the same equations as `Cb.ldKappa`. For `ldKappaW_work` the lemmas under
"No entry exceeds the class's number" show, by recursion on towers and on the request, that no entry
of a list of bits at w exceeds any n with w ≤ n; they are used at n = `ws.top`.

Limits: what is said and what is not: the head of Cb/Ld/LdKappaW.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaW

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

theorem ldKappaW_pack {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (P P' : LdReqPack F E) (e : P = P') (w : ℕ) (κ : ℝ≥0∞) (h : P'.r.BelowW w κ) : P.r.BelowW w κ :=
  e ▸ h

theorem ldKappaW : Spec.ldKappaW := by
  intro F E _ _ _ _ _ Kc p Z L R core first a₁ more hm b Ls T qφ q κ' κ ws h hK hQ
  have hR : Z.R.r.BelowW ws.ins κ :=
    ldKappaW_pack Z.R.toLdObjD.pack _ h.reqIs ws.ins κ
      (ldKappaW_req R _ first a₁ more hm b Ls T ws.ins κ hQ.bFirst hQ.bMore
        hQ.bSegs hQ.bTail hQ.bLast)
  exact ldKappaW_objR Z.R κ ws.off ws.lk ws.sh ws.ins _ _ _ _ _ _ _ hK.wf hK.lin
    (ldKappaW_pre _ Z.tw₁ ws.off κ h.p₁.isT hK.t₁.bridge hK.t₁.tow)
    (ldKappaW_pre _ Z.tw₂ ws.off κ h.p₂.isT hK.t₂.bridge hK.t₂.tow)
    (ldKappaW_pre _ Z.tw₃ ws.off κ h.p₃.isT hK.t₃.bridge hK.t₃.tow) hK.link
    (ldKappaW_pre _ Z.twK ws.lk κ h.pK.isT hK.tK.bridge hK.tK.tow) hR hK.linB
    (ldKappaW_pre _ Z.tw₁B ws.sh κ h.p₁B.isT hK.t₁B.bridge hK.t₁B.tow)
    (ldKappaW_pre _ Z.tw₂B ws.ins κ h.p₂B.isT hK.t₂B.bridge hK.t₂B.tow)
    (ldKappaW_pre _ Z.tw₃B ws.ins κ h.p₃B.isT hK.t₃B.bridge hK.t₃B.tow)

/-! ### No entry exceeds the class's number -/

/-- all entries are at most n -/
def LeAll (n : ℕ) (L : List ℕ) : Prop := ∀ b ∈ L, b ≤ n

theorem leAll_nil (n : ℕ) : LeAll n [] := fun _ h => absurd h (List.not_mem_nil)
theorem leAll_app {n : ℕ} {L L' : List ℕ} (h : LeAll n L) (h' : LeAll n L') : LeAll n (L ++ L') :=
  fun b hb => (List.mem_append.1 hb).elim (h b) (h' b)
theorem leAll_cons {n a : ℕ} {L : List ℕ} (ha : a ≤ n) (h : LeAll n L) : LeAll n (a :: L) :=
  fun b hb => (List.mem_cons.1 hb).elim (fun e => e ▸ ha) (h b)
theorem leAll_rep {n a : ℕ} (ha : a ≤ n) (k : ℕ) : LeAll n (List.replicate k a) := fun _ hb =>
  (List.eq_of_mem_replicate hb) ▸ ha

section
variable {E : Type} [Field E] [Fintype E]

theorem LdTowC.bits_le {n w : ℕ} (hw : w ≤ n) :
    ∀ {a : LdJoint E} (T : LdTowC a), LeAll n (T.bits w) := by
  intro a T
  induction T with
  | base a t cov d bad L2 => exact leAll_cons (Nat.zero_le n) (leAll_cons hw (leAll_nil n))
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    exact leAll_app
      (leAll_app (leAll_rep (Nat.zero_le n) _)
        (leAll_cons (Nat.zero_le n) (leAll_cons hw (leAll_nil n)))) ih

theorem LdTowG.bits_le {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
    {Sb : B → Type} {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} {n w : ℕ}
    (hw : w ≤ n) (T : LdTowG G Sb sl Z) : LeAll n (T.bits w) := by
  cases T with
  | plain T => exact T.bits_le hw
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    exact leAll_app
      (leAll_app (leAll_rep (Nat.zero_le n) _)
        (leAll_cons (Nat.zero_le n) (leAll_cons hw (leAll_nil n))))
      (rest.bits_le hw)

theorem LdRunD.bitsT_le {S : Sig E} (D : LdRunD S) (T : D.Tow) {n w : ℕ} (hw : w ≤ n) :
    LeAll n (D.bitsT T w) :=
  LdTowG.bits_le hw T

variable {Kc : Type}

theorem LdSeg.bits_le {a d : LdStage E Kc} (s : LdSeg a d) {n w : ℕ} (hw : w ≤ n) :
    LeAll n (s.bits w) :=
  leAll_app (leAll_app
      (leAll_app (leAll_app (leAll_rep (Nat.zero_le n) _) (leAll_rep (Nat.zero_le n) _))
        (leAll_rep (Nat.zero_le n) _))
      (leAll_rep (Nat.zero_le n) _)) (leAll_rep hw _)

theorem LdSegs.bits_le {n w : ℕ} (hw : w ≤ n) :
    ∀ {a b : LdStage E Kc} (S : LdSegs a b), LeAll n (S.bits w) := by
  intro a b S
  induction S with
  | nil => rw [LdSegs.bits]; exact leAll_nil n
  | snoc S s ih => rw [LdSegs.bits]; exact leAll_app ih (s.bits_le hw)

theorem LdReq.bits_le {a z : LdStage E Kc} (r : LdReq a z) {n w : ℕ} (hw : w ≤ n) :
    LeAll n (r.bits w) :=
  leAll_app (leAll_app (leAll_app (leAll_rep (Nat.zero_le n) _) (leAll_rep (Nat.zero_le n) _))
      (LdSegs.bits_le hw r.segs))
    (leAll_rep (Nat.zero_le n) _)

end

theorem linBits_le {n w : ℕ} (hw : w ≤ n) : LeAll n (linBits w) := fun b hb => by
  simp only [linBits, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact Nat.zero_le n | exact hw

theorem lkBits_le {n w : ℕ} (hw : w ≤ n) : LeAll n (lkBits w) := fun b hb => by
  simp only [lkBits, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> first | exact Nat.zero_le n | exact hw

theorem ldKappaW_work : Spec.ldKappaW_work := by
  intro F E _ _ _ _ _ Kc p Z L R core first a₁ more hm b Ls T qφ q κ' κ ws h hK hQ
  have hB := ldKappaW F E Kc p Z L R core first a₁ more hm b Ls T qφ q κ' κ ws h hK hQ
  have o1 : ws.off ≤ ws.top := le_trans (le_max_left _ _) (le_max_left _ _)
  have o2 : ws.lk ≤ ws.top := le_trans (le_max_right _ _) (le_max_left _ _)
  have o3 : ws.sh ≤ ws.top := le_trans (le_max_left _ _) (le_max_right _ _)
  have o4 : ws.ins ≤ ws.top := le_trans (le_max_right _ _) (le_max_right _ _)
  have z0 : (0 : ℕ) ≤ ws.top := Nat.zero_le _
  refine ⟨fun g hg => SubsR.nums_belowB_of_is _ _ κ hB g hg,
    (SubsR.nums_belowB_exists _ _ κ hB).imp fun _ hg => hg.1,
    fun g hg =>
      ⟨belowB_allLe _ _ ?_, belowB_allLe _ _ ?_, belowB_allLe _ _ ?_,
        belowB_allLe _ _ ?_, belowB_allLe _ _ ?_⟩⟩
  · rw [hg.wf]; exact leAll_rep z0 _
  · rw [hg.linOff]
    exact leAll_app (linBits_le o1)
      (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ Z.tw₁ o1))
        (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ Z.tw₂ o1))
          (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ Z.tw₃ o1)) (leAll_nil _))))
  · rw [hg.link]
    exact leAll_app (lkBits_le o2)
      (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ Z.twK o2)) (leAll_nil _))
  · rw [hg.req]; exact Z.R.r.bits_le o4
  · rw [hg.linOn]
    exact leAll_app (linBits_le o3)
      (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ Z.tw₁B o3))
        (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ Z.tw₂B o4))
          (leAll_app (leAll_cons z0 (LdRunD.bitsT_le _ Z.tw₃B o4)) (leAll_nil _))))

end Cb
