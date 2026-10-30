-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/RealB.lean: what is not shown is not made: the prover's program (`erase_Pp_reply`,
below) (words of this library: lean/GLOSSARY.md).

What is not shown leaves no trace, as far as it holds before any change of the oracles:
 * a batch without a request of the adversary's own runs the prover, shows nothing and keeps the
   key, so it can be left out (`Rom.forgetCall`);
 * in a batch with own requests the proof string of a slot is made, after all hashing, by reading
   secret strings: no coin, no oracle query. So the program that makes proof strings for the own
   requests only is the same oracle algorithm, as far as the reply goes.

  `Silent`  a program with tokens that only reads: `pure` and `reveal`
  `erase_proveB_mask`  as oracle algorithms (`erase`): the compiled prover with fewer proof strings
                       = the compiled prover, with the other proof strings struck out afterwards
  `erase_PpJ_reply`, `erase_Pp_reply`  the second point, for the prover's program

Limits: this file does not prove the first point, and it proves nothing on the real experiment as a
whole.
-/
import Compile.Batch.Chall
import Compile.Batch.SpecGhost
import Compile.EraseKit
import Rom.Forget
import Rom.Bridge

noncomputable section

namespace Compile.Batch
open Iop Rom
open Compile.GlueB (GCall ownPf realW)

namespace RealB

/-! ## Programs that only read -/

section Silent

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- The program samples no coin, makes no query and makes no token: it only reads strings. -/
def Silent : Step S sp α → Prop
  | .pure _ => True
  | .reveal _ k => ∀ vs, Silent (k vs)
  | .sample _ _ => False
  | .plain _ _ _ => False
  | .fresh _ _ => False
  | .marked _ _ _ _ _ _ => False

theorem Silent.bind {c : Step S sp α} {g : α → Step S sp β}
    (h : Silent c) (hg : ∀ a, Silent (g a)) : Silent (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | reveal ts k ih => exact fun vs => ih vs (h vs)
  | sample n k _ => exact h.elim
  | plain o q k _ => exact h.elim
  | fresh l k _ => exact h.elim
  | marked o t us pt inj k _ => exact h.elim

/-- As an oracle algorithm such a program is a value, and it leaves the store as it is. -/
theorem erase_silent {c : Step S sp α} (h : Silent c) (vs : List Bits) :
    ∃ a, erase c vs = OComp.pure (a, vs) := by
  induction c with
  | pure a => exact ⟨a, rfl⟩
  | reveal ts k ih => exact ih _ (h _)
  | sample n k _ => exact h.elim
  | plain o q k _ => exact h.elim
  | fresh l k _ => exact h.elim
  | marked o t us pt inj k _ => exact h.elim

end Silent

/-! ## Striking out -/

/-- strike out the entries whose number, counted from j, has no flag -/
def mask {β : Type} (fl : ℕ → Bool) : ℕ → List (Option β) → List (Option β)
  | _, [] => []
  | j, π :: r => (if fl j then π else none) :: mask fl (j + 1) r

theorem getD_mask {β : Type} (fl : ℕ → Bool) : ∀ (j : ℕ) (l : List (Option β)) (s : ℕ),
    (mask fl j l).getD s none = if fl (j + s) then l.getD s none else none
  | _, [], s => by simp [mask]
  | j, π :: r, 0 => by simp [mask]
  | j, π :: r, s + 1 => by
      simp only [mask, List.getD_cons_succ, getD_mask fl (j + 1) r s]
      rw [show j + 1 + s = j + (s + 1) by omega]

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## The proof strings are made by reading -/

theorem silent_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    Silent (openT (lam := lam) (K := K) (L := L) t j a) := fun _ => trivial

theorem silent_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) :
    Silent (openE (K := K) (L := L) t j a) := by
  unfold openE
  split
  · exact fun _ => trivial
  · trivial

theorem silent_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos)
    (o : r.Orc) (tr : TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ l : List ℕ, Silent (opensComp (K := K) (L := L) dec posAt o tr isRead f l)
  | [] => trivial
  | j :: js => by
      simp only [opensComp, step_bind_eq]
      refine (silent_opensComp dec posAt o tr isRead f js).bind fun f' => ?_
      split
      · split_ifs
        · exact (silent_openT _ _ _).bind fun _ => trivial
        · trivial
      · trivial

theorem silent_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Silent (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) := by
  unfold opensOpt
  split
  · trivial
  · exact silent_opensComp _ _ _ _ _ _ _

/-- Opening the positions read in the trees of one component, from tree number k on, only reads.
The depths and the trees are two lists of any lengths: where either list ends, nothing more is
opened. -/
theorem silent_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      Silent (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | k, _ :: ds, tr :: trs, f =>
    (silent_opensTrees dec posAt o isRead (k + 1) ds trs f).bind fun f' =>
      silent_opensComp dec (posAt k) o tr isRead f' _

theorem silent_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      Silent (opensB (L := L) s A W τ tjs t0s isRead)
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (w, W), (m, _, τ), tjs, t0s, isRead => by
      simp only [opensB, step_bind_eq]
      exact (silent_opensOpt _ _ _ _ _ _ _).bind fun _ =>
          (silent_opensOpt _ _ _ _ _ _ _).bind fun _ =>
        (silent_opensB s A W τ _ _ _).bind fun _ => trivial

theorem silent_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ l : List E.Pos, Silent (opensExtB (K := K) (L := L) we y trees isRead l)
  | [] => trivial
  | p :: ps => by
      simp only [opensExtB, step_bind_eq]
      refine (silent_opensExtB we y trees isRead ps).bind fun f => ?_
      split_ifs
      · exact (silent_openE _ _ _).bind fun _ => trivial
      · trivial

section Prove

variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

theorem silent_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    Silent (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) := by
  unfold finishSlot
  dsimp only
  split_ifs
  · trivial
  · exact fun vs =>
      (silent_opensB _ _ _ _ _ _ _).bind fun _ => (silent_opensExtB _ _ _ _ _).bind fun _ => trivial

/-- the proof string of one slot, as finishAll makes it -/
def headOf (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) :
    St lam K L (Option (OneProtocolProof lam Q)) :=
  match acc.x with
  | some (x, cj) => if fl j then finishSlot Q H wq wp trees w c0 a0 j x cj acc else pure none
  | none => pure none

theorem erase_headOf (fl fl' : ℕ → Bool) (hsub : ∀ j, fl j = true → fl' j = true) (c0 : H.Coin0)
    (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    erase (headOf (L := L) Q H wq wp trees w fl c0 a0 j acc) vs =
      (erase (headOf (L := L) Q H wq wp trees w fl' c0 a0 j acc) vs).bind fun o =>
        OComp.pure (if fl j then o.1 else none, o.2) := by
  unfold headOf
  rcases acc.x with _ | ⟨x, cj⟩
  · show OComp.pure (none, vs) = OComp.pure (if fl j then none else none, vs)
    rw [ite_self]
  · dsimp only
    cases hj : fl j
    · have hs : Silent
          (if fl' j then finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc
            else pure none) := by
        split_ifs
        · exact silent_finishSlot Q H wq wp trees w c0 a0 j x cj acc
        · trivial
      obtain ⟨a, ha⟩ := erase_silent hs vs
      rw [ha]
      rfl
    · rw [hsub j hj]
      simp only [if_true]
      obtain ⟨a, ha⟩ :=
        erase_silent (silent_finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) vs
      rw [ha]
      rfl

theorem erase_finishAll_mask
    (fl fl' : ℕ → Bool) (hsub : ∀ j, fl j = true → fl' j = true) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (zs : List (SlotAcc lam K (Y × H.Coin))) (j : ℕ) (vs : List Bits),
      erase (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs) vs =
        (erase (finishAll (L := L) Q H wq wp trees w fl' c0 a0 j zs) vs).bind fun o =>
          OComp.pure (mask fl j o.1, o.2)
  | [], _, _ => rfl
  | acc :: zs, j, vs => by
      have e : ∀ g : ℕ → Bool, finishAll (L := L) Q H wq wp trees w g c0 a0 j (acc :: zs)
          = (headOf (L := L) Q H wq wp trees w g c0 a0 j acc).bind fun π =>
              (finishAll (L := L) Q H wq wp trees w g c0 a0 (j + 1) zs).bind fun r =>
                pure (π :: r) := fun _ => rfl
      rw [e fl, e fl']
      simp only [erase_bind, erase_headOf (L := L) Q H wq wp trees w fl fl' hsub c0 a0 j acc vs,
        erase_finishAll_mask fl fl' hsub c0 a0 zs (j + 1), OComp.bind_assoc, OComp.bind,
        step_pure_eq, erase_pure, mask]

/-- Fewer proof strings (fl implies fl') = all those of fl', and then some struck out. -/
theorem erase_proveB_mask (fl fl' : ℕ → Bool) (hsub : ∀ j, fl j = true → fl' j = true)
    (xs : List (Option Y)) (vs : List Bits) :
    erase (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs =
      (erase (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl' xs) vs).bind
        fun o => OComp.pure (mask fl 0 o.1, o.2) := by
  unfold proveB
  simp only [erase_bind, OComp.bind_assoc,
    erase_finishAll_mask (L := L) Q H wq wp trees w fl fl' hsub]

end Prove

/-! ## The reply reads the proofs of the own requests only -/

section Reply

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem ownFlag_zero (s : X × Unit × Bool) (b : ZKCP.Gen.Batch X Unit) :
    ownFlag (s :: b) 0 = s.2.2 := rfl

theorem ownFlag_succ (s : X × Unit × Bool) (b : ZKCP.Gen.Batch X Unit) (a : ℕ) :
    ownFlag (s :: b) (a + 1) = ownFlag b a := by
  simp [ownFlag]

theorem ownPf_cons {Pf : Type} (s : X × Unit × Bool) (b : ZKCP.Gen.Batch X Unit)
    (π : Pf) (l : List Pf) :
    ownPf (s :: b) (π :: l) = (if s.2.2 then [π] else []) ++ ownPf b l := by
  cases h : s.2.2 <;> simp [ownPf, h]

theorem ownPf_congr {Pf : Type} :
    ∀ (b : ZKCP.Gen.Batch X Unit) (l₁ l₂ : List Pf),
      l₁.length = l₂.length → (∀ a, ownFlag b a = true → l₁[a]? = l₂[a]?) → ownPf b l₁ = ownPf b l₂
  | [], _, _, _, _ => by simp [ownPf]
  | _ :: _, [], [], _, _ => rfl
  | _ :: _, [], _ :: _, h, _ => by simp at h
  | _ :: _, _ :: _, [], h, _ => by simp at h
  | s :: b, π₁ :: l₁, π₂ :: l₂, hl, h => by
      rw [ownPf_cons, ownPf_cons, ownPf_congr b l₁ l₂ (by simpa using hl) fun a ha => by
        have := h (a + 1) (by rw [ownFlag_succ]; exact ha)
        simpa using this]
      cases hs : s.2.2
      · rfl
      · have := h 0 (by rw [ownFlag_zero]; exact hs)
        simp only [List.getElem?_cons_zero, Option.some.injEq] at this
        rw [this]

theorem ownPf_of_not_hasOwn {Pf : Type} (b : ZKCP.Gen.Batch X Unit)
    (h : hasOwn b = false) (l : List Pf) : ownPf b l = [] := by
  unfold ownPf
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro s hs
  have h1 := (List.of_mem_zip hs).1
  unfold hasOwn at h
  rw [List.any_eq_false] at h
  exact h s.1 h1

theorem val_fitLen {β : Type} (d : β) (n : ℕ) (l : List β) (h : l.length = n) :
    (fitLen d n l).val = l := by
  show (l ++ List.replicate n d).take n = l
  rw [← h, List.take_left']
  rfl

theorem length_reqs (b : ZKCP.Gen.Batch X Unit) : (reqs b).length = b.pairs.length := by simp [reqs]

theorem slotFlags_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (fr : ℕ → Bool) (a : Fin N) :
    slotFlags σ fr (σ a).val = fr a.val := by
  unfold slotFlags
  rw [dif_pos (σ a).isLt]
  simp

theorem slotFlags_le {N : ℕ} (σ : Equiv.Perm (Fin N)) (fr : ℕ → Bool)
    (s : ℕ) (h : slotFlags σ fr s = true) :
    slotFlags σ (fun _ => true) s = true := by
  unfold slotFlags at h ⊢
  split_ifs with hs
  · rfl
  · rw [dif_neg hs] at h
    exact Bool.noConfusion h

/-- the proofs of a batch, from the proof strings of the slots -/
def prfsOf (j : ℕ) (cm : Dig lam) (piL : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)))
    (σ : Equiv.Perm (Fin L.maxBatchSize)) (n : ℕ) (πs : List (Option (OneProtocolProof lam L.onlineBatch))) : List (Prf lam L) :=
  (List.range n).map fun a =>
    ⟨j, cm, piL, if h : a < L.maxBatchSize then πs.getD (σ ⟨a, h⟩).val none else none⟩

/-- Striking out the proof strings of the slots that hold no own request does not change the reply.
-/
theorem replyOf_mask (b : ZKCP.Gen.Batch X Unit) (j : ℕ) (cm : Dig lam)
    (piL : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)))
    (σ : Equiv.Perm (Fin L.maxBatchSize)) (πs : List (Option (OneProtocolProof lam L.onlineBatch))) :
    replyOf b (prfsOf j cm piL σ (reqs b).length (mask (slotFlags σ (ownFlag b)) 0 πs)) =
      replyOf b (prfsOf j cm piL σ (reqs b).length πs) := by
  unfold replyOf
  rw [val_fitLen _ _ _ (by simp [prfsOf, length_reqs]),
    val_fitLen _ _ _ (by simp [prfsOf, length_reqs])]
  refine congrArg Sum.inr (ownPf_congr b _ _ (by simp [prfsOf]) fun a ha => ?_)
  unfold prfsOf
  simp only [List.getElem?_map]
  cases hr : (List.range (reqs b).length)[a]? with
  | none => rfl
  | some a' =>
    have ha' : a' = a := by
      rw [List.getElem?_eq_some_iff] at hr
      obtain ⟨h1, h2⟩ := hr
      rw [← h2, List.getElem_range]
    subst ha'
    simp only [Option.map_some, Option.some.injEq, Prf.mk.injEq, true_and]
    by_cases h : a' < L.maxBatchSize
    · rw [dif_pos h, dif_pos h, getD_mask, Nat.zero_add,
        slotFlags_apply σ (ownFlag b) ⟨a', h⟩, ha, if_pos rfl]
    · rw [dif_neg h, dif_neg h]

end Reply

/-! ## The prover's program -/

section Worlds

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

theorem erase_PpJ_reply {γ : Type} (k : IskH lam L) (b : ZKCP.Gen.Batch X Unit) (j : ℕ)
    (σ : Equiv.Perm (Fin L.maxBatchSize)) (vs : List Bits) (st : γ) :
    ((erase (PpJ W WP p k (ownFlag b) (reqs b) j σ) vs).bind fun o =>
        OComp.pure (replyOf b o.1, st)) =
      (erase (PpJ W WP p k (fun _ => true) (reqs b) j σ) vs).bind fun o =>
        OComp.pure (replyOf b o.1, st) := by
  unfold PpJ
  cases k.leaves[j]? with
  | none => rfl
  | some lf =>
    dsimp only
    simp only [erase_bind, OComp.bind_assoc]
    rw [erase_proveB_mask p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ _ _ _
        (slotFlags σ (ownFlag b)) (slotFlags σ fun _ => true) (slotFlags_le σ (ownFlag b))]
    simp only [OComp.bind_assoc, OComp.bind, step_pure_eq, erase_pure]
    exact congrArg _ (funext fun o => congrArg (fun z => OComp.pure (z, st))
      (replyOf_mask b j lf.node.tree.root lf.piL σ o.1))

theorem erase_Pp_reply {γ : Type} (k : IskH lam L) (b : ZKCP.Gen.Batch X Unit)
    (vs : List Bits) (st : γ) :
    ((erase (Pp W WP p k (ownFlag b) (reqs b)) vs).bind fun o => OComp.pure (replyOf b o.1, st)) =
      (erase (Pp W WP p k (fun _ => true) (reqs b)) vs).bind fun o =>
        OComp.pure (replyOf b o.1, st) := by
  unfold Pp drawT
  simp only [erase_sample, erase_bind, erase_pure, OComp.bind, erase_PpJ_reply W WP p k b _ _ _ st]

end Worlds

end RealB

end Compile.Batch
