-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineChainAll.lean: from a state with `TidyO` and at least n₀ tokens in which
every slot is at its start, with different salts, all Fiat-Shamir chains of a batch obey the rules
of deferred programming (`Step`, `Step.run`, Rom/Defer.lean), if no round is shared (`joins` = 0) or
there are 2^depthReq slots: the induction over the rounds (words of this library: lean/GLOSSARY.md).

theorem safeChainT0 : Spec.safeChainT0 (Compile/Batch/DisciplineProve.lean, which also tells what
the chains leave behind), and with it `safeProveB`, `safeCB`, `safePB`. The induction, `safe_chainT`
(among its hypotheses: `TidyO`, `ChainInv`), is over a local round (`safe_eachLo`), the joining
round (`safe_joinM`, `safe_reqT`), a later shared round, and a shared round without format (at the
start or after the later local rounds: Compile/Batch/Prover.lean). A Fiat-Shamir query of a shared
round may have proof-of-work bits: `safe_fbG` (Compile/Batch/DisciplineLoop.lean) takes the search
as one unit.
-/
import Compile.Batch.DisciplineJoin
import Compile.Batch.DisciplineChainSh
import Compile.Batch.DisciplineChainNum
import Compile.Batch.DisciplineProve

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh
    length_afterMark cnt1 mem_evs_afterMark)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {Y : Type}

/-- Under `SlotI`: the open ends of a slot are tokens of the execution (from n₀ on). -/
theorem SlotI.open_new {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT}
    {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotI p d n₀ done ph a0 j acc)
    {u : Tok} (hu : OpenOf ph acc u) : n₀ ≤ u := by
  cases ph with
  | shr tk0 =>
    rcases hu with rfl | rfl
    · exact h.fin.new _ (Or.inl h.cap.2.2.2.2.1)
    · exact h.fin.new _ (Or.inr (Or.inl h.cap.2.2.2.2.2.1))
  | first => exact (show u = acc.tk from hu) ▸ h.fin.new _ (Or.inl h.cap.2.2)
  | loc => exact (show u = acc.tk from hu) ▸ h.fin.new _ (Or.inl h.cap.2.2)
  | aft => exact (show u = acc.tk from hu) ▸ h.fin.new _ (Or.inl h.cap.2.2)

theorem SlotI.live_new {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT}
    {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotI p d n₀ done ph a0 j acc) :
    n₀ ≤ live ph acc :=
  h.fin.new _ (Or.inl h.cap.mem)

/-- Under `Kept`: the number of the final attempt is at most `moreOf gr` -/
theorem Kept.le_more {C P : Type} {gr : Option (GrW C P)} {nc : Option ℕ}
    {dd : List Tok} (h : Kept gr nc dd) : nc.getD 0 ≤ moreOf gr := by
  cases gr with
  | none =>
    cases nc with
    | none => exact Nat.zero_le _
    | some _ => exact absurd h.1 (by simp)
  | some g => exact h.2.2 g rfl

/-- what the chains leave behind -/
def ChainPost (p : Params) (n₀ : ℕ) (dn : List (ℕ × ℕ)) (M : OracleName → ℕ) (d : DSt (spec lam K L))
    (out : List (SlotAcc lam K Y) × Acc0) (d' : DSt (spec lam K L)) : Prop :=
  TidyO (rulesB K L lam p) d' ∧ Run (fun u => n₀ ≤ u) (fun u => n₀ ≤ u) NoTok zr M d d' ∧
    AllFrom (fun j acc => ∃ Op, SlotF d' n₀ dn Op out.2 j acc) 0 out.1 ∧ Trees0 d' n₀ dn out.2.trees

/-- a run before the rest of the chains -/
theorem ChainPost.pre {n₀ : ℕ} {dn : List (ℕ × ℕ)} {M M₁ M₂ : OracleName → ℕ}
    {d d₁ d' : DSt (spec lam K L)} {out : List (SlotAcc lam K Y) × Acc0} {Cc Ch : Tok → Prop}
    (hr : Run Cc Ch NoTok zr M₁ d d₁) (hCc : ∀ u, Cc u → n₀ ≤ u) (hCh : ∀ u, Ch u → n₀ ≤ u)
    (hM : ∀ o, M₁ o + M₂ o ≤ M o) (h : ChainPost p n₀ dn M₂ d₁ out d') :
    ChainPost p n₀ dn M d out d' := by
  have h1 : Run (fun u => n₀ ≤ u) (fun u => n₀ ≤ u) NoTok zr M₁ d d₁ :=
    hr.mono (fun u hu => Or.inl (hCc u hu))
      (fun u hu => Or.inl (hCh u hu)) (fun _ hu => hu.elim) (fun _ => le_rfl) (fun _ => le_rfl)
  exact ⟨h.1,
    h1.trans h.2.1 (fun _ hu => Or.inl hu) (fun _ hu => Or.inl hu)
      (fun _ hu => hu.elim) (fun _ => le_rfl) hM,
    h.2.2⟩

theorem safe_chainT (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq n₀ : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (q : OPos s) → OSym s q → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (done : List (ℕ × ℕ)) (d : DSt (spec lam K L)),
      TidyO (rulesB K L lam p) d → ChainInv p d n₀ done ph a0 zs →
      (jn ph s A = 0 ∨ zs.length = 2 ^ depthReq) → (∀ tk0, ph = PhT.shr tk0 → n₀ ≤ tk0) →
      SafeO (rulesB K L lam p) (chainT p.sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0) d
        (ChainPost p n₀ (done ++ depthsOf s A W) (MCh t ph s A W zs.length) d)
  | [], _, _, _, _, _, ph, _, zs, a0, done, d, hd, h, _, _ => by
      show ChainPost p n₀ (done ++ []) _ d (zs.map Prod.snd, a0) d
      rw [List.append_nil]
      exact ⟨hd, Run.refl d,
        AllFrom.map Prod.snd (fun j z hz => ⟨_, hz.fin⟩) 0 zs h.slots, h.trees0⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, done, d, hd, h, hN, hsh => by
      have hdn : done ++ depthsOf (r :: s) (a, A) (w, W) =
          (done ++ [(w.depthJ, w.depth0)]) ++ depthsOf s A W := by
        rw [List.append_assoc]; rfl
      rw [hdn]
      have hlive : ∀ u,
          (∃ z ∈ zs, u = live ph z.2) → n₀ ≤ u ∧ ¬ Sealed d u := fun u ⟨z, hz, hu⟩ => by
        obtain ⟨j', hI⟩ := AllFrom.of_mem 0 zs h.slots z hz
        exact hu ▸ ⟨hI.live_new, hI.cap.not_sealed⟩
      unfold chainT
      split
      · -- a local round
        rename_i ph _ _ hk
        refine SafeO.bind _ _ d
          (SafeO.mono ?_ _ d
            (safe_eachLo t cms xin a w _ _ i ph n₀ done a0 zs 0 d hd h.le h.slots h.nodup))
        rintro zs' d₁ ⟨hd₁, hr₁, hall₁, hnd₁, _, hlen₁⟩
        have hinv₁ := ChainInv.of_eachLo hall₁ hnd₁ (h.trees0.keeps hr₁ fun u hu => (hlive u hu).2)
          (le_trans h.le hr₁.length_le) h.req
        refine SafeO.mono (fun out d' hp => ?_) _ d₁
          (safe_chainT t cms xin depthReq n₀ s A W _ _ (i + 1) ph.afterLo _ zs' _ _ d₁ hd₁ hinv₁
            (by rw [Num.jn_afterLo A hk ph, hlen₁]; exact hN)
            (fun tk0 he => by cases ph <;> cases he))
        rw [hlen₁] at hp
        exact hp.pre hr₁ (fun u hu => (hlive u hu).1) (fun u ⟨z, hz, hu⟩ => by
          obtain ⟨j', hI⟩ := AllFrom.of_mem 0 zs h.slots z hz
          exact hI.open_new hu) (MCh_lo t ph a A w W zs.length hk)
      · -- the joining round
        rename_i _ _ hk
        have hlenN : zs.length = 2 ^ depthReq := by
          rcases hN with h0 | h0
          · rw [show jn PhT.loc (r :: s) (a, A) = joins (r :: s) (a, A) from rfl,
              Num.joins_cons_sh A hk] at h0
            exact absurd h0 (by simp)
          · exact h0
        refine SafeO.bind _ _ d
          (SafeO.mono ?_ _ d (safe_joinM t a w _ _ i n₀ done a0 zs 0 d hd h.le h.slots h.nodup))
        rintro o d₁ ⟨hd₁, hr₁, hall₁, hmap₁, hnd₁, _, hlen₁⟩
        have hcl : o.2.length = zs.length := by rw [hmap₁, List.length_map, hlen₁]
        have hrdy : Ready lam d₁ o.2 := ⟨fun c hc => by
          rw [hmap₁] at hc
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc
          obtain ⟨j', hJ⟩ := AllFrom.of_mem 0 o.1 hall₁ z hz
          exact ⟨hJ.unt, hJ.len⟩, hnd₁⟩
        have hn₁ : n₀ ≤ d₁.vals.length := le_trans h.le hr₁.length_le
        refine SafeO.bind _ _ d₁
          (SafeO.mono ?_ _ d₁ (safe_reqT depthReq o.2 d₁ hd₁ (hcl.trans hlenN) hrdy))
        rintro rq d₂ ⟨hd₂, hr₂, hPA, hC, hroot, hrlen, hrnew, hsePA⟩
        refine safe_withTree w.has0 w.depth0 _ _ d₂ hd₂ _ fun tr0 d₃ hd₃ hr₃ htt => ?_
        have hroot₃ : Untouched d₃ rq.root := hroot.grows hr₃.grows (fun x => x) (fun x => x)
        have hus : ∀ u ∈ rtL tr0, u < d₃.vals.length := fun u hu => htt.lt hu
        have htu : rq.root ∉ rtL tr0 := fun hu => absurd (htt.le hu) (Nat.not_le.mpr hroot.lt)
        have hbit : min p.sFS lam ≤ (d₃.val rq.root).length := by
          rw [(hrlen.grows hr₃.grows).2]
          exact min_le_right _ _
        have hpre : LoopPre p d₃ t rq.root ([] ++ (tr0.map TTree.root).toList) :=
          ⟨hus, htu, hroot₃.freeAt _, fun _ => hroot₃.freeAt _, hbit⟩
        refine safe_fbG (us := []) hpre w.gr0 _ _ fun nc dd bl tl d₄ hK hT => ?_
        have hd₄ := hpre.tidy hd₃ hT
        have htl : d₃.vals.length ≤ tl :=
          hT.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        have hinv₄ := ChainInv.after_join (p := p) w hall₁ hmap₁ hnd₁ hn₁ (h.req (Or.inr rfl))
          (h.trees0.keeps hr₁ fun u hu => (hlive u hu).2) hd₁ hd₂ hr₂ hPA hC hroot hrnew hsePA hd₃
          hr₃ htt t (nc.toList ++ a0.nons) hd₄ hT bl
        have hn₃ : n₀ ≤ d₃.vals.length := le_trans (le_trans hn₁ hr₂.length_le) hr₃.length_le
        refine SafeO.mono (fun out d' hp => ?_) _ _
          (safe_chainT t cms xin depthReq n₀ s A W _ _ (i + 1) (PhT.shr tl) _ _ _ _ _ hd₄ hinv₄
            (Or.inl rfl) (fun tk0 he => by injection he with he; exact he ▸ le_trans hn₃ htl))
        rw [List.length_map, hlen₁] at hp
        have hcs_new : ∀ u, u ∈ o.2 → n₀ ≤ u := fun u hu => by
          rw [hmap₁] at hu
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
          obtain ⟨j', hJ⟩ := AllFrom.of_mem 0 o.1 hall₁ z hz
          exact hJ.fin.new _ (Or.inl hJ.mem)
        rw [hcl] at hr₂
        refine ChainPost.pre hr₁ (fun u hu => (hlive u hu).1) (fun u hu => (hlive u hu).1) (M₂ := fun o' =>
          (cnt1 (S := spec lam K L) OracleName.rleaf zs.length o' +
            cnt1 (S := spec lam K L) OracleName.rnode zs.length o') +
          ((cnt1 (S := spec lam K L) OracleName.leaf (2 ^ w.depth0) o' +
            cnt1 (S := spec lam K L) OracleName.node (2 ^ w.depth0) o') +
          (MFb t (moreOf w.gr0) o' + MCh t (PhT.shr tl) s A W zs.length o'))) (fun o' => ?_)
          (ChainPost.pre hr₂ hcs_new hcs_new (fun _ => le_rfl)
            (ChainPost.pre hr₃ (fun _ hu => hu.elim) (fun _ hu => hu.elim) (fun _ => le_rfl)
            (ChainPost.pre (hT.run (R := NoTok) (e := zr))
              (fun u hu => hu ▸ le_trans hn₁ hrnew) (fun u hu => by
                rcases hu with rfl | hu
                · exact le_trans hn₁ hrnew
                · exact le_trans (le_trans hn₁ hr₂.length_le) (htt.le hu)) (fun o'' => Nat.add_le_add_right (count_osTry_le t (Kept.le_more hK) o'') _) hp)))
        have := MCh_join (L := L) t tl a A w W zs.length hk o'
        unfold MJ
        beta_reduce
        omega
      · -- a later shared round
        rename_i _ _ tk0 hk
        obtain ⟨hu0, hl0, _⟩ := h.shr tk0 rfl
        refine safe_withTree w.has0 w.depth0 _ _ d hd _ fun tr0 d₁ hd₁ hr₁ htt => ?_
        have hu0₁ : Untouched d₁ tk0 := hu0.grows hr₁.grows (fun x => x) (fun x => x)
        have hus : ∀ u ∈ rtL tr0, u < d₁.vals.length := fun u hu => htt.lt hu
        have htu : tk0 ∉ rtL tr0 := fun hu => absurd (htt.le hu) (Nat.not_le.mpr hu0.lt)
        have hbit : min p.sFS lam ≤ (d₁.val tk0).length := by
          rw [(hl0.grows hr₁.grows).2]
          exact min_le_right _ _
        have hpre : LoopPre p d₁ t tk0 ([] ++ (tr0.map TTree.root).toList) :=
          ⟨hus, htu, hu0₁.freeAt _, fun _ => hu0₁.freeAt _, hbit⟩
        refine safe_fbG (us := []) hpre w.gr0 _ _ fun nc dd bl tl d₂ hK hT => ?_
        have hd₂ := hpre.tidy hd₁ hT
        have htl : d₁.vals.length ≤ tl :=
          hT.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        have hinv₂ := ChainInv.after_f5 w h hd hd₁ hr₁ htt t (nc.toList ++ a0.nons) hd₂ hT bl
        have hn₁ : n₀ ≤ d₁.vals.length := le_trans h.le hr₁.length_le
        refine SafeO.mono (fun out d' hp => ?_) _ _
          (safe_chainT t cms xin depthReq n₀ s A W _ _ (i + 1) (PhT.shr tl) _ _ _ _ _ hd₂ hinv₂
            (Or.inl rfl) (fun tk he => by injection he with he; exact he ▸ le_trans hn₁ htl))
        rw [List.length_map] at hp
        refine ChainPost.pre hr₁ (fun _ hu => hu.elim) (fun _ hu => hu.elim) (M₂ := fun o' =>
          MFb t (moreOf w.gr0) o' + MCh t (PhT.shr tl) s A W zs.length o') (fun o' => ?_)
          (ChainPost.pre (hT.run (R := NoTok) (e := zr))
            (fun u hu => hu ▸ hsh tk0 rfl) (fun u hu => by
              rcases hu with rfl | hu
              · exact hsh _ rfl
              · exact le_trans h.le (htt.le hu)) (fun o'' => Nat.add_le_add_right (count_osTry_le t (Kept.le_more hK) o'') _) hp)
        have := MCh_f5 (L := L) t tk0 tl a A w W zs.length o'
        beta_reduce
        omega
      · -- a shared round without format
        rename_i ph _ _ hk hnl hns
        have hph : ph = PhT.first ∨ ph = PhT.aft := by
          cases ph with
          | first => exact Or.inl rfl
          | aft => exact Or.inr rfl
          | loc => exact (hnl rfl).elim
          | shr tk0 => exact (hns tk0 rfl).elim
        refine SafeO.mono (fun out d' hp => ?_) _ d
          (safe_chainT t cms xin depthReq n₀ s A W _ _ (i + 1) ph _ _ _ _ d hd
            (h.skip (fun tk0 he => hns tk0 he) w (blk0 lam K) (w.depthJ, w.depth0)) ?_ hsh)
        · rw [List.length_map] at hp
          exact ChainPost.pre (M₁ := zr) (Run.refl (Cc := NoTok) (Ch := NoTok) d)
            (fun _ hu => hu.elim) (fun _ hu => hu.elim)
            (fun o' => by rw [Nat.zero_add]; exact MCh_skip t ph a A w W zs.length hk hph o') hp
        · rcases hph with rfl | rfl
          · rcases hN with h0 | h0
            · rw [show jn PhT.first (r :: s) (a, A) = joins (r :: s) (a, A) from rfl,
                Num.joins_cons_sh A hk] at h0
              exact absurd h0 (by simp)
            · exact Or.inr (by rw [List.length_map]; exact h0)
          · exact Or.inl rfl

/-- Under the hypotheses of its statement, all chains of a batch obey the rules, from the start
(`Spec.safeChainT0`). -/
theorem safeChainT0 : Spec.safeChainT0 := by
  intro I X lam K L p Z t cms xin depthReq s A W embS embP σ0 zs n₀ d hd hn hall hnd hN
  have h := safe_chainT (p := p) t cms xin depthReq n₀ s A W embS embP 0 PhT.first
    σ0 zs ⟨[], [], none, [], []⟩ [] d hd
    ⟨hall, List.Forall₂.nil, hnd, hn, (fun tk0 he => by cases he), (fun _ => rfl)⟩
    hN (fun tk0 he => by cases he)
  rw [List.nil_append, MCh_first] at h
  exact h

/-- Under the hypotheses of its statement, one execution of the compiled prover obeys the rules
(`Spec.safeProveB`). -/
theorem safeProveB : Spec.safeProveB := safeProveB_of safeChainT0

/-- Under the hypotheses of its statement, the committer of the compiled scheme obeys the rules
(`Spec.safeCB`). -/
theorem safeCB : Spec.safeCB := safeCB_of safeProveB

/-- Under the hypotheses of its statement, the prover of the compiled scheme obeys the rules
(`Spec.safePB`). -/
theorem safePB : Spec.safePB := safePB_of safeProveB

end Compile.Batch.Disc
