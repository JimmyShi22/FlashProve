-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2ChainAll.lean: all rounds of the compiled prover, and with them the scheme's
committer and prover, are proved to obey `SafeO2` (CompileK/Defer2Safe.lean), each under the
hypotheses of its statement: a condition from which `advAlw_of_safeO2`, under its hypotheses, gives
the premise `AdvAlw` of the lemma on deferred programming of the random oracle (`Rom.Spec.defer2`,
CompileK/SpecDefer2.lean). The committer and the prover of the scheme with batches
(Compile/Batch/Star.lean: `Cp`, `Pp`: the base scheme's whole token programs) obey the discipline
with joint charges (`SafeO2`): `safeCB2` : `Spec.safeCB2`, `safePB2` : `Spec.safePB2`, proved
outright (no statement on one execution is assumed): from every state that is orderly both ways
(`TidyBoth`); for the prover: 2^depthReq slots and a key whose trees stand both ways (`IskOKB2`):
the inner vertices of the token trees (over prover messages) and of the request trees are charged to
both children (2 λ) (not the trees over encoded indices: their leaves' digests are shown and their
upper part is made of plain evaluations: nothing is gained or asked there), and whenever a right
child is shown its left neighbour is shown with it or was shown before.

The analogue for `SafeO2` (CompileK/Defer2Safe.lean) of Compile/Batch/DisciplineChainAll.lean.
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

Main names, each under the hypotheses of its statement:
  `safe2_chainT`: the induction over the rounds.
  `safeCB2`, `safePB2`: `Spec.safeCB2`, `Spec.safePB2` (CompileK/Defer2Star.lean): the committer,
    the prover.
In `Spec.safeCB2`, `Spec.safePB2` the rules are `rulesT` .. (maxMoreB W): the library's `rulesB`
with the further names for later tries below the scheme's own largest number.

The counts in this file's statements (`MCh`, `mProveB`) are those of Compile/Batch/, and their
lemmas are used unchanged.

Three things might be expected: roots and index leaves' digests are held by no vertex; the request
tree's sets are paths; the chains' tokens are no vertex's further tokens. Among the clauses in the
ends of this file's statements, each under its hypotheses, are these, which say of a set of tokens
that it is closed upwards, in (iii) but for shown tokens: (i) at the end of the chains (`chainT`;
`safe2_chainT`, `safeChainT02`), the set of a slot's tokens (`ClUp`, in `SlotF2`,
CompileK/Defer2Slot.lean); (ii) there too, for each leaf of a shared tree, its salt with the tokens
beside and on its way to the root (`TTUp`, CompileK/Defer2Tree.lean, in `Trees02`); (iii) at the end
of `Cp` and of `Pp` (`safeCB2`, `safePB2`), each pair of handles of a tree over an encoded index in
the key (`IskH`): the charged token is in the pair or shown (`UpClosed`, CompileK/Defer2Safe.lean,
in `IskOKB2`, which is a premise of `safePB2` too). None of these says of any token of its set that
no vertex holds it. `ChainInv2` is built in the proof of `safeChainT02`, `SlotF2` at the chains' end
in `safe2_chainT`; `SlotI2` at the start: CompileK/Defer2Init.lean (`safe2_initAll`); each from its
premises.

Limits: what it is not:
  (1) `AdvAlw` for the base scheme's challenger. `advAlw_of_safeO2` wants a property of (adversary,
    state); the challenger runs the prover behind a translation of token numbers.
  (2) So no bound: `Rom.Spec.defer2` is not applied here.
  (3) No ζ with a sharper hash term.
  (4) The base scheme only: the later storeys are not looked at: free empty slots, pruned sets of
    paths, seeds, the lazy prover.
(1) to (4) are said of this file and of what it imports. CompileK/Defer2Door.lean, which imports it,
goes on (its limits: that file's head), each lemma under the hypotheses of its statement:
`door_step` applies `safeCB2` and `safePB2`; `door_alw1` has `AdvAlw` (nothing asked at a halt) at
the challenger with the base prover; `door_rel_step`, `door_alw2` pass to the challenger with the
prover with free empty slots; `hopU2` applies `Rom.DeferTail2.defer2`.









Words used in this file. The discipline with joint charges, closed upwards, orderly both ways, both
ways: the paragraph "Words used in this file." of CompileK/Defer2Chain.lean's head holds here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Join
import CompileK.Defer2ChainSh
import CompileK.Defer2Prove
import Compile.Batch.DisciplineChainAll

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh
    length_afterMark cnt1 mem_evs_afterMark)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ} {Y : Type}

/-- Under `h`: the open ends of a slot are tokens of the execution: they have numbers from n₀ on. -/
theorem SlotI2.open_new {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT}
    {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotI2 p d n₀ done ph a0 j acc)
    {u : Tok} (hu : OpenOf ph acc u) : n₀ ≤ u := by
  cases ph with
  | shr tk0 =>
    rcases hu with rfl | rfl
    · exact h.fin.new _ (Or.inl h.cap.2.2.2.2.1)
    · exact h.fin.new _ (Or.inr (Or.inl h.cap.2.2.2.2.2.1))
  | first => exact (show u = acc.tk from hu) ▸ h.fin.new _ (Or.inl h.cap.2.2)
  | loc => exact (show u = acc.tk from hu) ▸ h.fin.new _ (Or.inl h.cap.2.2)
  | aft => exact (show u = acc.tk from hu) ▸ h.fin.new _ (Or.inl h.cap.2.2)

theorem SlotI2.live_new {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {ph : PhT}
    {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotI2 p d n₀ done ph a0 j acc) :
    n₀ ≤ live ph acc :=
  h.fin.new _ (Or.inl h.cap.mem)

/-- what the chains leave behind -/
def ChainPost2 (p : Params) (mG n₀ : ℕ) (dn : List (ℕ × ℕ)) (M : OracleName → ℕ) (d : DSt (spec lam K L))
    (out : List (SlotAcc lam K Y) × Acc0) (d' : DSt (spec lam K L)) : Prop :=
  TidyBoth p mG d' ∧
  Run (fun u => n₀ ≤ u) (fun u => n₀ ≤ u) NoTok zr M d d' ∧
  AllFrom (fun j acc => ∃ Op, SlotF2 d' n₀ dn Op out.2 j acc) 0 out.1 ∧
  Trees02 d' n₀ dn out.2.trees

/-- a run before the rest of the chains -/
theorem ChainPost2.pre {n₀ : ℕ} {dn : List (ℕ × ℕ)} {M M₁ M₂ : OracleName → ℕ}
    {d d₁ d' : DSt (spec lam K L)} {out : List (SlotAcc lam K Y) × Acc0} {Cc Ch : Tok → Prop}
    (hr : Run Cc Ch NoTok zr M₁ d d₁) (hCc : ∀ u, Cc u → n₀ ≤ u) (hCh : ∀ u, Ch u → n₀ ≤ u)
    (hM : ∀ o, M₁ o + M₂ o ≤ M o) (h : ChainPost2 p mG n₀ dn M₂ d₁ out d') :
    ChainPost2 p mG n₀ dn M d out d' := by
  have h1 : Run (fun u => n₀ ≤ u) (fun u => n₀ ≤ u) NoTok zr M₁ d d₁ :=
    hr.mono (fun u hu => Or.inl (hCc u hu))
      (fun u hu => Or.inl (hCh u hu)) (fun _ hu => hu.elim) (fun _ => le_rfl) (fun _ => le_rfl)
  exact ⟨h.1,
    h1.trans h.2.1 (fun _ hu => Or.inl hu) (fun _ hu => Or.inl hu)
      (fun _ hu => hu.elim) (fun _ => le_rfl) hM,
    h.2.2⟩

theorem safe2_chainT (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq n₀ : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (q : OPos s) → OSym s q → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (done : List (ℕ × ℕ)) (d : DSt (spec lam K L)),
      TidyBoth p mG d → ChainInv2 p d n₀ done ph a0 zs →
      (jn ph s A = 0 ∨ zs.length = 2 ^ depthReq) →
      (∀ tk0, ph = PhT.shr tk0 → n₀ ≤ tk0) → maxMore s A W ≤ mG →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (chainT p.sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0) d
        (ChainPost2 p mG n₀ (done ++ depthsOf s A W) (MCh t ph s A W zs.length) d)
  | [], _, _, _, _, _, ph, _, zs, a0, done, d, hd, h, _, _, _ => by
      show ChainPost2 p mG n₀ (done ++ []) _ d (zs.map Prod.snd, a0) d
      rw [List.append_nil]
      exact ⟨hd, Run.refl d,
        AllFrom.map Prod.snd (fun j z hz => ⟨_, hz.fin⟩) 0 zs h.slots, h.trees0⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, done, d, hd, h, hN, hsh, hmx => by
      have hmx' : max (max (moreOf w.grJ) (moreOf w.gr0)) (maxMore s A W) ≤ mG := hmx
      have hmJ : moreOf w.grJ ≤ mG := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hmx'
      have hm0 : moreOf w.gr0 ≤ mG := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hmx'
      have hmS : maxMore s A W ≤ mG := le_trans (le_max_right _ _) hmx'
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
        refine SafeO2.bind _ _ d
          (SafeO2.mono ?_ _ d
            (safe2_eachLo t cms xin a w _ _ i ph n₀ done a0 hmJ zs 0 d hd h.le h.slots h.nodup))
        rintro zs' d₁ ⟨hd₁, hr₁, hall₁, hnd₁, _, hlen₁, hj₁⟩
        have hinv₁ := ChainInv2.of_eachLo hall₁ hnd₁
          (h.trees0.keeps hr₁ (fun u hu => (hlive u hu).2) hj₁ fun _ hu => hu.elim)
          (le_trans h.le hr₁.length_le) h.req
        refine SafeO2.mono (fun out d' hp => ?_) _ d₁
          (safe2_chainT t cms xin depthReq n₀ s A W _ _ (i + 1) ph.afterLo _ zs' _ _ d₁ hd₁ hinv₁
            (by rw [Num.jn_afterLo A hk ph, hlen₁]; exact hN)
            (fun tk0 he => by cases ph <;> cases he) hmS)
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
        refine SafeO2.bind _ _ d
          (SafeO2.mono ?_ _ d (safe2_joinM t a w _ _ i n₀ done a0 zs 0 d hd h.le h.slots h.nodup))
        rintro o d₁ ⟨hd₁, hr₁, hall₁, hmap₁, hnd₁, _, hlen₁, hj₁⟩
        have hcl : o.2.length = zs.length := by rw [hmap₁, List.length_map, hlen₁]
        have hrdy : Ready lam d₁ o.2 := ⟨fun c hc => by
          rw [hmap₁] at hc
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hc
          obtain ⟨j', hJ⟩ := AllFrom.of_mem 0 o.1 hall₁ z hz
          exact ⟨hJ.unt, hJ.len⟩, hnd₁⟩
        have hn₁ : n₀ ≤ d₁.vals.length := le_trans h.le hr₁.length_le
        refine SafeO2.bind _ _ d₁
          (SafeO2.mono ?_ _ d₁ (safe2_reqT depthReq o.2 d₁ hd₁ (hcl.trans hlenN) hrdy))
        rintro rq d₂ ⟨hd₂, hr₂, hPA, hC, hroot, hrlen, hrnew, hsePA, hRPA⟩
        refine safe2_withTree w.has0 w.depth0 _ _ d₂ hd₂ _ fun tr0 d₃ hd₃ hr₃ htt => ?_
        have hroot₃ : Untouched d₃ rq.root := hroot.grows hr₃.grows (fun x => x) (fun x => x)
        have hus : ∀ u ∈ rtL tr0, u < d₃.vals.length := fun u hu => htt.lt hu
        have htu : rq.root ∉ rtL tr0 := fun hu => absurd (htt.le hu) (Nat.not_le.mpr hroot.lt)
        have hbit : min p.sFS lam ≤ (d₃.val rq.root).length := by
          rw [(hrlen.grows hr₃.grows).2]
          exact min_le_right _ _
        have hpre : LoopPre p d₃ t rq.root ([] ++ (tr0.map TTree.root).toList) :=
          ⟨hus, htu, hroot₃.freeAt _, fun _ => hroot₃.freeAt _, hbit⟩
        refine safe2_fbG (us := []) hpre w.gr0 (fun g hg => by rw [hg] at hm0; exact hm0)
          _ _ fun nc dd bl tl d₄ hK hT => ?_
        have hd₄ := hpre.tidy2 (le_trans (Kept.le_more hK) hm0) hd₃ hT
        have htl : d₃.vals.length ≤ tl :=
          hT.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        have hinv₄ := ChainInv2.after_join (p := p) w hall₁ hmap₁ hnd₁ hn₁ (h.req (Or.inr rfl))
          (h.trees0.keeps hr₁ (fun u hu => (hlive u hu).2) hj₁ fun _ hu => hu.elim) hd₁ hd₂ hr₂ hPA
          hC hroot hrnew hsePA hRPA hd₃ hr₃ htt t (nc.toList ++ a0.nons) hd₄ hT bl
        have hn₃ : n₀ ≤ d₃.vals.length := le_trans (le_trans hn₁ hr₂.length_le) hr₃.length_le
        refine SafeO2.mono (fun out d' hp => ?_) _ _
          (safe2_chainT t cms xin depthReq n₀ s A W _ _ (i + 1) (PhT.shr tl) _ _ _ _ _ hd₄ hinv₄
            (Or.inl rfl) (fun tk0 he => by injection he with he; exact he ▸ le_trans hn₃ htl) hmS)
        rw [List.length_map, hlen₁] at hp
        have hcs_new : ∀ u, u ∈ o.2 → n₀ ≤ u := fun u hu => by
          rw [hmap₁] at hu
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hu
          obtain ⟨j', hJ⟩ := AllFrom.of_mem 0 o.1 hall₁ z hz
          exact hJ.fin.new _ (Or.inl hJ.mem)
        rw [hcl] at hr₂
        refine ChainPost2.pre hr₁ (fun u hu => (hlive u hu).1) (fun u hu => (hlive u hu).1) (M₂ := fun o' =>
          (cnt1 (S := spec lam K L) OracleName.rleaf zs.length o' +
            cnt1 (S := spec lam K L) OracleName.rnode zs.length o') +
          ((cnt1 (S := spec lam K L) OracleName.leaf (2 ^ w.depth0) o' +
            cnt1 (S := spec lam K L) OracleName.node (2 ^ w.depth0) o') +
          (MFb t (moreOf w.gr0) o' + MCh t (PhT.shr tl) s A W zs.length o'))) (fun o' => ?_)
          (ChainPost2.pre hr₂ hcs_new hcs_new (fun _ => le_rfl)
            (ChainPost2.pre hr₃ (fun _ hu => hu.elim) (fun _ hu => hu.elim) (fun _ => le_rfl)
            (ChainPost2.pre (hT.run (R := NoTok) (e := zr))
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
        refine safe2_withTree w.has0 w.depth0 _ _ d hd _ fun tr0 d₁ hd₁ hr₁ htt => ?_
        have hu0₁ : Untouched d₁ tk0 := hu0.grows hr₁.grows (fun x => x) (fun x => x)
        have hus : ∀ u ∈ rtL tr0, u < d₁.vals.length := fun u hu => htt.lt hu
        have htu : tk0 ∉ rtL tr0 := fun hu => absurd (htt.le hu) (Nat.not_le.mpr hu0.lt)
        have hbit : min p.sFS lam ≤ (d₁.val tk0).length := by
          rw [(hl0.grows hr₁.grows).2]
          exact min_le_right _ _
        have hpre : LoopPre p d₁ t tk0 ([] ++ (tr0.map TTree.root).toList) :=
          ⟨hus, htu, hu0₁.freeAt _, fun _ => hu0₁.freeAt _, hbit⟩
        refine safe2_fbG (us := []) hpre w.gr0 (fun g hg => by rw [hg] at hm0; exact hm0)
          _ _ fun nc dd bl tl d₂ hK hT => ?_
        have hd₂ := hpre.tidy2 (le_trans (Kept.le_more hK) hm0) hd₁ hT
        have htl : d₁.vals.length ≤ tl :=
          hT.tail_ge tl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        have hinv₂ := ChainInv2.after_f5 w h hd hd₁ hr₁ htt t (nc.toList ++ a0.nons) hd₂ hT bl
        have hn₁ : n₀ ≤ d₁.vals.length := le_trans h.le hr₁.length_le
        refine SafeO2.mono (fun out d' hp => ?_) _ _
          (safe2_chainT t cms xin depthReq n₀ s A W _ _ (i + 1) (PhT.shr tl) _ _ _ _ _ hd₂ hinv₂
            (Or.inl rfl) (fun tk he => by injection he with he; exact he ▸ le_trans hn₁ htl) hmS)
        rw [List.length_map] at hp
        refine ChainPost2.pre hr₁ (fun _ hu => hu.elim) (fun _ hu => hu.elim) (M₂ := fun o' =>
          MFb t (moreOf w.gr0) o' + MCh t (PhT.shr tl) s A W zs.length o') (fun o' => ?_)
          (ChainPost2.pre (hT.run (R := NoTok) (e := zr))
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
        refine SafeO2.mono (fun out d' hp => ?_) _ d
          (safe2_chainT t cms xin depthReq n₀ s A W _ _ (i + 1) ph _ _ _ _ d hd
            (h.skip (fun tk0 he => hns tk0 he) w (blk0 lam K) (w.depthJ, w.depth0)) ?_ hsh hmS)
        · rw [List.length_map] at hp
          exact ChainPost2.pre (M₁ := zr) (Run.refl (Cc := NoTok) (Ch := NoTok) d)
            (fun _ hu => hu.elim) (fun _ hu => hu.elim)
            (fun o' => by rw [Nat.zero_add]; exact MCh_skip t ph a A w W zs.length hk hph o') hp
        · rcases hph with rfl | rfl
          · rcases hN with h0 | h0
            · rw [show jn PhT.first (r :: s) (a, A) = joins (r :: s) (a, A) from rfl,
                Num.joins_cons_sh A hk] at h0
              exact absurd h0 (by simp)
            · exact Or.inr (by rw [List.length_map]; exact h0)
          · exact Or.inl rfl

/-- Under the hypotheses of its statement (`Spec.safeChainT02`, CompileK/Defer2Prove.lean), all
chains of a batch obey the rules, from the start. -/
theorem safeChainT02 : Spec.safeChainT02 := by
  intro I X lam K L p mG Z t cms xin depthReq s A W embS embP σ0 zs n₀ d hd hn hall hnd hN hmx
  have h := safe2_chainT (p := p) t cms xin depthReq n₀ s A W embS embP 0 PhT.first σ0 zs
    ⟨[], [], none, [], []⟩ [] d hd
    ⟨hall, List.Forall₂.nil, hnd, hn, (fun tk0 he => by cases he), (fun _ => rfl)⟩ hN
    (fun tk0 he => by cases he) hmx
  rw [List.nil_append, MCh_first] at h
  exact h

/-- the empty state is orderly both ways: so safeCB2 starts somewhere -/
theorem tidyBoth_init : TidyBoth (K := K) (L := L) (lam := lam) p mG (DSt.init _) :=
  ⟨TidyO.init, fun _ h => absurd h List.not_mem_nil⟩

/-- Under the hypotheses of its statement (`Spec.safeProveB2`, CompileK/Defer2Star.lean), one
execution of the compiled prover obeys the rules. -/
theorem safeProveB2 : Spec.safeProveB2 := safeProveB2_of safeChainT02

/-- Under the hypotheses of its statement (`Spec.safeCB2`, CompileK/Defer2Star.lean), the committer
of the scheme with batches obeys the rules. -/
theorem safeCB2 : Spec.safeCB2 := safeCB2_of safeProveB2

/-- Under the hypotheses of its statement (`Spec.safePB2`, CompileK/Defer2Star.lean), the prover of
the scheme with batches obeys the rules. -/
theorem safePB2 : Spec.safePB2 := safePB2_of safeProveB2


end Compile.Batch.Disc
