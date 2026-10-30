-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Late2b.lean: the chains of a batch, continued (Compile/Batch/Late2.lean): the shared
rounds, with proof-of-work bits or without, and every shape (`late_chainT`: from `RoundsQueryLayout.OKG` and a
coherent annotation). `Late`: Rom/DeferLate.lean; `skB`: Compile/Batch/Mirror.lean (words of this
library: lean/GLOSSARY.md).

Notation: in Compile/Batch/Late2.lean: `curOf ph acc`: the token to which the next query of the slot
is charged; `actL ph zs`: the active tokens; `Fr Act n Γ Γ'`: below n and off the active tokens, Γ'
records nothing beyond Γ but closures without data; `ChainStmt s A W`: the statement for one shape;
`Base Γ u` (Compile/Batch/Late1.lean): only closures without data are recorded for the token u; in
Compile/Batch/Prover.lean: `hear`: a slot receives a shared verifier message; `Acc0`: what the
shared part has accumulated; `Head.f4`, `Head.f5` (Compile/Batch/Oracles.lean): (F4): the joining
round; (F5): a later shared round; the letters `t`, `cms`, `sMT`, `depthReq`, `a0`: the legend of
Compile/Batch/Late2.lean.
-/
import Compile.Batch.Late2

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

section Steps
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

theorem map_hearL {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (zs : List (SlotSt lam K Y (r :: s))) :
    (zs.map fun z => ((none : Option (Rho (r :: s))), z.2)).map (hearL bl noted) =
      (zs.map (hear w bl noted)).map fun z => ((none : Option (Rho s)), z.2) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun z _ => rfl

theorem map_cur_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (ph : PhT) (zs : List (SlotSt lam K Y (r :: s))) :
    (zs.map (hear w bl noted)).map (fun z => curOf ph z.2) = zs.map fun z => curOf ph z.2 := by
  rw [List.map_map]
  exact List.map_congr_left fun z _ => by cases ph <;> rfl

/-- the queries of one round record closures at the charged token alone, which is active -/
theorem fr_setFb {C P : Type} {Act : List Tok} {n : ℕ} (Γ : Cx lam K L) {u : Tok} (hu : u ∈ Act)
    (gr : Option (GrW C P)) (i : ℕ) (hd : List Bits → Bits → Head lam X) (has : Bool) (rtAt : ℕ)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) (m : ℕ) :
    Fr Act n Γ (setFb gr t [u] i hd has rtAt emb α m Γ) := fun v _ hva o pt hp => by
  rw [setFb_ne_tok t u i hd has rtAt gr emb α m Γ fun e => hva (by rw [e]; exact hu)] at hp
  exact Or.inl hp

theorem chain_skip {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh)
    (ih : ChainStmt (L := L) sMT t cms xin depthReq s A W)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT)
    (hph : ph = .first ∨ ph = .aft) (m0 : a.M0) (k0 : a.kind.Sh r.Chal → SStrat s A)
    (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0) (n : ℕ) (Γ : Cx lam K L) (hF : Fut n Γ)
    (hpw : (actL ph zs).Pairwise (fun u v : ℕ => u < v))
    (hact : ∀ a' ∈ actL ph zs, n > a' ∧ Base Γ a') (hlen : HasSh s A → zs.length = 2 ^ depthReq)
    (hreq : ph = .first ∨ ph = .loc → a0.req = none) :
    Late (ChainPost t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 n Γ) n Γ
      (chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0)
      (skB sMT t depthReq (r :: s) (a, A) (w, W) ph none
        (zs.map fun z => ((none : Option (Rho (r :: s))), z.2)) a0) := by
  rw [chainT_skip sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph hph,
    skB_skip sMT t depthReq a A w W none _ a0 hk ph hph, map_hearL w]
  have hactE : actL ph (zs.map (hear w (blk0 lam K) false)) = actL ph zs := by
    unfold actL; rw [map_cur_hear]
  refine Late.mono
    (ih (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph
      (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (zs.map (hear w (blk0 lam K) false))
      { a0 with trees := a0.trees ++ [none] } n Γ hF (by rw [hactE]; exact hpw)
      (by rw [hactE]; exact hact) (fun h => by rw [List.length_map]; exact hlen h) hreq)
    fun n' Γ' out out' hpost => ?_
  obtain ⟨e0, b1, hF', hFr', new0, ntr0, nN0, nD0, e1, e2, hn0, e3, e4, hD0, hrq, hall'⟩ := hpost
  rw [hactE] at hFr'
  refine ⟨e0, b1, hF', hFr', new0, none :: ntr0, nN0, nD0, e1, by rw [e2]; simp,
    hn0, e3, e4, hD0, ?_, ?_⟩
  · rcases hph with rfl | rfl <;> exact hrq
  · rw [List.forall₂_map_left_iff] at hall'
    exact hall'.imp fun z acc' hS => slotK_skip t cms xin a A w W hk embS embP i ph hph m0 k0 hS

theorem chain_shr {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh) (hco : a.Coherent) (hw : w.OKG)
    (ih : ChainStmt (L := L) sMT t cms xin depthReq s A W)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (tk0 : ℕ) (m0 : a.M0)
    (k0 : a.kind.Sh r.Chal → SStrat s A) (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0) (n : ℕ)
    (Γ : Cx lam K L) (hF : Fut n Γ) (hpw : (actL (.shr tk0) zs).Pairwise (fun u v : ℕ => u < v))
    (hact : ∀ a' ∈ actL (.shr tk0) zs, n > a' ∧ Base Γ a')
    (hlen : HasSh s A → zs.length = 2 ^ depthReq) :
    Late (ChainPost t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i
        (.shr tk0) (m0, k0) zs a0 n Γ)
      n Γ
      (chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i (.shr tk0) (m0, k0) zs a0)
      (skB sMT t depthReq (r :: s) (a, A) (w, W) (.shr tk0) none
        (zs.map fun z => ((none : Option (Rho (r :: s))), z.2)) a0) := by
  rw [chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk,
    skB_shr sMT t depthReq a A w W none _ a0 hk]
  have htk := hact tk0 (List.mem_append.2 (Or.inr (by simp)))
  have hcs : ∀ c ∈ zs.map (fun z => curOf (.shr tk0) z.2), c < tk0 ∧ Base Γ c := fun c hc =>
    ⟨(List.pairwise_append.1 hpw).2.2 c hc tk0 (by simp),
      (hact c (List.mem_append.2 (Or.inl hc))).2⟩
  unfold tree0
  refine late_withTree sMT w.has0 w.depth0 _ hF fun n3 Γ3 tr0 hs0 a1 hF3 fr3 hT3 => ?_
  refine late_fbG w w.gr0 t i tk0 [] (tr0.map TTree.root) _ _ (fun α => embP (.inl (.inl α)))
    (a.pl0 m0) w.has0 (by rw [Option.isSome_map, hs0]) fun nc dd bl tl hK htl hdd => ?_
  rw [map_hearL w]
  set Γs := setFb w.gr0 t [tk0] i (fun _ => Head.f5) w.has0 0 (fun α => embP (.inl (.inl α)))
    (a.pl0 m0) (nc.getD 0) Γ3 with hΓs
  have hsne : ∀ v, v ≠ tk0 → Γs v = Γ3 v := fun v hv => setFb_ne_tok _ _ _ _ _ _ _ _ _ _ Γ3 hv
  have hactE : actL (.shr tl) (zs.map (hear w bl false)) =
      zs.map (fun z => curOf (.shr tk0) z.2) ++ [tl] := by
    unfold actL
    rw [map_cur_hear]
    rfl
  have hF4 : Fut (tl + 1) Γs :=
    fut_setFb _ _ _ _ _ _ _ _ _ _ hF3 (by have := htk.1; omega) (by omega)
  refine Late.mono
    (ih (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (.shr tl)
      (k0 (a.kind.shOf (w.chal bl))) (zs.map (hear w bl false))
      { a0 with
        trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
        nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
      (tl + 1) _ hF4 ?_ ?_ (fun h => by rw [List.length_map]; exact hlen h) (fun h => by simp at h))
    fun n' Γ' out out' hpost => ?_
  · rw [hactE, List.pairwise_append]
    refine ⟨(List.pairwise_append.1 hpw).1, by simp, fun c hc v hv => ?_⟩
    rw [List.mem_singleton.1 hv]
    have := (hcs c hc).1
    have := htk.1
    omega
  · rw [hactE]
    intro a' ha'
    rcases List.mem_append.1 ha' with h | h
    · have h1 := (hcs a' h).1
      have h2 := htk.1
      exact ⟨by omega, ((hcs a' h).2.congr (fr3 a' (by omega))).congr (hsne a' (Nat.ne_of_lt h1))⟩
    · rw [List.mem_singleton.1 h]
      refine ⟨by omega, cov_of_none fun o => ?_⟩
      show Γs tl o = none
      rw [hsne tl (by have := htk.1; omega)]
      exact hF3 tl htl o
  · obtain ⟨e0, b1, hF', hFr', new0, ntr0, nN0, nD0, e1, e2, hn0, e3, e4, hD0, hrq, hall'⟩ := hpost
    rw [hactE] at hFr'
    have hFr04 : Fr (actL (.shr tk0) zs) n Γ Γs :=
      (Fr.of_ext (Ext.of_frame fr3) _).trans
        (fr_setFb t (n := n) Γ3 (List.mem_append.2 (Or.inr (by simp))) _ _ _ _ _ _ _ _)
        le_rfl fun _ h => Or.inl h
    refine ⟨e0, by omega, hF', hFr04.trans hFr' (by omega) (fun a' ha' => ?_), tl :: new0,
      tr0 :: ntr0, nc.toList ++ nN0, nD0 ++ dd, by rw [e1]; simp, by rw [e2]; simp,
      fun u hu => ?_, by rw [e3, List.reverse_append, toList_reverse]; simp, by rw [e4]; simp,
      fun u hu => ?_, hrq, ?_⟩
    · rcases List.mem_append.1 ha' with h | h
      · exact Or.inl (List.mem_append.2 (Or.inl h))
      · rw [List.mem_singleton.1 h]; exact Or.inr (by omega)
    · rcases List.mem_cons.1 hu with h | h
      · rw [h]; omega
      · have := hn0 u h; omega
    · rcases List.mem_append.1 hu with h | h
      · exact ⟨by have := (hD0 u h).1; omega, (hD0 u h).2⟩
      · have d1 : @LE.le ℕ _ n3 u := (hdd u h).1
        have d2 : @LT.lt ℕ _ u tl := (hdd u h).2
        have h0 := htk.1
        refine ⟨by omega,
          Cov.fr (cov_of_none fun o => ?_) hFr' (by omega) (fun hm => ?_) (baseUp_base u)⟩
        · show Γs u o = none
          rw [hsne u (by omega)]
          exact hF3 u d1 o
        · rcases List.mem_append.1 hm with h' | h'
          · have := (hcs u h').1
            omega
          · have h'' : @Eq ℕ u tl := List.mem_singleton.1 h'
            omega
    · rw [List.forall₂_map_left_iff] at hall'
      refine (forall₂_mem hall').imp fun z acc' hzS => ?_
      obtain ⟨hz, hS⟩ := hzS
      have hzc := (hcs _ (List.mem_map.2 ⟨z, hz, rfl⟩)).1
      refine slotK_shr t cms xin a A w W hk hco hw embS embP i tk0 m0 k0 (n := n) (n2 := n)
        (n3 := n3) hK.1 hS hFr' (by omega) (by omega)
        (hT3.congr fun u h1 _ => hsne u (by have := htk.1; omega)) (fun a' ha' => ?_)
        (fun P hP hPc =>
            cov_setFb_of _ _ _ _ _ _ _ _ _ _ (Base.cov (htk.2.congr (fr3 tk0 htk.1)) hP) hPc)
          htk.1 (fun hm => ?_) (fun e => ?_) (fun u hu => ?_)
      · rcases List.mem_append.1 ha' with h | h
        · have := (hcs a' h).1
          have := htk.1
          exact Or.inl (by omega)
        · rw [List.mem_singleton.1 h]; exact Or.inr htl
      · rcases List.mem_append.1 hm with h | h
        · have := (hcs _ h).1; omega
        · have : tk0 = tl := List.mem_singleton.1 h
          have := htk.1
          omega
      · have h' : curOf (.shr tk0) z.2 = tk0 := e
        omega
      · rcases List.mem_cons.1 hu with h | h
        · rw [h]; omega
        · have := hn0 u h; omega

theorem chain_join {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh) (hco : a.Coherent) (hw : w.OKG)
    (ih : ChainStmt (L := L) sMT t cms xin depthReq s A W)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (m0 : a.M0)
    (k0 : a.kind.Sh r.Chal → SStrat s A) (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0) (n : ℕ)
    (Γ : Cx lam K L) (hF : Fut n Γ) (hpw : (actL .loc zs).Pairwise (fun u v : ℕ => u < v))
    (hact : ∀ a' ∈ actL .loc zs, n > a' ∧ Base Γ a') (hlen : zs.length = 2 ^ depthReq) :
    Late (ChainPost t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) zs a0 n Γ)
      n Γ (chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) zs a0)
      (skB sMT t depthReq (r :: s) (a, A) (w, W) .loc none
        (zs.map fun z => ((none : Option (Rho (r :: s))), z.2)) a0) := by
  rw [chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk,
    skB_join sMT t depthReq a A w W none _ a0 hk]
  have hactE0 : actL .loc zs = zs.map fun z => z.2.tk := by simp [actL, curOf]
  rw [hactE0] at hpw hact
  refine Late.bind
    (late_joinM sMT t a w _ _ i n zs n Γ le_rfl hF hpw fun z hz =>
      hact _ (List.mem_map.2 ⟨z, hz, rfl⟩))
    fun n1 Γ1 o o' h1 => ?_
  obtain ⟨zs1', cs'⟩ := o'
  obtain ⟨e1', e2', e3', a1, hF1, fr1, hpw1, hx1, hallJ⟩ := h1
  obtain rfl : zs1' = o.1.map fun x => ((none : Option (Rho (r :: s))), x.2) := e1'
  obtain rfl : cs' = o.2 := e2'
  have hcs : ∀ c ∈ o.2, n ≤ c ∧ n1 > c ∧ Base Γ1 c := fun c hc => by
    rw [e3'] at hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    exact hx1 x hx
  refine Late.bind
    (late_reqT depthReq o.2 hF1 (fun c hc => (hcs c hc).2.1)
      (by rw [e3', List.length_map, ← hallJ.length_eq]; exact hlen))
    fun n2 Γ2 rq rq' h2 => ?_
  obtain ⟨rfl, a2, hF2, hE2, hS2, hD2⟩ := h2
  unfold tree0
  refine late_withTree sMT w.has0 w.depth0 _ hF2 fun n3 Γ3 tr0 hs0 a3 hF3 fr3 hT3 => ?_
  refine late_fbG w w.gr0 t i rq.root [] (tr0.map TTree.root) _ _ (fun α => embP (.inl (.inl α)))
    (a.pl0 m0) w.has0 (by rw [Option.isSome_map, hs0]) fun nc dd bl tl hK htl hdd => ?_
  rw [map_hearL w]
  obtain ⟨hr1, hr2, hrB⟩ := hD2 _ (sized_root depthReq rq.levels hS2)
  set root : ℕ := rq.root with hroot
  have hr1' : n1 ≤ root := hr1
  have hr2' : n2 > root := hr2
  set Γs := setFb w.gr0 t [root] i (fun _ => Head.f4 cms) w.has0 0 (fun α => embP (.inl (.inl α)))
    (a.pl0 m0) (nc.getD 0) Γ3 with hΓs
  have hsne : ∀ v, v ≠ root → Γs v = Γ3 v := fun v hv => setFb_ne_tok _ _ _ _ _ _ _ _ _ _ Γ3 hv
  have hactE : actL (.shr tl) (o.1.map (hear w bl true)) = o.2 ++ [tl] := by
    unfold actL
    rw [map_cur_hear, e3']
    rfl
  have hF4 : Fut (tl + 1) Γs := fut_setFb _ _ _ _ _ _ _ _ _ _ hF3 (by omega) (by omega)
  have hE14 : Ext n1 Γ1 Γs :=
    (hE2.trans (Ext.of_frame fr3) a2).trans (n' := n1)
      (Ext.of_frame fun u hu => hsne u (by omega)) le_rfl
  refine Late.mono
    (ih (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (.shr tl)
      (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
      { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
        nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
      (tl + 1) _ hF4 ?_ ?_ (fun _ => by rw [List.length_map, ← hallJ.length_eq]; exact hlen)
      (fun h => by simp at h))
    fun n' Γ' out out' hpost => ?_
  · rw [hactE, List.pairwise_append]
    refine ⟨by rw [e3']; exact hpw1, by simp, fun c hc v hv => ?_⟩
    rw [List.mem_singleton.1 hv]
    have := (hcs c hc).2.1
    omega
  · rw [hactE]
    intro a' ha'
    rcases List.mem_append.1 ha' with h | h
    · have h1 := (hcs a' h).2.1
      exact ⟨by omega, (hcs a' h).2.2.ext hE14 h1⟩
    · rw [List.mem_singleton.1 h]
      refine ⟨by omega, cov_of_none fun o' => ?_⟩
      show Γs tl o' = none
      rw [hsne tl (by omega)]
      exact hF3 tl htl o'
  · obtain ⟨e0, b1, hF', hFr', new0, ntr0, nN0, nD0, e1, e2, hn0, e3, e4, hD0, hrq, hall'⟩ := hpost
    rw [hactE] at hFr'
    have hrq' : out.2.req = some rq := hrq
    have hFr01 : Fr (actL .loc zs) n Γ Γ1 := fun u hu hua o' pt hp => Or.inl (by
      rw [← fr1 u hu (by rw [← hactE0]; exact hua)]; exact hp)
    have hnotA : ∀ u : ℕ, n1 ≤ u → n2 > u → u ∉ o.2 ++ [tl] := fun u h1 h2 hm => by
      rcases List.mem_append.1 hm with h | h
      · have := (hcs u h).2.1; omega
      · have : u = tl := List.mem_singleton.1 h
        omega
    refine ⟨e0, by omega, hF',
      (hFr01.trans (Fr.of_ext hE14 []) a1 (fun _ h => absurd h (by simp))).trans
        hFr' (by omega) (fun a' ha' => ?_),
      tl :: new0, tr0 :: ntr0, nc.toList ++ nN0, nD0 ++ dd, by rw [e1]; simp, by rw [e2]; simp,
      fun u hu => ?_, by rw [e3, List.reverse_append, toList_reverse]; simp, by rw [e4]; simp,
      fun u hu => ?_, ?_, ?_⟩
    · rcases List.mem_append.1 ha' with h | h
      · exact Or.inr (hcs a' h).1
      · rw [List.mem_singleton.1 h]; exact Or.inr (by omega)
    · rcases List.mem_cons.1 hu with h | h
      · rw [h]; omega
      · have := hn0 u h; omega
    · rcases List.mem_append.1 hu with h | h
      · exact ⟨by have := (hD0 u h).1; omega, (hD0 u h).2⟩
      · have d1 : @LE.le ℕ _ n3 u := (hdd u h).1
        have d2 : @LT.lt ℕ _ u tl := (hdd u h).2
        refine ⟨by omega,
          Cov.fr (cov_of_none fun o' => ?_) hFr' (by omega) (fun hm => ?_) (baseUp_base u)⟩
        · show Γs u o' = none
          rw [hsne u (by omega)]
          exact hF3 u d1 o'
        · rcases List.mem_append.1 hm with h' | h'
          · have := (hcs u h').2.1
            omega
          · have h'' : @Eq ℕ u tl := List.mem_singleton.1 h'
            omega
    · intro rq2 hq
      obtain rfl : rq = rq2 := Option.some.inj (hrq'.symm.trans hq)
      refine ⟨hS2, by show n ≤ root; omega, fun u hu hne => ?_⟩
      obtain ⟨u1, u2, u3⟩ := hD2 u hu
      exact Cov.fr ((u3.congr (fr3 u u2)).congr (hsne u hne)) hFr' (by omega)
        (hnotA u u1 u2) (baseUp_base u)
    · have hT0 : T0of .loc out.2.req (tl :: new0) = root :: tl :: new0 := by rw [hrq']; rfl
      rw [hT0]
      rw [List.forall₂_map_left_iff] at hall'
      refine forall₂_comp (fun z z1 acc' hzf hS => ?_) (forall₂_mem hallJ) hall'
      obtain ⟨hz, hf⟩ := hzf
      have hFr2 := hFr'
      rw [e3'] at hFr2
      refine slotK_join t cms xin a A w W hk hco hw embS embP i m0 k0 (n2 := n2) (n3 := n3)
        (n4 := tl + 1) hK.1 hf hE14 hS hFr2 a3 htl rfl (hT3.congr fun u h1 _ => hsne u (by omega))
        (fun a' ha' => ⟨(hcs a' (by rw [e3']; exact ha')).1, (hcs a' (by rw [e3']; exact ha')).2.1⟩)
        (fun P hP hPc =>
          cov_setFb_of _ _ _ _ _ _ _ _ _ _ (Base.cov (hrB.congr (fr3 root hr2')) hP) hPc)
        hr1' hr2' (hact _ (List.mem_map.2 ⟨z, hz, rfl⟩)).1 hn0

end Steps

/-! ## Every shape -/

theorem kind_cases (k : Kind) : k = .lo ∨ k = .sh := by cases k <;> simp

/-- For `RoundsQueryLayout.OKG` and a coherent annotation, `ChainStmt`: under its hypotheses all chains of a
batch and the hashing of all chains of a batch in `LStep`, without points (`skB`) are related by
`Late`, with `ChainPost` at the end. -/
theorem late_chainT {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam))
    (xin : Y → Option X) (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      RoundsQueryLayout.OKG s A W → A.Coherent → ChainStmt (L := L) sMT t cms xin depthReq s A W
  | [], PUnit.unit, (), _, _ => chain_nil sMT t cms xin depthReq
  | _ :: s, (a, A), (w, W), hW, hA => by
      intro embS embP i ph S0 zs a0 n Γ hF hpw hact hlen hreq
      obtain ⟨m0, k0⟩ := S0
      have ih := late_chainT sMT t cms xin depthReq s A W hW.2 hA.2
      rcases kind_cases a.kind with hk | hk
      · exact chain_lo sMT t cms xin depthReq a A w W hk ih embS embP i ph m0 k0 zs a0 n Γ hF hpw
          hact (fun h => hlen (Or.inr h)) hreq
      · cases ph with
        | first =>
          exact chain_skip sMT t cms xin depthReq a A w W hk ih embS embP i .first (Or.inl rfl)
            m0 k0 zs a0 n Γ hF hpw hact (fun h => hlen (Or.inr h)) hreq
        | aft =>
          exact chain_skip sMT t cms xin depthReq a A w W hk ih embS embP i .aft (Or.inr rfl)
            m0 k0 zs a0 n Γ hF hpw hact (fun h => hlen (Or.inr h)) hreq
        | loc =>
          exact chain_join sMT t cms xin depthReq a A w W hk hA.1 hW.1 ih embS embP i m0 k0 zs a0 n
            Γ hF hpw hact (hlen (Or.inl hk))
        | shr tk0 =>
          exact chain_shr sMT t cms xin depthReq a A w W hk hA.1 hW.1 ih embS embP i tk0 m0 k0 zs a0
            n Γ hF hpw hact (fun h => hlen (Or.inr h))

end Compile.Batch
