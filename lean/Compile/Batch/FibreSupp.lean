-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/FibreSupp.lean: two facts on the hash work of a batch (`skB`,
Compile/Batch/Mirror.lean).

  1  The hash work does not depend on what a slot holds. `skB_reZ`: the hash work on the new slots
     is the hash work on the old ones, with the new contents put in at the end. So the honest
     prover's slots (instance and coins) and the reduction's (instance, verifier messages, output)
     see the same hash work.
  2  With verifier messages given, the hash blocks yield them. `CohG`: what is given to the slots
     agrees, in the shared rounds, with what is given to the shared chain. `supp_skB`: under `CohG`,
     `RoundsQueryLayout.OKG`, `RoundSplits.FmtFrom` and two lengths, in every run, a slot to which ρ is given ends
     with hash blocks that yield ρ (`rhoOf`) except for the proof-of-work bits (`RoundsQueryLayout.zero` of
     both sides: the searches sample these bits themselves), and what it holds is unchanged.
     `cohG_drawR`: the messages of `Fibre.drawR`, given to the slots with flag true and (from the
     first of these) to the shared chain, agree in this sense.

Notation: `Iv N₀ δ Q st` (Compile/Batch/Fibre.lean): the run of Q under the renumbering of tokens
(`virtL N₀ δ`, Compile/Step1_defc_L.lean) from the state st; `N₀`, `δ`: natural numbers; "in every
run": for every element of `(Iv N₀ δ … st).support`; `Lp lam K L α` (Compile/Batch/Mirror.lean):
`LStep (spec lam K L) (split lam K L) α`, a program; `LS lam K L` (Compile/Batch/Fibre.lean):
`LSt (spec lam K L)`, a state; `skB sMT t dR s A W ph f0 zs a0` (Compile/Batch/Mirror.lean): the
hashing of all chains of a batch; f0: the challenges of a slot's transcript from which the shared
ones are taken, if they are given; zs: for each slot the challenges that are still to come, if they
are given, and its accumulator (`SlotSk`); a0: what the shared part has accumulated (`Acc0`,
Compile/Batch/Prover.lean); `rhoOf` (Compile/Batch/Prover.lean): the verifier messages of a slot's
transcript, from the blocks that the slot has received; `RoundsQueryLayout.zero` (Iop/BatchWire.lean): the
verifier randomness with all test bits set to 0.
-/
import Compile.Batch.Fibre

noncomputable section

namespace Compile.Batch.Fibre
open Iop Rom Prob
open Compile.DefC (lbind_assoc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## 1. The hash work does not depend on what a slot holds -/

section Par
variable {Y Y' : Type}

/-- the same accumulator, holding p -/
def setX (p : Option Y') (acc : SlotAcc lam K Y) : SlotAcc lam K Y' :=
  ⟨p, acc.tk, acc.c, acc.blocks, acc.trees, acc.toks, acc.nons, acc.dead⟩

/-- slot number j holds p j -/
def reX (p : ℕ → Option Y') : List (SlotAcc lam K Y) → List (SlotAcc lam K Y')
  | [] => []
  | a :: l => setX (p 0) a :: reX (fun j => p (j + 1)) l

def reZ {s : Shape} (p : ℕ → Option Y') : List (SlotSk lam K Y s) → List (SlotSk lam K Y' s)
  | [] => []
  | z :: l => (z.1, setX (p 0) z.2) :: reZ (fun j => p (j + 1)) l

theorem map_snd_reZ {s : Shape} :
    ∀ (p : ℕ → Option Y') (zs : List (SlotSk lam K Y s)),
      (reZ p zs).map Prod.snd = reX p (zs.map Prod.snd)
  | _, [] => rfl
  | p, z :: l => by
    show setX (p 0) z.2 :: (reZ (fun j => p (j + 1)) l).map Prod.snd =
      setX (p 0) z.2 :: reX (fun j => p (j + 1)) (l.map Prod.snd)
    rw [map_snd_reZ]

theorem map_hearL_reZ {r : Round} {s : Shape} (bl : Blk lam K) (noted : Bool) :
    ∀ (p : ℕ → Option Y') (zs : List (SlotSk lam K Y (r :: s))),
      (reZ p zs).map (hearL bl noted) = reZ p (zs.map (hearL bl noted))
  | _, [] => rfl
  | p, z :: l => by
    show hearL bl noted (z.1, setX (p 0) z.2) :: (reZ (fun j => p (j + 1)) l).map (hearL bl noted) =
      _
    rw [map_hearL_reZ]
    rfl

theorem zip_reX {s : Shape} :
    ∀ (p : ℕ → Option Y') (fos : List (Option (Rho s))) (accs : List (SlotAcc lam K Y)),
      fos.zip (reX p accs) = reZ p (fos.zip accs)
  | _, [], _ => by simp [reZ]
  | _, _ :: _, [] => rfl
  | p, fo :: fos, acc :: accs => by
    show (fo, setX (p 0) acc) :: fos.zip (reX (fun j => p (j + 1)) accs) =
      (fo, setX (p 0) acc) :: reZ (fun j => p (j + 1)) (fos.zip accs)
    rw [zip_reX]

variable (sMT : ℕ) (t : Tag) (dR : ℕ)

theorem skSlotLo_setX {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (ph : PhT)
    (p : Option Y') (z : SlotSk lam K Y (r :: s)) :
    skSlotLo (L := L) sMT t w ph (z.1, setX p z.2) =
      (skSlotLo sMT t w ph z).bind fun z' => LStep.pure (z'.1, setX p z'.2) := by
  obtain ⟨fo, acc⟩ := z
  rw [skSlotLo, skSlotLo, withTreeL_eq, withTreeL_eq, lbind_assoc]
  refine congrArg _ (funext fun tr => ?_)
  rw [fbSlotGL_bind]
  rfl

theorem each_skSlotLo_reZ {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (ph : PhT) :
    ∀ (p : ℕ → Option Y') (zs : List (SlotSk lam K Y (r :: s))),
      eachL (skSlotLo (L := L) sMT t w ph) (reZ p zs) =
        (eachL (skSlotLo sMT t w ph) zs).bind fun zs' => LStep.pure (reZ p zs')
  | _, [] => rfl
  | p, z :: l => by
    show eachL _ ((z.1, setX (p 0) z.2) :: reZ (fun j => p (j + 1)) l) = _
    rw [eachL_cons, eachL_cons, skSlotLo_setX, each_skSlotLo_reZ w ph (fun j => p (j + 1)) l]
    simp only [lbind_assoc]
    rfl

theorem skSlotJoin_setX {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a)
    (p : Option Y') (z : SlotSk lam K Y (r :: s)) :
    skSlotJoin (L := L) sMT t w (z.1, setX p z.2) =
      (skSlotJoin sMT t w z).bind fun z' => LStep.pure (z'.1, setX p z'.2) := by
  obtain ⟨fo, acc⟩ := z
  rw [skSlotJoin, skSlotJoin, withTreeL_eq, withTreeL_eq, lbind_assoc]
  rfl

theorem skJoinM_reZ {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) :
    ∀ (p : ℕ → Option Y') (zs : List (SlotSk lam K Y (r :: s))),
      skJoinM (L := L) sMT t w (reZ p zs) =
        (skJoinM sMT t w zs).bind fun o => LStep.pure (reZ p o.1, o.2)
  | _, [] => rfl
  | p, z :: l => by
    show (skSlotJoin sMT t w (z.1, setX (p 0) z.2)).bind (fun z' =>
        (skJoinM sMT t w (reZ (fun j => p (j + 1)) l)).bind fun o =>
          LStep.pure (z' :: o.1, z'.2.c :: o.2)) =
      ((skSlotJoin sMT t w z).bind fun z' =>
        (skJoinM sMT t w l).bind fun o => LStep.pure (z' :: o.1, z'.2.c :: o.2)).bind _
    rw [skSlotJoin_setX, skJoinM_reZ w (fun j => p (j + 1)) l]
    simp only [lbind_assoc]
    rfl

/-- a shared round that has no format -/
theorem skB_bad {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh) (ph : PhT) (hph : ph = .first ∨ ph = .aft)
    (f0 : Option (Rho (r :: s))) (zs : List (SlotSk lam K Y (r :: s))) (a0 : Acc0) :
    skB (L := L) sMT t dR (r :: s) (a, A) (w, W) ph f0 zs a0 =
      skB sMT t dR s A W ph (f0.map Prod.snd) (zs.map (hearL (blk0 lam K) false))
        { a0 with trees := a0.trees ++ [none] } := by
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rcases hph with rfl | rfl <;> rfl

/-- The hash work does not depend on what a slot holds. -/
theorem skB_reZ (p : ℕ → Option Y') :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (ph : PhT) (f0 : Option (Rho s))
        (zs : List (SlotSk lam K Y s)) (a0 : Acc0),
      skB (L := L) sMT t dR s A W ph f0 (reZ p zs) a0 =
        (skB sMT t dR s A W ph f0 zs a0).bind fun o => LStep.pure (reX p o.1, o.2)
  | [], _, _, _, _, zs, a0 => by
    show LStep.pure ((reZ p zs).map Prod.snd, a0) = LStep.pure (reX p (zs.map Prod.snd), a0)
    rw [map_snd_reZ]
  | r :: s, (a, A), (w, W), ph, f0, zs, a0 => by
    cases hk : a.kind with
    | lo =>
      rw [skB_lo sMT t dR w W hk, skB_lo sMT t dR w W hk, each_skSlotLo_reZ,
        lbind_assoc, lbind_assoc]
      exact congrArg _ (funext fun zs' => skB_reZ p s A W _ _ zs' _)
    | sh =>
      cases ph with
      | loc =>
        rw [skB_join sMT t dR w W hk, skB_join sMT t dR w W hk, skJoinM_reZ]
        simp only [lbind_assoc]
        refine congrArg _ (funext fun o => ?_)
        show (reqL dR o.2).bind _ = _
        refine congrArg _ (funext fun rq => congrArg _ (funext fun tr0 => ?_))
        rw [fbGL_bind]
        refine congrArg _ (funext fun nc => funext fun dd => funext fun bl => funext fun tl => ?_)
        rw [map_hearL_reZ]
        exact skB_reZ p s A W _ _ _ _
      | shr tk0 =>
        rw [skB_shr sMT t dR w W hk, skB_shr sMT t dR w W hk, lbind_assoc]
        refine congrArg _ (funext fun tr0 => ?_)
        rw [fbGL_bind]
        refine congrArg _ (funext fun nc => funext fun dd => funext fun bl => funext fun tl => ?_)
        rw [map_hearL_reZ]
        exact skB_reZ p s A W _ _ _ _
      | first =>
        rw [skB_bad sMT t dR w W hk .first (Or.inl rfl),
          skB_bad sMT t dR w W hk .first (Or.inl rfl), map_hearL_reZ]
        exact skB_reZ p s A W _ _ _ _
      | aft =>
        rw [skB_bad sMT t dR w W hk .aft (Or.inr rfl),
          skB_bad sMT t dR w W hk .aft (Or.inr rfl), map_hearL_reZ]
        exact skB_reZ p s A W _ _ _ _

end Par

/-! ## 2. With verifier messages given, the hash blocks yield them, except for the proof-of-work
bits (hypotheses: `supp_skB`) -/

/-- a relation between the entries of three lists of one length -/
def All3 {α β γ : Type} (R : α → β → γ → Prop) : List α → List β → List γ → Prop
  | [], [], [] => True
  | a :: l, b :: m, c :: n => R a b c ∧ All3 R l m n
  | _, _, _ => False

theorem All3.len {α β γ : Type} {R : α → β → γ → Prop} :
    ∀ {l : List α} {m : List β} {n : List γ},
      All3 R l m n → l.length = m.length ∧ m.length = n.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: l, _ :: m, _ :: n, h => by
    have ih := All3.len (l := l) (m := m) (n := n) h.2
    simp [ih.1, ih.2]
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- What is given to the slots agrees, in the shared rounds, with what is given to the shared
chain. -/
def CohG : (s : Shape) → (A : RoundSplits s) → Option (Rho s) → List (Option (Rho s)) → Prop
  | [], _, _, _ => True
  | _ :: s, (a, A), f0, fos =>
      (a.kind = .sh → ∀ ρ, some ρ ∈ fos → ∃ ρ0, f0 = some ρ0 ∧ ρ.1 = ρ0.1) ∧
      CohG s A (f0.map Prod.snd) (fos.map (Option.map Prod.snd))

section Supp
variable {Y : Type}

/-- the slot holds what it held, and if ρ was given to it, the hash blocks that it has gathered
since yield ρ, except for the proof-of-work bits (which the searches sample themselves) -/
def Yields (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (fo : Option (Rho s)) (acc acc' : SlotAcc lam K Y) : Prop :=
  acc'.x = acc.x ∧
  ∀ ρ, fo = some ρ →
    ∃ bls,
      acc'.blocks = acc.blocks ++ bls ∧ RoundsQueryLayout.zero s A W (rhoOf s A W bls) = RoundsQueryLayout.zero s A W ρ

/-- one round: one more hash block, which yields the verifier message, except for its proof-of-work
bits, if one was given -/
def Yield1 {r : Round} {a : RAnn r} (w : WireRB lam K r a)
    (h : Option r.Chal) (acc acc' : SlotAcc lam K Y) : Prop :=
  acc'.x = acc.x ∧
  ∃ bl, acc'.blocks = acc.blocks ++ [bl] ∧ ∀ c, h = some c → w.zero (w.chal bl) = w.zero c

theorem all3_nil :
    ∀ (fos : List (Option (Rho []))) (accs : List (SlotAcc lam K Y)),
      fos.length = accs.length → All3 (Yields [] PUnit.unit PUnit.unit) fos accs accs
  | [], [], _ => trivial
  | _ :: fos, acc :: accs, h =>
    ⟨⟨rfl, fun _ _ => ⟨[], (List.append_nil _).symm, rfl⟩⟩, all3_nil fos accs (by simpa using h)⟩

/-- a round, and then the later rounds -/
theorem all3_comp {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) :
    ∀ (fos : List (Option (Rho (r :: s)))) (accs accs1 outs : List (SlotAcc lam K Y)),
      All3 (Yield1 w) (fos.map (Option.map Prod.fst)) accs accs1 →
      All3 (Yields s A W) (fos.map (Option.map Prod.snd)) accs1 outs →
      All3 (Yields (r :: s) (a, A) (w, W)) fos accs outs
  | [], [], [], [], _, _ => trivial
  | fo :: fos, acc :: accs, acc1 :: accs1, out :: outs, h1, h2 => by
    refine ⟨⟨h2.1.1.trans h1.1.1, ?_⟩, all3_comp w W fos accs accs1 outs h1.2 h2.2⟩
    intro ρ hρ
    obtain ⟨bl, hbl, hc⟩ := h1.1.2
    obtain ⟨bls, hbls, hr⟩ := h2.1.2 ρ.2 (by rw [hρ]; rfl)
    refine ⟨bl :: bls, by rw [hbls, hbl, List.append_assoc]; rfl, ?_⟩
    show (w.zero (w.chal bl), RoundsQueryLayout.zero s A W (rhoOf s A W bls)) =
      (w.zero ρ.1, RoundsQueryLayout.zero s A W ρ.2)
    rw [hc ρ.1 (by rw [hρ]; rfl), hr]
  | [], [], [], _ :: _, _, h2 => h2.elim
  | [], [], _ :: _, _, h1, _ => h1.elim
  | [], _ :: _, _, _, h1, _ => h1.elim
  | _ :: _, [], _, _, h1, _ => h1.elim
  | _ :: _, _ :: _, [], _, h1, _ => h1.elim
  | _ :: _, _ :: _, _ :: _, [], _, h2 => h2.elim

/-- all slots receive one hash block -/
theorem all3_hear {r : Round} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K) (noted : Bool) :
    ∀ (hs : List (Option r.Chal)) (accs accs' : List (SlotAcc lam K Y)), hs.length = accs.length →
      List.Forall₂ (fun x x' : SlotAcc lam K Y => x'.x = x.x ∧ x'.blocks = x.blocks) accs accs' →
      (∀ c, some c ∈ hs → w.zero (w.chal bl) = w.zero c) →
      All3 (Yield1 w) hs accs (accs'.map (hearAcc bl noted))
  | [], [], _, _, .nil, _ => trivial
  | h :: hs, _ :: accs, _, hl, .cons (l₂ := accs') e es, hc =>
    ⟨⟨e.1, bl, by show _ ++ [bl] = _; rw [e.2],
        fun c hh => hc c (by rw [hh]; exact List.mem_cons_self)⟩,
      all3_hear w bl noted hs accs accs' (by simpa using hl) es fun c hm =>
        hc c (List.mem_cons_of_mem _ hm)⟩

theorem forall₂_same :
    ∀ accs : List (SlotAcc lam K Y),
      List.Forall₂ (fun x x' : SlotAcc lam K Y => x'.x = x.x ∧ x'.blocks = x.blocks) accs accs
  | [] => .nil
  | _ :: l => .cons ⟨rfl, rfl⟩ (forall₂_same l)

variable (N₀ δ : ℕ) (sMT : ℕ) (t : Tag) (dR : ℕ)

theorem zero_lo {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .lo) (c : r.Chal) :
    w.zero c = zeroG w.grJ c := by
  unfold WireRB.zero
  rw [hk]
  cases w.grJ <;> rfl

theorem zero_sh {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .sh) (c : r.Chal) :
    w.zero c = zeroG w.gr0 c := by
  unfold WireRB.zero
  rw [hk]
  cases w.gr0 <;> rfl

section LoopSupp
variable {β P : Type} {r : Round} {a : RAnn r} (w : WireRB lam K r a)

/-- Under the hypotheses below: the answer of a final attempt yields the given verifier message,
except for the proof-of-work bits. -/
theorem kept_of_law (hw : w.OKG) (g : GrW r.Chal P) (hg : g.OK) (c : r.Chal) (last : Bool)
    (x : (Fin K → Dig lam) × Dig lam) (hx : x ∈ (ansLaw w g (some c) last).support)
    (hk : last = true ∨ g.ok (w.chal x.1) = true) :
    g.set (fun _ => false) (w.chal x.1) = g.set (fun _ => false) c := by
  obtain ⟨y, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
  by_cases hb : (last || decide (zBits g.b y = fun _ => false)) = true
  · simp only [hb, if_true] at hy
    rw [LoopLaw.chal_of_memB w hw _ x hy, hg.set_set]
  · simp only [hb, Bool.false_eq_true, if_false] at hy
    have h1 := LoopLaw.tst_of_memT w g hw hg _ x hy
    rw [Bool.or_eq_true, not_or] at hb
    rcases hk with hk | hk
    · exact absurd hk hb.1
    · exact absurd (decide_eq_true (h1.symm.trans (of_decide_eq_true hk))) hb.2

variable (t' : Tag) (tk : Tok) (us : List Tok) (h : Option r.Chal)

theorem supp_fbWL (hw : w.OKG) (g : GrW r.Chal P) (hg : g.OK)
    (k : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) :
    ∀ (n j : ℕ) (dd : List Tok) (st : LS lam K L),
      ∀ y ∈ (Iv N₀ δ (fbWL w g (ansB w) t' tk us h k n j dd) st).support, ∃ m dd' bl tl st',
        y ∈ (Iv N₀ δ (k m dd' bl tl) st').support ∧
        ∀ c, h = some c → g.set (fun _ => false) (w.chal bl) = g.set (fun _ => false) c
  | 0, j, dd, st, y, hy => by
      rw [fbWL, Iv_tryW] at hy
      obtain ⟨x, hx, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
      exact ⟨_, _, _, _, _, hy,
        fun c hc => by subst hc; exact kept_of_law w hw g hg c true x hx (Or.inl rfl)⟩
  | n + 1, j, dd, st, y, hy => by
      rw [fbWL, Iv_tryW] at hy
      obtain ⟨x, hx, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
      rw [Iv_ite] at hy
      by_cases ho : g.ok (w.chal ((split lam K L).split (OracleName.fbw t' j) x).1) = true
      · rw [if_pos ho] at hy
        exact ⟨_, _, _, _, _, hy,
          fun c hc => by subst hc; exact kept_of_law w hw g hg c false x hx (Or.inr ho)⟩
      · rw [if_neg ho] at hy
        exact supp_fbWL hw g hg k n (j + 1) _ _ y hy

/-- Under the hypotheses below: what the search passes on is a hash block that yields the given
verifier message, except for the proof-of-work bits. -/
theorem supp_fbGL (hw : w.OKG) (gr : Option (GrW r.Chal P)) (hgr : ∀ g, gr = some g → g.OK)
    (k : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) (st : LS lam K L) :
    ∀ y ∈ (Iv N₀ δ (fbGL w gr (ansB w) t' tk us h k) st).support, ∃ nc dd bl tl st',
      y ∈ (Iv N₀ δ (k nc dd bl tl) st').support ∧
      ∀ c, h = some c → zeroG gr (w.chal bl) = zeroG gr c := by
  intro y hy
  cases gr with
  | none =>
      have hy' : y ∈ (Iv N₀ δ (fbL t' tk us (ansB w h) (k none [])) st).support := hy
      rw [Iv_fbL_eq] at hy'
      obtain ⟨x, hx, hy'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy'
      exact ⟨_, _, _, _, _, hy', fun c hc => by subst hc; exact chal_of_mem w hw c x hx⟩
  | some g =>
      have hg := hgr g rfl
      have hy' : y ∈ (Iv N₀ δ (fbTGL w g (ansB w) t' tk us h fun m => k (some m)) st).support := hy
      unfold fbTGL at hy'
      cases hm : g.more with
      | zero =>
          rw [hm] at hy'
          have hy2 : y ∈
              (Iv N₀ δ
                (tryL w g (ansB w) h true fun A => fbL t' tk us A fun bl tl => k (some 0) [] bl tl)
                st).support := hy'
          rw [Iv_tryF] at hy2
          obtain ⟨x, hx, hy2⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy2
          exact ⟨_, _, _, _, _, hy2,
            fun c hc => by subst hc; exact kept_of_law w hw g hg c true x hx (Or.inl rfl)⟩
      | succ n =>
          rw [hm] at hy'
          have hy2 : y ∈
              (Iv N₀ δ (tryL w g (ansB w) h false fun A =>
                  fbL t' tk us A fun bl tl =>
                    if g.ok (w.chal bl) then k (some 0) [] bl tl
                    else fbWL w g (ansB w) t' tk us h (fun m => k (some m)) n 0 [tl]) st).support :=
            hy'
          rw [Iv_tryF] at hy2
          obtain ⟨x, hx, hy2⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy2
          rw [Iv_ite] at hy2
          by_cases ho : g.ok (w.chal ((split lam K L).split (OracleName.fb t') x).1) = true
          · rw [if_pos ho] at hy2
            exact ⟨_, _, _, _, _, hy2,
              fun c hc => by subst hc; exact kept_of_law w hw g hg c false x hx (Or.inr ho)⟩
          · rw [if_neg ho] at hy2
            obtain ⟨m, dd', bl, tl, st', h1, h2⟩ :=
              supp_fbWL N₀ δ w t' tk us h hw g hg (fun m => k (some m)) n 0 _ _ y hy2
            exact ⟨_, _, _, _, _, h1, h2⟩

end LoopSupp

theorem supp_loAcc {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hw : w.OKG) (hk : a.kind = .lo)
    (ph : PhT) (h : Option r.Chal) (acc : SlotAcc lam K Y) (st : LS lam K L) :
    ∀ y ∈ (Iv N₀ δ (loAcc (L := L) sMT t w ph h acc) st).support, Yield1 w h acc y.1 := by
  intro y hy
  unfold loAcc at hy
  rw [Iv_bind] at hy
  obtain ⟨z, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
  have key : ∀ (tk : Tok) (us : List Tok), y ∈
    (Iv N₀ δ (fbGL (L := L) w w.grJ (ansB w) t tk us h fun nc dd bl tl =>
        LStep.pure
          { acc with
            tk := tl, blocks := acc.blocks ++ [bl], trees := acc.trees ++ [z.1],
            toks := acc.toks ++ [tl], nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead })
      z.2).support →
      Yield1 w h acc y.1 := by
    intro tk us hy
    obtain ⟨nc, dd, bl, tl, st', hy, hc⟩ := supp_fbGL N₀ δ w t tk us h hw w.grJ hw.grJ_ok _ _ y hy
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy
    rw [hy]
    exact ⟨rfl, _, rfl, fun c hh => by rw [zero_lo w hk, zero_lo w hk]; exact hc c hh⟩
  cases ph <;> exact key _ _ hy

theorem supp_eachLo {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hw : w.OKG)
    (hk : a.kind = .lo) (ph : PhT) :
    ∀ (hs : List (Option r.Chal)) (accs : List (SlotAcc lam K Y)), hs.length = accs.length →
      ∀ st : LS lam K L, ∀ y ∈ (Iv N₀ δ (eachLo (L := L) sMT t w ph (hs.zip accs)) st).support,
        All3 (Yield1 w) hs accs y.1
  | [], [], _, st, y, hy => by
    have hy' : y ∈ (Iv N₀ δ (LStep.pure [] : Lp lam K L (List (SlotAcc lam K Y))) st).support := hy
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy'
    rw [hy']
    trivial
  | h :: hs, acc :: accs, hl, st, y, hy => by
    unfold eachLo at hy
    rw [List.zip_cons_cons, eachL_cons, Iv_bind] at hy
    obtain ⟨y1, h1, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    rw [Iv_bind] at hy
    obtain ⟨y2, h2, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy
    rw [hy]
    exact ⟨supp_loAcc N₀ δ sMT t w hw hk ph h acc st y1 h1,
      supp_eachLo w hw hk ph hs accs (by simpa using hl) y1.2 y2 h2⟩

theorem supp_joinAccs {r : Round} {a : RAnn r} (w : WireRB lam K r a) :
    ∀ (accs : List (SlotAcc lam K Y)) (st : LS lam K L),
      ∀ y ∈ (Iv N₀ δ (joinAccs (L := L) sMT t w accs) st).support,
        List.Forall₂ (fun x x' : SlotAcc lam K Y => x'.x = x.x ∧ x'.blocks = x.blocks) accs y.1.1
  | [], st, y, hy => by
    have hy' : y ∈
        (Iv N₀ δ (LStep.pure ([], []) : Lp lam K L (List (SlotAcc lam K Y) × List Tok))
          st).support := hy
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy'
    rw [hy']
    exact .nil
  | acc :: accs, st, y, hy => by
    have hy' : y ∈
        (Iv N₀ δ ((joAcc (L := L) sMT t w acc).bind fun x =>
            (joinAccs sMT t w accs).bind fun o => LStep.pure (x :: o.1, x.c :: o.2)) st).support :=
      hy
    rw [Iv_bind] at hy'
    obtain ⟨y1, h1, hy'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy'
    rw [Iv_bind] at hy'
    obtain ⟨y2, h2, hy'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy'
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy'
    rw [hy']
    refine .cons ?_ (supp_joinAccs w accs y1.2 y2 h2)
    unfold joAcc at h1
    rw [Iv_bind] at h1
    obtain ⟨z, -, h1⟩ := (PMF.mem_support_bind_iff _ _ _).1 h1
    have h1' : y1 ∈
        ((PMF.uniformOfFinset (Finset.univ : Finset ((spec lam K L).Rng (OracleName.g t)))
          Finset.univ_nonempty).bind fun x =>
            Iv N₀ δ (LStep.pure
                  { acc with
                    c := z.2.vals.length - δ, trees := acc.trees ++ [z.1],
                    toks := acc.toks ++ [z.2.vals.length - δ] } : Lp lam K L (SlotAcc lam K Y))
                _).support := h1
    obtain ⟨x, -, h1'⟩ := (PMF.mem_support_bind_iff _ _ _).1 h1'
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at h1'
    rw [h1']
    exact ⟨rfl, rfl⟩

/-- from coherence: in a shared round an answer from the set of the shared chain yields what is
given to every slot, except for the proof-of-work bits -/
theorem chal_of_cohG {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .sh)
    (f0 : Option (Rho (r :: s))) (fos : List (Option (Rho (r :: s))))
    (hc : ∀ ρ, some ρ ∈ fos → ∃ ρ0, f0 = some ρ0 ∧ ρ.1 = ρ0.1) (bl : Blk lam K)
    (hx : ∀ c, f0.map Prod.fst = some c → zeroG w.gr0 (w.chal bl) = zeroG w.gr0 c) :
    ∀ c, some c ∈ fos.map (Option.map Prod.fst) → w.zero (w.chal bl) = w.zero c := by
  intro c hm
  obtain ⟨fo, hfo, he⟩ := List.mem_map.1 hm
  cases fo with
  | none => cases he
  | some ρ =>
    obtain ⟨ρ0, h0, h1⟩ := hc ρ hfo
    subst h0
    have e : ρ.1 = c := Option.some.inj he
    rw [← e, h1, zero_sh w hk, zero_sh w hk]
    exact hx ρ0.1 rfl

/-- Under the hypotheses below: in every run of the hash work, each slot holds what it held, and a
slot to which ρ was given has gathered hash blocks that yield ρ, except for the proof-of-work bits.
-/
theorem supp_skB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ ph : PhT, RoundSplits.FmtFrom s A (toF ph) →
        ∀ (f0 : Option (Rho s)) (fos : List (Option (Rho s))) (accs : List (SlotAcc lam K Y)),
          fos.length = accs.length → CohG s A f0 fos →
          ∀ (a0 : Acc0) (st : LS lam K L),
            ∀ y ∈ (Iv N₀ δ (skB (L := L) sMT t dR s A W ph f0 (fos.zip accs) a0) st).support,
              All3 (Yields s A W) fos accs y.1.1
  | [], _, _, _, ph, _, f0, fos, accs, hl, _, a0, st, y, hy => by
    have hy' : y ∈
        (Iv N₀ δ (LStep.pure ((fos.zip accs).map Prod.snd, a0) :
            Lp lam K L (List (SlotAcc lam K Y) × Acc0)) st).support := hy
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy'
    rw [hy']
    show All3 _ fos accs ((fos.zip accs).map Prod.snd)
    rw [List.map_snd_zip (le_of_eq hl.symm)]
    exact all3_nil fos accs hl
  | r :: s, (a, A), (w, W), hW, ph, hF, f0, fos, accs, hl, hc, a0, st, y, hy => by
    have hl1 : (fos.map (Option.map Prod.fst)).length = accs.length := by
      rw [List.length_map]; exact hl
    cases hk : a.kind with
    | lo =>
      have hF' : RoundSplits.FmtFrom s A (toF ph.afterLo) := by
        rw [toF_afterLo]
        have : a.NoShared ∧ RoundSplits.FmtFrom s A (toF ph).afterLo := by
          simpa only [RoundSplits.FmtFrom, hk] using hF
        exact this.2
      rw [Iv_skB_lo N₀ δ sMT t dR w W hk ph f0 fos accs hl a0 st] at hy
      obtain ⟨y1, h1, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
      have a1 := supp_eachLo N₀ δ sMT t w hW.1 hk ph _ accs hl1 st y1 h1
      have l2 : (fos.map (Option.map Prod.snd)).length = y1.1.length :=
        (List.length_map _).trans (hl.trans a1.len.2)
      exact all3_comp w W fos accs y1.1 y.1.1 a1
        (supp_skB s A W hW.2 _ hF' _ _ y1.1 l2 hc.2 _ _ y hy)
    | sh =>
      cases ph with
      | first => simp only [RoundSplits.FmtFrom, hk, toF] at hF
      | aft => simp only [RoundSplits.FmtFrom, hk, toF] at hF
      | loc =>
        have hF' : RoundSplits.FmtFrom s A .shr := by simpa only [RoundSplits.FmtFrom, hk, toF] using hF
        rw [Iv_skB_join N₀ δ sMT t dR w W hk f0 fos accs hl a0 st] at hy
        obtain ⟨z, hz, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
        obtain ⟨nc, dd, bl, tl, st', hy, hx⟩ :=
          supp_fbGL N₀ δ w t _ _ _ hW.1 w.gr0 hW.1.gr0_ok _ _ y hy
        have hj : List.Forall₂ (fun x x' : SlotAcc lam K Y => x'.x = x.x ∧ x'.blocks = x.blocks)
            accs z.1.1.1 := by
          simp only [preJ, Iv_bind, Iv_pure, PMF.mem_support_bind_iff,
            PMF.support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨y1, h1, y2, -, y3, -, rfl⟩ := hz
          exact supp_joinAccs N₀ δ sMT t w accs st y1 h1
        have a1 :=
          all3_hear w bl true _ accs z.1.1.1 hl1 hj (chal_of_cohG w hk f0 fos (hc.1 hk) bl hx)
        have l2 : (fos.map (Option.map Prod.snd)).length = (z.1.1.1.map (hearAcc bl true)).length :=
          (List.length_map _).trans (hl.trans a1.len.2)
        exact all3_comp w W fos accs _ y.1.1 a1
          (supp_skB s A W hW.2 (.shr _) hF' _ _ _ l2 hc.2 _ _ y hy)
      | shr tk0 =>
        have hF' : RoundSplits.FmtFrom s A .shr := by
          have : a.NoSlot ∧ RoundSplits.FmtFrom s A .shr := by simpa only [RoundSplits.FmtFrom, hk, toF] using hF
          exact this.2
        rw [Iv_skB_shr N₀ δ sMT t dR w W hk tk0 f0 fos accs a0 st] at hy
        obtain ⟨z, hz, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
        obtain ⟨nc, dd, bl, tl, st', hy, hx⟩ :=
          supp_fbGL N₀ δ w t _ _ _ hW.1 w.gr0 hW.1.gr0_ok _ _ y hy
        have a1 := all3_hear w bl false _ accs accs hl1 (forall₂_same accs)
          (chal_of_cohG w hk f0 fos (hc.1 hk) bl hx)
        have l2 : (fos.map (Option.map Prod.snd)).length = (accs.map (hearAcc bl false)).length :=
          (List.length_map _).trans (hl.trans a1.len.2)
        exact all3_comp w W fos accs _ y.1.1 a1
          (supp_skB s A W hW.2 (.shr _) hF' _ _ _ l2 hc.2 _ _ y hy)

end Supp

/-! ### The messages of drawR are coherent -/

theorem first_of_mem {β : Type} :
    ∀ (l : List (Option β)) (x : β), some x ∈ l → ∃ y, first l = some y ∧ some y ∈ l
  | none :: l, x, h => by
    obtain ⟨y, h1, h2⟩ := first_of_mem l x (by simpa using h)
    exact ⟨y, h1, List.mem_cons_of_mem _ h2⟩
  | some z :: l, _, _ => ⟨z, rfl, List.mem_cons_self⟩

theorem mem_of_mem_mask {β : Type} :
    ∀ (fl : List Bool) (l : List β) (x : β), some x ∈ mask fl l → x ∈ l
  | [], _, _, h => by simp [mask] at h
  | _ :: _, [], _, h => by simp [mask] at h
  | b :: fl, y :: l, x, h => by
    rw [mask_cons] at h
    rcases List.mem_cons.1 h with h | h
    · cases b
      · simp at h
      · simp only [if_true, Option.some.injEq] at h
        rw [h]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_mask fl l x h)

/-- The messages of drawR, given to the slots with flag true and, from the first of these, to the
shared chain, are coherent. -/
theorem cohG_drawR :
    ∀ (s : Shape) (A : RoundSplits s) (n : ℕ) (fl : List Bool),
      ∀ rs ∈ (drawR s A n).support, CohG s A (first (mask fl rs)) (mask fl rs)
  | [], _, _, _, _, _ => trivial
  | r :: s, (a, A), n, fl, rs, hrs => by
    have hrs' : rs ∈
        ((headsOf a n).bind fun hs =>
          (drawR s A n).map fun ts => (hs.zip ts : List (r.Chal × Rho s))).support := hrs
    obtain ⟨hs, hhs, h2⟩ := (PMF.mem_support_bind_iff _ _ _).1 hrs'
    obtain ⟨ts, hts, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 h2
    have hlen : hs.length = ts.length := by rw [len_headsOf a n hs hhs, len_drawR s A n ts hts]
    refine ⟨fun hk ρ hρ => ?_, ?_⟩
    · -- in a shared round all heads are one value
      unfold headsOf at hhs
      rw [hk] at hhs
      obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hhs
      have hall : ∀ ρ' : r.Chal × Rho s,
          some ρ' ∈ mask fl ((List.replicate n c).zip ts) → ρ'.1 = c := by
        intro ρ' h'
        have h3 := mem_of_mem_mask fl _ ρ' h'
        exact List.eq_of_mem_replicate (List.of_mem_zip (a := ρ'.1) (b := ρ'.2) h3).1
      obtain ⟨ρ0, e0, m0⟩ := first_of_mem _ ρ hρ
      exact ⟨ρ0, e0, (hall ρ hρ).trans (hall ρ0 m0).symm⟩
    · have e1 : (first (mask fl (hs.zip ts : List (Rho (r :: s))))).map Prod.snd =
          first (mask fl ts) := by
        rw [first_map, given_snd fl hs ts hlen]
      have e2 : (mask fl (hs.zip ts : List (Rho (r :: s)))).map (Option.map Prod.snd) =
          mask fl ts :=
        given_snd fl hs ts hlen
      show CohG s A ((first (mask fl (hs.zip ts : List (Rho (r :: s))))).map Prod.snd)
        ((mask fl (hs.zip ts : List (Rho (r :: s)))).map (Option.map Prod.snd))
      rw [e1, e2]
      exact cohG_drawR s A n fl ts hts

end Compile.Batch.Fibre
