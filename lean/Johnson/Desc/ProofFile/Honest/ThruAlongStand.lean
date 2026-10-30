-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruAlongStand.lean: what joins a law that speaks at a run to the rule
of Honest/ThruAlong.lean, and the old rule's premises against the new. The rule's premises tell
where the walk stands in front of a block: the rounds lp, the challenges dp, the state z. Laws at a
run speak of the run's played rounds, of midSharedAtW and midAtW at a part's address, and of the
verifier's fold. Here are the three ties, once for every kind.

  ThreadsC.toP, ThreadsC.along   ThreadsC gives ThreadsP and YesAlong: the old rule's premises give
                       the new
  along_grows, grows_first, grows_shared   the run's rounds and columns go through the
                       stand: in front what the walk holds, then the block's own
  called_of_played     a round told at an address: so the part was called
  walk_inside, reach_inside   inside a block the walk is what its rounds lay
  midIn_of_reach, midShared_of_reach, midFirst_of_reach   the state before a part
                       at an address, from the walk that stands there
  reach_fold           at a block with a round the verifier's state is the fold over the blocks in
                       front

By what. Honest/Law/AcceptC.lean (member_laid, bind_grows), Honest/Law/WalkFold.lean (start_tied,
walk_tied, fold_some), Honest/Law/WalkOn.lean (say_eq, heard_eq), Honest/Law/Rule/WalkLaw.lean
(runC_parts, settle_wait).

Limits.
  * reach_fold and reach_inside are at a block with a round: at one without a round the premises of
    the rule do not tell z (Honest/ThruAlong.lean, head).
  * Nothing on what a part's rounds are worth; nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruAlong

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W Y Pb W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The old rule gives the new -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- The part of ThreadsC that the run's return reads. -/
def ThreadsC.toP (T : ThreadsC F Bk H w₀ rc x k R) : ThreadsP F Bk H w₀ rc x k R where
  I₁ := T.I₁
  I₂ := T.I₂
  I₃ := T.I₃
  h₁ := T.h₁
  h₂ := T.h₂
  h₃ := T.h₃
  a₁ := T.a₁
  a₂ := T.a₂
  a₃ := fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ i₁ i₂ hs j₁ j₂ => by
    obtain ⟨s, g₁, g₂⟩ := T.a₃ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ i₁ i₂ j₁ j₂
    rw [hs] at g₁
    cases g₁
    exact g₂

/-- **ThreadsC gives YesAlong, at every run.** -/
theorem ThreadsC.along (T : ThreadsC F Bk H w₀ rc x k R) (ρ : Draws) (r : RunC F) :
    YesAlong ρ r T.toP T.f₁ T.f₂ T.f₃ where
  y₁ := fun j b hb => SaysYes.along (L := ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩) (T.y₁ j b hb) _ _ _ _ _ _
  y₂ := fun j b hb => SaysYes.along (L := ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩) (T.y₂ j b hb) _ _ _ _ _ _
  y₃ := fun z₁ z₂ _ _ j b hb =>
    SaysYes.along (L := ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩)
      (T.y₃ j b hb) _ _ _ _ _ _
  st₃ := fun e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ _ _ i₁ i₂ j₁ j₂ =>
    (T.a₃ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ i₁ i₂ j₁ j₂).imp fun _ h => h.1
  fin := fun e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ _ i₁ i₂ i₃ => T.fin e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ i₁ i₂ i₃

end

/-! ## 2 The run goes through the stand -/

/-- **What a walk holds at its end**: what it holds at the stand, then the block's own, then the
rest. -/
theorem along_grows (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) {A₀ : Except Refusal (ChainProgress S Cl W Y)}
    {lp l lq : List (Step W Y)} {dp ds dq : List Fmt.Drawn} {b : Block S Cl}
    {t : List (Block S Cl)} {z z' : ChainProgress S Cl W Y} {m : Mid W Y} {y : List Played × Mid W Y}
    {cols : List OpenedColumn} (hn₀ : dp.length = lp.length)
    (hA : A₀.bind (walk L lp dp) = ChainProgress.settle L (b :: t) z) (ho : z.own = [])
    (hm : z.mid = some m) (hn : l.length = b.rounds.length) (hdl : ds.length = l.length)
    (hp0 : ∀ u ∈ l, u.move.isSome = false → u.addr.part = 0) (hp : play l ds [] m = .ok y)
    (hc : fillCols (readsOf L.chain L.firstTree ((envOf L.stored taken z.laid).add y.1).stored
      ((envOf L.stored taken z.laid).add y.1).tree b.rounds ds) [] = .ok cols)
    (hw : A₀.bind (walk L (lp ++ l ++ lq) (dp ++ ds ++ dq)) = .ok z') :
    ∃ ps cs, z'.laid = z.laid ++ y.1 ++ ps ∧ z'.cols = z.cols ++ cols ++ cs := by
  have Y₁ := play_yields _ _ _ _ _ hp
  have hdr' : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ Y₁
  have hdr : y.1.map (·.drawn) = ds := by
    have e := hdr'
    unfold roundsOf at e
    rw [List.map_map] at e
    exact e
  have hE : (envOf L.stored taken z.laid).add y.1 = envOf L.stored taken (z.laid ++ y.1) :=
    envOf_add _ _ _ _
  have f₁ : fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
      (y.1.map (·.drawn))) [] = .ok cols := by
    rw [hdr, hL]
    rw [hE] at hc
    exact hc
  have hlay : lays l ds z.mid = .ok (y.1, some y.2) := by
    rw [hm]
    exact lays_of_play _ _ _ _ hp0 hp
  have e₁ : A₀.bind (walk L (lp ++ l ++ lq) (dp ++ ds ++ dq)) =
      (ChainProgress.settle L (b :: t) z).bind fun a => (walk L l ds a).bind (walk L lq dq) := by
    rw [List.append_assoc, List.append_assoc, walk_seq L lp dp (l ++ lq) (ds ++ dq) hn₀ A₀, hA]
    exact congrArg (Except.bind _) (funext fun a => walk_append L lq dq l ds a hdl)
  rw [e₁, member_laid L b t z l ds (y.1, some y.2) cols ho hn hlay f₁] at hw
  exact bind_grows L hw

/-- A round told at an address: the part there was called. -/
theorem called_of_played {F : FileDescription Xi} {r : RunC F} {a : Addr} {p : Played}
    (hp : p ∈ r.run.played.1 ++ r.run.played.2.1 ++ r.run.played.2.2) (ht : p.told = true)
    (hq : p.place = a.place) (hn : p.part = a.part) : r.called a = true :=
  List.any_eq_true.2 ⟨p, hp, by simp [ht, hq, hn]⟩

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : RunC F} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **The shared chain's rounds and columns of a run go through the stand.** -/
theorem grows_shared (h : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
    {lp l lq : List (Step (Common W₀ Rc Ky) X₀)} {dp ds dq : List Fmt.Drawn} {b : Block F.S₂ F.Cl}
    {t : List (Block F.S₂ F.Cl)} {z : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀}
    {m : Mid (Common W₀ Rc Ky) X₀} {y : List Played × Mid (Common W₀ Rc Ky) X₀} {cols : List OpenedColumn}
    (hl₀ : R.shared = lp ++ l ++ lq) (hd₀ : ρ.shared = dp ++ ds ++ dq)
    (hn₀ : dp.length = lp.length)
    (hA : (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
      (some (F.start₂ (F.pub x))) []).bind (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ lp dp) =
      ChainProgress.settle ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (b :: t) z)
    (ho : z.own = []) (hm : z.mid = some m) (hn : l.length = b.rounds.length)
    (hdl : ds.length = l.length) (hp0 : ∀ u ∈ l, u.move.isSome = false → u.addr.part = 0)
    (hp : play l ds [] m = .ok y)
    (hc : fillCols (readsOf 1 0
      ((envOf (H.storedWords w₀ rc) (fun _ _ => none) z.laid).add y.1).stored
      ((envOf (H.storedWords w₀ rc) (fun _ _ => none) z.laid).add y.1).tree b.rounds ds) [] =
      .ok cols) :
    ∃ ps cs, r.run.played.2.1 = z.laid ++ y.1 ++ ps ∧
      r.run.views.2.1.opened = z.cols ++ cols ++ cs := by
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', -, -, -, ha₂, hz₂, -, -, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) ps [] []).1).symm
  refine along_grows (lq := lq) (dq := dq) (z' := z₂) ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo hn₀ hA ho hm
    hn hdl hp0 hp hc ?_
  rw [← hl₀, ← hd₀]
  exact (congrArg (fun e => e.bind (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared))
    ha₂).trans hz₂

/-- The first chain's. -/
theorem grows_first (h : runC F B H w₀ rc x c ρ = .ok r) (hR : ready F B H w₀ rc x c = .ok R)
    {lp l lq : List (Step (Local W₀ Rc Xi Tr) X)} {dp ds dq : List Fmt.Drawn} {b : Block F.S₁ F.Cl}
    {t : List (Block F.S₁ F.Cl)} {z : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X}
    {m : Mid (Local W₀ Rc Xi Tr) X} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hl₀ : R.first = lp ++ l ++ lq) (hd₀ : ρ.first = dp ++ ds ++ dq)
    (hn₀ : dp.length = lp.length)
    (hA : (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
      (some (F.start₁ (F.pub x))) []).bind (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ lp dp) =
      ChainProgress.settle ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (b :: t) z)
    (ho : z.own = []) (hm : z.mid = some m) (hn : l.length = b.rounds.length)
    (hdl : ds.length = l.length) (hp0 : ∀ u ∈ l, u.move.isSome = false → u.addr.part = 0)
    (hp : play l ds [] m = .ok y)
    (hc : fillCols (readsOf 0 0
      ((envOf (H.storedWords w₀ rc) (fun _ _ => none) z.laid).add y.1).stored
      ((envOf (H.storedWords w₀ rc) (fun _ _ => none) z.laid).add y.1).tree b.rounds ds) [] =
      .ok cols) :
    ∃ ps cs, r.run.played.1 = z.laid ++ y.1 ++ ps ∧ r.run.views.1.opened = z.cols ++ cols ++ cs := by
  obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hz₁, -, -, -, -, -, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) ps [] []).1).symm
  refine along_grows (lq := lq) (dq := dq) (z' := z₁) ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo hn₀ hA ho hm
    hn hdl hp0 hp hc ?_
  rw [← hl₀, ← hd₀]
  exact (congrArg (fun e => e.bind (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first))
    ha₁).trans hz₁

end

/-! ## 3 Inside a block, and at an address -/

/-- **Inside a block, short of its last round, the walk is what the rounds lay.** -/
theorem walk_inside {L : Lay} {b : Block S Cl} {bs : List (Block S Cl)} :
    ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (z : ChainProgress S Cl W Y)
      (y : List Played × Option (Mid W Y)), z.todo = b :: bs →
    z.own.length + l.length < b.rounds.length → lays l ds z.mid = .ok y →
    walk L l ds z = .ok (z.grown y)
  | [], [], z, y, _, _, hy => by
    simp only [lays] at hy
    cases hy
    cases z
    simp [walk, ChainProgress.grown]
  | [], _ :: _, _, _, _, _, h => by simp [lays] at h
  | _ :: _, [], _, _, _, _, h => by simp [lays] at h
  | s :: l, d :: ds, z, y, ht, hn, hy => by
    obtain ⟨mid, ver, refused, laid, reads, cols, todo, own⟩ := z
    have ht' : todo = b :: bs := ht
    subst ht'
    simp only [lays] at hy
    obtain ⟨x, hx, hy⟩ := exBind_ok hy
    obtain ⟨m', hm, hy⟩ := exBind_ok hy
    obtain ⟨y', hy', rfl⟩ := exMap_ok hy
    simp only [walk]
    rw [say_eq, hx]
    show ((ChainProgress.heard L ⟨mid, ver, refused, laid, reads, cols, b :: bs, own⟩ s x d).bind
      fun z' => walk L l ds z') = _
    rw [heard_eq, hm]
    show ((ChainProgress.settle L (b :: bs) ⟨m', ver, refused,
               laid ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩], reads, cols,
               b :: bs, own ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩]⟩).bind
        fun z' => walk L l ds z') = _
    have hn' : own.length + (l.length + 1) < b.rounds.length := hn
    rw [settle_wait L b bs _ (by
      show (own ++ [_]).length < b.rounds.length
      rw [List.length_append]
      show own.length + 1 < b.rounds.length
      omega)]
    show walk L l ds ⟨m', ver, refused,
      laid ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩], reads, cols,
      b :: bs, own ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩]⟩ = _
    rw [walk_inside l ds _ y' rfl (by
      show (own ++ [_]).length + l.length < b.rounds.length
      rw [List.length_append]
      show own.length + 1 + l.length < b.rounds.length
      omega) hy']
    refine congrArg Except.ok ?_
    unfold ChainProgress.grown
    simp only [List.append_assoc, List.singleton_append]

/-- **From the stand, a part of the block's rounds**: where the walk stands, short of the block's
last round. -/
theorem reach_inside {L : Lay} {A₀ : Except Refusal (ChainProgress S Cl W Y)} {lp l' : List (Step W Y)}
    {dp d' : List Fmt.Drawn} {b : Block S Cl} {t : List (Block S Cl)} {z : ChainProgress S Cl W Y}
    {y' : List Played × Option (Mid W Y)} (hn₀ : dp.length = lp.length)
    (hA : A₀.bind (walk L lp dp) = ChainProgress.settle L (b :: t) z) (ho : z.own = [])
    (hlt : l'.length < b.rounds.length) (hy : lays l' d' z.mid = .ok y') :
    A₀.bind (walk L (lp ++ l') (dp ++ d')) = .ok ({ z with todo := b :: t }.grown y') := by
  have hpos : z.own.length < b.rounds.length := by
    rw [ho]
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  rw [walk_seq L lp dp l' d' hn₀ A₀, hA, settle_wait L b t z hpos]
  exact walk_inside l' d' { z with todo := b :: t } y' rfl
    (by
      show z.own.length + l'.length < b.rounds.length
      rw [ho]
      simpa using hlt) hy

/-- **The state before an address, from the walk that stands there.** -/
theorem midIn_of_reach {L : Lay} {A₀ : Except Refusal (ChainProgress S Cl W Y)}
    {lp lq : List (Step W Y)} {dp dq : List Fmt.Drawn} {a : Addr} (hn₀ : dp.length = lp.length)
    (hany : (lp ++ lq).any (·.addr == a) = true)
    (htw : ((lp ++ lq).takeWhile fun s => s.addr != a).length = lp.length) :
    (A₀.bind fun a₂ => midInW L (lp ++ lq) (dp ++ dq) a₂ a) =
      (A₀.bind (walk L lp dp)).map (·.mid) := by
  cases A₀ with
  | error e => rfl
  | ok a₂ =>
    show midInW L (lp ++ lq) (dp ++ dq) a₂ a = (walk L lp dp a₂).map (·.mid)
    unfold midInW
    dsimp only
    rw [hany, htw, List.take_left' rfl, List.take_left' hn₀]
    rfl

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **midSharedAtW, from the walk that stands at the address.** -/
theorem midShared_of_reach (hR : ready F B H w₀ rc x c = .ok R) {a : Addr}
    {lp lq : List (Step (Common W₀ Rc Ky) X₀)} {dp dq : List Fmt.Drawn}
    (hl₀ : R.shared = lp ++ lq) (hd₀ : ρ.shared = dp ++ dq) (hn₀ : dp.length = lp.length)
    (hany : R.shared.any (·.addr == a) = true)
    (htw : (R.shared.takeWhile fun s => s.addr != a).length = lp.length) :
    midSharedAtW F B H w₀ rc x c ρ a =
      ((ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
        (some (F.start₂ (F.pub x))) []).bind
        (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ lp dp)).map (·.mid) := by
  have e : midSharedAtW F B H w₀ rc x c ρ a = (ready F B H w₀ rc x c).bind fun R =>
      (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
        (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
      midInW ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared a₂ a := rfl
  rw [e, hR]
  show ((ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
    (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
    midInW ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared a₂ a) = _
  rw [hl₀, hd₀] at *
  exact midIn_of_reach hn₀ hany htw

/-- **midAtW at an address of the first chain, from the walk that stands there.** -/
theorem midFirst_of_reach (hR : ready F B H w₀ rc x c = .ok R) {a : Addr}
    {lp lq : List (Step (Local W₀ Rc Xi Tr) X)} {dp dq : List Fmt.Drawn}
    (hl₀ : R.first = lp ++ lq) (hd₀ : ρ.first = dp ++ dq) (hn₀ : dp.length = lp.length)
    (hany : R.first.any (·.addr == a) = true)
    (htw : (R.first.takeWhile fun s => s.addr != a).length = lp.length) :
    midAtW F B H w₀ rc x c ρ a =
      ((ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
        (some (F.start₁ (F.pub x))) []).bind
        (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ lp dp)).map (·.mid) := by
  have e : midAtW F B H w₀ rc x c ρ a = (ready F B H w₀ rc x c).bind fun R =>
      (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
        (some (F.start₁ (F.pub x))) []).bind fun a₁ =>
      if R.first.any (·.addr == a) then midInW ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first a₁ a
      else _ := rfl
  rw [e, hR]
  show ((ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
    (some (F.start₁ (F.pub x))) []).bind fun a₁ =>
    if R.first.any (·.addr == a) then midInW ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first a₁ a
    else _) = _
  simp only [hany, if_true]
  rw [hl₀, hd₀] at *
  exact midIn_of_reach hn₀ hany htw

end

/-! ## 4 The verifier's state -/

/-- **At a block with a round the verifier's state is the fold over the blocks in front**, with
nothing left over. -/
theorem reach_fold {L : Lay} {bs₀ pre t : List (Block S Cl)} {b : Block S Cl} {m₀ : Mid W Y}
    {s₀ s : S} {front : List OpenedColumn} {lp : List (Step W Y)} {dp : List Fmt.Drawn}
    {z : ChainProgress S Cl W Y}
    (hA : (ChainProgress.start L bs₀ (some m₀) (some s₀) front).bind (walk L lp dp) =
      ChainProgress.settle L (b :: t) z)
    (hb : bs₀ = pre ++ b :: t) (hpos : 0 < b.rounds.length) (ho : z.own = [])
    (hv : z.ver = some s) :
    foldBlocks L.firstTree pre s₀ (roundsOf z.laid) z.cols = .ok (s, [], []) := by
  have hlt : z.own.length < b.rounds.length := by
    rw [ho]
    exact hpos
  rw [settle_wait L b t z hlt] at hA
  obtain ⟨a, ha, hw⟩ := exBind_ok hA
  obtain ⟨t0, o0, -⟩ := start_tied L bs₀ (some m₀) (some s₀) ha
  obtain ⟨tz, -, -⟩ := walk_tied L bs₀ _ lp dp a { z with todo := b :: t } t0 o0 hw
  obtain ⟨done, fr, e1, e2, e3, e4, e5⟩ := tz
  have e1' : pre ++ b :: t = done ++ b :: t := hb.symm.trans e1
  have ed : pre = done := by simpa using e1'
  subst ed
  have e2' : z.laid = fr ++ z.own := e2
  rw [ho, List.append_nil] at e2'
  subst e2'
  have e5' : z.ver = (foldBlocks L.firstTree pre s₀ (roundsOf z.laid) z.cols).toOption.map (·.1) := e5
  rw [hv] at e5'
  exact (fold_some L.firstTree pre s₀ s _ _ (by rw [roundsOf_length]; exact e3) e4).1 e5'.symm

end ProofFile.Honest

#print axioms ProofFile.Honest.ThreadsC.toP
#print axioms ProofFile.Honest.ThreadsC.along
#print axioms ProofFile.Honest.along_grows
#print axioms ProofFile.Honest.called_of_played
#print axioms ProofFile.Honest.grows_shared
#print axioms ProofFile.Honest.grows_first
#print axioms ProofFile.Honest.walk_inside
#print axioms ProofFile.Honest.reach_inside
#print axioms ProofFile.Honest.midIn_of_reach
#print axioms ProofFile.Honest.midShared_of_reach
#print axioms ProofFile.Honest.midFirst_of_reach
#print axioms ProofFile.Honest.reach_fold
