-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruAlongJ.lean: the rule of Honest/ThruAlong.lean with a sentence on
the verifier's state in hand, for a house that states at AcceptedJ and NextJ. J cannot be added after
the rule: it is carried from block to block by CarriesOn, which asks that no fall fires, and PlaysOn
does not. So it rides in the rule's own recursion, as in Honest/Law/AcceptJ.lean.

  SaysYesAlongJ, SaysYesAlong.toJ, SaysYesJ.along   the second condition at one walk, with J in hand
  chain_accepts_alongJ   one chain: chain_acceptsJ with SaysYesAlongJ
  YesAlongJ, YesAlong.toJ   what a run asks of the yes, with sentences J₁, J₂, J₃
  runC_accepts_alongJ  the file, with a test on the falls
  yes_at_requestStrategyTrackingVerifier_alongJ at the strategy of honestBatchProverOfFile

By what. The text of chain_acceptsJ, runC_acceptsJ, CarriesOn, SaysYesJ
(Honest/Law/AcceptJ.lean), and of Honest/ThruAlong.lean.

Limits. Those of Honest/ThruAlong.lean. The rule's falls are untouched.
-/
import Johnson.Desc.ProofFile.Honest.ThruAlong
import Johnson.Desc.ProofFile.Honest.Law.AcceptJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD chainsOf view₁ view₂ view₃)
open _root_.Run.PQ (CK SgX)

variable {S Cl Xi V W Y Pb W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-! ## 1 The condition -/

/-- **The same with a sentence on the verifier's state in hand.** SaysYesAlong is its case J := True;
SaysYesJ (Honest/Law/AcceptJ.lean) gives it as SaysYes gives SaysYesAlong. -/
def SaysYesAlongJ (φ : Face V W Pb) (Bk : ProverCoinCounts) (k : Coins Bk) (L : Lay)
    (taken : Nat → Nat → Option (Place × Table)) (hs : List (Placed V W Y))
    (b : Block S Cl) (fall : S → List Fmt.Drawn → Option String)
    (A : Coins Bk → S → Mid W Y → Env → Prop) (J : S → Prop) (A₀ : Except Refusal (ChainProgress S Cl W Y))
    (l₀ : List (Step W Y)) (d₀ : List Fmt.Drawn) (bs₀ : List (Block S Cl)) : Prop :=
  ∀ s m ds l y cols lp dp lq dq t z pre, l₀ = lp ++ l ++ lq → d₀ = dp ++ ds ++ dq →
    dp.length = lp.length → bs₀ = pre ++ b :: t → lp.length = (pre.flatMap (·.rounds)).length →
    A₀.bind (walk L lp dp) = ChainProgress.settle L (b :: t) z → z.own = [] →
    z.mid = some m → z.ver = some s → A k s m (envOf L.stored taken z.laid) → J s →
    drawsFit b.rounds ds = true →
    chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none → fall s ds = none →
    chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) (φ.sees m.st.input) [b] hs = .ok l →
    play l ds [] m = .ok y →
    fillCols (readsOf L.chain L.firstTree ((envOf L.stored taken z.laid).add y.1).stored
      ((envOf L.stored taken z.laid).add y.1).tree b.rounds ds) [] = .ok cols →
    ∃ s' n, b.step L.firstTree s (roundsOf y.1) cols = .ok (s', n)

/-- SaysYesAlong gives it, at any J. -/
theorem SaysYesAlong.toJ {φ : Face V W Pb} {Bk : ProverCoinCounts} {L : Lay} {hs : List (Placed V W Y)}
    {b : Block S Cl} {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W Y → Env → Prop} {A₀ : Except Refusal (ChainProgress S Cl W Y)}
    {k : Coins Bk} {taken : Nat → Nat → Option (Place × Table)}
    {l₀ : List (Step W Y)} {d₀ : List Fmt.Drawn} {bs₀ : List (Block S Cl)}
    (h : SaysYesAlong φ Bk k L taken hs b fall A A₀ l₀ d₀ bs₀) (J : S → Prop) :
    SaysYesAlongJ φ Bk k L taken hs b fall A J A₀ l₀ d₀ bs₀ :=
  fun s m ds l y cols lp dp lq dq t z pre e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ hA _ hd hst hf hc hp hcols =>
    h s m ds l y cols lp dp lq dq t z pre e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ hA hd hst hf hc hp hcols

/-- SaysYesJ gives it, at any walk. -/
theorem SaysYesJ.along {φ : Face V W Pb} {Bk : ProverCoinCounts} {L : Lay} {hs : List (Placed V W Y)}
    {b : Block S Cl} {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W Y → Env → Prop} {J : S → Prop}
    (h : SaysYesJ φ Bk L.chain L.firstTree hs b fall A J)
    (k : Coins Bk) (taken : Nat → Nat → Option (Place × Table))
    (A₀ : Except Refusal (ChainProgress S Cl W Y)) (l₀ : List (Step W Y)) (d₀ : List Fmt.Drawn)
    (bs₀ : List (Block S Cl)) : SaysYesAlongJ φ Bk k L taken hs b fall A J A₀ l₀ d₀ bs₀ :=
  fun s m ds l y cols _ _ _ _ _ z _ _ _ _ _ _ _ _ _ _ hA hJ hd hst hf hc hp hcols =>
    h k s m (envOf L.stored taken z.laid) ds l y cols hA hJ hd hst hf hc hp hcols

/-! ## 2 One chain -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **One chain.** chain_acceptsJ, with the yes asked along the walk. lp, dp, pre: what has been
walked of l₀, d₀ and bs₀ in front of z. -/
theorem chain_accepts_alongJ (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (k : Coins Bk) (v : Option V)
    (A₀ : Except Refusal (ChainProgress S Cl W Y)) (l₀ : List (Step W Y)) (d₀ : List Fmt.Drawn)
    (bs₀ : List (Block S Cl)) :
    ∀ (bs : List (Block S Cl)) (I : Nat → Coins Bk → S → Mid W Y → Env → Prop)
      (fl : Nat → S → List Fmt.Drawn → Option String) (J : Nat → S → Prop),
    (∀ j b, bs[j]? = some b → PlaysOn φ Bk L.chain L.firstTree hs b (I j) (I (j + 1))) →
    (∀ j b, bs[j]? = some b → SaysYesAlongJ φ Bk k L taken hs b (fl j) (I j) (J j) A₀ l₀ d₀ bs₀) →
    (∀ j b, bs[j]? = some b →
      CarriesOn φ Bk L.chain L.firstTree hs b (fl j) (I j) (J j) (J (j + 1))) →
    ∀ (l : List (Step W Y)) (z z' : ChainProgress S Cl W Y) (ds : List Fmt.Drawn) (s : S) (m : Mid W Y)
      (lp : List (Step W Y)) (dp : List Fmt.Drawn) (pre : List (Block S Cl)),
    l₀ = lp ++ l → d₀ = dp ++ ds → dp.length = lp.length → bs₀ = pre ++ bs →
    lp.length = (pre.flatMap (·.rounds)).length →
    A₀.bind (walk L lp dp) = ChainProgress.settle L bs z →
    (∀ u ∈ l, u.move.isSome = false → u.addr.part = 0) → z.own = [] → z.mid = some m →
    z.ver = some s → φ.sees m.st.input = v → I 0 k s m (envOf L.stored taken z.laid) → J 0 s →
    chainStopAt v bs hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v bs hs = .ok l →
    drawsFit (bs.flatMap (·.rounds)) ds = true →
    (ChainProgress.settle L bs z).bind (walk L l ds) = .ok z' →
    fallFree L.firstTree bs fl s ((roundsOf z'.laid).drop z.laid.length)
      (z'.cols.drop z.cols.length) →
    ∃ s' m', z'.ver = some s' ∧ z'.mid = some m' ∧
      I bs.length k s' m' (envOf L.stored taken z'.laid) ∧ J bs.length s'
  | [], I, fl, J, _, _, _, l, z, z', ds, s, m, _, _, _, _, _, _, _, _, _, _, ho, hm, hv, _, h0, j0,
      _, hl, hd, hz, _ => by
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [drawsFit] at hd
    subst hds
    simp only [chainSteps] at hl
    cases hl
    have hz' : (Except.ok { z with todo := [] } : Except Refusal (ChainProgress S Cl W Y)) = .ok z' := hz
    cases hz'
    exact ⟨s, m, hv, hm, h0, j0⟩
  | b :: t, I, fl, J, h, hy, hcar, l, z, z', ds, s, m, lp, dp, pre, hl₀, hd₀, hn₀, hb₀, hq₀, hA, hp0,
      ho, hm, hv, hsee, h0, j0, hst, hl, hd, hz, hff => by
    have hl' : chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v ([b] ++ t) hs = .ok l := hl
    rw [chainSteps_append] at hl'
    obtain ⟨l₁, hl₁, hl'⟩ := exBind_ok hl'
    obtain ⟨l₂, hl₂, rfl⟩ := exMap_ok hl'
    rw [List.flatMap_cons, drawsFit_append, Bool.and_eq_true] at hd
    obtain ⟨hd₁, hd₂⟩ := hd
    have hdecl : l₁.map (·.decl) = b.rounds := by
      have e := steps_decl hl₁
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
      exact e
    have hn : l₁.length = b.rounds.length := by rw [← hdecl, List.length_map]
    have hlen₁ : (ds.take b.rounds.length).length = l₁.length := by
      rw [drawsFit_length _ _ hd₁, hn]
    have hW : walk L (l₁ ++ l₂) ds = fun a : ChainProgress S Cl W Y =>
        (walk L l₁ (ds.take b.rounds.length) a).bind (walk L l₂ (ds.drop b.rounds.length)) := by
      funext a
      have e' := walk_append L l₂ (ds.drop b.rounds.length) l₁ (ds.take b.rounds.length) a hlen₁
      rw [List.take_append_drop] at e'
      exact e'
    rw [hW] at hz
    have hst' : ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt v g.parts m.loc (ds.take b.rounds.length)).or
          (chainStopAt v t hs (m.loc ++ ds.take b.rounds.length)
            (ds.drop b.rounds.length)) = none := hst
    obtain ⟨hs₁, hs₂⟩ := or_none hst'
    have hs₁' : chainStopAt v [b] hs m.loc (ds.take b.rounds.length) = none := by
      show ((hs.find? fun g => g.place == b.place).bind fun g =>
        rowStopAt v g.parts m.loc
          ((ds.take b.rounds.length).take b.rounds.length)).or (none : Option Why) = none
      rw [List.take_take, Nat.min_self, hs₁]
      rfl
    obtain ⟨y, cols, p₁, f₁, hB⟩ := h 0 b (by simp) k s m _ (ds.take b.rounds.length) l₁ h0 hd₁
      (by rw [hsee]; exact hs₁') (by rw [hsee]; exact hl₁)
    obtain ⟨e1, e2, -⟩ := play_mid _ _ _ _ _ p₁
    have Y₁ := play_yields _ _ _ _ _ p₁
    have hyl : y.1.length = b.rounds.length := by rw [yields_length _ _ _ _ Y₁, hn]
    have hdr' : (roundsOf y.1).map (·.drawn) = ds.take b.rounds.length := yields_drawn _ _ _ _ Y₁
    have hdr : y.1.map (·.drawn) = ds.take b.rounds.length := by
      have e := hdr'
      unfold roundsOf at e
      rw [List.map_map] at e
      exact e
    have hE : (envOf L.stored taken z.laid).add y.1 = envOf L.stored taken (z.laid ++ y.1) :=
      envOf_add _ _ _ _
    have f₁' : fillCols (readsOf L.chain L.firstTree L.stored (L.tree (z.laid ++ y.1)) b.rounds
        (y.1.map (·.drawn))) [] = .ok cols := by
      rw [hdr, hL]
      rw [hE] at f₁
      exact f₁
    have hlay : lays l₁ (ds.take b.rounds.length) z.mid = .ok (y.1, some y.2) := by
      rw [hm]
      exact lays_of_play _ _ _ _ (fun u hu => hp0 u (List.mem_append_left _ hu)) p₁
    have hA' : A₀.bind (walk L (lp ++ l₁) (dp ++ ds.take b.rounds.length)) =
        ChainProgress.settle L t (z.askedO L b (y.1, some y.2) cols) := by
      have e₁ := member_laid L b t z l₁ (ds.take b.rounds.length) (y.1, some y.2) cols ho hn hlay f₁'
        Except.ok
      have e₂ : (fun a : ChainProgress S Cl W Y => (walk L l₁ (ds.take b.rounds.length) a).bind Except.ok) =
          walk L l₁ (ds.take b.rounds.length) := by
        funext a
        exact except_bind_ok _
      rw [e₂, except_bind_ok] at e₁
      rw [walk_seq L lp dp l₁ (ds.take b.rounds.length) hn₀ A₀, hA]
      exact e₁
    rw [member_laid L b t z l₁ _ (y.1, some y.2) cols ho hn hlay f₁'] at hz
    obtain ⟨ps, cs, g1, g2⟩ := bind_grows L hz
    have g1' : z'.laid = z.laid ++ y.1 ++ ps := g1
    have g2' : z'.cols = z.cols ++ cols ++ cs := g2
    have r0 : (roundsOf z'.laid).drop z.laid.length = roundsOf y.1 ++ roundsOf ps := by
      rw [g1', roundsOf_append, roundsOf_append, List.append_assoc,
        List.drop_left' (roundsOf_length _)]
    have c0 : z'.cols.drop z.cols.length = cols ++ cs := by
      rw [g2', List.append_assoc, List.drop_left' rfl]
    rw [r0, c0] at hff
    have hrn : (roundsOf y.1).length = b.rounds.length := by rw [roundsOf_length, hyl]
    obtain ⟨ff1, ff2⟩ := hff
    rw [List.take_left' hrn] at ff1 ff2
    rw [List.drop_left' hrn] at ff2
    rw [hdr'] at ff1
    obtain ⟨s', n', hstep⟩ := hy 0 b (by simp) s m (ds.take b.rounds.length) l₁ y cols lp dp l₂
      (ds.drop b.rounds.length) t z pre (by rw [hl₀, List.append_assoc])
      (by rw [hd₀, List.append_assoc, List.take_append_drop]) hn₀ hb₀ hq₀ hA ho hm hv h0 j0 hd₁
      (by rw [hsee]; exact hs₁') ff1 (by rw [hsee]; exact hl₁) p₁ f₁
    have j' := hcar 0 b (by simp) k s m _ (ds.take b.rounds.length) l₁ y cols s' n' h0 j0 hd₁
      (by rw [hsee]; exact hs₁') ff1 (by rw [hsee]; exact hl₁) p₁ f₁ hstep
    have hwant : (b.want L.firstTree (roundsOf y.1)).length = cols.length := by
      have e := congrArg List.length (fillCols_kept _ _ _ f₁)
      rw [readsOf_wants, List.length_map] at e
      unfold Block.want
      rw [hdr']
      exact e.symm
    have hn' : n' = cols.length := by
      have e := ((step_iff L.firstTree b s s' _ _ n').1 hstep).2.2
      rw [e]
      exact hwant
    have hstep' : b.step L.firstTree s (roundsOf y.1) (cols ++ cs) = .ok (s', n') := by
      rw [step_more L.firstTree b s _ cols cs (Nat.le_of_eq hwant)]
      exact hstep
    have ff3 := ff2 s' n' hstep'
    rw [hn', List.drop_left' rfl] at ff3
    have hj : judge L.firstTree b s (roundsOf y.1) cols = some s' := by
      unfold judge
      rw [hstep]
      rfl
    have hB' := hB s' n' hstep
    rw [hE] at hB'
    have hver : (z.askedO L b (y.1, some y.2) cols).ver = some s' := by
      show (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols) = some s'
      rw [hv]
      exact hj
    have hmid : (z.askedO L b (y.1, some y.2) cols).mid = some (y.2.took cols) := by
      show (if (z.ver.bind fun s => judge L.firstTree b s (roundsOf y.1) cols).isSome
        then some (y.2.took cols) else none) = some (y.2.took cols)
      rw [hv]
      show (if (judge L.firstTree b s (roundsOf y.1) cols).isSome then some (y.2.took cols)
        else none) = _
      rw [hj]
      rfl
    refine chain_accepts_alongJ L taken hL k v A₀ l₀ d₀ bs₀ t (fun j => I (j + 1))
      (fun j => fl (j + 1)) (fun j => J (j + 1))
      (fun j b' hj' => h (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj'))
      (fun j b' hj' => hy (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj'))
      (fun j b' hj' => hcar (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj')) l₂
      (z.askedO L b (y.1, some y.2) cols) z' (ds.drop b.rounds.length) s' (y.2.took cols)
      (lp ++ l₁) (dp ++ ds.take b.rounds.length) (pre ++ [b]) (by rw [hl₀, List.append_assoc])
      (by rw [hd₀, List.append_assoc, List.take_append_drop])
      (by rw [List.length_append, List.length_append, hn₀, hlen₁])
      (by rw [hb₀, List.append_assoc]; rfl)
      (by
        rw [List.length_append, List.flatMap_append, List.length_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, hq₀, hn]) hA'
      (fun u hu => hp0 u (List.mem_append_right _ hu)) rfl hmid hver
      (by
        show φ.sees y.2.st.input = v
        rw [e1]
        exact hsee)
      hB' j'
      (by
        show chainStopAt v t hs y.2.loc _ = none
        rw [e2]
        exact hs₂)
      hl₂ hd₂ hz ?_
    show fallFree L.firstTree t (fun j => fl (j + 1)) s'
      ((roundsOf z'.laid).drop (z.laid ++ y.1).length) (z'.cols.drop (z.cols ++ cols).length)
    have r1 : (roundsOf z'.laid).drop (z.laid ++ y.1).length = roundsOf ps := by
      rw [g1', roundsOf_append, List.drop_left' (roundsOf_length _)]
    have c1 : z'.cols.drop (z.cols ++ cols).length = cs := by
      rw [g2', List.drop_left' rfl]
    rw [r1, c1]
    exact ff3


end

/-! ## 3 The file -/

/-- **The same with a sentence on the verifier's state at each chain**: J₁, J₂, J₃ by the block's
number, asked at the chains' starts and carried from block to block. -/
structure YesAlongJ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X} (ρ : Draws) (r : RunC F)
    (T : ThreadsP F Bk H w₀ rc x k R) (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂))
    (f₃ : List (Fall F.S₃)) (J₁ : Nat → F.S₁ → Prop) (J₂ : Nat → F.S₂ → Prop)
    (J₃ : Nat → F.S₃ → Prop) : Prop where
  y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
    SaysYesAlongJ .own Bk k ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) H.first b (fallOf f₁ b.place)
      (T.I₁ j) (J₁ j)
      (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
        (some (F.start₁ (F.pub x))) []) R.first ρ.first F.first.blocksInOrder
  y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
    SaysYesAlongJ .shared Bk k ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) H.shared b (fallOf f₂ b.place)
      (T.I₂ j) (J₂ j)
      (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
        (some (F.start₂ (F.pub x))) []) R.shared ρ.shared F.shared.blocksInOrder
  y₃ : ∀ (z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X) (z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀),
    (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
      (some (F.start₁ (F.pub x))) []).bind
      (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first) = .ok z₁ →
    (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
      (some (F.start₂ (F.pub x))) []).bind
      (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared) = .ok z₂ →
    ∀ j b, F.second.blocksInOrder[j]? = some b →
    SaysYesAlongJ .own Bk k ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
      (taken₃ z₁.laid z₂.laid) H.second b (fallOf f₃ b.place) (T.I₃ j) (J₃ j)
      (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
        (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
        (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)) R.second ρ.second F.second.blocksInOrder
  c₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
    CarriesOn .own Bk 0 0 H.first b (fallOf f₁ b.place) (T.I₁ j) (J₁ j) (J₁ (j + 1))
  c₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
    CarriesOn .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (T.I₂ j) (J₂ j) (J₂ (j + 1))
  c₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
    CarriesOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (T.I₃ j) (J₃ j) (J₃ (j + 1))
  j₁ : J₁ 0 (F.start₁ (F.pub x))
  j₂ : J₂ 0 (F.start₂ (F.pub x))
  st₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, r.ends.1 = some e₁ → r.ends.2.1 = some e₂ →
    T.I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ → T.I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
    m₁.opened = some o₁ → m₂.opened = some o₂ →
    J₁ F.first.blocksInOrder.length e₁ → J₂ F.shared.blocksInOrder.length e₂ →
    ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧ J₃ 0 s₃
  fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, r.ends = (some e₁, some e₂, some e₃) →
    T.I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ → T.I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
    T.I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ → J₁ F.first.blocksInOrder.length e₁ →
    J₂ F.shared.blocksInOrder.length e₂ → J₃ F.second.blocksInOrder.length e₃ → F.fin x e₁ e₂ e₃ = true

/-- YesAlong is its case at the sentences that always hold. -/
theorem YesAlong.toJ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {ρ : Draws} {r : RunC F}
    {T : ThreadsP F Bk H w₀ rc x k R} {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)}
    {f₃ : List (Fall F.S₃)} (Y : YesAlong ρ r T f₁ f₂ f₃) :
    YesAlongJ ρ r T f₁ f₂ f₃ (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) where
  y₁ := fun j b hj => (Y.y₁ j b hj).toJ _
  y₂ := fun j b hj => (Y.y₂ j b hj).toJ _
  y₃ := fun z₁ z₂ h₁ h₂ j b hj => (Y.y₃ z₁ z₂ h₁ h₂ j b hj).toJ _
  c₁ := fun _ _ _ => carriesOn_true _ _ _ _ _ _ _ _ _
  c₂ := fun _ _ _ => carriesOn_true _ _ _ _ _ _ _ _ _
  c₃ := fun _ _ _ => carriesOn_true _ _ _ _ _ _ _ _ _
  j₁ := trivial
  j₂ := trivial
  st₃ := fun e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ h₁ h₂ i₁ i₂ p₁ p₂ _ _ =>
    (Y.st₃ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ h₁ h₂ i₁ i₂ p₁ p₂).imp fun _ h => ⟨h, trivial⟩
  fin := fun e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ h i₁ i₂ i₃ _ _ _ =>
    Y.fin e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ h i₁ i₂ i₃

/-- **The rule for a file's acceptance, with the yes asked at the run, and sentences in hand.** -/
theorem runC_accepts_alongJ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hp : F.planOk = true) (hx : F.okStart x = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (T : ThreadsP F Bk H w₀ rc x k R)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (J₁ : Nat → F.S₁ → Prop) (J₂ : Nat → F.S₂ → Prop) (J₃ : Nat → F.S₃ → Prop)
    (Y : YesAlongJ ρ r T f₁ f₂ f₃ J₁ J₂ J₃) (hv : viewsFall F f₁ f₂ f₃ x r.run.views = none) :
    (∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨n₁, n₂, n₃⟩ := fallFree_of_views h f₁ f₂ f₃ hv
  have C₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
      CarriesOn .own Bk 0 0 H.first b (fallsBy f₁ F.first.blocksInOrder j) (T.I₁ j) (J₁ j) (J₁ (j + 1)) := by
    intro j b hj
    have e : fallsBy f₁ F.first.blocksInOrder j = fallOf f₁ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact Y.c₁ j b hj
  have C₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      CarriesOn .shared Bk 1 0 H.shared b (fallsBy f₂ F.shared.blocksInOrder j) (T.I₂ j) (J₂ j)
        (J₂ (j + 1)) := by
    intro j b hj
    have e : fallsBy f₂ F.shared.blocksInOrder j = fallOf f₂ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact Y.c₂ j b hj
  have C₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      CarriesOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallsBy f₃ F.second.blocksInOrder j) (T.I₃ j) (J₃ j)
        (J₃ (j + 1)) := by
    intro j b hj
    have e : fallsBy f₃ F.second.blocksInOrder j = fallOf f₃ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact Y.c₃ j b hj
  have Y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYesAlongJ .own Bk k ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) H.first b
        (fallsBy f₁ F.first.blocksInOrder j) (T.I₁ j) (J₁ j)
        (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
          (some (F.start₁ (F.pub x))) []) R.first ρ.first F.first.blocksInOrder := by
    intro j b hj
    have e : fallsBy f₁ F.first.blocksInOrder j = fallOf f₁ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact Y.y₁ j b hj
  have Y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYesAlongJ .shared Bk k ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) H.shared b
        (fallsBy f₂ F.shared.blocksInOrder j) (T.I₂ j) (J₂ j)
        (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
          (some (F.start₂ (F.pub x))) []) R.shared ρ.shared F.shared.blocksInOrder := by
    intro j b hj
    have e : fallsBy f₂ F.shared.blocksInOrder j = fallOf f₂ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact Y.y₂ j b hj
  have Y₃ : ∀ (z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X) (z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀),
      (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
        (some (F.start₁ (F.pub x))) []).bind
        (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first) = .ok z₁ →
      (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
        (some (F.start₂ (F.pub x))) []).bind
        (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared) = .ok z₂ →
      ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYesAlongJ .own Bk k ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
        (taken₃ z₁.laid z₂.laid) H.second b (fallsBy f₃ F.second.blocksInOrder j) (T.I₃ j) (J₃ j)
        (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
          (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
          (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)) R.second ρ.second F.second.blocksInOrder := by
    intro z₁ z₂ h₁ h₂ j b hj
    have e : fallsBy f₃ F.second.blocksInOrder j = fallOf f₃ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact Y.y₃ z₁ z₂ h₁ h₂ j b hj
  obtain ⟨-, tr, htr, hown, hcom, s1, s2, s3⟩ := ready_ok hR
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hρ
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, -⟩ := hρ
  unfold silentAt at hsil
  rw [htr] at hsil
  have hsil' : (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder
      H.first [] ρ.first).or
      ((chainStopAt (Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder
        H.shared [] ρ.shared).or
        (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second
          ρ.first ρ.second)) = none := hsil
  obtain ⟨t1, t23⟩ := or_none hsil'
  obtain ⟨t2, t3⟩ := or_none t23
  rw [← hown] at t1 t3
  rw [← hcom] at t2
  have hyes := runC_yes_iff h
  obtain ⟨R', b₁, z₁, b₂, z₂, b₃, z₃, hR', hb₁, hw₁, hq, hb₂, hw₂, hb₃, hw₃, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) ps [] []).1).symm
  have hseal := seal_back hq
  have hst := storedWords_lt H w₀ rc
  -- the first chain
  have X₁ : (ChainProgress.settle ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
      ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
        F.first.blocksInOrder, []⟩).bind
      (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first) = .ok z₁ := by
    have e : ChainProgress.settle ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
        ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
          F.first.blocksInOrder, []⟩ = .ok b₁ := hb₁
    rw [e]
    exact hw₁
  have n₁' : fallFree 0 F.first.blocksInOrder (fallsBy f₁ F.first.blocksInOrder) (F.start₁ (F.pub x)) (roundsOf z₁.laid)
      z₁.cols := by
    have e : (withEmptySealRound (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩ : Fmt.View)).rounds =
        roundsOf z₁.laid := hseal
    have n := n₁
    rw [show (withEmptySealRound (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩ : Fmt.View)).rounds =
      roundsOf z₁.laid from e] at n
    exact n
  obtain ⟨e₁, m₁, v1, q1, i1, g1⟩ := chain_accepts_alongJ (φ := Face.own) (hs := H.first)
    ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.own.sees R.own)
    (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
      (some (F.start₁ (F.pub x))) []) R.first ρ.first F.first.blocksInOrder
    F.first.blocksInOrder T.I₁ (fallsBy f₁ F.first.blocksInOrder) J₁ T.h₁ Y₁ C₁ R.first _ z₁ ρ.first
    (F.start₁ (F.pub x))
    { R.start₁ H with opened := some [] } [] [] [] rfl rfl rfl rfl rfl
    ((walk_nil_nil _ _).trans rfl)
    (steps_part0 _ _ s1) rfl rfl rfl rfl T.a₁ Y.j₁ t1 s1 d1 X₁ n₁'
  -- the shared chain
  have X₂ : (ChainProgress.settle ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
      ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
        F.shared.blocksInOrder, []⟩).bind
      (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared) = .ok z₂ := by
    have e : ChainProgress.settle ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
        ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
          F.shared.blocksInOrder, []⟩ = .ok b₂ := hb₂
    rw [e]
    exact hw₂
  obtain ⟨e₂, m₂, v2, q2, i2, g2⟩ := chain_accepts_alongJ (φ := Face.shared) (hs := H.shared)
    ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.shared.sees R.common)
    (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
      (some (F.start₂ (F.pub x))) []) R.shared ρ.shared F.shared.blocksInOrder
    F.shared.blocksInOrder T.I₂ (fallsBy f₂ F.shared.blocksInOrder) J₂ T.h₂ Y₂ C₂ R.shared _ z₂ ρ.shared
    (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] } [] [] [] rfl rfl rfl rfl rfl
    ((walk_nil_nil _ _).trans rfl) (steps_part0 _ _ s2) rfl rfl rfl rfl T.a₂ Y.j₂ t2 s2 d2 X₂ n₂
  -- the second chain's start
  have inv₁ : z₁.Inv [] := walk_inv _ [] _ _ b₁ z₁ (start_inv hb₁) hw₁
  have inv₂ : z₂.Inv [] := walk_inv _ [] _ _ b₂ z₂ (start_inv hb₂) hw₂
  obtain ⟨s₃, hs₃, js₃⟩ := Y.st₃ e₁ _ _ e₂ _ _ z₁.cols z₂.cols v1 v2 i1 i2 (inv₁ m₁ q1) (inv₂ m₂ q2)
    g1 g2
  have i0 := T.a₃ _ _ _ _ _ _ s₃ z₁.cols z₂.cols i1 i2 hs₃ (inv₁ m₁ q1) (inv₂ m₂ q2)
  rw [envThird_eq] at i0
  have hdoor : door₃ F x z₁.ver z₂.ver = some s₃ := by
    rw [v1, v2]
    show (F.start₃ (F.pub x) e₁ e₂).toOption = some s₃
    rw [hs₃]
    rfl
  have l1 : m₁.loc = ρ.first := (walk_mid hb₁ hw₁ q1).2.1
  -- the second chain
  have hL₃ : ∀ ps, treeThird z₁.laid z₂.laid ps =
      (envOf (H.storedWords w₀ rc) (taken₃ z₁.laid z₂.laid) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) z₁.laid z₂.laid ps).2).symm
  have X₃ : (ChainProgress.settle ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
      F.second.blocksInOrder
      ⟨some { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) }, some s₃, none, [], [],
        [], F.second.blocksInOrder, []⟩).bind
      (walk ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ R.second
        ρ.second) = .ok z₃ := by
    have e := hb₃
    rw [q1, q2, hdoor] at e
    have e' : ChainProgress.settle ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
        F.second.blocksInOrder
        ⟨some { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) }, some s₃, none, [], [],
          [], F.second.blocksInOrder, []⟩ = .ok b₃ := e
    rw [e']
    exact hw₃
  have hA₃ : (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
      F.second.blocksInOrder (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
      (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)).bind
      (walk ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ [] []) =
      ChainProgress.settle ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
      ⟨some { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) }, some s₃, none, [], [],
        [], F.second.blocksInOrder, []⟩ := by
    rw [walk_nil_nil, q1, q2, hdoor]
    rfl
  obtain ⟨e₃, m₃, v3, -, i3, g3⟩ := chain_accepts_alongJ (φ := Face.own) (hs := H.second)
    ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ (taken₃ z₁.laid z₂.laid) hL₃
    k (Face.own.sees R.own)
    (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
      (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
      (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)) R.second ρ.second F.second.blocksInOrder
    F.second.blocksInOrder T.I₃ (fallsBy f₃ F.second.blocksInOrder) J₃ T.h₃
    (Y₃ z₁ z₂ ((congrArg (fun e => e.bind (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first))
        hb₁).trans hw₁)
      ((congrArg (fun e => e.bind (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared))
        hb₂).trans hw₂))
    C₃ R.second _ z₃ ρ.second s₃
    { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) } [] [] [] rfl rfl rfl rfl rfl hA₃
    (steps_part0 _ _ s3) rfl rfl rfl rfl i0 js₃
    (by
      show chainStopAt (Face.own.sees R.own) F.second.blocksInOrder H.second m₁.loc ρ.second = none
      rw [l1]
      exact t3)
    s3 d3 X₃ (n₃ e₁ e₂ s₃ v1 v2 hs₃)
  have hends : ((z₁.ver, z₂.ver, z₃.ver) : Option F.S₁ × Option F.S₂ × Option F.S₃) =
      (some e₁, some e₂, some e₃) := by rw [v1, v2, v3]
  refine ⟨⟨e₁, e₂, e₃, hends⟩, hyes.2 ⟨hp, hx, ?_, ?_, ?_, e₁, e₂, e₃, hends,
    Y.fin e₁ _ _ e₂ _ _ e₃ _ _ hends i1 i2 i3 g1 g2 g3⟩⟩
  · exact (okViewW_split _ _).2 ⟨okViewW_dropLast (walk_said _ _ _ b₁ z₁ (drawsFit_elems _ _ d1)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₁)).trans rfl) hw₁),
      walk_lt _ hst _ _ b₁ z₁ (start_lt _ hst _ _ _ hb₁) hw₁⟩
  · exact (okViewW_split _ _).2 ⟨walk_said _ _ _ b₂ z₂ (drawsFit_elems _ _ d2)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₂)).trans rfl) hw₂,
      walk_lt _ hst _ _ b₂ z₂ (start_lt _ hst _ _ _ hb₂) hw₂⟩
  · exact (okViewW_split _ _).2 ⟨walk_said _ _ _ b₃ z₃ (drawsFit_elems _ _ d3)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₃)).trans rfl) hw₃,
      walk_lt _ hst _ _ b₃ z₃ (start_lt _ hst _ _ _ hb₃) hw₃⟩


/-! ## 4 At the strategy -/

/-- The same with sentences on the verifier's state: YesAlongJ in place of YesAlong. -/
theorem yes_at_requestStrategyTrackingVerifier_alongJ (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
    (silent : Xi → TF → TJ → T3 → Bool) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R2]
    [Nonempty R2] [Fintype R3] [Inhabited R3] (J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3)
    (sh : Ky → F.S₂) (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str) (w : W₀ × Rc × Sd)
    (x : Xi) (c : (Purse Bk.shared × R2) × ((Purse Bk.first × Purse Bk.second) × R3))
    (y : (Iop.oneExternalString (2 ^ D.a) SgX).Str) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ = .ok R)
    (hp : F.planOk = true) (hq : sealPlain F = true) (hD : DataFits F D)
    (h4 : halvedAll F H = true) (h0 : F.okStart x = true) (hP : PlanServes H w.1 w.2.1 R)
    (hk : ∀ r2 r3, (J r2 r3).keyOf w.1 w.2.1 w.2.2 = H.key x)
    (hsh : sh (H.key x) = F.start₂ (F.pub x))
    (hy : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ s ∈ d.stored, ∀ (p : Nat) (h : p < 2 ^ D.a),
      H.storedWords w.1 w.2.1 s.item p = some (y ⟨p, h⟩).2)
    (hdue : (drawsAt C D tF tJ t3 ρ).due F = true)
    (hw : ρ ∉ (honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.withheld w x)
    (T : ThreadsP F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ R)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (J₁ : Nat → F.S₁ → Prop) (J₂ : Nat → F.S₂ → Prop) (J₃ : Nat → F.S₃ → Prop)
    (Y : ∀ r, runC F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) = .ok r →
      YesAlongJ (drawsAt C D tF tJ t3 ρ) r T f₁ f₂ f₃ J₁ J₂ J₃)
    (hfall : ∀ r, runC F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) =
      .ok r → viewsFall F f₁ f₂ f₃ x r.run.views = none) :
    F.run x
      (view₁ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1)
      (view₂ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1)
      (view₃ C D tF tJ t3 y
        (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1) = true ∧
    ((chainsOf C D tF tJ t3).msgF
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 c.2.2).front w.1 w.2.1 w.2.2 x ∧
    ((chainsOf C D tF tJ t3).msgJ
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 default).join w.1 w.2.1 w.2.2 ∧
    ((chainsOf C D tF tJ t3).msg3
      (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1).2 =
      (J c.1.2 c.2.2).seam w.1 w.2.1 w.2.2 x := by
  obtain ⟨-, tr, htr, -⟩ := ready_ok hR
  have hsil : silentAt F H w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ) = none := by
    have h1 := (withheldC_iff C D tF tJ t3 F silent Bk H J sh ext w x (by rw [htr]; rfl) ρ).not.1
      hw
    cases hs : silentAt F H w.1 w.2.1 x (drawsAt C D tF tJ t3 ρ) with
    | none => rfl
    | some z =>
      rw [hs] at h1
      exact absurd rfl h1
  obtain ⟨r, hr⟩ := runC_returns hR hq hdue hsil hP T.I₁ T.I₂ T.I₃ T.h₁ T.h₂ T.h₃ T.a₁ T.a₂ T.a₃
  obtain ⟨-, hyes⟩ := runC_accepts_alongJ hr hR hp h0 hdue hsil T f₁ f₂ f₃ J₁ J₂ J₃ (Y r hr)
    (hfall r hr)
  obtain ⟨v1, v2, v3, m1, m2, m3⟩ := views_of_stratC C D tF tJ t3 F Bk H (J c.1.2 default)
    (J c.1.2 c.2.2) sh w c.1.1 x c.2.1 y ρ hr hp hD h4 (hk _ _) (hk _ _) hsh hy
  have e : (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1 =
      trAtC C D tF tJ t3 F Bk H (J c.1.2 default) (J c.1.2 c.2.2) sh w c.1.1 x c.2.1 ρ := rfl
  rw [e, v1, v2, v3]
  exact ⟨hyes, m1, m2, m3⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.SaysYesAlongJ
#print axioms ProofFile.Honest.SaysYesAlong.toJ
#print axioms ProofFile.Honest.SaysYesJ.along
#print axioms ProofFile.Honest.chain_accepts_alongJ
#print axioms ProofFile.Honest.YesAlongJ
#print axioms ProofFile.Honest.YesAlong.toJ
#print axioms ProofFile.Honest.runC_accepts_alongJ
#print axioms ProofFile.Honest.yes_at_requestStrategyTrackingVerifier_alongJ
