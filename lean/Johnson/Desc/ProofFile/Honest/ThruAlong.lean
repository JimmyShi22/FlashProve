-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruAlong.lean: the rule for a file's acceptance, with the verifier's
yes asked at the run alone. The rule of Honest/Law/AcceptC.lean asks SaysYes over every state that an
invariant allows and at every list of challenges. A run's return does not need that: runC_returns
takes PlaysOn and no SaysYes. So where the run stands, the yes of each sub-protocol can be asked at
the walk's own state and the run's own challenges, with the run in hand: the fifth of a place's
statements alone; PlaysOn stays as it is. A law that speaks at a run (hrun, and the part called) is
joined to the rule by Honest/ThruAlongStand.lean.

  SaysYesAlong         the second condition, at one walk: at the list of rounds and challenges that
                       the walk goes through, at the place where it stands
  SaysYes.along        the second condition gives it, at any walk
  chain_accepts_along  one chain: chain_accepts with SaysYesAlong
  YesAlong             what a run asks of the yes, beside ThreadsP: the three chains, the second
                       chain's start, the last test
  runC_accepts_along   the file, with a test on the falls
  yes_at_requestStrategyTrackingVerifier_along  at the strategy of honestBatchProverOfFile: yes_at_stratC with ThreadsP and YesAlong

By what. The text of chain_accepts, runC_accepts (Honest/Law/AcceptC.lean), runC_accepts_views
(Honest/Law/FallFree.lean) and yes_at_stratC (Honest/Law/ThreadStratC.lean), with three premises
turned: the block's yes, the second chain's start and the last test, each asked at the run;
ThreadsP (Honest/Law/OwedParts.lean). ThreadsC gives all three: ThreadsC.along
(Honest/ThruAlongStand.lean).

How a place pays SaysYesAlong. Its premises say that the blocks pre stand in front of the block and
that the walk, over their rounds lp and challenges dp, stands at z. At a block with a round that
tells z. At a block without a round it does not: settle asks the block at once, so the equation
holds z only through that block's own verdict, and a payer there has to give the yes as SaysYes asks
it, at every state of its invariant. saysYes_seat and its like are
general in their A and their fall: in a place's own proof they serve at A := «the state is this
run's» and at a fall of that proof alone that answers at every other list of challenges. The falls
of the rule stay what they are: they are measured, and hfall reads them.

Limits.
  * PlaysOn stays asked at every state that the invariants allow: the run's return comes from it.
  * A place may read the run only in front of its block and at the block's own rounds: behind a
    block that rejects the run holds substitutes. At a place's premises no block in front has
    rejected (z.ver = some s); nothing here says that a block behind it accepts.
  * YesAlong.fin and YesAlong.st₃ are asked at the run's own ends.
  * The rules conclude that FileDescription.run accepts: one of the nine tests of the verdict, as in
    Honest/Law/AcceptC.lean. They are conditional and pointwise: nothing on how likely a stop or a
    fall is.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC
import Johnson.Desc.ProofFile.Honest.Law.OwedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD chainsOf view₁ view₂ view₃)
open _root_.Run.PQ (CK SgX)

variable {S Cl Xi V W Y Pb W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-! ## 1 The condition -/

/-- A result, bound to its own return. -/
theorem except_bind_ok {ε α : Type} (e : Except ε α) : e.bind Except.ok = e := by
  cases e <;> rfl

/-- A walk over no round returns where it stands. -/
theorem walk_nil_nil (L : Lay) (e : Except Refusal (ChainProgress S Cl W Y)) :
    e.bind (walk L [] []) = e := by
  cases e <;> rfl

/-- A walk over two stretches of rounds, from a result. -/
theorem walk_seq (L : Lay) (lp : List (Step W Y)) (dp : List Fmt.Drawn) (l : List (Step W Y))
    (d : List Fmt.Drawn) (hn : dp.length = lp.length) (A₀ : Except Refusal (ChainProgress S Cl W Y)) :
    A₀.bind (walk L (lp ++ l) (dp ++ d)) = (A₀.bind (walk L lp dp)).bind (walk L l d) := by
  cases A₀ with
  | error e => rfl
  | ok a => exact walk_append L l d lp dp a hn

/-- **The second condition at one walk.** k: the run's coins. A₀: where the walk starts. l₀, d₀, bs₀:
its rounds, challenges and blocks. As SaysYes, at the one state where the walk stands in front of the
block, with the blocks pre, their rounds lp and challenges dp behind it, at the tables that the walk
has laid (envOf L.stored taken z.laid), and at the block's own stretch of rounds l and challenges ds.
At a block without a round the premises do not tell z: see the file's head. -/
def SaysYesAlong (φ : Face V W Pb) (Bk : ProverCoinCounts) (k : Coins Bk) (L : Lay)
    (taken : Nat → Nat → Option (Place × Table)) (hs : List (Placed V W Y))
    (b : Block S Cl) (fall : S → List Fmt.Drawn → Option String)
    (A : Coins Bk → S → Mid W Y → Env → Prop) (A₀ : Except Refusal (ChainProgress S Cl W Y))
    (l₀ : List (Step W Y)) (d₀ : List Fmt.Drawn) (bs₀ : List (Block S Cl)) : Prop :=
  ∀ s m ds l y cols lp dp lq dq t z pre, l₀ = lp ++ l ++ lq → d₀ = dp ++ ds ++ dq →
    dp.length = lp.length → bs₀ = pre ++ b :: t → lp.length = (pre.flatMap (·.rounds)).length →
    A₀.bind (walk L lp dp) = ChainProgress.settle L (b :: t) z → z.own = [] →
    z.mid = some m → z.ver = some s → A k s m (envOf L.stored taken z.laid) →
    drawsFit b.rounds ds = true →
    chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none → fall s ds = none →
    chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) (φ.sees m.st.input) [b] hs = .ok l →
    play l ds [] m = .ok y →
    fillCols (readsOf L.chain L.firstTree ((envOf L.stored taken z.laid).add y.1).stored
      ((envOf L.stored taken z.laid).add y.1).tree b.rounds ds) [] = .ok cols →
    ∃ s' n, b.step L.firstTree s (roundsOf y.1) cols = .ok (s', n)

/-- SaysYes gives it, at any walk. -/
theorem SaysYes.along {φ : Face V W Pb} {Bk : ProverCoinCounts} {L : Lay} {hs : List (Placed V W Y)}
    {b : Block S Cl} {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W Y → Env → Prop} (h : SaysYes φ Bk L.chain L.firstTree hs b fall A)
    (k : Coins Bk) (taken : Nat → Nat → Option (Place × Table))
    (A₀ : Except Refusal (ChainProgress S Cl W Y)) (l₀ : List (Step W Y)) (d₀ : List Fmt.Drawn)
    (bs₀ : List (Block S Cl)) : SaysYesAlong φ Bk k L taken hs b fall A A₀ l₀ d₀ bs₀ :=
  fun s m ds l y cols _ _ _ _ _ z _ _ _ _ _ _ _ _ _ _ hA hd hst hf hc hp hcols =>
    h k s m (envOf L.stored taken z.laid) ds l y cols hA hd hst hf hc hp hcols

/-! ## 2 One chain -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **One chain.** chain_accepts, with the yes asked along the walk. lp, dp: what has been walked
of l₀ and d₀ in front of z. -/
theorem chain_accepts_along (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (k : Coins Bk) (v : Option V)
    (A₀ : Except Refusal (ChainProgress S Cl W Y)) (l₀ : List (Step W Y)) (d₀ : List Fmt.Drawn)
    (bs₀ : List (Block S Cl)) :
    ∀ (bs : List (Block S Cl)) (I : Nat → Coins Bk → S → Mid W Y → Env → Prop)
      (fl : Nat → S → List Fmt.Drawn → Option String),
    (∀ j b, bs[j]? = some b → PlaysOn φ Bk L.chain L.firstTree hs b (I j) (I (j + 1))) →
    (∀ j b, bs[j]? = some b → SaysYesAlong φ Bk k L taken hs b (fl j) (I j) A₀ l₀ d₀ bs₀) →
    ∀ (l : List (Step W Y)) (z z' : ChainProgress S Cl W Y) (ds : List Fmt.Drawn) (s : S) (m : Mid W Y)
      (lp : List (Step W Y)) (dp : List Fmt.Drawn) (pre : List (Block S Cl)),
    l₀ = lp ++ l → d₀ = dp ++ ds → dp.length = lp.length → bs₀ = pre ++ bs →
    lp.length = (pre.flatMap (·.rounds)).length →
    A₀.bind (walk L lp dp) = ChainProgress.settle L bs z →
    (∀ u ∈ l, u.move.isSome = false → u.addr.part = 0) → z.own = [] → z.mid = some m →
    z.ver = some s → φ.sees m.st.input = v → I 0 k s m (envOf L.stored taken z.laid) →
    chainStopAt v bs hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v bs hs = .ok l →
    drawsFit (bs.flatMap (·.rounds)) ds = true →
    (ChainProgress.settle L bs z).bind (walk L l ds) = .ok z' →
    fallFree L.firstTree bs fl s ((roundsOf z'.laid).drop z.laid.length)
      (z'.cols.drop z.cols.length) →
    ∃ s' m', z'.ver = some s' ∧ z'.mid = some m' ∧
      I bs.length k s' m' (envOf L.stored taken z'.laid)
  | [], I, fl, _, _, l, z, z', ds, s, m, _, _, _, _, _, _, _, _, _, _, ho, hm, hv, _, h0, _, hl, hd,
      hz, _ => by
    have hds : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => simp [drawsFit] at hd
    subst hds
    simp only [chainSteps] at hl
    cases hl
    have hz' : (Except.ok { z with todo := [] } : Except Refusal (ChainProgress S Cl W Y)) = .ok z' := hz
    cases hz'
    exact ⟨s, m, hv, hm, h0⟩
  | b :: t, I, fl, h, hy, l, z, z', ds, s, m, lp, dp, pre, hl₀, hd₀, hn₀, hb₀, hq₀, hA, hp0, ho, hm,
      hv, hsee, h0, hst, hl, hd, hz, hff => by
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
      (by rw [hd₀, List.append_assoc, List.take_append_drop]) hn₀ hb₀ hq₀ hA ho hm hv h0 hd₁
      (by rw [hsee]; exact hs₁') ff1 (by rw [hsee]; exact hl₁) p₁ f₁
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
    refine chain_accepts_along L taken hL k v A₀ l₀ d₀ bs₀ t (fun j => I (j + 1))
      (fun j => fl (j + 1))
      (fun j b' hj' => h (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj'))
      (fun j b' hj' => hy (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj')) l₂
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
      hB'
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

/-- **What a run asks of the yes**, beside ThreadsP, at the run r at ρ: the three chains at their
walks, the second chain's start and the last test at the run's ends. -/
structure YesAlong {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X} (ρ : Draws) (r : RunC F)
    (T : ThreadsP F Bk H w₀ rc x k R) (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂))
    (f₃ : List (Fall F.S₃)) : Prop where
  y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
    SaysYesAlong .own Bk k ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) H.first b (fallOf f₁ b.place) (T.I₁ j)
      (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
        (some (F.start₁ (F.pub x))) []) R.first ρ.first F.first.blocksInOrder
  y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
    SaysYesAlong .shared Bk k ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) H.shared b (fallOf f₂ b.place)
      (T.I₂ j)
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
    SaysYesAlong .own Bk k ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
      (taken₃ z₁.laid z₂.laid) H.second
      b (fallOf f₃ b.place) (T.I₃ j)
      (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
        (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
        (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)) R.second ρ.second F.second.blocksInOrder
  st₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, r.ends.1 = some e₁ → r.ends.2.1 = some e₂ →
    T.I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ → T.I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
    m₁.opened = some o₁ → m₂.opened = some o₂ → ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃
  fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, r.ends = (some e₁, some e₂, some e₃) →
    T.I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ → T.I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
    T.I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ → F.fin x e₁ e₂ e₃ = true

/-- **The rule for a file's acceptance, with the yes asked at the run.** -/
theorem runC_accepts_along {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hp : F.planOk = true) (hx : F.okStart x = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (T : ThreadsP F Bk H w₀ rc x k R)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (Y : YesAlong ρ r T f₁ f₂ f₃) (hv : viewsFall F f₁ f₂ f₃ x r.run.views = none) :
    (∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨n₁, n₂, n₃⟩ := fallFree_of_views h f₁ f₂ f₃ hv
  have Y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYesAlong .own Bk k ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) H.first b
        (fallsBy f₁ F.first.blocksInOrder j) (T.I₁ j)
        (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
          (some (F.start₁ (F.pub x))) []) R.first ρ.first F.first.blocksInOrder := by
    intro j b hj
    have e : fallsBy f₁ F.first.blocksInOrder j = fallOf f₁ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact Y.y₁ j b hj
  have Y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYesAlong .shared Bk k ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) H.shared b
        (fallsBy f₂ F.shared.blocksInOrder j) (T.I₂ j)
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
      SaysYesAlong .own Bk k ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
        (taken₃ z₁.laid z₂.laid) H.second b (fallsBy f₃ F.second.blocksInOrder j) (T.I₃ j)
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
  obtain ⟨e₁, m₁, v1, q1, i1⟩ := chain_accepts_along (φ := Face.own) (hs := H.first)
    ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.own.sees R.own)
    (ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
      (some (F.start₁ (F.pub x))) []) R.first ρ.first F.first.blocksInOrder
    F.first.blocksInOrder T.I₁ (fallsBy f₁ F.first.blocksInOrder) T.h₁ Y₁ R.first _ z₁ ρ.first (F.start₁ (F.pub x))
    { R.start₁ H with opened := some [] } [] [] [] rfl rfl rfl rfl rfl
    ((walk_nil_nil _ _).trans rfl)
    (steps_part0 _ _ s1) rfl rfl rfl rfl T.a₁ t1 s1 d1 X₁ n₁'
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
  obtain ⟨e₂, m₂, v2, q2, i2⟩ := chain_accepts_along (φ := Face.shared) (hs := H.shared)
    ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.shared.sees R.common)
    (ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
      (some (F.start₂ (F.pub x))) []) R.shared ρ.shared F.shared.blocksInOrder
    F.shared.blocksInOrder T.I₂ (fallsBy f₂ F.shared.blocksInOrder) T.h₂ Y₂ R.shared _ z₂ ρ.shared
    (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] } [] [] [] rfl rfl rfl rfl rfl
    ((walk_nil_nil _ _).trans rfl) (steps_part0 _ _ s2) rfl rfl rfl rfl T.a₂ t2 s2 d2 X₂ n₂
  -- the second chain's start
  have inv₁ : z₁.Inv [] := walk_inv _ [] _ _ b₁ z₁ (start_inv hb₁) hw₁
  have inv₂ : z₂.Inv [] := walk_inv _ [] _ _ b₂ z₂ (start_inv hb₂) hw₂
  obtain ⟨s₃, hs₃⟩ := Y.st₃ e₁ _ _ e₂ _ _ z₁.cols z₂.cols v1 v2 i1 i2 (inv₁ m₁ q1) (inv₂ m₂ q2)
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
  obtain ⟨e₃, m₃, v3, -, i3⟩ := chain_accepts_along (φ := Face.own) (hs := H.second)
    ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ (taken₃ z₁.laid z₂.laid) hL₃
    k (Face.own.sees R.own)
    (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
      (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
      (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)) R.second ρ.second F.second.blocksInOrder
    F.second.blocksInOrder T.I₃ (fallsBy f₃ F.second.blocksInOrder) T.h₃
    (Y₃ z₁ z₂ ((congrArg (fun e => e.bind (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first))
        hb₁).trans hw₁)
      ((congrArg (fun e => e.bind (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared))
        hb₂).trans hw₂))
    R.second _ z₃ ρ.second s₃
    { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) } [] [] [] rfl rfl rfl rfl rfl hA₃
    (steps_part0 _ _ s3) rfl rfl rfl rfl i0
    (by
      show chainStopAt (Face.own.sees R.own) F.second.blocksInOrder H.second m₁.loc ρ.second = none
      rw [l1]
      exact t3)
    s3 d3 X₃ (n₃ e₁ e₂ s₃ v1 v2 hs₃)
  have hends : ((z₁.ver, z₂.ver, z₃.ver) : Option F.S₁ × Option F.S₂ × Option F.S₃) =
      (some e₁, some e₂, some e₃) := by rw [v1, v2, v3]
  refine ⟨⟨e₁, e₂, e₃, hends⟩, hyes.2 ⟨hp, hx, ?_, ?_, ?_, e₁, e₂, e₃, hends,
    Y.fin e₁ _ _ e₂ _ _ e₃ _ _ hends i1 i2 i3⟩⟩
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

/-- **At the strategy of honestBatchProverOfFile, with the yes asked at the run.** yes_at_stratC with ThreadsP in
place of ThreadsC, and with YesAlong at the run that runC returns. -/
theorem yes_at_requestStrategyTrackingVerifier_along (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)
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
    (Y : ∀ r, runC F Bk H w.1 w.2.1 x ⟨c.2.1.1, c.1.1, c.2.1.2⟩ (drawsAt C D tF tJ t3 ρ) = .ok r →
      YesAlong (drawsAt C D tF tJ t3 ρ) r T f₁ f₂ f₃)
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
  obtain ⟨-, hyes⟩ := runC_accepts_along hr hR hp h0 hdue hsil T f₁ f₂ f₃ (Y r hr) (hfall r hr)
  obtain ⟨v1, v2, v3, m1, m2, m3⟩ := views_of_stratC C D tF tJ t3 F Bk H (J c.1.2 default)
    (J c.1.2 c.2.2) sh w c.1.1 x c.2.1 y ρ hr hp hD h4 (hk _ _) (hk _ _) hsh hy
  have e : (((honestBatchProverOfFile C D tF tJ t3 F silent Bk H J sh ext).one.strat w x c).run ρ).1 =
      trAtC C D tF tJ t3 F Bk H (J c.1.2 default) (J c.1.2 c.2.2) sh w c.1.1 x c.2.1 ρ := rfl
  rw [e, v1, v2, v3]
  exact ⟨hyes, m1, m2, m3⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.except_bind_ok
#print axioms ProofFile.Honest.walk_nil_nil
#print axioms ProofFile.Honest.walk_seq
#print axioms ProofFile.Honest.SaysYesAlong
#print axioms ProofFile.Honest.SaysYes.along
#print axioms ProofFile.Honest.chain_accepts_along
#print axioms ProofFile.Honest.YesAlong
#print axioms ProofFile.Honest.runC_accepts_along
#print axioms ProofFile.Honest.yes_at_requestStrategyTrackingVerifier_along
