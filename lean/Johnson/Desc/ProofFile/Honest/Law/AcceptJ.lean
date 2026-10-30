-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/AcceptJ.lean: THE FILE's RULE FOR ACCEPTANCE WITH A THIRD FAMILY:
WHAT HOLDS ALONG A RUN AT WHICH NOTHING HAS STOPPED AND NO FALL HAS SPOKEN. `runC_accepts`
(Honest/Law/AcceptC.lean) carries one family of invariants, by the members' first law (`PlaysOn`,
Honest/Law/ThreadC.lean), which stands AT ALL CHALLENGES, fall or not: so it cannot hold a fact that
fails where a fall speaks (at a batching: that a drawn value is not 0, on which the shape of the
state behind hangs). That rule's induction has, at each member, that member's «no stop», «no fall»
and its step's yes in hand at the line where the next invariant is made. Here a second family J, on
the verifier's state alone, is carried by a third law a member under just these (`CarriesOn`), and
is in hand where a member's yes is asked (`SaysYesJ`).

WHAT THIS IS. Two definitions: premises' forms. Two conditional lemmas on our own fold, pointwise,
WHOSE PROOFS ARE `chain_accepts`' AND `runC_accepts`' OWN, with two premises and one line more a
chain. Two corollaries hold the elder forms against the new. None of the library's goals.

  1  `CarriesOn`, `SaysYesJ`, `saysYesJ_of`, `carriesOn_true`
  2  `chain_acceptsJ`   ONE CHAIN
  3  `runC_acceptsJ`   THE FILE

MET FOR NOTHING. All four ways of `runC_accepts`' head; and a fifth: A J THAT HOLDS AT NO START.
`PlaysOn` is `runC_accepts`' own: the run must return, fall or not (the rule of
Honest/Law/RunsFile.lean takes no J).

Limits. As `runC_accepts`, the states at which the invariants are asked at the starts among them,
and that `PlaysOn`, `SaysYesJ` and `CarriesOn` are asked at every value of the field `opened` that
the invariant allows: at a prover with a part that reads the columns and errs at `none` (its duty:
Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant that lets `none` through before that
part's sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits).
Its premises are shown here of no description. Nothing on how likely a stop or a fall is. Among the
hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round, and as many
challenges as rounds): `chain_acceptsJ`; `Draws.due` (the challenges are
such as the description's rounds can draw; the first chain's last challenge is the empty one):
`runC_acceptsJ`; `FileDescription.planOk` (the library's executable test): `runC_acceptsJ`; `ready … = .ok`
(`ready` returns at these coins): `runC_acceptsJ`; `FileDescription.okStart` (the library's executable
test, at the instance): `runC_acceptsJ`; `runC … = .ok` (`runC` returns at these coins and
challenges): `runC_acceptsJ`. This file proves nothing about soundness, completeness, hiding or any
other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.AcceptC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W Y Pb W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The two forms -/

/-- ONE MEMBER's THIRD LAW: WHAT IS CARRIED UNDER «NO STOP, NO FALL» ALONE. J, J': sentences on the
verifier's state in front of the member and behind it. Where the first law's invariant A and J hold
in front (A alone can pin the state's field `opened`), the member's rounds can draw the challenges,
no part stops, THE MEMBER's FALL SAYS NOTHING, and the member's own step says yes on what is played
and laid: J' holds behind. It is a definition: a premise's form. Nothing is claimed of it, and it is
none of the library's goals. -/
def CarriesOn (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : Nat) (hs : List (Placed V W Y))
    (b : Block S Cl) (fall : S → List Fmt.Drawn → Option String)
    (A : Coins Bk → S → Mid W Y → Env → Prop) (J J' : S → Prop) : Prop :=
  ∀ k s m E ds l y cols s' n, A k s m E → J s → drawsFit b.rounds ds = true →
    chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none → fall s ds = none →
    chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs = .ok l →
    play l ds [] m = .ok y →
    fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] = .ok cols →
    b.step ft s (roundsOf y.1) cols = .ok (s', n) → J' s'

/-- THE SECOND LAW WITH J IN HAND: outside the stops and outside its fall, AT A STATE THAT MEETS J,
the member's own step says yes. `SaysYes` (Honest/Law/ThreadC.lean) is its case J := fun _ => True.
A definition: a premise's form. -/
def SaysYesJ (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : Nat) (hs : List (Placed V W Y))
    (b : Block S Cl) (fall : S → List Fmt.Drawn → Option String)
    (A : Coins Bk → S → Mid W Y → Env → Prop) (J : S → Prop) : Prop :=
  ∀ k s m E ds l y cols, A k s m E → J s → drawsFit b.rounds ds = true →
    chainStopAt (φ.sees m.st.input) [b] hs m.loc ds = none → fall s ds = none →
    chainSteps Bk (Bk.rowsOf chain) (k.look chain) (φ.sees m.st.input) [b] hs = .ok l →
    play l ds [] m = .ok y →
    fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] = .ok cols →
    ∃ s' n, b.step ft s (roundsOf y.1) cols = .ok (s', n)

/-- The elder second law gives the new one, at whatever J. -/
theorem saysYesJ_of {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat} {hs : List (Placed V W Y)}
    {b : Block S Cl} {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W Y → Env → Prop} (h : SaysYes φ Bk chain ft hs b fall A)
    (J : S → Prop) : SaysYesJ φ Bk chain ft hs b fall A J :=
  fun k s m E ds l y cols hA _ hd hst hf hl hp hc => h k s m E ds l y cols hA hd hst hf hl hp hc

/-- At the sentence that always holds nothing is owed. -/
theorem carriesOn_true (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : Nat) (hs : List (Placed V W Y))
    (b : Block S Cl) (fall : S → List Fmt.Drawn → Option String)
    (A : Coins Bk → S → Mid W Y → Env → Prop) (J : S → Prop) :
    CarriesOn φ Bk chain ft hs b fall A J (fun _ => True) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial

/-! ## 2 One chain -/

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **ONE CHAIN, WITH THE THIRD FAMILY.** As `chain_accepts` (Honest/Law/AcceptC.lean), whose proof
this is, with two premises and one line more: J is asked at the chain's start, is carried from
member to member under «no stop, no fall», is in hand where a member's yes is asked, and holds at
the chain's end. -/
theorem chain_acceptsJ (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (k : Coins Bk) (v : Option V) :
    ∀ (bs : List (Block S Cl)) (I : Nat → Coins Bk → S → Mid W Y → Env → Prop)
      (fl : Nat → S → List Fmt.Drawn → Option String) (J : Nat → S → Prop),
    (∀ j b, bs[j]? = some b → PlaysOn φ Bk L.chain L.firstTree hs b (I j) (I (j + 1))) →
    (∀ j b, bs[j]? = some b → SaysYesJ φ Bk L.chain L.firstTree hs b (fl j) (I j) (J j)) →
    (∀ j b, bs[j]? = some b →
      CarriesOn φ Bk L.chain L.firstTree hs b (fl j) (I j) (J j) (J (j + 1))) →
    ∀ (l : List (Step W Y)) (z z' : ChainProgress S Cl W Y) (ds : List Fmt.Drawn) (s : S) (m : Mid W Y),
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
  | [], I, fl, J, _, _, _, l, z, z', ds, s, m, _, ho, hm, hv, _, h0, j0, _, hl, hd, hz, _ => by
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
  | b :: t, I, fl, J, h, hy, hc, l, z, z', ds, s, m, hp0, ho, hm, hv, hsee, h0, j0, hst, hl, hd, hz,
      hff => by
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
    obtain ⟨s', n', hstep⟩ := hy 0 b (by simp) k s m _ (ds.take b.rounds.length) l₁ y cols h0 j0
      hd₁ (by rw [hsee]; exact hs₁') ff1 (by rw [hsee]; exact hl₁) p₁ f₁
    have hJ' := hc 0 b (by simp) k s m _ (ds.take b.rounds.length) l₁ y cols s' n' h0 j0 hd₁
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
    refine chain_acceptsJ L taken hL k v t (fun j => I (j + 1)) (fun j => fl (j + 1))
      (fun j => J (j + 1))
      (fun j b' hj' => h (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj'))
      (fun j b' hj' => hy (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj'))
      (fun j b' hj' => hc (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj')) l₂
      (z.askedO L b (y.1, some y.2) cols) z' (ds.drop b.rounds.length) s' (y.2.took cols)
      (fun u hu => hp0 u (List.mem_append_right _ hu)) rfl hmid hver
      (by
        show φ.sees y.2.st.input = v
        rw [e1]
        exact hsee)
      hB' hJ'
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

/-- **THE FILE's RULE FOR ACCEPTANCE, WITH THE THIRD FAMILY.** As `runC_accepts`
(Honest/Law/AcceptC.lean), whose proof this is. J₁, J₂, J₃: sentences on the three chains'
verifier's states, by the member's number: at the two starts (j₁, j₂); behind the door from the two
ends (a₃); in hand at the last test (fin). A conditional lemma on our own fold, pointwise. Its end
is `FileDescription.run`'s yes, one of the nine tests of the reduction's verdict: not a verifier's accept.
It is none of the library's goals. -/
theorem runC_acceptsJ {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hp : F.planOk = true) (hx : F.okStart x = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none)
    (I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (fl₁ : Nat → F.S₁ → List Fmt.Drawn → Option String)
    (fl₂ : Nat → F.S₂ → List Fmt.Drawn → Option String)
    (fl₃ : Nat → F.S₃ → List Fmt.Drawn → Option String)
    (J₁ : Nat → F.S₁ → Prop) (J₂ : Nat → F.S₂ → Prop) (J₃ : Nat → F.S₃ → Prop)
    (h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1)))
    (h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      PlaysOn .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1)))
    (h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1)))
    (y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYesJ .own Bk 0 0 H.first b (fl₁ j) (I₁ j) (J₁ j))
    (y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYesJ .shared Bk 1 0 H.shared b (fl₂ j) (I₂ j) (J₂ j))
    (y₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYesJ .own Bk 2 F.lastChainFirstTreeNumber H.second b (fl₃ j) (I₃ j) (J₃ j))
    (c₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
      CarriesOn .own Bk 0 0 H.first b (fl₁ j) (I₁ j) (J₁ j) (J₁ (j + 1)))
    (c₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      CarriesOn .shared Bk 1 0 H.shared b (fl₂ j) (I₂ j) (J₂ j) (J₂ (j + 1)))
    (c₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      CarriesOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (fl₃ j) (I₃ j) (J₃ j) (J₃ (j + 1)))
    (a₁ : I₁ 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₂ : I₂ 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (j₁ : J₁ 0 (F.start₁ (F.pub x))) (j₂ : J₂ 0 (F.start₂ (F.pub x)))
    (a₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → J₁ F.first.blocksInOrder.length e₁ →
      J₂ F.shared.blocksInOrder.length e₂ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
        I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂) ∧ J₃ 0 s₃)
    (fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
      J₁ F.first.blocksInOrder.length e₁ → J₂ F.shared.blocksInOrder.length e₂ → J₃ F.second.blocksInOrder.length e₃ →
      F.fin x e₁ e₂ e₃ = true)
    (n₁ : fallFree 0 F.first.blocksInOrder fl₁ (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1).rounds
      r.run.views.1.opened)
    (n₂ : fallFree 0 F.shared.blocksInOrder fl₂ (F.start₂ (F.pub x)) r.run.views.2.1.rounds
      r.run.views.2.1.opened)
    (n₃ : ∀ e₁ e₂ s₃, r.ends.1 = some e₁ → r.ends.2.1 = some e₂ →
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      fallFree F.lastChainFirstTreeNumber F.second.blocksInOrder fl₃ s₃ r.run.views.2.2.rounds r.run.views.2.2.opened) :
    (∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
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
  -- chain 1
  have X₁ : (ChainProgress.settle ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
      ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
        F.first.blocksInOrder, []⟩).bind
      (walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first) = .ok z₁ := by
    have e : ChainProgress.settle ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
        ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
          F.first.blocksInOrder, []⟩ = .ok b₁ := hb₁
    rw [e]
    exact hw₁
  have n₁' : fallFree 0 F.first.blocksInOrder fl₁ (F.start₁ (F.pub x)) (roundsOf z₁.laid) z₁.cols := by
    have e : (withEmptySealRound (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩ : Fmt.View)).rounds =
        roundsOf z₁.laid := hseal
    have n := n₁
    rw [show (withEmptySealRound (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩ : Fmt.View)).rounds =
      roundsOf z₁.laid from e] at n
    exact n
  obtain ⟨e₁, m₁, v1, q1, i1, u1⟩ := chain_acceptsJ (φ := Face.own) (hs := H.first)
    ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.own.sees R.own)
    F.first.blocksInOrder I₁ fl₁ J₁ h₁ y₁ c₁ R.first _ z₁ ρ.first (F.start₁ (F.pub x))
    { R.start₁ H with opened := some [] }
    (steps_part0 _ _ s1) rfl rfl rfl rfl a₁ j₁ t1 s1 d1 X₁ n₁'
  -- chain 2
  have X₂ : (ChainProgress.settle ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
      ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
        F.shared.blocksInOrder, []⟩).bind
      (walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared) = .ok z₂ := by
    have e : ChainProgress.settle ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
        ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
          F.shared.blocksInOrder, []⟩ = .ok b₂ := hb₂
    rw [e]
    exact hw₂
  obtain ⟨e₂, m₂, v2, q2, i2, u2⟩ := chain_acceptsJ (φ := Face.shared) (hs := H.shared)
    ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.shared.sees R.common)
    F.shared.blocksInOrder I₂ fl₂ J₂ h₂ y₂ c₂ R.shared _ z₂ ρ.shared (F.start₂ (F.pub x))
    { R.start₂ H with opened := some [] }
    (steps_part0 _ _ s2) rfl rfl rfl rfl a₂ j₂ t2 s2 d2 X₂ n₂
  -- the door
  have inv₁ : z₁.Inv [] := walk_inv _ [] _ _ b₁ z₁ (start_inv hb₁) hw₁
  have inv₂ : z₂.Inv [] := walk_inv _ [] _ _ b₂ z₂ (start_inv hb₂) hw₂
  obtain ⟨s₃, hs₃, i0, u0⟩ :=
    a₃ _ _ _ _ _ _ z₁.cols z₂.cols i1 i2 u1 u2 (inv₁ m₁ q1) (inv₂ m₂ q2)
  rw [envThird_eq] at i0
  have hdoor : door₃ F x z₁.ver z₂.ver = some s₃ := by
    rw [v1, v2]
    show (F.start₃ (F.pub x) e₁ e₂).toOption = some s₃
    rw [hs₃]
    rfl
  have l1 : m₁.loc = ρ.first := (walk_mid hb₁ hw₁ q1).2.1
  -- chain 3
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
  obtain ⟨e₃, m₃, v3, -, i3, u3⟩ := chain_acceptsJ (φ := Face.own) (hs := H.second)
    ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ (taken₃ z₁.laid z₂.laid) hL₃
    k (Face.own.sees R.own) F.second.blocksInOrder I₃ fl₃ J₃ h₃ y₃ c₃ R.second _ z₃ ρ.second s₃
    { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) } (steps_part0 _ _ s3) rfl rfl rfl
    rfl i0 u0
    (by
      show chainStopAt (Face.own.sees R.own) F.second.blocksInOrder H.second m₁.loc ρ.second = none
      rw [l1]
      exact t3)
    s3 d3 X₃ (n₃ e₁ e₂ s₃ v1 v2 hs₃)
  have hends : ((z₁.ver, z₂.ver, z₃.ver) : Option F.S₁ × Option F.S₂ × Option F.S₃) =
      (some e₁, some e₂, some e₃) := by rw [v1, v2, v3]
  refine ⟨⟨e₁, e₂, e₃, hends⟩, hyes.2 ⟨hp, hx, ?_, ?_, ?_, e₁, e₂, e₃, hends,
    fin _ _ _ _ _ _ _ _ _ i1 i2 i3 u1 u2 u3⟩⟩
  · exact (okViewW_split _ _).2 ⟨okViewW_dropLast (walk_said _ _ _ b₁ z₁ (drawsFit_elems _ _ d1)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₁)).trans rfl) hw₁),
      walk_lt _ hst _ _ b₁ z₁ (start_lt _ hst _ _ _ hb₁) hw₁⟩
  · exact (okViewW_split _ _).2 ⟨walk_said _ _ _ b₂ z₂ (drawsFit_elems _ _ d2)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₂)).trans rfl) hw₂,
      walk_lt _ hst _ _ b₂ z₂ (start_lt _ hst _ _ _ hb₂) hw₂⟩
  · exact (okViewW_split _ _).2 ⟨walk_said _ _ _ b₃ z₃ (drawsFit_elems _ _ d3)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) (start_laid hb₃)).trans rfl) hw₃,
      walk_lt _ hst _ _ b₃ z₃ (start_lt _ hst _ _ _ hb₃) hw₃⟩


end ProofFile.Honest

#print axioms ProofFile.Honest.saysYesJ_of
#print axioms ProofFile.Honest.carriesOn_true
#print axioms ProofFile.Honest.chain_acceptsJ
#print axioms ProofFile.Honest.runC_acceptsJ
#print axioms ProofFile.Honest.CarriesOn
#print axioms ProofFile.Honest.SaysYesJ
