-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/CellOf.lean: a part as a cell (Honest/Law/Rule/Cell.lean).
For a `Member` of a side (Honest/Side.lean), with its simulator, at a stretch of a session: its cell
(`cellOf`); that the cell's stage is the stretch's stage (Honest/Law/Rule/Real.lean: `Act.stage`),
as a function (`cell_stage`), where `get` and `put` are a lens on the part's own row, the part takes
the count that the book has for it, and the session's honest side at the part's address is
`partShows` at `pre` and `dry`; and that the two conditions of `Good` on a part by itself, `exact`
and `fresh`, give the cell's two conditions (`RowOk.exact`, `RowOk.fresh`,
Honest/Law/Rule/Items.lean)
at challenges that fit the part's rounds (`drawsFit`), at positions within `bud`, where the part is
not stopped by its second stop (for `exact` also: `pb` is the public value of the input, `φ.pub`).

  1  `castAll`, `map_cast`, `lend_cast`   blocks typed at the part's own names and counts, and at
     the entries': one list, written in two ways
  2  `lendPart_opt`   the coins that a part is given: its own row, and the blocks of the entries
     that name it
  3  `cellOf`   the definition
  4  `cell_stage`   the cell's stage is the stretch's
  5  `cell_exact`, `cell_fresh`   the two conditions

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Items
import Johnson.Desc.ProofFile.Honest.Law.Rule.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi S Cl V W Y Pb : Type}

/-! ## 1 One list, written in two ways -/

/- Blocks typed at one list of names and counts, read at an equal list. -/
def castAll {A B : List (String × Due)} (h : A = B) (x : CsAll A) : CsAll B := h ▸ x

theorem map_cast {A B : List (String × Due)} (h : A = B) {d : Due} {γ : Type}
    (f : Cs d × CsAll B → γ) :
    (unif (Cs d × CsAll A)).map (fun c => f (c.1, castAll h c.2)) =
      (unif (Cs d × CsAll B)).map f := by
  subst h
  rfl

theorem lend_cast (look : Addr → (d : Due) × Cs d) (E : List Ahead) {ds : List (String × Due)}
    (h : E.map Ahead.named = ds) : (lend look ds E).toOption = (runs look E).map (castAll h) := by
  subst h
  rw [lend_runs]
  cases runs look E <;> rfl

/-! ## 2 The coins that a part is given -/

theorem lendPart_opt {Bk : ProverCoinCounts} {a : Addr} {ch : Nat} (p : Part V W Y)
    {get : Coins Bk → Cs p.takes} {put : Cs p.takes → Coins Bk → Coins Bk}
    (hrow : RowAt Bk a ch p.takes get put) (hdue : p.takes = dueAt (Bk.rowsOf ch) a)
    (h₂ : (spentE Bk a).map Ahead.named = p.spends)
    (h₃ : (carryE Bk a).map Ahead.named = p.carries) (k : Coins Bk) :
    (lendPart Bk (Bk.rowsOf ch) (k.look ch) a p).toOption =
      (runs (k.look ch) (spentE Bk a)).bind fun sp =>
        (runs (k.look ch) (carryE Bk a)).map fun ca => (get k, castAll h₂ sp, castAll h₃ ca) := by
  have e2 := lend_cast (k.look ch) (spentE Bk a) h₂
  have e3 := lend_cast (k.look ch) (carryE Bk a) h₃
  have hg : (p.takes != dueAt (Bk.rowsOf ch) a) = false := by
    rw [← hdue]
    simp
  have hc : (k.look ch a).2.cut ⟨0, 0⟩ p.takes = some (get k) := by
    rw [hrow.self ch (Or.inl rfl) k]
    exact Cs.cut_zero _
  unfold lendPart
  simp only [hg, Bool.false_eq_true, if_false, hc]
  show ((lend (k.look ch) p.spends (spentE Bk a)).bind fun sp =>
    (lend (k.look ch) p.carries (carryE Bk a)).map fun ca => (get k, sp, ca)).toOption = _
  cases hs : lend (k.look ch) p.spends (spentE Bk a) with
  | error er =>
    rw [hs] at e2
    cases hr : runs (k.look ch) (spentE Bk a) with
    | none => rfl
    | some sp' =>
      rw [hr] at e2
      cases e2
  | ok sp =>
    rw [hs] at e2
    cases hr : runs (k.look ch) (spentE Bk a) with
    | none =>
      rw [hr] at e2
      cases e2
    | some sp' =>
      rw [hr] at e2
      have es : sp = castAll h₂ sp' := Option.some.inj e2
      cases hcx : lend (k.look ch) p.carries (carryE Bk a) with
      | error er =>
        rw [hcx] at e3
        show (none : Option p.Coins) = ((runs (k.look ch) (carryE Bk a)).map fun ca =>
          (get k, castAll h₂ sp', castAll h₃ ca))
        cases hr3 : runs (k.look ch) (carryE Bk a) with
        | none => rfl
        | some ca' =>
          rw [hr3] at e3
          cases e3
      | ok ca =>
        rw [hcx] at e3
        cases hr3 : runs (k.look ch) (carryE Bk a) with
        | none =>
          rw [hr3] at e3
          cases e3
        | some ca' =>
          rw [hr3] at e3
          have ec : ca = castAll h₃ ca' := Option.some.inj e3
          rw [es, ec]
          rfl

/-! ## 3 The cell -/

section
variable {F : FileDescription Xi} {Bk : ProverCoinCounts}

/-- **A part as a cell**, at a stretch's rounds, challenges and positions. `dry`: the state and the
challenges before the part; what the part has been shown is not taken from `dry` but from what has
been produced (`Laid.front`), and so are the opened columns that the part is handed: those that
`Laid.front` holds for the reads of the declared rounds `pre` (`Before.opened`, `readsBefore`,
Honest/Side.lean), as `partShows` has them. `st`: the stored tables' columns that go into
`Laid.front`. `ft`: the number in the label of the chain's first own tree. `pb`, `get` and `put` are
free here: the lemmas tie them (`hpb`: `pb` is the public value of the input; `hrow`: a lens on the
part's own row).
`speaks` and `tell`: what the part shows and what its simulator outputs, each through `zipLen`:
`none` at another number of rounds than challenges. `live`: the verifier has not rejected in chain
number `ch`. `sub`: the stretch's fixed substitutes (`Stretch.sub`). `On`: the side's parameter; the
cell's `On` is that parameter together with `Before.holds` at what has been produced before.

The opened columns are laid from `Laid.front` by the formula of `Good.exact`'s premise, so that
premise holds here by `rfl`. That these functions, folded over a file's acts, lay what a run of
`runC` shows is `model` (Honest/Law/Rule/Model.lean), under its own hypotheses; nothing in this file
says it. That the state which `midAtW` or `midSharedAtW` returns in front of a part holds these
columns, at `Run.beforeAt`, is the proposition `Tie1` (Honest/Ties.lean), which no theorem of this
library proves; with the `Before` written out: `tie_first`, `tie_shared`, `tie_second_at`
(Honest/Law/Rule/OpenedRun.lean), under their premises. -/
noncomputable def cellOf (φ : Face V W Pb) (σ : Side S Cl V W Y Pb) (u : Member V W Y Pb) (pb : Pb)
    (ch ft : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (dry : Mid W Y)
    (st : List (Nat × Nat × List UInt64)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (get : Coins Bk → Cs u.part.takes)
    (put : Cs u.part.takes → Coins Bk → Coins Bk)
    (h₂ : (spentE Bk ⟨σ.block.place, u.number⟩).map Ahead.named = u.part.spends)
    (h₃ : (carryE Bk ⟨σ.block.place, u.number⟩).map Ahead.named = u.part.carries)
    (On : CsAll u.part.carries → Mid W Y → Before → Prop) :
    Cell Bk (Stand F) (List (Shown × Fmt.Drawn)) where
  addr := ⟨σ.block.place, u.number⟩
  chain := ch
  takes := u.part.takes
  get := get
  put := put
  speaks := fun c sp ca Z => (σ.shows φ u (c, castAll h₂ sp, castAll h₃ ca)
    ⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
      (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩ ds asks).bind (zipLen ds)
  live := fun Z => Z.live ch
  sub := Stretch.sub ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks, none⟩
  simTakes := u.sim.takes
  tell := fun Z c => (u.sim.tell pb (Z.laid.front ch st) ds asks c).bind (zipLen ds)
  On := fun ca Z => On (castAll h₃ ca) ⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
        (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩
      (Z.laid.front ch st) ∧
    (Z.laid.front ch st).holds ch ft (u.rounds.map (·.1)) ds = true
  add := fun Z new => { Z with laid := Z.laid.add ch new }

variable (φ : Face V W Pb) (σ : Side S Cl V W Y Pb) (u : Member V W Y Pb) (pb : Pb) (ch ft : Nat)
  (pre : List (Nat × Nat × List Fmt.DeclaredRound))
  (dry : Mid W Y) (st : List (Nat × Nat × List UInt64)) (ds : List Fmt.Drawn)
  (asks : List (List (List Nat))) (get : Coins Bk → Cs u.part.takes)
  (put : Cs u.part.takes → Coins Bk → Coins Bk)
  (h₂ : (spentE Bk ⟨σ.block.place, u.number⟩).map Ahead.named = u.part.spends)
  (h₃ : (carryE Bk ⟨σ.block.place, u.number⟩).map Ahead.named = u.part.carries)
  (On : CsAll u.part.carries → Mid W Y → Before → Prop)

/-! ## 4 The cell's stage is the stretch's -/

/- **The cell's stage is the stretch's stage.** `hrow`: `get` and `put` are a lens on the part's
own row (`RowAt`, Honest/Law/Rule/LentAt.lean). `hdue`: the part takes the count that the book has
for it. `hR`: `R` at the part's address is `partShows` at `pre` and `dry`. -/
theorem cell_stage (x : Xi) (R : RealAt Bk)
    (hrow : RowAt Bk ⟨σ.block.place, u.number⟩ ch u.part.takes get put)
    (hdue : u.part.takes = dueAt (Bk.rowsOf ch) ⟨σ.block.place, u.number⟩)
    (hR : R ch ⟨σ.block.place, u.number⟩ = partShows φ σ u Bk ch pre dry) :
    (cellOf (F := F) φ σ u pb ch ft pre dry st ds asks get put h₂ h₃ On).stage =
      Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks,
        some ⟨u.sim.takes, u.sim.tell pb⟩⟩ : Act F) := by
  have hshow : ∀ (k : Coins Bk) (Z : Stand F),
      (cellOf (F := F) φ σ u pb ch ft pre dry st ds asks get put h₂ h₃ On).stage.shows k Z =
        (Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks,
          some ⟨u.sim.takes, u.sim.tell pb⟩⟩ : Act F)).shows k Z := by
    intro k Z
    have hl := lendPart_opt u.part hrow hdue h₂ h₃ k
    show (if Z.live ch = true then
        (((some (get k)).bind fun c => (runs (k.look ch) (spentE Bk ⟨σ.block.place, u.number⟩)).bind
          fun sp => (runs (k.look ch) (carryE Bk ⟨σ.block.place, u.number⟩)).bind fun ca =>
            (σ.shows φ u (c, castAll h₂ sp, castAll h₃ ca)
              ⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
                (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩ ds
              asks).bind (zipLen ds)).getD [])
        else Stretch.sub ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks, none⟩) =
      if Z.live ch = true then
        (if (some (⟨u.sim.takes, u.sim.tell pb⟩ : Teller)).isSome = true then
          ((R ch ⟨σ.block.place, u.number⟩ k (Z.laid.front ch st) ds asks).bind (zipLen ds)).getD []
        else _) else Stretch.sub ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks,
          some ⟨u.sim.takes, u.sim.tell pb⟩⟩
    have hsome : (some (⟨u.sim.takes, u.sim.tell pb⟩ : Teller)).isSome = true := rfl
    rw [if_pos hsome, hR]
    unfold partShows
    rw [hl]
    cases runs (k.look ch) (spentE Bk ⟨σ.block.place, u.number⟩) with
    | none => rfl
    | some sp =>
      cases runs (k.look ch) (carryE Bk ⟨σ.block.place, u.number⟩) with
      | none => rfl
      | some ca => rfl
  have htell : ∀ Z : Stand F,
      (cellOf (F := F) φ σ u pb ch ft pre dry st ds asks get put h₂ h₃ On).stage.tells Z =
        (Act.stage x st R (.lay ⟨ch, ⟨σ.block.place, u.number⟩, u.rounds, ds, asks,
          some ⟨u.sim.takes, u.sim.tell pb⟩⟩ : Act F)).tells Z := by
    intro Z
    cases hz : Z.live ch with
    | true =>
      show (if Z.live ch = true then _ else _) = Stretch.lay _ (Z.live ch) _
      rw [hz]
      rfl
    | false =>
      show (if Z.live ch = true then _ else _) = Stretch.lay _ (Z.live ch) _
      rw [hz]
      rfl
  have e1 := funext fun k => funext fun Z => hshow k Z
  have e2 := funext htell
  show (⟨_, _, _⟩ : Kit.Stage (Coins Bk) (Stand F) (List (Shown × Fmt.Drawn))) = ⟨_, _, _⟩
  exact congr (congr (congrArg Kit.Stage.mk e1) e2) rfl

/-! ## 5 The two conditions -/

section
variable {ord : List Place} {A B : Coins Bk → S → Mid W Y → Env → Prop}
  {OnG : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop}
  {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}

/-- **The spender's condition.** -/
theorem cell_exact (hG : Good pre φ σ Bk ord ch ft A B OnG bud) (hu : u ∈ σ.members)
    (hpb : pb = φ.pub dry.st.input) (hfit : drawsFit (u.rounds.map (·.1)) ds = true)
    (hbud : bud u.number ds asks)
    (hstop : u.part.stopAt (φ.sees dry.st.input) dry.loc ds ≠ some .hid) :
    ∀ ca (Z : Stand F),
      (cellOf (F := F) φ σ u pb ch ft pre dry st ds asks get put h₂ h₃ (OnG u)).On ca Z →
      (unif (Cs u.part.takes × CsAll ((spentE Bk ⟨σ.block.place, u.number⟩).map Ahead.named))).map
        (fun c => (cellOf (F := F) φ σ u pb ch ft pre dry st ds asks get put h₂ h₃ (OnG u)).speaks
          c.1 c.2 ca Z) =
      (unif (Cs u.sim.takes)).map
        ((cellOf (F := F) φ σ u pb ch ft pre dry st ds asks get put h₂ h₃ (OnG u)).tell Z) := by
  intro ca Z hOn
  have h := hG.exact u hu (castAll h₃ ca) ⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
      (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩
    (Z.laid.front ch st) ds asks hOn.1 rfl rfl hfit hbud hOn.2 hstop
  have h' := congrArg (PMF.map fun o : Option (List Shown) => o.bind (zipLen ds)) h
  rw [PMF.map_comp, PMF.map_comp] at h'
  have hc := map_cast h₂ (d := u.part.takes) fun c : Cs u.part.takes × CsAll u.part.spends =>
    (σ.shows φ u (c.1, c.2, castAll h₃ ca) ⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
      (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩ ds
      asks).bind (zipLen ds)
  refine hc.trans (h'.trans ?_)
  rw [hpb]
  rfl

/-- **The owner's condition.** `Good.fresh` runs over every state, so over every value of its field
`opened` (Honest/Side.lean, Limits); this lemma uses it at the one value that the cell lays. -/
theorem cell_fresh (hG : Good pre φ σ Bk ord ch ft A B OnG bud) (hu : u ∈ σ.members)
    (hfit : drawsFit (u.rounds.map (·.1)) ds = true) (hbud : bud u.number ds asks)
    (hstop : u.part.stopAt (φ.sees dry.st.input) dry.loc ds ≠ some .hid) :
    ∀ (p : Addr) sp ca (Z : Stand F),
      (unif (Cs u.part.takes)).map (fun c => (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p),
        (cellOf (F := F) φ σ u pb ch ft pre dry st ds asks get put h₂ h₃ (OnG u)).speaks c sp ca
          Z,
        cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a => (some a.1,
        (cellOf (F := F) φ σ u pb ch ft pre dry st ds asks get put h₂ h₃ (OnG u)).speaks a.2 sp ca
          Z,
        cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p)) := by
  intro p sp ca Z
  exact fresh_map (hG.fresh u hu p (castAll h₂ sp) (castAll h₃ ca)
    ⟨dry.st, dry.loc, (Z.laid.front ch st).seen,
      (Z.laid.front ch st).opened (readsBefore pre (Z.laid.front ch st))⟩ ds asks hfit hbud hstop)
    fun o : Option (List Shown) => o.bind (zipLen ds)

end

end

end ProofFile.Honest

#print axioms ProofFile.Honest.map_cast
#print axioms ProofFile.Honest.lend_cast
#print axioms ProofFile.Honest.lendPart_opt
#print axioms ProofFile.Honest.cell_stage
#print axioms ProofFile.Honest.cell_exact
#print axioms ProofFile.Honest.cell_fresh
#print axioms ProofFile.Honest.castAll
#print axioms ProofFile.Honest.cellOf
